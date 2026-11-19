// Main-thread StudioTransport proxy talking to `wasmWorker.ts` over zero-copy
// transferable ArrayBuffers so heavy Lean WASM remeshes never block 60fps rendering.

import type { JsonInputEvent } from '../gsir/types';
import type { LeanPresetCatalogItem, StudioTransport } from './types';
import { WasmTransport } from './wasm';

export interface WasmWorkerTransportOptions {
  /** Absolute or page-relative URL to grassmann.mjs / grassmann.<hash>.mjs / grassmann.wasm */
  wasmUrl: string;
  /** Optional explicit .wasm binary URL override (e.g. content-fingerprinted grassmann.<hash>.wasm) */
  wasmBinaryUrl?: string;
  /** Optional human-readable hash tag from wasm-manifest.json */
  manifestHash?: string;
}

interface PendingRpc {
  resolve: (value: unknown) => void;
  reject: (err: Error) => void;
}

export class WasmWorkerTransport implements StudioTransport {
  readonly kind = 'wasm' as const;
  readonly label: string;

  private readonly wasmUrl: string;
  private readonly wasmBinaryUrl?: string;
  private worker: Worker | null = null;
  private fallback: WasmTransport | null = null;
  private nextId = 1;
  private readonly pending = new Map<number, PendingRpc>();
  private disposed = false;

  constructor(options: WasmWorkerTransportOptions) {
    this.wasmUrl = options.wasmUrl;
    this.wasmBinaryUrl = options.wasmBinaryUrl;
    this.label = options.manifestHash
      ? `Lean WASM Worker (${options.manifestHash})`
      : `Lean WASM Worker (${options.wasmUrl})`;
  }

  async connect(signal?: AbortSignal): Promise<Uint8Array> {
    if (this.disposed) {
      throw new Error('WasmWorkerTransport is disposed');
    }

    const baseHref =
      typeof window !== 'undefined' && window.location?.href ? window.location.href : undefined;
    const resolvedWasmUrl = baseHref ? new URL(this.wasmUrl, baseHref).href : this.wasmUrl;
    const resolvedBinaryUrl = this.wasmBinaryUrl
      ? baseHref
        ? new URL(this.wasmBinaryUrl, baseHref).href
        : this.wasmBinaryUrl
      : undefined;

    // Fallback to direct main-thread WasmTransport if Web Workers are unavailable (e.g. Node/Vitest)
    if (typeof Worker === 'undefined') {
      this.fallback = new WasmTransport({
        wasmUrl: resolvedWasmUrl,
        wasmBinaryUrl: resolvedBinaryUrl,
      });
      return this.fallback.connect(signal);
    }

    const worker = new Worker(new URL('./wasmWorker.ts', import.meta.url), { type: 'module' });
    this.worker = worker;

    worker.onmessage = (ev: MessageEvent) => {
      const msg = ev.data as {
        id: number;
        ok: boolean;
        buffer?: ArrayBuffer;
        catalog?: LeanPresetCatalogItem[];
        error?: string;
      };
      const entry = this.pending.get(msg.id);
      if (!entry) return;
      this.pending.delete(msg.id);
      if (!msg.ok) {
        entry.reject(new Error(msg.error ?? 'WASM worker call failed'));
        return;
      }
      if (msg.buffer instanceof ArrayBuffer) {
        entry.resolve(new Uint8Array(msg.buffer));
      } else if (msg.catalog !== undefined) {
        entry.resolve(msg.catalog);
      } else {
        entry.resolve(undefined);
      }
    };

    worker.onerror = (ev) => {
      const err = new Error(ev.message || 'WASM worker crashed');
      for (const [, p] of this.pending) {
        p.reject(err);
      }
      this.pending.clear();
    };

    try {
      return (await this.rpc(
        { op: 'connect', wasmUrl: resolvedWasmUrl, wasmBinaryUrl: resolvedBinaryUrl },
        [],
        signal
      )) as Uint8Array;
    } catch (err) {
      this.dispose();
      throw err;
    }
  }

  async dispatchBin(event: Uint8Array): Promise<Uint8Array> {
    if (this.fallback) return this.fallback.dispatchBin(event);
    const copy = event.slice();
    return (await this.rpc({ op: 'dispatchBin', buffer: copy.buffer }, [copy.buffer])) as Uint8Array;
  }

  async dispatchJson(event: JsonInputEvent): Promise<Uint8Array> {
    if (this.fallback) return this.fallback.dispatchJson(event);
    return (await this.rpc({ op: 'dispatchJson', event })) as Uint8Array;
  }

  async getFrame(): Promise<Uint8Array> {
    if (this.fallback) return this.fallback.getFrame();
    return (await this.rpc({ op: 'getFrame' })) as Uint8Array;
  }

  async getPresetCatalog(): Promise<LeanPresetCatalogItem[]> {
    if (this.fallback) return this.fallback.getPresetCatalog();
    return (await this.rpc({ op: 'getPresetCatalog' })) as LeanPresetCatalogItem[];
  }

  dispose(): void {
    this.disposed = true;
    if (this.fallback) {
      this.fallback.dispose();
      this.fallback = null;
    }
    if (this.worker) {
      try {
        this.worker.postMessage({ id: 0, op: 'dispose' });
      } catch {
        // Ignore postMessage failure on terminated worker
      }
      this.worker.terminate();
      this.worker = null;
    }
    const err = new Error('WasmWorkerTransport disposed');
    for (const [, p] of this.pending) {
      p.reject(err);
    }
    this.pending.clear();
  }

  private rpc(
    payload: Record<string, unknown>,
    transfer: Transferable[] = [],
    signal?: AbortSignal
  ): Promise<unknown> {
    if (!this.worker) {
      return Promise.reject(new Error('WASM worker is not connected'));
    }
    const id = this.nextId++;
    return new Promise((resolve, reject) => {
      if (signal?.aborted) {
        reject(new Error('Aborted'));
        return;
      }
      const onAbort = () => {
        this.pending.delete(id);
        reject(new Error('WASM worker request timed out / aborted'));
      };
      signal?.addEventListener('abort', onAbort, { once: true });
      this.pending.set(id, {
        resolve: (val) => {
          signal?.removeEventListener('abort', onAbort);
          resolve(val);
        },
        reject: (err) => {
          signal?.removeEventListener('abort', onAbort);
          reject(err);
        },
      });
      this.worker!.postMessage({ id, ...payload }, transfer);
    });
  }
}

// Lean WASM C ABI Transport
// Talks directly to compiled Lean 4.36 Grassmann WASM via the canonical C ABI:
//   grassmann_initialize() -> i32   (called automatically when exported!)
//   grassmann_studio_create() -> u64
//   grassmann_studio_destroy(u64)
//   grassmann_studio_dispatch_bin(u64, eventPtr, eventLen, outPtr, outCap, outLenPtr) -> i32
//   grassmann_studio_dispatch_json(u64, jsonPtr, jsonLen, outPtr, outCap, outLenPtr) -> i32
//   grassmann_studio_get_frame(u64, outPtr, outCap, outLenPtr) -> i32  (#17 Fix #2)
//
// Supports BOTH:
//   1. Emscripten ES module factories (`grassmann_raw.mjs` / `grassmann_wasm.mjs` exporting HEAPU8 + _grassmann_*)
//   2. Standalone `.wasm` modules (`WebAssembly.instantiate`)
//
// Zero per-frame heap allocations: reuses a single caller-owned WASM output buffer, growing
// once on GSIR_ERR_BUF_SMALL (-3) and reading via grassmann_studio_get_frame (never double-mutating!).

import { encodeTick } from '../gsir/encoder';
import { GsirStatus, type JsonInputEvent } from '../gsir/types';
import type { LeanPresetCatalogItem, StudioTransport } from './types';

export interface GrassmannWasmExports {
  memory?: WebAssembly.Memory;
  wasmMemory?: WebAssembly.Memory;
  HEAPU8?: Uint8Array;
  malloc?: (bytes: number) => number;
  _malloc?: (bytes: number) => number;
  free?: (ptr: number) => void;
  _free?: (ptr: number) => void;
  grassmann_initialize?: () => number;
  _grassmann_initialize?: () => number;
  grassmann_studio_create?: () => bigint | number;
  _grassmann_studio_create?: () => bigint | number;
  grassmann_studio_destroy?: (session: bigint) => void;
  _grassmann_studio_destroy?: (session: bigint) => void;
  grassmann_studio_dispatch_bin?: (
    session: bigint,
    eventPtr: number,
    eventLen: number,
    outPtr: number,
    outCap: number,
    outLenPtr: number
  ) => number;
  _grassmann_studio_dispatch_bin?: (
    session: bigint,
    eventPtr: number,
    eventLen: number,
    outPtr: number,
    outCap: number,
    outLenPtr: number
  ) => number;
  grassmann_studio_dispatch_json?: (
    session: bigint,
    jsonPtr: number,
    jsonLen: number,
    outPtr: number,
    outCap: number,
    outLenPtr: number
  ) => number;
  _grassmann_studio_dispatch_json?: (
    session: bigint,
    jsonPtr: number,
    jsonLen: number,
    outPtr: number,
    outCap: number,
    outLenPtr: number
  ) => number;
  grassmann_studio_get_frame?: (
    session: bigint,
    outPtr: number,
    outCap: number,
    outLenPtr: number
  ) => number;
  _grassmann_studio_get_frame?: (
    session: bigint,
    outPtr: number,
    outCap: number,
    outLenPtr: number
  ) => number;
  grassmann_studio_preset_catalog?: (
    outPtr: number,
    outCap: number,
    outLenPtr: number
  ) => number;
  _grassmann_studio_preset_catalog?: (
    outPtr: number,
    outCap: number,
    outLenPtr: number
  ) => number;
}

export interface WasmTransportOptions {
  /** URL to compiled grassmann.wasm or Emscripten grassmann.mjs (default: './wasm/grassmann.mjs') */
  wasmUrl?: string;
  /** Optional explicit .wasm binary URL override (e.g. content-fingerprinted grassmann.<hash>.wasm from manifest) */
  wasmBinaryUrl?: string;
  /** Optional custom exports loader (used by tests or embedded Emscripten glue) */
  loadExports?: () => Promise<GrassmannWasmExports>;
  /** Initial caller-owned output buffer capacity in bytes (default: 256 KB) */
  initialOutCap?: number;
  /** Initial reusable input scratch buffer capacity in bytes (default: 16 KB) */
  initialInCap?: number;
}

export interface WasmManifest {
  version: number;
  hash: string;
  mjs?: string;
  wasm?: string;
  loaderFile?: string;
  wasmFile?: string;
  bytes?: number;
  gzipBytes?: number;
  presetCount?: number;
}

/**
 * Resolves a content-fingerprinted WASM manifest (cache: no-store) when available
 * so warm browser caches always load the newest fingerprinted grassmann.<hash>.{mjs,wasm}.
 * Supports both `{ loaderFile, wasmFile }` (build-wasm.sh) and `{ mjs, wasm }` formats.
 */
export async function fetchWasmManifest(
  manifestUrl = './wasm/wasm-manifest.json',
  signal?: AbortSignal
): Promise<{ mjsUrl: string; wasmUrl: string; hash: string } | null> {
  try {
    const baseHref =
      typeof globalThis !== 'undefined' && 'location' in globalThis && globalThis.location?.href
        ? globalThis.location.href
        : undefined;
    const resolvedManifest = baseHref ? new URL(manifestUrl, baseHref).href : manifestUrl;
    const resp = await fetch(resolvedManifest, { cache: 'no-store', signal });
    const ct = resp.headers.get('content-type') ?? '';
    if (!resp.ok || ct.includes('text/html')) return null;
    const data = (await resp.json()) as Partial<WasmManifest>;
    const mjsRel = data.loaderFile ?? data.mjs;
    const wasmRel = data.wasmFile ?? data.wasm;
    if (typeof mjsRel !== 'string' || typeof wasmRel !== 'string') return null;
    const mjsUrl = new URL(mjsRel, resolvedManifest).href;
    const wasmUrl = new URL(wasmRel, resolvedManifest).href;
    return { mjsUrl, wasmUrl, hash: data.hash ?? 'manifest' };
  } catch {
    return null;
  }
}

interface ResolvedExports {
  getMemoryBuffer: () => ArrayBuffer;
  malloc: (bytes: number) => number;
  free: (ptr: number) => void;
  initialize?: () => number;
  create: () => bigint;
  destroy: (session: bigint) => void;
  dispatchBin: (
    session: bigint,
    eventPtr: number,
    eventLen: number,
    outPtr: number,
    outCap: number,
    outLenPtr: number
  ) => number;
  dispatchJson: (
    session: bigint,
    jsonPtr: number,
    jsonLen: number,
    outPtr: number,
    outCap: number,
    outLenPtr: number
  ) => number;
  getFrame: (session: bigint, outPtr: number, outCap: number, outLenPtr: number) => number;
  presetCatalog?: (outPtr: number, outCap: number, outLenPtr: number) => number;
}

const textEncoder = new TextEncoder();
const textDecoder = new TextDecoder('utf-8');

function resolveExports(raw: GrassmannWasmExports): ResolvedExports {
  const malloc = raw.malloc ?? raw._malloc;
  const free = raw.free ?? raw._free;
  const initialize = raw.grassmann_initialize ?? raw._grassmann_initialize;
  const createRaw = raw.grassmann_studio_create ?? raw._grassmann_studio_create;
  const destroy = raw.grassmann_studio_destroy ?? raw._grassmann_studio_destroy;
  const dispatchBin = raw.grassmann_studio_dispatch_bin ?? raw._grassmann_studio_dispatch_bin;
  const dispatchJson = raw.grassmann_studio_dispatch_json ?? raw._grassmann_studio_dispatch_json;
  const getFrame = raw.grassmann_studio_get_frame ?? raw._grassmann_studio_get_frame;
  const presetCatalog = raw.grassmann_studio_preset_catalog ?? raw._grassmann_studio_preset_catalog;

  const hasMem = Boolean(raw.memory || raw.wasmMemory || raw.HEAPU8);
  if (!hasMem || !malloc || !free || !createRaw || !destroy || !dispatchBin || !dispatchJson || !getFrame) {
    throw new Error(
      'grassmann.wasm is missing one or more required C ABI exports: ' +
        'memory/HEAPU8, malloc, free, grassmann_studio_{create,destroy,dispatch_bin,dispatch_json,get_frame}'
    );
  }

  return {
    getMemoryBuffer: () => {
      if (raw.memory) return raw.memory.buffer;
      if (raw.wasmMemory) return raw.wasmMemory.buffer;
      if (raw.HEAPU8) return raw.HEAPU8.buffer as ArrayBuffer;
      throw new Error('WASM linear memory unavailable');
    },
    malloc,
    free,
    initialize,
    create: () => BigInt(createRaw()),
    destroy,
    dispatchBin,
    dispatchJson,
    getFrame,
    presetCatalog,
  };
}

export class WasmTransport implements StudioTransport {
  readonly kind = 'wasm' as const;
  readonly label: string;

  private readonly wasmUrl: string;
  private readonly wasmBinaryUrl?: string;
  private readonly loadExportsFn?: () => Promise<GrassmannWasmExports>;
  private exports: ResolvedExports | null = null;
  private session = 0n;

  // Caller-owned reusable buffers in WASM linear memory
  private inPtr = 0;
  private inCap = 0;
  private outPtr = 0;
  private outCap = 0;
  private outLenPtr = 0;

  private readonly initialOutCap: number;
  private readonly initialInCap: number;

  constructor(options: WasmTransportOptions = {}) {
    this.wasmUrl = options.wasmUrl ?? './grassmann.wasm';
    this.wasmBinaryUrl = options.wasmBinaryUrl;
    this.loadExportsFn = options.loadExports;
    this.initialOutCap = Math.max(4096, options.initialOutCap ?? 256 * 1024);
    this.initialInCap = Math.max(1024, options.initialInCap ?? 16 * 1024);
    this.label = `Lean WASM (${this.wasmUrl})`;
  }

  async connect(signal?: AbortSignal): Promise<Uint8Array> {
    if (this.exports && this.session !== 0n) {
      return this.getFrame();
    }

    const baseHref =
      typeof globalThis !== 'undefined' && 'location' in globalThis && globalThis.location?.href
        ? globalThis.location.href
        : undefined;

    let raw: GrassmannWasmExports;
    if (this.loadExportsFn) {
      raw = await this.loadExportsFn();
    } else if (this.wasmUrl.endsWith('.mjs') || this.wasmUrl.endsWith('.js')) {
      // Resolve relative to document/worker URL (NOT bundled /assets/index-*.js!) so Vite/Vercel builds load /wasm/*.mjs cleanly
      const resolvedUrl = baseHref ? new URL(this.wasmUrl, baseHref).href : this.wasmUrl;
      const resolvedBinaryUrl = this.wasmBinaryUrl
        ? baseHref
          ? new URL(this.wasmBinaryUrl, baseHref).href
          : this.wasmBinaryUrl
        : undefined;
      // Pre-flight check ensures Vite SPA fallback HTML doesn't produce a browser MIME error
      const probe = await fetch(resolvedUrl, { method: 'GET', signal });
      const ct = probe.headers.get('content-type') ?? '';
      if (!probe.ok || ct.includes('text/html')) {
        throw new Error(`WASM JS loader not found at ${resolvedUrl} (HTTP ${probe.status}, ${ct || 'unknown'})`);
      }
      const modNs = (await import(/* @vite-ignore */ resolvedUrl)) as {
        default?: (opts?: Record<string, unknown>) => Promise<GrassmannWasmExports>;
        loadGrassmannWasm?: (opts?: Record<string, unknown>) => Promise<{ mod: GrassmannWasmExports }>;
      };
      const moduleOpts = {
        locateFile: (file: string) => {
          if (resolvedBinaryUrl && file.endsWith('.wasm')) {
            return resolvedBinaryUrl;
          }
          return new URL(file, resolvedUrl).href;
        },
      };
      if (typeof modNs.default === 'function') {
        raw = await modNs.default(moduleOpts);
      } else if (typeof modNs.loadGrassmannWasm === 'function') {
        const loaded = await modNs.loadGrassmannWasm(moduleOpts);
        raw = loaded.mod;
      } else {
        throw new Error(`Emscripten glue module at ${resolvedUrl} has no default factory export`);
      }
    } else {
      const resolvedUrl = baseHref ? new URL(this.wasmUrl, baseHref).href : this.wasmUrl;
      const resp = await fetch(resolvedUrl, { signal });
      const ct = resp.headers.get('content-type') ?? '';
      if (!resp.ok || ct.includes('text/html')) {
        throw new Error(`Failed to fetch ${resolvedUrl} (HTTP ${resp.status})`);
      }
      const bytes = await resp.arrayBuffer();
      const instantiated = await WebAssembly.instantiate(bytes, {
        env: {
          emscripten_notify_memory_growth: () => {
            // Views always re-read getMemoryBuffer() dynamically
          },
        },
      });
      raw = instantiated.instance.exports as unknown as GrassmannWasmExports;
    }

    const ex = resolveExports(raw);
    if (ex.initialize) {
      const initRc = ex.initialize();
      if (initRc !== GsirStatus.OK) {
        throw new Error(`grassmann_initialize failed with status ${initRc}`);
      }
    }

    this.exports = ex;
    this.session = ex.create();
    if (this.session === 0n) {
      throw new Error('grassmann_studio_create returned null session handle (0)');
    }

    this.outLenPtr = ex.malloc(8);
    this.ensureInCapacity(this.initialInCap);
    this.ensureOutCapacity(this.initialOutCap);

    // Fetch initial full snapshot frame
    return this.dispatchBin(encodeTick(0, 0, true));
  }

  async dispatchBin(event: Uint8Array): Promise<Uint8Array> {
    const ex = this.requireReady();
    this.ensureInCapacity(event.byteLength);
    new Uint8Array(ex.getMemoryBuffer(), this.inPtr, event.byteLength).set(event);

    const rc = ex.dispatchBin(
      this.session,
      this.inPtr,
      event.byteLength,
      this.outPtr,
      this.outCap,
      this.outLenPtr
    );
    return this.finalizeFrameCall(rc, 'dispatch_bin');
  }

  async dispatchJson(event: JsonInputEvent): Promise<Uint8Array> {
    const ex = this.requireReady();
    const jsonBytes = textEncoder.encode(JSON.stringify(event));
    this.ensureInCapacity(jsonBytes.byteLength);
    new Uint8Array(ex.getMemoryBuffer(), this.inPtr, jsonBytes.byteLength).set(jsonBytes);

    const rc = ex.dispatchJson(
      this.session,
      this.inPtr,
      jsonBytes.byteLength,
      this.outPtr,
      this.outCap,
      this.outLenPtr
    );
    return this.finalizeFrameCall(rc, 'dispatch_json');
  }

  async getFrame(): Promise<Uint8Array> {
    const ex = this.requireReady();
    const rc = ex.getFrame(this.session, this.outPtr, this.outCap, this.outLenPtr);
    return this.finalizeFrameCall(rc, 'get_frame');
  }

  async getPresetCatalog(): Promise<LeanPresetCatalogItem[]> {
    const ex = this.requireReady();
    if (!ex.presetCatalog) return [];
    const lenPtr = ex.malloc(8);
    try {
      ex.presetCatalog(0, 0, lenPtr);
      const len = new DataView(ex.getMemoryBuffer(), lenPtr, 4).getUint32(0, true);
      if (len === 0) return [];
      const buf = ex.malloc(len);
      try {
        const rc = ex.presetCatalog(buf, len, lenPtr);
        if (rc !== GsirStatus.OK) return [];
        const bytes = new Uint8Array(ex.getMemoryBuffer(), buf, len).slice();
        const parsed = JSON.parse(textDecoder.decode(bytes));
        return Array.isArray(parsed) ? (parsed as LeanPresetCatalogItem[]) : [];
      } finally {
        ex.free(buf);
      }
    } finally {
      ex.free(lenPtr);
    }
  }

  dispose(): void {
    if (this.exports) {
      if (this.session !== 0n) {
        this.exports.destroy(this.session);
        this.session = 0n;
      }
      if (this.inPtr !== 0) {
        this.exports.free(this.inPtr);
        this.inPtr = 0;
        this.inCap = 0;
      }
      if (this.outPtr !== 0) {
        this.exports.free(this.outPtr);
        this.outPtr = 0;
        this.outCap = 0;
      }
      if (this.outLenPtr !== 0) {
        this.exports.free(this.outLenPtr);
        this.outLenPtr = 0;
      }
      this.exports = null;
    }
  }

  private requireReady(): ResolvedExports {
    if (!this.exports || this.session === 0n) {
      throw new Error('WasmTransport is not connected');
    }
    return this.exports;
  }

  private ensureInCapacity(needed: number): void {
    const ex = this.requireReady();
    if (needed <= this.inCap && this.inPtr !== 0) return;
    if (this.inPtr !== 0) ex.free(this.inPtr);
    const nextCap = Math.max(needed, this.inCap * 2, 4096);
    this.inPtr = ex.malloc(nextCap);
    this.inCap = nextCap;
  }

  private ensureOutCapacity(needed: number): void {
    const ex = this.requireReady();
    if (needed <= this.outCap && this.outPtr !== 0) return;
    if (this.outPtr !== 0) ex.free(this.outPtr);
    const nextCap = (Math.max(needed, this.outCap * 2, 4096) + 7) & ~7;
    this.outPtr = ex.malloc(nextCap);
    this.outCap = nextCap;
  }

  private readOutLen(): number {
    const ex = this.requireReady();
    const dv = new DataView(ex.getMemoryBuffer(), this.outLenPtr, 4);
    return dv.getUint32(0, true);
  }

  /**
   * Handles C ABI return codes.
   * On GSIR_ERR_BUF_SMALL (-3): grows the reusable outBuf ONCE and calls
   * grassmann_studio_get_frame (NEVER re-invoking dispatch_* so state is never double-mutated!).
   */
  private finalizeFrameCall(rc: number, opName: string): Uint8Array {
    const ex = this.requireReady();
    let status = rc;

    if (status === GsirStatus.ERR_BUF_SMALL) {
      const required = this.readOutLen();
      if (required === 0) {
        throw new Error(`WASM ${opName} returned GSIR_ERR_BUF_SMALL with required size 0`);
      }
      this.ensureOutCapacity(required);
      status = ex.getFrame(this.session, this.outPtr, this.outCap, this.outLenPtr);
    }

    if (status !== GsirStatus.OK) {
      throw new Error(`WASM ${opName} failed with status ${status}`);
    }

    const len = this.readOutLen();
    const copy = new Uint8Array(len);
    copy.set(new Uint8Array(ex.getMemoryBuffer(), this.outPtr, len));
    return copy;
  }
}

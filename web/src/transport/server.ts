// Native Lean `ga-server` HTTP + WebSocket Binary GSIR v1 Transport
// Default local dev URL: http://127.0.0.1:8787 (configurable via ?server=... or VITE_GA_SERVER_URL)
// Supports binary WebSocket streaming (ws://.../ws) with automatic HTTP fallback
// (POST /api/event/bin, POST /api/event/json, GET /api/frame).

import { encodeTick } from '../gsir/encoder';
import type { JsonInputEvent } from '../gsir/types';
import type { LeanPresetCatalogItem, LeanTourStopItem, StudioTransport } from './types';

export interface ServerTransportOptions {
  baseUrl?: string;
  preferWebSocket?: boolean;
  timeoutMs?: number;
}

interface PendingWsRequest {
  resolve: (bytes: Uint8Array) => void;
  reject: (err: Error) => void;
  timer: ReturnType<typeof setTimeout>;
}

function normalizeBaseUrl(raw: string): string {
  return raw.replace(/\/+$/, '');
}

function toWebSocketUrl(httpUrl: string): string {
  if (httpUrl.startsWith('https://')) return `wss://${httpUrl.slice(8)}/ws`;
  if (httpUrl.startsWith('http://')) return `ws://${httpUrl.slice(7)}/ws`;
  return `${httpUrl}/ws`;
}

export class ServerTransport implements StudioTransport {
  readonly kind = 'server' as const;
  readonly label: string;

  private readonly baseUrl: string;
  private readonly preferWebSocket: boolean;
  private readonly timeoutMs: number;
  private ws: WebSocket | null = null;
  private wsOpen = false;
  private readonly wsQueue: PendingWsRequest[] = [];
  private disposed = false;

  constructor(options: ServerTransportOptions = {}) {
    this.baseUrl = normalizeBaseUrl(options.baseUrl ?? 'http://127.0.0.1:8787');
    this.preferWebSocket = options.preferWebSocket ?? true;
    this.timeoutMs = options.timeoutMs ?? 8000;
    this.label = `Lean Native (${this.baseUrl})`;
  }

  async connect(signal?: AbortSignal): Promise<Uint8Array> {
    if (this.preferWebSocket && typeof WebSocket !== 'undefined') {
      try {
        await this.openWebSocket(signal);
        // Request full initial snapshot (#17 Fix #2)
        return await this.sendViaWs(encodeTick(0, 0, true));
      } catch {
        this.closeWebSocket();
        // Fall through cleanly to HTTP binary endpoints
      }
    }

    // HTTP connect: fetch initial full frame (forceFullSnapshot via POST /api/event/bin, fallback GET /api/frame)
    try {
      return await this.postBinaryHttp(encodeTick(0, 0, true), signal);
    } catch {
      return await this.getFrameHttp(signal);
    }
  }

  async dispatchBin(event: Uint8Array): Promise<Uint8Array> {
    if (this.wsOpen && this.ws && this.ws.readyState === WebSocket.OPEN) {
      return this.sendViaWs(event);
    }
    return this.postBinaryHttp(event);
  }

  async dispatchJson(event: JsonInputEvent): Promise<Uint8Array> {
    if (this.wsOpen && this.ws && this.ws.readyState === WebSocket.OPEN) {
      return this.sendViaWs(JSON.stringify(event));
    }
    return this.postJsonHttp(event);
  }

  async getFrame(): Promise<Uint8Array> {
    return this.getFrameHttp();
  }

  async getPresetCatalog(): Promise<LeanPresetCatalogItem[]> {
    try {
      const resp = await fetch(`${this.baseUrl}/api/presets`, {
        method: 'GET',
        headers: { Accept: 'application/json' },
      });
      if (!resp.ok) return [];
      const parsed = await resp.json();
      return Array.isArray(parsed) ? (parsed as LeanPresetCatalogItem[]) : [];
    } catch {
      return [];
    }
  }

  async getTourCatalog(): Promise<LeanTourStopItem[]> {
    try {
      const resp = await fetch(`${this.baseUrl}/api/tour`, {
        method: 'GET',
        headers: { Accept: 'application/json' },
      });
      if (!resp.ok) return [];
      const parsed = await resp.json();
      return Array.isArray(parsed) ? (parsed as LeanTourStopItem[]) : [];
    } catch {
      return [];
    }
  }

  dispose(): void {
    this.disposed = true;
    this.closeWebSocket();
  }

  private openWebSocket(signal?: AbortSignal): Promise<void> {
    return new Promise((resolve, reject) => {
      const wsUrl = toWebSocketUrl(this.baseUrl);
      const ws = new WebSocket(wsUrl);
      ws.binaryType = 'arraybuffer';

      const timer = setTimeout(() => {
        ws.close();
        reject(new Error(`WebSocket connection to ${wsUrl} timed out`));
      }, Math.min(2500, this.timeoutMs));

      const onAbort = () => {
        clearTimeout(timer);
        ws.close();
        reject(new Error('WebSocket connect aborted'));
      };
      signal?.addEventListener('abort', onAbort, { once: true });

      ws.onopen = () => {
        clearTimeout(timer);
        signal?.removeEventListener('abort', onAbort);
        this.ws = ws;
        this.wsOpen = true;
        resolve();
      };

      ws.onerror = () => {
        clearTimeout(timer);
        signal?.removeEventListener('abort', onAbort);
        if (!this.wsOpen) {
          reject(new Error(`WebSocket connection failed (${wsUrl})`));
        }
      };

      ws.onmessage = (ev) => {
        const next = this.wsQueue.shift();
        if (!next) return;
        clearTimeout(next.timer);
        if (ev.data instanceof ArrayBuffer) {
          next.resolve(new Uint8Array(ev.data));
        } else if (ev.data instanceof Blob) {
          ev.data.arrayBuffer().then(
            (ab) => next.resolve(new Uint8Array(ab)),
            (err) => next.reject(err instanceof Error ? err : new Error(String(err)))
          );
        } else {
          next.reject(new Error('Unexpected non-binary WebSocket message from ga-server'));
        }
      };

      ws.onclose = () => {
        this.wsOpen = false;
        this.ws = null;
        while (this.wsQueue.length > 0) {
          const item = this.wsQueue.shift()!;
          clearTimeout(item.timer);
          item.reject(new Error(this.disposed ? 'Transport disposed' : 'WebSocket disconnected'));
        }
      };
    });
  }

  private closeWebSocket(): void {
    if (this.ws) {
      try {
        this.ws.close();
      } catch {
        // ignore
      }
      this.ws = null;
    }
    this.wsOpen = false;
  }

  private sendViaWs(payload: Uint8Array | string): Promise<Uint8Array> {
    const ws = this.ws;
    if (!ws || ws.readyState !== WebSocket.OPEN) {
      return Promise.reject(new Error('WebSocket not open'));
    }
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        const idx = this.wsQueue.findIndex((q) => q.resolve === resolve);
        if (idx >= 0) this.wsQueue.splice(idx, 1);
        reject(new Error('ga-server WebSocket request timed out'));
      }, this.timeoutMs);

      this.wsQueue.push({ resolve, reject, timer });
      ws.send(payload);
    });
  }

  private async postBinaryHttp(event: Uint8Array, signal?: AbortSignal): Promise<Uint8Array> {
    const body = new Uint8Array(event.byteLength);
    body.set(event);
    const resp = await fetch(`${this.baseUrl}/api/event/bin`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/octet-stream' },
      body,
      signal,
    });
    if (!resp.ok) {
      throw new Error(`ga-server /api/event/bin failed (HTTP ${resp.status})`);
    }
    return new Uint8Array(await resp.arrayBuffer());
  }

  private async postJsonHttp(event: JsonInputEvent, signal?: AbortSignal): Promise<Uint8Array> {
    const resp = await fetch(`${this.baseUrl}/api/event/json`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(event),
      signal,
    });
    if (!resp.ok) {
      throw new Error(`ga-server /api/event/json failed (HTTP ${resp.status})`);
    }
    return new Uint8Array(await resp.arrayBuffer());
  }

  private async getFrameHttp(signal?: AbortSignal): Promise<Uint8Array> {
    const resp = await fetch(`${this.baseUrl}/api/frame`, {
      method: 'GET',
      headers: { Accept: 'application/octet-stream' },
      signal,
    });
    if (!resp.ok) {
      throw new Error(`ga-server /api/frame failed (HTTP ${resp.status})`);
    }
    return new Uint8Array(await resp.arrayBuffer());
  }
}

export * from './types';
export * from './server';
export * from './wasm';
export * from './wasmWorkerTransport';
export * from './eventQueue';
export * from './fixture';

import { ServerTransport } from './server';
import type { StudioTransport } from './types';
import { WasmTransport, fetchWasmManifest } from './wasm';
import { WasmWorkerTransport } from './wasmWorkerTransport';

export interface AutoConnectConfig {
  serverUrl?: string;
  wasmUrl?: string;
  preferred?: 'auto' | 'server' | 'wasm';
  /** Use dedicated Web Worker for WASM (default: true in browsers, keeps UI at 60fps during remeshes) */
  useWorker?: boolean;
}

export function resolveTransportConfigFromEnv(): AutoConnectConfig {
  const params = typeof window !== 'undefined' ? new URLSearchParams(window.location.search) : null;
  const envServer =
    (import.meta as unknown as { env?: Record<string, string | undefined> }).env?.VITE_GA_SERVER_URL;
  const envWasm =
    (import.meta as unknown as { env?: Record<string, string | undefined> }).env?.VITE_GRASSMANN_WASM_URL;

  const queryServer = params?.get('server') ?? undefined;
  const queryWasm = params?.get('wasm') ?? undefined;
  const queryMode = params?.get('transport') as 'auto' | 'server' | 'wasm' | null;
  const queryWorker = params?.get('worker');

  let preferred: 'auto' | 'server' | 'wasm' = queryMode ?? 'auto';
  if (queryServer && !queryMode) preferred = 'server';
  if (queryWasm && !queryMode) preferred = 'wasm';

  return {
    serverUrl: queryServer ?? envServer ?? 'http://127.0.0.1:8787',
    wasmUrl: queryWasm ?? envWasm ?? './wasm/grassmann.mjs',
    preferred,
    useWorker: queryWorker !== '0' && queryWorker !== 'false',
  };
}

/**
 * Tries Lean backends in priority order (never falling back to any JS GA math!).
 * Auto mode probes content-fingerprinted `./wasm/wasm-manifest.json` (cache: no-store) first,
 * then canonical `./wasm/grassmann.mjs`, running in a dedicated Web Worker so heavy remeshes
 * never block 60fps UI/orbit rendering, then falls back to native Lean `ga-server`.
 */
export async function connectLeanBackend(
  config: AutoConnectConfig
): Promise<{ transport: StudioTransport; initialFrame: Uint8Array }> {
  const useWorker = config.useWorker !== false && typeof Worker !== 'undefined';
  const makeWasm = (wasmUrl: string, wasmBinaryUrl?: string, manifestHash?: string): StudioTransport =>
    useWorker
      ? new WasmWorkerTransport({ wasmUrl, wasmBinaryUrl, manifestHash })
      : new WasmTransport({ wasmUrl, wasmBinaryUrl });

  const candidates: Array<() => StudioTransport> = [];

  if (config.preferred !== 'server') {
    // 1. Prefer content-fingerprinted WASM manifest (cache-busted, zero stale upgrades!)
    const manifest = await fetchWasmManifest('./wasm/wasm-manifest.json');
    if (manifest) {
      candidates.push(() => makeWasm(manifest.mjsUrl, manifest.wasmUrl, manifest.hash));
    }
    const wasmCandidates = Array.from(
      new Set([
        config.wasmUrl ?? './wasm/grassmann.mjs',
        './wasm/grassmann.mjs',
        './wasm/grassmann_raw.mjs',
        './wasm/grassmann.wasm',
        './grassmann.wasm',
      ])
    );
    for (const url of wasmCandidates) {
      candidates.push(() => makeWasm(url));
    }
  }

  if (config.preferred === 'server') {
    candidates.push(() => new ServerTransport({ baseUrl: config.serverUrl }));
  } else if (config.preferred !== 'wasm') {
    candidates.push(() => new ServerTransport({ baseUrl: config.serverUrl }));
  }

  const errors: string[] = [];

  for (const makeTransport of candidates) {
    const transport = makeTransport();
    try {
      const controller = new AbortController();
      const timeout = setTimeout(() => controller.abort(), 3500);
      try {
        const initialFrame = await transport.connect(controller.signal);
        return { transport, initialFrame };
      } finally {
        clearTimeout(timeout);
      }
    } catch (err) {
      transport.dispose();
      errors.push(`${transport.label}: ${(err as Error).message}`);
    }
  }

  throw new Error(`No live Lean backend reachable (${errors.join(' | ')})`);
}

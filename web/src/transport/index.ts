export * from './types';
export * from './server';
export * from './wasm';
export * from './fixture';

import { ServerTransport } from './server';
import type { StudioTransport } from './types';
import { WasmTransport } from './wasm';

export interface AutoConnectConfig {
  serverUrl?: string;
  wasmUrl?: string;
  preferred?: 'auto' | 'server' | 'wasm';
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

  let preferred: 'auto' | 'server' | 'wasm' = queryMode ?? 'auto';
  if (queryServer && !queryMode) preferred = 'server';
  if (queryWasm && !queryMode) preferred = 'wasm';

  return {
    serverUrl: queryServer ?? envServer ?? 'http://127.0.0.1:8787',
    wasmUrl: queryWasm ?? envWasm ?? './wasm/grassmann.mjs',
    preferred,
  };
}

/**
 * Tries Lean backends in priority order (never falling back to any JS GA math!).
 * Auto mode probes zero-config static Lean WASM first (./wasm/grassmann.mjs,
 * ./wasm/grassmann_raw.mjs, ./wasm/grassmann.wasm, ./grassmann.wasm), then falls
 * back to native Lean ga-server WebSocket/HTTP (http://127.0.0.1:8787 or ?server=).
 */
export async function connectLeanBackend(
  config: AutoConnectConfig
): Promise<{ transport: StudioTransport; initialFrame: Uint8Array }> {
  const wasmCandidates = Array.from(
    new Set([
      config.wasmUrl ?? './wasm/grassmann.mjs',
      './wasm/grassmann.mjs',
      './wasm/grassmann_raw.mjs',
      './wasm/grassmann.wasm',
      './grassmann.wasm',
    ])
  );

  const candidates: Array<() => StudioTransport> = [];

  if (config.preferred === 'server') {
    candidates.push(() => new ServerTransport({ baseUrl: config.serverUrl }));
  } else if (config.preferred === 'wasm') {
    for (const url of wasmCandidates) candidates.push(() => new WasmTransport({ wasmUrl: url }));
  } else {
    // Zero-config static Vercel hosting first: try Lean WASM, then native ga-server
    for (const url of wasmCandidates) candidates.push(() => new WasmTransport({ wasmUrl: url }));
    candidates.push(() => new ServerTransport({ baseUrl: config.serverUrl }));
  }

  const errors: string[] = [];

  for (const makeTransport of candidates) {
    const transport = makeTransport();
    try {
      const controller = new AbortController();
      const timeout = setTimeout(() => controller.abort(), 2200);
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

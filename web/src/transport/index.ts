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
    wasmUrl: queryWasm ?? envWasm ?? './grassmann.wasm',
    preferred,
  };
}

/**
 * Tries Lean backends in priority order (never falling back to any JS GA math!).
 * Returns { transport, initialFrame } when a real Lean backend responds, or throws with details.
 */
export async function connectLeanBackend(
  config: AutoConnectConfig
): Promise<{ transport: StudioTransport; initialFrame: Uint8Array }> {
  const order: Array<'wasm' | 'server'> =
    config.preferred === 'wasm'
      ? ['wasm']
      : config.preferred === 'server'
        ? ['server']
        : // Auto: on localhost try native ga-server first, then WASM; on deployed hosts try WASM first
          typeof window !== 'undefined' &&
            (window.location.hostname === 'localhost' || window.location.hostname === '127.0.0.1')
          ? ['server', 'wasm']
          : ['wasm', 'server'];

  const errors: string[] = [];

  for (const kind of order) {
    const transport: StudioTransport =
      kind === 'server'
        ? new ServerTransport({ baseUrl: config.serverUrl })
        : new WasmTransport({ wasmUrl: config.wasmUrl });

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
      errors.push(`${kind}: ${(err as Error).message}`);
    }
  }

  throw new Error(`No live Lean backend reachable (${errors.join(' | ')})`);
}

import type { JsonInputEvent } from '../gsir/types';

export type TransportKind = 'server' | 'wasm' | 'fixture';

export type TransportConnectionState = 'disconnected' | 'connecting' | 'connected' | 'error';

export interface TransportTelemetry {
  kind: TransportKind;
  state: TransportConnectionState;
  label: string;
  lastRoundTripUs: number;
  lastFrameBytes: number;
  errorMessage?: string;
}

export interface LeanPresetCatalogItem {
  id: string;
  title: string;
  category: string;
  algebra: string;
  description: string;
  sampleCode?: string;
  signature?: string;
  badge?: string;
}

/**
 * Pluggable Lean backend transport.
 * Every implementation returns raw little-endian GSIR v1 binary frames produced by Lean.
 */
export interface StudioTransport {
  readonly kind: TransportKind;
  readonly label: string;
  connect(signal?: AbortSignal): Promise<Uint8Array>;
  dispatchBin(event: Uint8Array): Promise<Uint8Array>;
  dispatchJson(event: JsonInputEvent): Promise<Uint8Array>;
  getFrame(): Promise<Uint8Array>;
  getPresetCatalog?(): Promise<LeanPresetCatalogItem[]>;
  dispose(): void;
}

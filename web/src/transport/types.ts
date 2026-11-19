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

export interface LeanTourStopItem {
  index: number;
  id: string;
  title: string;
  presetId: string;
  mode: string;
  algebra: string;
  formula: string;
  summary: string;
  tryIt: string;
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
  getTourCatalog?(): Promise<LeanTourStopItem[]>;
  dispose(): void;
}

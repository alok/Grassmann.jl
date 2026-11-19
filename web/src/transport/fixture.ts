// Read-only Static Binary .gsir Snapshot Transport (for offline inspection & tests only).
// Contains ZERO Geometric Algebra math or scene simulation — strictly returns supplied binary GSIR bytes.

import type { JsonInputEvent } from '../gsir/types';
import type { StudioTransport } from './types';

export class StaticGsirTransport implements StudioTransport {
  readonly kind = 'fixture' as const;
  readonly label: string;

  private readonly bytes: Uint8Array;

  constructor(bytes: Uint8Array, label = 'Static GSIR Snapshot') {
    this.bytes = new Uint8Array(bytes);
    this.label = label;
  }

  async connect(): Promise<Uint8Array> {
    return this.bytes;
  }

  async dispatchBin(_event: Uint8Array): Promise<Uint8Array> {
    return this.bytes;
  }

  async dispatchJson(_event: JsonInputEvent): Promise<Uint8Array> {
    return this.bytes;
  }

  async getFrame(): Promise<Uint8Array> {
    return this.bytes;
  }

  dispose(): void {
    // Nothing to release
  }
}

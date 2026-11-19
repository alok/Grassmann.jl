// Dedicated Web Worker hosting the single-threaded Lean 4.36 Grassmann WASM module.
// Keeps heavy 3D Marching-Tetrahedra / evalSurface / evalImplicit remeshes completely off
// the UI / Three.js render thread, returning binary GSIR frames via zero-copy transferable ArrayBuffers.

import type { JsonInputEvent } from '../gsir/types';
import { WasmTransport } from './wasm';

type WorkerRequest =
  | { id: number; op: 'connect'; wasmUrl: string; wasmBinaryUrl?: string }
  | { id: number; op: 'dispatchBin'; buffer: ArrayBuffer }
  | { id: number; op: 'dispatchJson'; event: JsonInputEvent }
  | { id: number; op: 'getFrame' }
  | { id: number; op: 'getPresetCatalog' }
  | { id: number; op: 'getTourCatalog' }
  | { id: number; op: 'dispose' };

type WorkerResponse =
  | { id: number; ok: true; buffer: ArrayBuffer }
  | { id: number; ok: true; catalog: unknown[] }
  | { id: number; ok: true; tour: unknown[] }
  | { id: number; ok: true }
  | { id: number; ok: false; error: string };

let transport: WasmTransport | null = null;

function postReply(msg: WorkerResponse, transfer: Transferable[] = []): void {
  (self as unknown as { postMessage: (m: unknown, t?: Transferable[]) => void }).postMessage(
    msg,
    transfer
  );
}

function toTransferableBuffer(bytes: Uint8Array): ArrayBuffer {
  if (bytes.byteOffset === 0 && bytes.byteLength === bytes.buffer.byteLength && bytes.buffer instanceof ArrayBuffer) {
    return bytes.buffer;
  }
  return bytes.slice().buffer;
}

self.onmessage = async (ev: MessageEvent<WorkerRequest>) => {
  const req = ev.data;
  try {
    switch (req.op) {
      case 'connect': {
        transport?.dispose();
        transport = new WasmTransport({
          wasmUrl: req.wasmUrl,
          wasmBinaryUrl: req.wasmBinaryUrl,
        });
        const frame = await transport.connect();
        const buf = toTransferableBuffer(frame);
        postReply({ id: req.id, ok: true, buffer: buf }, [buf]);
        return;
      }
      case 'dispatchBin': {
        if (!transport) throw new Error('WASM worker not connected');
        const frame = await transport.dispatchBin(new Uint8Array(req.buffer));
        const buf = toTransferableBuffer(frame);
        postReply({ id: req.id, ok: true, buffer: buf }, [buf]);
        return;
      }
      case 'dispatchJson': {
        if (!transport) throw new Error('WASM worker not connected');
        const frame = await transport.dispatchJson(req.event);
        const buf = toTransferableBuffer(frame);
        postReply({ id: req.id, ok: true, buffer: buf }, [buf]);
        return;
      }
      case 'getFrame': {
        if (!transport) throw new Error('WASM worker not connected');
        const frame = await transport.getFrame();
        const buf = toTransferableBuffer(frame);
        postReply({ id: req.id, ok: true, buffer: buf }, [buf]);
        return;
      }
      case 'getPresetCatalog': {
        if (!transport) throw new Error('WASM worker not connected');
        const catalog = await transport.getPresetCatalog();
        postReply({ id: req.id, ok: true, catalog });
        return;
      }
      case 'getTourCatalog': {
        if (!transport) throw new Error('WASM worker not connected');
        const tour = await transport.getTourCatalog();
        postReply({ id: req.id, ok: true, tour });
        return;
      }
      case 'dispose': {
        transport?.dispose();
        transport = null;
        postReply({ id: req.id, ok: true });
        return;
      }
    }
  } catch (err) {
    postReply({
      id: req.id,
      ok: false,
      error: err instanceof Error ? err.message : String(err),
    });
  }
};

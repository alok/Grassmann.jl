// Unified Ordered Event Pump for Grassmann Studio
// Guarantees:
// 1. Strict FIFO ordering across BOTH binary GSIR InputEvents and JSON InputEvents.
// 2. Coalesces ONLY continuous events (DragHandle for same handleId, Tick, SetCamera)
//    when they appear consecutively at the tail of the pending queue — NEVER jumping
//    over or overwriting a discrete boundary event (WedgeAction, WedgeGesture, EditCoeff,
//    LoadPreset, EvalScript, EvalSurface, EvalImplicit, EvalParametric, etc.)!
// 3. Zero lost discrete actions under slow remeshes or rapid 60fps pointer drags.

import { InputEventKind, type JsonInputEvent } from '../gsir/types';

export type QueuedStudioEvent =
  | {
      kind: 'bin';
      bytes: Uint8Array;
      inputTimestampMs: number;
      coalesceKey: string | null;
      syncCamera: boolean;
      label: string;
    }
  | {
      kind: 'json';
      event: JsonInputEvent;
      inputTimestampMs: number;
      coalesceKey: null;
      syncCamera: boolean;
      label: string;
    };

/**
 * Classifies a binary GSIR InputEvent header to determine whether it is a
 * continuous stream event eligible for tail-coalescing, or a discrete boundary event.
 */
export function classifyBinaryCoalesceKey(bytes: Uint8Array): string | null {
  if (bytes.byteLength < 1) return null;
  const tag = bytes[0]!;
  if (tag === InputEventKind.TICK) {
    // Only coalesce regular ticks (never forceFullSnapshot ticks where flags b0 = 1)
    const flags = bytes.byteLength >= 4 ? bytes[1]! : 0;
    return (flags & 1) !== 0 ? null : 'tick';
  }
  if (tag === InputEventKind.SET_CAMERA) {
    return 'camera';
  }
  if (tag === InputEventKind.DRAG_HANDLE && bytes.byteLength >= 8) {
    const dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
    const handleId = dv.getUint32(4, true);
    return `drag:${handleId}`;
  }
  // All discrete actions (EditCoeff, WedgeGesture, WedgeAction, SlicePlane, etc.)
  // are strict non-coalescing boundaries!
  return null;
}

export interface EventQueueHandlers {
  execute: (item: QueuedStudioEvent) => Promise<void>;
  onBusyChange?: (busy: boolean, pendingCount: number, isHeavy: boolean) => void;
  onError?: (err: unknown, item: QueuedStudioEvent) => void;
}

const HEAVY_JSON_OPS = new Set<JsonInputEvent['op']>([
  'evalSurface',
  'evalImplicit',
  'evalParametric',
  'evalEquations',
  'evalScript',
  'loadPreset',
]);

export class OrderedStudioEventQueue {
  private readonly queue: QueuedStudioEvent[] = [];
  private readonly handlers: EventQueueHandlers;
  private draining = false;
  private disposed = false;

  constructor(handlers: EventQueueHandlers) {
    this.handlers = handlers;
  }

  get pendingCount(): number {
    return this.queue.length;
  }

  get isBusy(): boolean {
    return this.draining;
  }

  enqueueBinary(bytes: Uint8Array, inputTimestampMs = performance.now()): void {
    if (this.disposed) return;
    const coalesceKey = classifyBinaryCoalesceKey(bytes);
    const label = bytes.byteLength > 0 ? `bin:0x${bytes[0]!.toString(16)}` : 'bin';
    const item: QueuedStudioEvent = {
      kind: 'bin',
      bytes,
      inputTimestampMs,
      coalesceKey,
      syncCamera: false,
      label,
    };

    // Tail-only coalescing: only replace the LAST queued item if it has the exact same
    // continuous coalesceKey. Any discrete event between them forms a strict barrier!
    if (coalesceKey !== null && this.queue.length > 0) {
      const tail = this.queue[this.queue.length - 1]!;
      if (tail.coalesceKey === coalesceKey) {
        this.queue[this.queue.length - 1] = item;
        return;
      }
    }

    this.queue.push(item);
    void this.drain();
  }

  enqueueJson(
    event: JsonInputEvent,
    options?: { syncCamera?: boolean; inputTimestampMs?: number }
  ): Promise<void> {
    if (this.disposed) return Promise.resolve();
    const item: QueuedStudioEvent = {
      kind: 'json',
      event,
      inputTimestampMs: options?.inputTimestampMs ?? performance.now(),
      coalesceKey: null,
      syncCamera: options?.syncCamera ?? event.op === 'loadPreset',
      label: `json:${event.op}`,
    };

    return new Promise<void>((resolve) => {
      const wrapped = Object.assign(item, { _resolve: resolve });
      this.queue.push(wrapped);
      void this.drain();
    });
  }

  clearPending(): void {
    while (this.queue.length > 0) {
      const dropped = this.queue.shift() as (QueuedStudioEvent & { _resolve?: () => void }) | undefined;
      dropped?._resolve?.();
    }
  }

  dispose(): void {
    this.disposed = true;
    this.clearPending();
  }

  private async drain(): Promise<void> {
    if (this.draining || this.disposed) return;
    this.draining = true;

    try {
      while (this.queue.length > 0 && !this.disposed) {
        const next = this.queue.shift() as QueuedStudioEvent & { _resolve?: () => void };
        const isHeavy = next.kind === 'json' && HEAVY_JSON_OPS.has(next.event.op);
        this.handlers.onBusyChange?.(true, this.queue.length, isHeavy);
        try {
          await this.handlers.execute(next);
        } catch (err) {
          this.handlers.onError?.(err, next);
        } finally {
          next._resolve?.();
        }
      }
    } finally {
      this.draining = false;
      this.handlers.onBusyChange?.(false, 0, false);
    }
  }
}

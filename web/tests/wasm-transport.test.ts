import { describe, expect, it } from 'vitest';
import {
  GsirStatus,
  buildAllSectionsFixtureBytes,
  decodeGsirFrame,
  encodeGsirFrame,
  encodeWedgeGesture,
} from '../src/gsir';
import { WasmTransport, type GrassmannWasmExports } from '../src/transport';

/**
 * In-memory mock implementing the exact Lean C ABI surface to verify:
 * 1. Caller-owned buffer reuse
 * 2. GSIR_ERR_BUF_SMALL (-3) grows buffer and calls grassmann_studio_get_frame
 *    WITHOUT re-calling dispatch_bin/dispatch_json (preventing double mutation per #17 Fix #2!)
 */
function createMockCAbiWasm(oversizedFrame: Uint8Array): {
  exports: GrassmannWasmExports;
  stats: { dispatchBinCalls: number; dispatchJsonCalls: number; getFrameCalls: number; destroyed: boolean };
} {
  const memory = new WebAssembly.Memory({ initial: 16 }); // 1 MB
  let bump = 64;
  let lastFrame = oversizedFrame;
  let mutationCount = 0n;
  const stats = { dispatchBinCalls: 0, dispatchJsonCalls: 0, getFrameCalls: 0, destroyed: false };

  function writeFrame(outPtr: number, outCap: number, outLenPtr: number): number {
    const dv = new DataView(memory.buffer);
    dv.setUint32(outLenPtr, lastFrame.byteLength, true);
    if (outCap < lastFrame.byteLength) {
      return GsirStatus.ERR_BUF_SMALL;
    }
    new Uint8Array(memory.buffer, outPtr, lastFrame.byteLength).set(lastFrame);
    return GsirStatus.OK;
  }

  const exports: GrassmannWasmExports = {
    memory,
    _malloc(bytes: number) {
      bump = (bump + 7) & ~7;
      const ptr = bump;
      bump += Math.max(8, bytes);
      return ptr;
    },
    _free() {
      // bump allocator mock
    },
    _grassmann_studio_create() {
      return 1n;
    },
    _grassmann_studio_destroy(session: bigint) {
      if (session === 1n) stats.destroyed = true;
    },
    _grassmann_studio_dispatch_bin(session, _eventPtr, _eventLen, outPtr, outCap, outLenPtr) {
      if (session !== 1n) return GsirStatus.ERR_BAD_HANDLE;
      stats.dispatchBinCalls++;
      mutationCount++;
      // Produce a frame larger than 4096 bytes on second call to force GSIR_ERR_BUF_SMALL
      if (stats.dispatchBinCalls === 2) {
        const bigPositions = new Float32Array(600 * 3);
        const bigNormals = new Float32Array(600 * 3);
        const bigIndices = new Uint32Array(300);
        lastFrame = encodeGsirFrame({
          frameSeq: mutationCount,
          meshAssets: [
            {
              meshId: 999n,
              dirtyHash: mutationCount,
              positions: bigPositions,
              normals: bigNormals,
              colors: null,
              indices: bigIndices,
            },
          ],
          meta: { version: 1, title: `Mutation #${mutationCount}` },
        });
      } else {
        lastFrame = oversizedFrame;
      }
      return writeFrame(outPtr, outCap, outLenPtr);
    },
    _grassmann_studio_dispatch_json(session, _jsonPtr, _jsonLen, outPtr, outCap, outLenPtr) {
      if (session !== 1n) return GsirStatus.ERR_BAD_HANDLE;
      stats.dispatchJsonCalls++;
      mutationCount++;
      lastFrame = encodeGsirFrame({
        frameSeq: mutationCount,
        meta: { version: 1, title: `JSON Mutation #${mutationCount}` },
      });
      return writeFrame(outPtr, outCap, outLenPtr);
    },
    _grassmann_studio_get_frame(session, outPtr, outCap, outLenPtr) {
      if (session !== 1n) return GsirStatus.ERR_BAD_HANDLE;
      stats.getFrameCalls++;
      return writeFrame(outPtr, outCap, outLenPtr);
    },
  };

  return { exports, stats };
}

describe('WasmTransport C ABI Contract (#17 Fix #2)', () => {
  it('grows output buffer on GSIR_ERR_BUF_SMALL and fetches cached frame via get_frame without double-mutating', async () => {
    const initialFixture = buildAllSectionsFixtureBytes();
    const { exports, stats } = createMockCAbiWasm(initialFixture);

    const transport = new WasmTransport({
      loadExports: async () => exports,
      initialOutCap: 4096, // intentionally smaller than oversized second frame (~15 KB)
    });

    // Connect dispatches initial Tick(0,0, forceFullSnapshot=true)
    const initBytes = await transport.connect();
    expect(decodeGsirFrame(initBytes).header.frameSeq).toBe(42n);
    expect(stats.dispatchBinCalls).toBe(1);
    expect(stats.getFrameCalls).toBe(0);

    // Dispatch WedgeGesture that produces an oversized frame -> MUST trigger ERR_BUF_SMALL -> get_frame ONCE!
    const gestureBytes = encodeWedgeGesture(0, 1, [1, 0, 0], [-1, 0, 0], false);
    const respBytes = await transport.dispatchBin(gestureBytes);
    const decoded = decodeGsirFrame(respBytes);

    expect(stats.dispatchBinCalls).toBe(2); // NEVER re-called!
    expect(stats.getFrameCalls).toBe(1); // Retrieved cleanly via grassmann_studio_get_frame!
    expect(decoded.header.frameSeq).toBe(2n);
    expect(decoded.meta?.title).toBe('Mutation #2');
    expect(decoded.meshAssets).toHaveLength(1);
    expect(decoded.meshAssets[0]!.meshId).toBe(999n);

    // Dispatch JSON evalSurface event (#17 Fix #5)
    const surfBytes = await transport.dispatchJson({
      op: 'evalSurface',
      expr: 'sin(x)*cos(y)',
      bounds: [-2, 2, -2, 2],
      gridN: 48,
    });
    expect(stats.dispatchJsonCalls).toBe(1);
    expect(decodeGsirFrame(surfBytes).meta?.title).toBe('JSON Mutation #3');

    transport.dispose();
    expect(stats.destroyed).toBe(true);
  });
});

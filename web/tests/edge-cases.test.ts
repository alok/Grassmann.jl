import { describe, expect, it, vi } from 'vitest';
import {
  GSIR_NO_LABEL,
  GsirSessionDecoder,
  GsirStatus,
  LineFlag,
  PlaneFlag,
  PointFlag,
  SegmentFlag,
  buildAllSectionsFixtureBytes,
  decodeGsirFrame,
  encodeDragHandle,
  encodeGsirFrame,
} from '../src/gsir';
import { ServerTransport, WasmTransport, type GrassmannWasmExports } from '../src/transport';

describe('GSIR Alignment & Edge-Case Torture Tests', () => {
  it('decodes 5 consecutive odd-idxCount MESH_ASSETS records on strict 8-byte boundaries', () => {
    const assets = Array.from({ length: 5 }, (_, idx) => {
      const nTris = idx * 2 + 1; // 1, 3, 5, 7, 9 -> idxCount = 3, 9, 15, 21, 27 (all ODD!)
      const idxCount = nTris * 3;
      const vertCount = 3;
      const indices = new Uint32Array(idxCount);
      for (let i = 0; i < idxCount; i++) indices[i] = i % 3;
      return {
        meshId: BigInt(500 + idx),
        dirtyHash: BigInt(1000 + idx),
        positions: new Float32Array([0, 0, 0, 1, 0, 0, 0, 1, 0]),
        normals: new Float32Array([0, 0, 1, 0, 0, 1, 0, 0, 1]),
        colors: idx % 2 === 0 ? new Float32Array(vertCount * 4).fill(1) : null,
        indices,
      };
    });

    const bytes = encodeGsirFrame({ frameSeq: 77n, meshAssets: assets });
    const decoded = decodeGsirFrame(bytes, { strictAlignment: true });
    expect(decoded.meshAssets).toHaveLength(5);
    for (let i = 0; i < 5; i++) {
      expect(decoded.meshAssets[i]!.meshId).toBe(BigInt(500 + i));
      expect(decoded.meshAssets[i]!.idxCount).toBe((i * 2 + 1) * 3);
      expect(decoded.meshAssets[i]!.indices.byteOffset % 4).toBe(0);
    }
  });

  it('preserves handleId = 0 gated strictly on draggable bit across points, segments, lines, planes (#17 Fix #3)', () => {
    const bytes = encodeGsirFrame({
      frameSeq: 88n,
      points: [
        { handleId: 0, flags: PointFlag.DRAGGABLE, pos: [0, 0, 0], radius: 0.1, rgba: [1, 1, 1, 1], labelIdx: GSIR_NO_LABEL },
        { handleId: 0, flags: 0, pos: [1, 0, 0], radius: 0.1, rgba: [1, 1, 1, 1], labelIdx: GSIR_NO_LABEL },
      ],
      segments: [
        { a: [0, 0, 0], b: [1, 0, 0], width: 2, rgba: [1, 1, 1, 1], flags: SegmentFlag.DRAGGABLE }, // hi16 handleId = 0
      ],
      lines: [
        { origin: [0, 0, 0], dir: [1, 0, 0], clip: 5, width: 2, rgba: [1, 1, 1, 1], flags: LineFlag.DRAGGABLE }, // hi16 handleId = 0
      ],
      planes: [
        { center: [0, 0, 0], u: [1, 0, 0], v: [0, 1, 0], extent: 2, rgba: [1, 1, 1, 0.3], flags: PlaneFlag.DRAGGABLE, labelIdx: GSIR_NO_LABEL },
      ],
    });

    const frame = decodeGsirFrame(bytes);
    expect(frame.points[0]!.handleId).toBe(0);
    expect(frame.points[0]!.draggable).toBe(true);
    expect(frame.points[1]!.handleId).toBe(0);
    expect(frame.points[1]!.draggable).toBe(false);
    expect(frame.segments[0]!.handleId).toBe(0);
    expect(frame.segments[0]!.draggable).toBe(true);
    expect(frame.lines[0]!.handleId).toBe(0);
    expect(frame.lines[0]!.draggable).toBe(true);
    expect(frame.planes[0]!.handleId).toBe(0);
    expect(frame.planes[0]!.draggable).toBe(true);
  });

  it('streams 100 consecutive frames with metaJsonLen=0 deltas and shader hash hydration', () => {
    const session = new GsirSessionDecoder();
    const first = session.decode(buildAllSectionsFixtureBytes());
    expect(first.meta?.opnsShaders?.[0]?.glsl).toContain('void main');

    for (let i = 1; i <= 100; i++) {
      const isDelta = i % 5 !== 0;
      const frameBytes = encodeGsirFrame({
        frameSeq: BigInt(42 + i),
        simTime: i * 0.016,
        meta: isDelta
          ? null
          : {
              version: 1,
              presetId: 'cga3d_opns_visualizer',
              opnsShaders: [{ hash: 'fixture_opns_v1' }], // body omitted -> hydrated from cache
            },
      });
      const decoded = session.decode(frameBytes);
      expect(decoded.header.frameSeq).toBe(BigInt(42 + i));
      expect(decoded.metaReused).toBe(isDelta);
      expect(decoded.meta?.opnsShaders?.[0]?.glsl).toContain('void main');
    }
  });
});

describe('Emscripten HEAPU8 + _grassmann_initialize & ServerTransport HTTP Tests', () => {
  it('calls _grassmann_initialize() and reads HEAPU8 memory cleanly in WasmTransport', async () => {
    const rawBuf = new ArrayBuffer(128 * 1024);
    const heapU8 = new Uint8Array(rawBuf);
    let bump = 64;
    let initCalled = false;
    const frame = buildAllSectionsFixtureBytes();

    const emscriptenLike: GrassmannWasmExports = {
      HEAPU8: heapU8,
      _malloc(bytes: number) {
        bump = (bump + 7) & ~7;
        const p = bump;
        bump += bytes;
        return p;
      },
      _free() {},
      _grassmann_initialize() {
        initCalled = true;
        return GsirStatus.OK;
      },
      _grassmann_studio_create() {
        if (!initCalled) return 0n;
        return 7n;
      },
      _grassmann_studio_destroy() {},
      _grassmann_studio_dispatch_bin(_s, _ep, _el, outPtr, outCap, outLenPtr) {
        new DataView(rawBuf).setUint32(outLenPtr, frame.byteLength, true);
        if (outCap < frame.byteLength) return GsirStatus.ERR_BUF_SMALL;
        heapU8.set(frame, outPtr);
        return GsirStatus.OK;
      },
      _grassmann_studio_dispatch_json(_s, _jp, _jl, outPtr, _outCap, outLenPtr) {
        new DataView(rawBuf).setUint32(outLenPtr, frame.byteLength, true);
        heapU8.set(frame, outPtr);
        return GsirStatus.OK;
      },
      _grassmann_studio_get_frame(_s, outPtr, _outCap, outLenPtr) {
        new DataView(rawBuf).setUint32(outLenPtr, frame.byteLength, true);
        heapU8.set(frame, outPtr);
        return GsirStatus.OK;
      },
    };

    const transport = new WasmTransport({ loadExports: async () => emscriptenLike });
    const bytes = await transport.connect();
    expect(initCalled).toBe(true);
    expect(decodeGsirFrame(bytes).header.frameSeq).toBe(42n);
    transport.dispose();
  });

  it('dispatches binary & JSON events over ServerTransport HTTP endpoints cleanly', async () => {
    const fixture = buildAllSectionsFixtureBytes();
    const seen: string[] = [];

    const origFetch = globalThis.fetch;
    globalThis.fetch = vi.fn(async (input: RequestInfo | URL) => {
      seen.push(String(input));
      return new Response(new Uint8Array(fixture), {
        status: 200,
        headers: { 'Content-Type': 'application/octet-stream' },
      });
    }) as unknown as typeof fetch;

    try {
      const server = new ServerTransport({
        baseUrl: 'http://127.0.0.1:8787/',
        preferWebSocket: false,
      });
      const initBytes = await server.connect();
      expect(decodeGsirFrame(initBytes).header.frameSeq).toBe(42n);

      const dragBytes = await server.dispatchBin(encodeDragHandle(0, 1, 2, 3));
      expect(decodeGsirFrame(dragBytes).points[0]!.handleId).toBe(0);

      const jsonBytes = await server.dispatchJson({ op: 'loadPreset', id: 'pga3d_slicing' });
      expect(decodeGsirFrame(jsonBytes).header.p).toBe(3);

      const frameBytes = await server.getFrame();
      expect(decodeGsirFrame(frameBytes).header.version).toBe(1);

      expect(seen).toEqual([
        'http://127.0.0.1:8787/api/event/bin',
        'http://127.0.0.1:8787/api/event/bin',
        'http://127.0.0.1:8787/api/event/json',
        'http://127.0.0.1:8787/api/frame',
      ]);
      server.dispose();
    } finally {
      globalThis.fetch = origFetch;
    }
  });
});

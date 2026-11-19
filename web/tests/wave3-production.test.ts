import { describe, expect, it } from 'vitest';
import vercelCfg from '../vercel.json';
import {
  GsirStatus,
  InputEventKind,
  WedgeActionCode,
  buildAllSectionsFixtureBytes,
  encodeDragHandle,
  encodeEditCoeff,
  encodeSetCamera,
  encodeTick,
  encodeWedgeAction,
} from '../src/gsir';
import { OrderedStudioEventQueue, WasmTransport, classifyBinaryCoalesceKey, type GrassmannWasmExports } from '../src/transport';
import {
  decodeExperimentFromHash,
  encodeExperimentToHash,
  parseGrassmannExperiment,
  serializeExperiment,
  type GrassmannExperimentV1,
} from '../src/ui/experiment';
import { highlightGaCode } from '../src/ui/gaHighlight';

describe('OrderedStudioEventQueue (Dots #84 / #87 regression suite)', () => {
  it('classifies continuous vs discrete binary events accurately', () => {
    expect(classifyBinaryCoalesceKey(encodeDragHandle(0, 1, 2, 3))).toBe('drag:0');
    expect(classifyBinaryCoalesceKey(encodeDragHandle(4, 1, 2, 3))).toBe('drag:4');
    expect(classifyBinaryCoalesceKey(encodeTick(0.016, 1.0, false))).toBe('tick');
    // forceFullSnapshot tick must NOT coalesce away!
    expect(classifyBinaryCoalesceKey(encodeTick(0.016, 1.0, true))).toBeNull();
    expect(classifyBinaryCoalesceKey(encodeSetCamera(new Float32Array(8), 45, 5))).toBe('camera');
    // Discrete actions are strict non-coalescing barriers
    expect(classifyBinaryCoalesceKey(encodeWedgeAction(WedgeActionCode.UNDO, 0))).toBeNull();
    expect(classifyBinaryCoalesceKey(encodeEditCoeff(0, 1, 0.5))).toBeNull();
  });

  it('coalesces rapid continuous drags while strictly preserving interleaved discrete WedgeAction & LoadPreset boundaries', async () => {
    const executed: string[] = [];
    let releaseFirst!: () => void;

    const queue = new OrderedStudioEventQueue({
      execute: async (item) => {
        if (item.kind === 'json' && item.event.op === 'evalSurface') {
          executed.push('evalSurface:start');
          await new Promise<void>((r) => {
            releaseFirst = r;
          });
          executed.push('evalSurface:done');
          return;
        }
        if (item.kind === 'bin') {
          const tag = item.bytes[0]!;
          if (tag === InputEventKind.DRAG_HANDLE) {
            const dv = new DataView(item.bytes.buffer, item.bytes.byteOffset, item.bytes.byteLength);
            const id = dv.getUint32(4, true);
            const x = dv.getFloat32(8, true);
            executed.push(`drag:${id}@${x.toFixed(1)}`);
          } else if (tag === InputEventKind.WEDGE_ACTION) {
            executed.push(`wedgeAction:${item.bytes[4]}`);
          } else if (tag === InputEventKind.EDIT_COEFF) {
            executed.push('editCoeff');
          }
          return;
        }
        executed.push(`json:${item.event.op}`);
      },
    });

    // 1. Start a slow 3D remesh
    const pSlow = queue.enqueueJson({
      op: 'evalSurface',
      expr: 'sin(x*y)',
      bounds: [-2, 2, -2, 2],
      gridN: 32,
    });

    // 2. While remesh is in-flight, fire 3 rapid drags on handle 0 -> should coalesce to the 3rd (x=3.0)
    queue.enqueueBinary(encodeDragHandle(0, 1.0, 0, 0));
    queue.enqueueBinary(encodeDragHandle(0, 2.0, 0, 0));
    queue.enqueueBinary(encodeDragHandle(0, 3.0, 0, 0));

    // 3. Fire a discrete WedgeAction UNDO -> MUST NOT be overwritten by later drags!
    queue.enqueueBinary(encodeWedgeAction(WedgeActionCode.UNDO, 0));

    // 4. Fire 2 more drags on handle 0 AFTER the discrete WedgeAction -> coalesce after the barrier, NEVER before!
    queue.enqueueBinary(encodeDragHandle(0, 4.0, 0, 0));
    queue.enqueueBinary(encodeDragHandle(0, 5.0, 0, 0));

    // 5. Fire discrete EditCoeff + LoadPreset
    queue.enqueueBinary(encodeEditCoeff(0, 2, 1.5));
    const pPreset = queue.enqueueJson({ op: 'loadPreset', id: 'pga3d_slicing' });

    // Release slow remesh and await full drain
    releaseFirst();
    await Promise.all([pSlow, pPreset]);

    expect(executed).toEqual([
      'evalSurface:start',
      'evalSurface:done',
      'drag:0@3.0',
      `wedgeAction:${WedgeActionCode.UNDO}`,
      'drag:0@5.0',
      'editCoeff',
      'json:loadPreset',
    ]);
  });
});

describe('WasmTransport.getPresetCatalog()', () => {
  it('reads dynamic JSON catalog via 2-step grassmann_studio_preset_catalog C ABI', async () => {
    const mem = new WebAssembly.Memory({ initial: 8 });
    const frameBytes = buildAllSectionsFixtureBytes();
    const catalogJson = JSON.stringify([
      {
        id: 'pga3d_slicing',
        title: '3D PGA Mesh Slicing (Bunny)',
        category: '3D PGA',
        algebra: 'PGA3',
        description: 'Live bunny slicer',
        sampleCode: 'let p = plane(0,1,0,0.2)',
      },
      {
        id: 'cga3d_opns_cyclide',
        title: '3D CGA OPNS Dupin Cyclide',
        category: '3D CGA',
        algebra: 'CGA3',
        description: 'GLSL 300 es raymarcher',
      },
    ]);
    const catalogBytes = new TextEncoder().encode(catalogJson);

    let bump = 1024;
    const mockExports: GrassmannWasmExports = {
      memory: mem,
      malloc: (n) => {
        const ptr = bump;
        bump = (bump + Math.max(8, n) + 7) & ~7;
        return ptr;
      },
      free: () => {},
      grassmann_studio_create: () => 1n,
      grassmann_studio_destroy: () => {},
      grassmann_studio_dispatch_bin: (_s, _ip, _il, outPtr, _oc, outLenPtr) => {
        new Uint8Array(mem.buffer, outPtr, frameBytes.byteLength).set(frameBytes);
        new DataView(mem.buffer, outLenPtr, 4).setUint32(0, frameBytes.byteLength, true);
        return GsirStatus.OK;
      },
      grassmann_studio_dispatch_json: () => GsirStatus.OK,
      grassmann_studio_get_frame: (_s, outPtr, _oc, outLenPtr) => {
        new Uint8Array(mem.buffer, outPtr, frameBytes.byteLength).set(frameBytes);
        new DataView(mem.buffer, outLenPtr, 4).setUint32(0, frameBytes.byteLength, true);
        return GsirStatus.OK;
      },
      grassmann_studio_preset_catalog: (outPtr, outCap, outLenPtr) => {
        new DataView(mem.buffer, outLenPtr, 4).setUint32(0, catalogBytes.byteLength, true);
        if (outPtr === 0 || outCap < catalogBytes.byteLength) {
          return GsirStatus.ERR_BUF_SMALL;
        }
        new Uint8Array(mem.buffer, outPtr, catalogBytes.byteLength).set(catalogBytes);
        return GsirStatus.OK;
      },
    };

    const transport = new WasmTransport({ loadExports: async () => mockExports });
    await transport.connect();
    const catalog = await transport.getPresetCatalog();
    expect(catalog).toHaveLength(2);
    expect(catalog[0]?.id).toBe('pga3d_slicing');
    expect(catalog[0]?.sampleCode).toBe('let p = plane(0,1,0,0.2)');
    expect(catalog[1]?.id).toBe('cga3d_opns_cyclide');
    transport.dispose();
  });
});

describe('Portable Cross-Client .grassmann.json Experiment Format', () => {
  it('round-trips through JSON and URL-safe #exp= hash identically', () => {
    const sample: GrassmannExperimentV1 = {
      version: 1,
      mode: 'calculator',
      presetId: 'pga3d_slicing',
      algebra: 'STA',
      script: 'let A = 1.1e2 + 0.4e3; A ^ B',
      implicitExpr: 'sin(x*2)*cos(y*2) + sin(y*2)*cos(z*2) + sin(z*2)*cos(x*2)',
      parametricExpr: {
        fx: '(1.2 + 0.45*v*cos(u*0.5))*cos(u)',
        fy: '0.45*v*sin(u*0.5)',
        fz: '(1.2 + 0.45*v*cos(u*0.5))*sin(u)',
      },
      handles: [
        { handleId: 0, pos: [0.1, 0.65, -0.2] },
        { handleId: 1, pos: [1.2, -0.4, 0.3] },
      ],
      wedgeLevel: 10,
      wedgeSeed: 1337,
      camera: {
        pos: [3.2, 2.5, 4.0],
        target: [0, 0.15, 0],
        isOrtho: false,
      },
    };

    const json = serializeExperiment(sample);
    const reparsed = parseGrassmannExperiment(json);
    expect(reparsed).toEqual(sample);

    const hash = encodeExperimentToHash(sample);
    expect(hash.startsWith('exp=')).toBe(true);
    const fromHash = decodeExperimentFromHash(hash.slice(4));
    expect(fromHash).toEqual(sample);
  });
});

describe('Vercel Cache & Header Configuration (Dots #84 / #87)', () => {
  it('never caches un-fingerprinted WASM/manifest immutably and omits unnecessary COOP/COEP headers', () => {
    const cfg = vercelCfg as {
      headers: Array<{ source: string; headers: Array<{ key: string; value: string }> }>;
    };

    const allHeaderKeys = cfg.headers.flatMap((r) => r.headers.map((h) => h.key.toLowerCase()));
    expect(allHeaderKeys).not.toContain('cross-origin-opener-policy');
    expect(allHeaderKeys).not.toContain('cross-origin-embedder-policy');

    const manifestRule = cfg.headers.find((r) => r.source.includes('wasm-manifest'));
    expect(manifestRule?.headers.some((h) => h.value.includes('must-revalidate'))).toBe(true);

    const canonicalRule = cfg.headers.find((r) => r.source === '/wasm/grassmann.:ext(wasm|mjs)');
    expect(canonicalRule?.headers.some((h) => h.value.includes('must-revalidate'))).toBe(true);
    expect(canonicalRule?.headers.some((h) => h.value.includes('immutable'))).toBe(false);

    const fingerprintedRule = cfg.headers.find((r) => r.source.includes(':hash([a-f0-9]+)'));
    expect(fingerprintedRule?.headers.some((h) => h.value.includes('immutable'))).toBe(true);
  });
});

describe('GA Syntax Highlighter (Wave 3B)', () => {
  it('colors GA operators, blades, keywords, numbers, hex swatches, comments, and escapes HTML safely', () => {
    const sample =
      '// Slice plane <script>\nlet cut = plane(0, 1, 0, 0.25) ^ e12 + 0x38bdf8\n"A & B" >>> ~R';
    const html = highlightGaCode(sample);
    expect(html).not.toContain('<script>');
    expect(html).toContain('&lt;script&gt;');
    expect(html).toContain('class="tok-comment"');
    expect(html).toContain('class="tok-kw"');
    expect(html).toContain('class="tok-blade">e12<');
    expect(html).toContain('class="tok-hex" style="--swatch:#38bdf8">0x38bdf8<');
    expect(html).toContain('class="tok-op">&gt;&gt;&gt;<');
    expect(html).toContain('class="tok-num">0.25<');
    // Character-for-character plain-text fidelity (zero caret drift!)
    const plain = html
      .replace(/<[^>]+>/g, '')
      .replace(/&lt;/g, '<')
      .replace(/&gt;/g, '>')
      .replace(/&amp;/g, '&');
    expect(plain).toBe(sample);
  });
});

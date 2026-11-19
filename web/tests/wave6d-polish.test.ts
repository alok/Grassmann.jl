import { describe, expect, it, vi } from 'vitest';
import { buildAllSectionsFixtureBytes } from '../src/gsir';
import { MAX_CACHED_OPNS_SHADERS, OpnsShaderCache, computeOpnsProxyBoxSize } from '../src/render/materials';
import { OrderedStudioEventQueue, WasmTransport, type GrassmannWasmExports } from '../src/transport';
import {
  decodeExperimentFromHash,
  encodeExperimentToHash,
  inferLegacySceneKind,
  normalizeSeedString,
  parseGrassmannExperiment,
  serializeExperiment,
  type GrassmannExperimentV1,
} from '../src/ui/experiment';
import { WEDGE_LEVELS } from '../src/ui/presets';
import { shouldIgnoreGlobalSpaceKey } from '../src/ui/studioApp';
import { GUIDED_TOUR_STOPS } from '../src/ui/tourModal';

describe('Wave 6D / Dots P0 #4: Exact .grassmann.json Experiment Restore & Lossless 64-Bit Seeds', () => {
  it('round-trips custom LiveScript, implicit GPU surface, and 64-bit procedural Wedge seed 9007199254740993 losslessly', () => {
    const customScriptExp: GrassmannExperimentV1 = {
      version: 1,
      mode: 'coffeeshop',
      sceneKind: 'script',
      presetId: '',
      algebra: 'PGA3',
      script: '@basis PGA3\nlet amp = slider("amp", 1.25, 0.1, 2.0)\nlet A = point(-amp, 0, 0)',
      implicitExpr: 'x^2 + y^2 + z^2 - 1',
      parametricExpr: { fx: 'u', fy: 'v', fz: '0' },
      handles: [],
      params: { amp: 1.45 },
      wedgeLevel: 1,
      wedgeSeed: '42',
      camera: { pos: [3, 2, 4], target: [0, 0, 0], isOrtho: false },
    };

    const parsedScript = parseGrassmannExperiment(serializeExperiment(customScriptExp));
    expect(parsedScript).toEqual(customScriptExp);
    expect(inferLegacySceneKind(parsedScript!)).toBe('script');
    expect(parsedScript?.presetId).toBe('');
    expect(parsedScript?.params).toEqual({ amp: 1.45 });

    const implicitGpuExp: GrassmannExperimentV1 = {
      version: 1,
      mode: 'calculator',
      sceneKind: 'implicit',
      presetId: '',
      algebra: 'PGA3',
      script: '',
      implicitExpr: 'x*x + y*y + z*z - 9',
      gpuRaymarch: true,
      bound: 4.0,
      parametricExpr: { fx: 'u', fy: 'v', fz: '0' },
      handles: [],
      wedgeLevel: 1,
      wedgeSeed: '42',
      camera: { pos: [5, 4, 6], target: [0, 0, 0], isOrtho: false },
    };

    const hashImp = encodeExperimentToHash(implicitGpuExp);
    const reparsedImp = decodeExperimentFromHash(hashImp.slice(4));
    expect(reparsedImp).toEqual(implicitGpuExp);
    expect(reparsedImp?.gpuRaymarch).toBe(true);
    expect(reparsedImp?.bound).toBe(4.0);

    // Lossless 64-bit seed above Number.MAX_SAFE_INTEGER (2^53 + 1 = 9007199254740993)
    const wedgeRandExp: GrassmannExperimentV1 = {
      version: 1,
      mode: 'wedge',
      sceneKind: 'wedgeRandom',
      presetId: '',
      algebra: 'PGA3',
      script: '',
      implicitExpr: '',
      parametricExpr: { fx: '0', fy: '0', fz: '0' },
      handles: [],
      wedgeLevel: 1,
      wedgeSeed: '9007199254740993',
      wedgeDim: 3,
      wedgeDifficulty: 2,
      camera: { pos: [3, 2, 4], target: [0, 0, 0], isOrtho: false },
    };

    const jsonRand = serializeExperiment(wedgeRandExp);
    const reparsedRand = parseGrassmannExperiment(jsonRand);
    expect(reparsedRand?.sceneKind).toBe('wedgeRandom');
    expect(reparsedRand?.wedgeSeed).toBe('9007199254740993');
    expect(reparsedRand?.wedgeSeed).not.toBe('9007199254740992');
    expect(normalizeSeedString(reparsedRand?.wedgeSeed)).toBe('9007199254740993');
    expect(reparsedRand?.wedgeDim).toBe(3);
    expect(reparsedRand?.wedgeDifficulty).toBe(2);

    const hashRand = encodeExperimentToHash(wedgeRandExp);
    const fromHashRand = decodeExperimentFromHash(hashRand.slice(4));
    expect(fromHashRand?.wedgeSeed).toBe('9007199254740993');
  });

  it('infers exact sceneKind safely for legacy v1 experiments that used synthetic presetIds', () => {
    expect(inferLegacySceneKind({ mode: 'coffeeshop', presetId: 'custom_script', script: 'let A = point(1,0,0)' })).toBe('script');
    expect(inferLegacySceneKind({ mode: 'calculator', presetId: 'implicit_gpu', script: '' })).toBe('implicit');
    expect(inferLegacySceneKind({ mode: 'calculator', presetId: 'surface_3d', script: '' })).toBe('surface');
    expect(inferLegacySceneKind({ mode: 'calculator', presetId: 'parametric_expr', script: '' })).toBe('parametric');
    expect(inferLegacySceneKind({ mode: 'coffeeshop', presetId: 'pga3d_slicing', script: '' })).toBe('preset');
  });
});

describe('Wave 6D / Dots P1 #9: Bounded LRU OpnsShaderCache (40 Varying Implicit Shaders)', () => {
  it('caps compiled ShaderMaterials and failed hashes strictly at MAX_CACHED_OPNS_SHADERS and disposes evicted materials', () => {
    const cache = new OpnsShaderCache();
    expect(MAX_CACHED_OPNS_SHADERS).toBe(24);

    const disposeSpies: Array<ReturnType<typeof vi.spyOn>> = [];
    for (let i = 0; i < 40; i++) {
      const entry = cache.getOrCreate({
        hash: `implicit_hash_${i}`,
        glsl: `float evalField(vec3 p) { return length(p) - ${(1.0 + i * 0.02).toFixed(3)}; }`,
      });
      expect(entry).not.toBeNull();
      disposeSpies.push(vi.spyOn(entry!.material, 'dispose'));
      expect(cache.size).toBeLessThanOrEqual(MAX_CACHED_OPNS_SHADERS);
    }

    expect(cache.size).toBe(MAX_CACHED_OPNS_SHADERS);
    // First 16 evicted materials MUST have been disposed cleanly (zero GPU leaks!)
    const disposedCount = disposeSpies.filter((spy) => spy.mock.calls.length > 0).length;
    expect(disposedCount).toBe(40 - MAX_CACHED_OPNS_SHADERS);

    // Failed hash tracking is also strictly bounded
    for (let i = 0; i < 40; i++) {
      cache.markFailed(`bad_hash_${i}`);
      expect(cache.failedCount).toBeLessThanOrEqual(MAX_CACHED_OPNS_SHADERS);
    }
    expect(cache.failedCount).toBe(MAX_CACHED_OPNS_SHADERS);
    expect(cache.hasFailed('bad_hash_0')).toBe(false);
    expect(cache.hasFailed('bad_hash_39')).toBe(true);

    cache.dispose();
    expect(cache.size).toBe(0);
    expect(cache.failedCount).toBe(0);
  });
});

describe('Wave 6D / Dots P1 #10: Explicit seekTime Coalescing & resetTime Barrier', () => {
  it('coalesces consecutive seekTime scrubs while preserving resetTime as a strict barrier', async () => {
    const executed: string[] = [];
    let release!: () => void;
    const q = new OrderedStudioEventQueue({
      execute: async (item) => {
        if (item.kind === 'json' && item.event.op === 'loadPreset') {
          executed.push('loadPreset:start');
          await new Promise<void>((r) => {
            release = r;
          });
          executed.push('loadPreset:done');
          return;
        }
        if (item.kind === 'json' && item.event.op === 'seekTime') {
          executed.push(`seekTime:${item.event.t.toFixed(2)}`);
          return;
        }
        if (item.kind === 'json' && item.event.op === 'resetTime') {
          executed.push('resetTime');
        }
      },
    });

    const p0 = q.enqueueJson({ op: 'loadPreset', id: 'pga3d_bouncing_cube' });
    const s1 = q.enqueueJson({ op: 'seekTime', t: 1.0 });
    const s2 = q.enqueueJson({ op: 'seekTime', t: 2.5 });
    const s3 = q.enqueueJson({ op: 'seekTime', t: 4.0 });
    const r0 = q.enqueueJson({ op: 'resetTime' });
    const s4 = q.enqueueJson({ op: 'seekTime', t: 0.5 });

    release();
    await Promise.all([p0, s1, s2, s3, r0, s4]);

    expect(executed).toEqual([
      'loadPreset:start',
      'loadPreset:done',
      'seekTime:4.00',
      'resetTime',
      'seekTime:0.50',
    ]);
  });
});

describe('Wave 6D / Dots P2 #11: Global Space Shortcut Accessibility Guard', () => {
  it('ignores Space on buttons, links, role=button, inputs, selects, textareas, and contenteditable controls', () => {
    expect(shouldIgnoreGlobalSpaceKey({ tagName: 'BUTTON' } as unknown as EventTarget, null)).toBe(true);
    expect(shouldIgnoreGlobalSpaceKey({ tagName: 'A' } as unknown as EventTarget, null)).toBe(true);
    expect(shouldIgnoreGlobalSpaceKey({ tagName: 'SELECT' } as unknown as EventTarget, null)).toBe(true);
    expect(shouldIgnoreGlobalSpaceKey({ tagName: 'INPUT' } as unknown as EventTarget, null)).toBe(true);
    expect(shouldIgnoreGlobalSpaceKey({ tagName: 'TEXTAREA' } as unknown as EventTarget, null)).toBe(true);
    expect(
      shouldIgnoreGlobalSpaceKey(
        { tagName: 'DIV', getAttribute: (k: string) => (k === 'role' ? 'button' : null) } as unknown as EventTarget,
        null
      )
    ).toBe(true);
    expect(
      shouldIgnoreGlobalSpaceKey(
        { tagName: 'DIV', isContentEditable: true } as unknown as EventTarget,
        null
      )
    ).toBe(true);
    // Child span inside a focused button must also be ignored via activeElement / closest
    expect(
      shouldIgnoreGlobalSpaceKey(
        { tagName: 'SPAN', closest: () => ({ tagName: 'BUTTON' }) } as unknown as EventTarget,
        null
      )
    ).toBe(true);
    expect(
      shouldIgnoreGlobalSpaceKey(
        { tagName: 'BODY' } as unknown as EventTarget,
        { tagName: 'BUTTON' } as unknown as Element
      )
    ).toBe(true);

    // Non-interactive canvas/body permits global Space Play/Pause
    expect(
      shouldIgnoreGlobalSpaceKey(
        { tagName: 'CANVAS', closest: () => null } as unknown as EventTarget,
        { tagName: 'BODY', closest: () => null } as unknown as Element
      )
    ).toBe(false);
  });
});

describe('Wave 6D / 7A: Interactive 6-Stop Guided GA Tour & 17 Wedge Levels', () => {
  it('defines 6 well-formed tour stops (0..5) with KaTeX formulas and interactive tryIt prompts', () => {
    expect(GUIDED_TOUR_STOPS).toHaveLength(6);
    GUIDED_TOUR_STOPS.forEach((stop, idx) => {
      expect(stop.index).toBe(idx);
      expect(stop.title.length).toBeGreaterThan(4);
      expect(stop.formula.length).toBeGreaterThan(4);
      expect(stop.tryIt.length).toBeGreaterThan(10);
      expect(stop.presetId.length).toBeGreaterThan(3);
    });
    expect(GUIDED_TOUR_STOPS[5]?.mode).toBe('wedge');
  });

  it('lists all 17 1-based Wedge levels (L1..L9 2D, L10..L17 3D Grand Finale)', () => {
    expect(WEDGE_LEVELS).toHaveLength(17);
    WEDGE_LEVELS.forEach((lv, idx) => {
      expect(lv.index).toBe(idx + 1);
      expect(lv.is3D).toBe(idx + 1 >= 10);
    });
    expect(WEDGE_LEVELS[16]?.label).toContain('L17');
  });

  it('reads dynamic tourCatalog JSON via the 2-step grassmann_studio_tour_catalog C ABI', async () => {
    const memory = new WebAssembly.Memory({ initial: 8 });
    let bump = 1024;
    const frameBytes = buildAllSectionsFixtureBytes();
    const tourPayload = new TextEncoder().encode(
      JSON.stringify([
        {
          index: 0,
          id: 'tour_points_lines',
          title: '1. Points & Lines',
          presetId: 'pga2d_points_and_lines',
          mode: 'coffeeShop',
          algebra: 'PGA2',
          formula: 'L = A \\vee B',
          summary: 'Join spans lines.',
          tryIt: 'Drag A and B.',
        },
        {
          index: 5,
          id: 'tour_play_wedge',
          title: '6. Play Wedge 2D/3D!',
          presetId: 'wedge_2d',
          mode: 'wedge',
          algebra: 'PGA2 / PGA3',
          formula: 'A \\vee B',
          summary: '17 puzzles.',
          tryIt: 'Pull A and B apart.',
        },
      ])
    );

    const mockExports: GrassmannWasmExports = {
      memory,
      malloc: (bytes) => {
        const ptr = (bump + 7) & ~7;
        bump = ptr + bytes + 16;
        return ptr;
      },
      free: () => {},
      grassmann_studio_create: () => 1n,
      grassmann_studio_destroy: () => {},
      grassmann_studio_dispatch_bin: (_s, _ep, _el, outPtr, outCap, outLenPtr) => {
        new DataView(memory.buffer, outLenPtr, 4).setUint32(0, frameBytes.byteLength, true);
        if (outCap < frameBytes.byteLength) return -3;
        new Uint8Array(memory.buffer, outPtr, frameBytes.byteLength).set(frameBytes);
        return 0;
      },
      grassmann_studio_dispatch_json: (_s, _jp, _jl, outPtr, outCap, outLenPtr) => {
        new DataView(memory.buffer, outLenPtr, 4).setUint32(0, frameBytes.byteLength, true);
        if (outCap < frameBytes.byteLength) return -3;
        new Uint8Array(memory.buffer, outPtr, frameBytes.byteLength).set(frameBytes);
        return 0;
      },
      grassmann_studio_get_frame: (_s, outPtr, outCap, outLenPtr) => {
        new DataView(memory.buffer, outLenPtr, 4).setUint32(0, frameBytes.byteLength, true);
        if (outCap < frameBytes.byteLength) return -3;
        new Uint8Array(memory.buffer, outPtr, frameBytes.byteLength).set(frameBytes);
        return 0;
      },
      grassmann_studio_tour_catalog: (outPtr, outCap, outLenPtr) => {
        new DataView(memory.buffer, outLenPtr, 4).setUint32(0, tourPayload.byteLength, true);
        if (outPtr === 0 || outCap < tourPayload.byteLength) return -3;
        new Uint8Array(memory.buffer, outPtr, tourPayload.byteLength).set(tourPayload);
        return 0;
      },
    };

    const transport = new WasmTransport({ loadExports: async () => mockExports });
    await transport.connect();
    const stops = await transport.getTourCatalog();
    expect(stops).toHaveLength(2);
    expect(stops[0]?.id).toBe('tour_points_lines');
    expect(stops[1]?.mode).toBe('wedge');
    transport.dispose();
  });

  it('sizes OPNS raymarching proxy box dynamically (>= 120 and >= 6*bound so bound=20 never clips)', () => {
    expect(computeOpnsProxyBoxSize(undefined, 1.6)).toBeGreaterThanOrEqual(120);
    expect(computeOpnsProxyBoxSize('// Implicit 3D: x-15 = 0, bound=20.000000', 2.2)).toBeGreaterThanOrEqual(120);
    expect(computeOpnsProxyBoxSize('vec3 bMax = vec3(20.0);', 20)).toBeGreaterThanOrEqual(120);
    expect(computeOpnsProxyBoxSize('vec3 bMax = vec3(30.0);', 20)).toBeGreaterThanOrEqual(180);
  });
});

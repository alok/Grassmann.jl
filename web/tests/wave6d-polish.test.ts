import { describe, expect, it, vi } from 'vitest';
import { MAX_CACHED_OPNS_SHADERS, OpnsShaderCache } from '../src/render/materials';
import { OrderedStudioEventQueue } from '../src/transport';
import {
  decodeExperimentFromHash,
  encodeExperimentToHash,
  inferLegacySceneKind,
  normalizeSeedString,
  parseGrassmannExperiment,
  serializeExperiment,
  type GrassmannExperimentV1,
} from '../src/ui/experiment';
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

describe('Wave 6D: Interactive 6-Stop Guided GA Tour', () => {
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
});

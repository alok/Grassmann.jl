// Portable Cross-Client `.grassmann.json` Experiment Format (v1)
// Matches native macOS/visionOS LeanCalculator / LeanStudioVision 1:1 so any CoffeeShop
// sketch, 3D surface, implicit/parametric scene, or Wedge puzzle can be exported, copied,
// shared via URL hash (#exp=...), dropped back in, or reopened identically on any platform.

import type { StudioMode } from './studioApp';

export type ExperimentSceneKind =
  | 'preset'
  | 'script'
  | 'surface'
  | 'implicit'
  | 'parametric'
  | 'wedgeLevel'
  | 'wedgeTutorial'
  | 'wedgeRandom';

export type WedgeTutorialId = 'T1' | 'T2' | 'T3' | 'T4' | 'T5' | 'T6';

export interface GrassmannExperimentV1 {
  version: 1;
  mode: StudioMode;
  /** Exact discriminated scene kind (Dots P0 #4) so restore dispatches the exact matching Lean op */
  sceneKind?: ExperimentSceneKind;
  presetId: string;
  algebra: string;
  script: string;
  surfaceExpr?: string;
  implicitExpr: string;
  gpuRaymarch?: boolean;
  bound?: number;
  parametricExpr: {
    fx: string;
    fy: string;
    fz: string;
  };
  handles: Array<{
    handleId: number;
    pos: [number, number, number];
  }>;
  params?: Record<string, number>;
  wedgeLevel: number;
  /** Lossless decimal string (for >53-bit 64-bit seeds like "9007199254740993") or legacy number */
  wedgeSeed: number | string;
  wedgeDim?: 2 | 3;
  wedgeDifficulty?: 0 | 1 | 2;
  wedgeTutorialId?: WedgeTutorialId;
  camera: {
    pos: [number, number, number];
    target: [number, number, number];
    isOrtho: boolean;
  };
}

const VALID_SCENE_KINDS = new Set<ExperimentSceneKind>([
  'preset',
  'script',
  'surface',
  'implicit',
  'parametric',
  'wedgeLevel',
  'wedgeTutorial',
  'wedgeRandom',
]);

const VALID_TUTORIAL_IDS = new Set<WedgeTutorialId>(['T1', 'T2', 'T3', 'T4', 'T5', 'T6']);

export function normalizeSeedString(seed: number | string | undefined): string {
  if (typeof seed === 'string' && /^\d+$/.test(seed.trim())) {
    return seed.trim();
  }
  if (typeof seed === 'number' && Number.isFinite(seed) && seed >= 0) {
    return String(Math.trunc(seed));
  }
  return '42';
}

export function inferLegacySceneKind(exp: Pick<GrassmannExperimentV1, 'mode' | 'sceneKind' | 'presetId' | 'script'>): ExperimentSceneKind {
  if (exp.sceneKind && VALID_SCENE_KINDS.has(exp.sceneKind)) {
    return exp.sceneKind;
  }
  if (exp.mode === 'wedge') return 'wedgeLevel';
  if (exp.presetId === 'custom_script') return 'script';
  if (exp.presetId === 'surface_3d') return 'surface';
  if (exp.presetId === 'implicit_expr' || exp.presetId === 'implicit_gpu') return 'implicit';
  if (exp.presetId === 'parametric_expr') return 'parametric';
  if (exp.presetId && exp.presetId.trim().length > 0) return 'preset';
  return exp.script.trim().length > 0 ? 'script' : 'preset';
}

export function serializeExperiment(exp: GrassmannExperimentV1): string {
  return JSON.stringify(exp, null, 2);
}

export function parseGrassmannExperiment(raw: string): GrassmannExperimentV1 | null {
  try {
    const parsed = JSON.parse(raw) as Partial<GrassmannExperimentV1>;
    if (!parsed || parsed.version !== 1) return null;
    const mode: StudioMode =
      parsed.mode === 'wedge' ||
      parsed.mode === 'calculator' ||
      parsed.mode === 'galculator' ||
      parsed.mode === 'coffeeshop'
        ? parsed.mode
        : 'coffeeshop';

    const handles: GrassmannExperimentV1['handles'] = Array.isArray(parsed.handles)
      ? parsed.handles
          .filter(
            (h): h is { handleId: number; pos: [number, number, number] } =>
              Boolean(h) &&
              typeof h.handleId === 'number' &&
              Array.isArray(h.pos) &&
              h.pos.length === 3 &&
              h.pos.every((n) => typeof n === 'number' && Number.isFinite(n))
          )
          .map((h) => ({ handleId: h.handleId, pos: [h.pos[0], h.pos[1], h.pos[2]] }))
      : [];

    const camPos =
      parsed.camera &&
      Array.isArray(parsed.camera.pos) &&
      parsed.camera.pos.length === 3 &&
      parsed.camera.pos.every((n) => typeof n === 'number' && Number.isFinite(n))
        ? ([parsed.camera.pos[0], parsed.camera.pos[1], parsed.camera.pos[2]] as [number, number, number])
        : ([3.4, 2.4, 4.1] as [number, number, number]);

    const camTarget =
      parsed.camera &&
      Array.isArray(parsed.camera.target) &&
      parsed.camera.target.length === 3 &&
      parsed.camera.target.every((n) => typeof n === 'number' && Number.isFinite(n))
        ? ([parsed.camera.target[0], parsed.camera.target[1], parsed.camera.target[2]] as [number, number, number])
        : ([0, 0.15, 0] as [number, number, number]);

    const wedgeSeed: number | string =
      typeof parsed.wedgeSeed === 'string' && /^\d+$/.test(parsed.wedgeSeed.trim())
        ? parsed.wedgeSeed.trim()
        : typeof parsed.wedgeSeed === 'number' && Number.isFinite(parsed.wedgeSeed)
          ? parsed.wedgeSeed
          : 42;

    const out: GrassmannExperimentV1 = {
      version: 1,
      mode,
      presetId: typeof parsed.presetId === 'string' ? parsed.presetId : 'pga3d_slicing',
      algebra: typeof parsed.algebra === 'string' ? parsed.algebra : 'PGA3',
      script: typeof parsed.script === 'string' ? parsed.script : '',
      implicitExpr:
        typeof parsed.implicitExpr === 'string'
          ? parsed.implicitExpr
          : 'sin(x)*cos(y) + sin(y)*cos(z) + sin(z)*cos(x)',
      parametricExpr: {
        fx: typeof parsed.parametricExpr?.fx === 'string' ? parsed.parametricExpr.fx : '(1 + 0.4*v*cos(u/2))*cos(u)',
        fy: typeof parsed.parametricExpr?.fy === 'string' ? parsed.parametricExpr.fy : '0.4*v*sin(u/2)',
        fz: typeof parsed.parametricExpr?.fz === 'string' ? parsed.parametricExpr.fz : '(1 + 0.4*v*cos(u/2))*sin(u)',
      },
      handles,
      wedgeLevel: typeof parsed.wedgeLevel === 'number' && Number.isFinite(parsed.wedgeLevel) ? parsed.wedgeLevel : 1,
      wedgeSeed,
      camera: {
        pos: camPos,
        target: camTarget,
        isOrtho: Boolean(parsed.camera?.isOrtho),
      },
    };

    if (parsed.sceneKind && VALID_SCENE_KINDS.has(parsed.sceneKind)) {
      out.sceneKind = parsed.sceneKind;
    }
    if (typeof parsed.surfaceExpr === 'string') {
      out.surfaceExpr = parsed.surfaceExpr;
    }
    if (typeof parsed.gpuRaymarch === 'boolean') {
      out.gpuRaymarch = parsed.gpuRaymarch;
    }
    if (typeof parsed.bound === 'number' && Number.isFinite(parsed.bound) && parsed.bound > 0) {
      out.bound = parsed.bound;
    }
    if (parsed.wedgeDim === 2 || parsed.wedgeDim === 3) {
      out.wedgeDim = parsed.wedgeDim;
    }
    if (parsed.wedgeDifficulty === 0 || parsed.wedgeDifficulty === 1 || parsed.wedgeDifficulty === 2) {
      out.wedgeDifficulty = parsed.wedgeDifficulty;
    }
    if (parsed.wedgeTutorialId && VALID_TUTORIAL_IDS.has(parsed.wedgeTutorialId)) {
      out.wedgeTutorialId = parsed.wedgeTutorialId;
    }
    if (parsed.params && typeof parsed.params === 'object' && !Array.isArray(parsed.params)) {
      const cleanParams: Record<string, number> = {};
      for (const [k, v] of Object.entries(parsed.params)) {
        if (typeof v === 'number' && Number.isFinite(v)) {
          cleanParams[k] = v;
        }
      }
      if (Object.keys(cleanParams).length > 0) {
        out.params = cleanParams;
      }
    }

    return out;
  } catch {
    return null;
  }
}

export function encodeExperimentToHash(exp: GrassmannExperimentV1): string {
  const json = JSON.stringify(exp);
  const bytes = new TextEncoder().encode(json);
  let bin = '';
  for (let i = 0; i < bytes.length; i++) {
    bin += String.fromCharCode(bytes[i]!);
  }
  const b64 = btoa(bin).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
  return `exp=${b64}`;
}

export function decodeExperimentFromHash(hashParam: string): GrassmannExperimentV1 | null {
  try {
    const padded = hashParam.replace(/-/g, '+').replace(/_/g, '/') + '='.repeat((4 - (hashParam.length % 4)) % 4);
    const bin = atob(padded);
    const bytes = new Uint8Array(bin.length);
    for (let i = 0; i < bin.length; i++) {
      bytes[i] = bin.charCodeAt(i);
    }
    const json = new TextDecoder().decode(bytes);
    return parseGrassmannExperiment(json);
  } catch {
    return null;
  }
}

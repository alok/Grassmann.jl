// Portable Cross-Client `.grassmann.json` Experiment Format (v1)
// Matches native macOS/visionOS LeanCalculator / LeanStudioVision 1:1 so any CoffeeShop
// sketch, 3D surface, implicit/parametric scene, or Wedge puzzle can be exported, copied,
// shared via URL hash (#exp=...), dropped back in, or reopened identically on any platform.

import type { StudioMode } from './studioApp';

export interface GrassmannExperimentV1 {
  version: 1;
  mode: StudioMode;
  presetId: string;
  algebra: string;
  script: string;
  implicitExpr: string;
  parametricExpr: {
    fx: string;
    fy: string;
    fz: string;
  };
  handles: Array<{
    handleId: number;
    pos: [number, number, number];
  }>;
  wedgeLevel: number;
  wedgeSeed: number;
  camera: {
    pos: [number, number, number];
    target: [number, number, number];
    isOrtho: boolean;
  };
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

    return {
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
      wedgeSeed: typeof parsed.wedgeSeed === 'number' && Number.isFinite(parsed.wedgeSeed) ? parsed.wedgeSeed : 42,
      camera: {
        pos: camPos,
        target: camTarget,
        isOrtho: Boolean(parsed.camera?.isOrtho),
      },
    };
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

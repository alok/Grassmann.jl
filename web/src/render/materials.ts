// Custom Museum-Grade GLSL Materials for GSIR Primitives:
// - Fresnel Glass Planes (0x05) with crisp border frame + optional grid
// - Fresnel Glass Spheres (0x07) with studio specular highlights & imaginary geodesic ghost
// - Oriented Bivector Disks & Parallelograms (0x09)
// - GPU-Instanced Flow Particle Comet Streaks (0x0D)
// - Lean-Emitted OPNS/IPNS Shader Cache (0x10) keyed strictly by shader.hash

import * as THREE from 'three';
import type { GsirOpnsUniform, OpnsShaderMeta, RgbaTuple } from '../gsir/types';

export function createFresnelPlaneMaterial(
  rgba: RgbaTuple,
  opts: { gridLines: boolean; selected: boolean; target: boolean; hint: boolean }
): THREE.ShaderMaterial {
  return new THREE.ShaderMaterial({
    transparent: true,
    depthWrite: false,
    side: THREE.DoubleSide,
    uniforms: {
      uColor: { value: new THREE.Color(rgba[0], rgba[1], rgba[2]) },
      uAlpha: { value: Math.max(0.14, Math.min(0.85, rgba[3])) },
      uGridLines: { value: opts.gridLines ? 1.0 : 0.0 },
      uSelected: { value: opts.selected ? 1.0 : 0.0 },
      uTarget: { value: opts.target ? 1.0 : 0.0 },
      uHint: { value: opts.hint ? 1.0 : 0.0 },
    },
    vertexShader: `
      varying vec2 vUv;
      varying vec3 vNormalW;
      varying vec3 vViewDirW;
      void main() {
        vUv = uv;
        vec4 worldPos = modelMatrix * vec4(position, 1.0);
        vNormalW = normalize(mat3(modelMatrix) * normal);
        vViewDirW = normalize(cameraPosition - worldPos.xyz);
        gl_Position = projectionMatrix * viewMatrix * worldPos;
      }
    `,
    fragmentShader: `
      uniform vec3 uColor;
      uniform float uAlpha;
      uniform float uGridLines;
      uniform float uSelected;
      uniform float uTarget;
      uniform float uHint;
      varying vec2 vUv;
      varying vec3 vNormalW;
      varying vec3 vViewDirW;

      void main() {
        vec2 edge = min(vUv, 1.0 - vUv);
        float border = 1.0 - smoothstep(0.008, 0.022, min(edge.x, edge.y));
        float fresnel = pow(1.0 - abs(dot(normalize(vNormalW), normalize(vViewDirW))), 2.2);

        float grid = 0.0;
        if (uGridLines > 0.5) {
          vec2 g = abs(fract(vUv * 8.0 - 0.5) - 0.5) / max(fwidth(vUv * 8.0), vec2(0.001));
          grid = (1.0 - min(min(g.x, g.y), 1.0)) * 0.25;
        }

        vec3 accent = uSelected > 0.5
          ? vec3(0.32, 0.96, 0.58)
          : (uTarget > 0.5 ? vec3(1.0, 0.36, 0.44) : mix(uColor, vec3(1.0), 0.45));

        vec3 col = mix(uColor, accent, clamp(border * 0.85 + fresnel * 0.45, 0.0, 1.0));
        col += accent * grid * 0.5;

        float baseAlpha = uHint > 0.5 ? uAlpha * 0.45 : uAlpha;
        float alpha = clamp(baseAlpha * (0.65 + 0.55 * fresnel) + border * 0.72 + grid * 0.25, 0.0, 0.94);
        gl_FragColor = vec4(col, alpha);
      }
    `,
  });
}

export function createFresnelSphereMaterial(rgba: RgbaTuple, imaginary: boolean): THREE.ShaderMaterial {
  return new THREE.ShaderMaterial({
    transparent: true,
    depthWrite: false,
    side: imaginary ? THREE.DoubleSide : THREE.FrontSide,
    wireframe: imaginary,
    uniforms: {
      uColor: { value: new THREE.Color(rgba[0], rgba[1], rgba[2]) },
      uAlpha: { value: imaginary ? Math.max(0.42, rgba[3]) : Math.max(0.16, Math.min(0.75, rgba[3])) },
      uImaginary: { value: imaginary ? 1.0 : 0.0 },
    },
    vertexShader: `
      varying vec3 vNormalW;
      varying vec3 vViewDirW;
      void main() {
        vec4 worldPos = modelMatrix * vec4(position, 1.0);
        vNormalW = normalize(mat3(modelMatrix) * normal);
        vViewDirW = normalize(cameraPosition - worldPos.xyz);
        gl_Position = projectionMatrix * viewMatrix * worldPos;
      }
    `,
    fragmentShader: `
      uniform vec3 uColor;
      uniform float uAlpha;
      uniform float uImaginary;
      varying vec3 vNormalW;
      varying vec3 vViewDirW;

      void main() {
        vec3 N = normalize(vNormalW);
        vec3 V = normalize(vViewDirW);
        float ndv = abs(dot(N, V));
        float fresnel = pow(1.0 - ndv, 2.4);

        // Two-point studio softbox specular highlights
        vec3 L1 = normalize(vec3(0.55, 0.78, 0.45));
        vec3 L2 = normalize(vec3(-0.7, 0.35, -0.5));
        float spec1 = pow(max(dot(N, normalize(L1 + V)), 0.0), 64.0);
        float spec2 = pow(max(dot(N, normalize(L2 + V)), 0.0), 28.0);

        vec3 base = uImaginary > 0.5 ? mix(uColor, vec3(1.0, 0.36, 0.58), 0.35) : uColor;
        vec3 col = base * (0.45 + 0.55 * ndv) + mix(base, vec3(1.0), 0.65) * fresnel * 0.9;
        col += vec3(1.0, 0.98, 0.95) * spec1 * 0.85 + vec3(0.55, 0.82, 1.0) * spec2 * 0.35;

        float alpha = uImaginary > 0.5
          ? uAlpha * (0.45 + 0.55 * fresnel)
          : clamp(uAlpha * 0.55 + fresnel * 0.62 + spec1 * 0.35, 0.08, 0.92);
        gl_FragColor = vec4(col, alpha);
      }
    `,
  });
}

export function createBivectorMaterial(rgba: RgbaTuple, isDisk: boolean): THREE.ShaderMaterial {
  return new THREE.ShaderMaterial({
    transparent: true,
    depthWrite: false,
    side: THREE.DoubleSide,
    uniforms: {
      uColor: { value: new THREE.Color(rgba[0], rgba[1], rgba[2]) },
      uAlpha: { value: Math.max(0.24, Math.min(0.85, rgba[3])) },
      uIsDisk: { value: isDisk ? 1.0 : 0.0 },
    },
    vertexShader: `
      varying vec2 vUv;
      void main() {
        vUv = uv;
        gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0);
      }
    `,
    fragmentShader: `
      uniform vec3 uColor;
      uniform float uAlpha;
      uniform float uIsDisk;
      varying vec2 vUv;

      void main() {
        float border = 0.0;
        float sweep = 0.0;
        if (uIsDisk > 0.5) {
          vec2 p = vUv * 2.0 - 1.0;
          float r = length(p);
          if (r > 1.0) discard;
          border = smoothstep(0.91, 0.97, r);
          float angle = atan(p.y, p.x);
          float rings = smoothstep(0.92, 0.98, sin(r * 18.849) * 0.5 + 0.5) * 0.16;
          sweep = ((angle + 3.14159265) / 6.2831853) * 0.22 + rings;
        } else {
          vec2 e = min(vUv, 1.0 - vUv);
          border = 1.0 - smoothstep(0.015, 0.036, min(e.x, e.y));
          sweep = (vUv.x * 0.16 + vUv.y * 0.16);
        }

        vec3 rimCol = mix(uColor, vec3(1.0, 0.96, 0.88), 0.55);
        vec3 col = mix(uColor * (0.85 + sweep), rimCol, border);
        float alpha = clamp(uAlpha + border * 0.52, 0.0, 0.96);
        gl_FragColor = vec4(col, alpha);
      }
    `,
  });
}

export function createFlowParticleMaterial(rgba: RgbaTuple, pointSize: number): THREE.ShaderMaterial {
  return new THREE.ShaderMaterial({
    transparent: true,
    depthWrite: false,
    blending: THREE.AdditiveBlending,
    uniforms: {
      uColor: { value: new THREE.Color(rgba[0], rgba[1], rgba[2]) },
      uAlpha: { value: rgba[3] },
      uTime: { value: 0 },
      uSpeed: { value: 1 },
      uSize: { value: Math.max(4.0, pointSize * 120.0) },
    },
    vertexShader: `
      attribute vec3 aEnd;
      attribute float aSeed;
      uniform float uTime;
      uniform float uSpeed;
      uniform float uSize;
      varying float vPhase;
      void main() {
        float phase = fract(uTime * uSpeed + aSeed);
        vPhase = phase;
        vec3 pos = mix(position, aEnd, phase);
        vec4 mvPosition = modelViewMatrix * vec4(pos, 1.0);
        gl_PointSize = clamp(uSize / max(-mvPosition.z, 0.5), 2.5, 22.0);
        gl_Position = projectionMatrix * mvPosition;
      }
    `,
    fragmentShader: `
      uniform vec3 uColor;
      uniform float uAlpha;
      varying float vPhase;
      void main() {
        vec2 c = gl_PointCoord * 2.0 - 1.0;
        float r2 = dot(c, c);
        if (r2 > 1.0) discard;
        float glow = exp(-r2 * 2.8);
        float envelope = sin(vPhase * 3.14159265);
        vec3 col = mix(uColor, vec3(1.0), glow * 0.5);
        gl_FragColor = vec4(col, glow * envelope * uAlpha);
      }
    `,
  });
}

const OPNS_MAX_COEFFS = 64;

const OPNS_VERTEX_SHADER_GLSL1 = `
  varying vec3 vWorldPos;
  varying vec3 vLocalPos;
  void main() {
    vLocalPos = position;
    vec4 wp = modelMatrix * vec4(position, 1.0);
    vWorldPos = wp.xyz;
    gl_Position = projectionMatrix * viewMatrix * wp;
  }
`;

const OPNS_VERTEX_SHADER_GLSL3 = `
  out vec3 vWorldPos;
  out vec3 vLocalPos;
  void main() {
    vLocalPos = position;
    vec4 wp = modelMatrix * vec4(position, 1.0);
    vWorldPos = wp.xyz;
    gl_Position = projectionMatrix * viewMatrix * wp;
  }
`;

function isGlsl3Shader(rawGlsl: string): boolean {
  return /#version\s+300\s+es/.test(rawGlsl) || /\bout\s+vec4\s+\w+/.test(rawGlsl);
}

function stripVersionDirective(rawGlsl: string): string {
  return rawGlsl.replace(/^\s*#version\s+300\s+es\s*\n?/m, '');
}

function wrapLeanOpnsGlsl(rawGlsl: string): string {
  // If Lean emitted a full fragment shader with `void main()`, use it directly.
  if (/\bvoid\s+main\s*\(/.test(rawGlsl)) {
    return rawGlsl;
  }
  // Otherwise, Lean emitted a field evaluator `float evalField(vec3 p)` — wrap with sphere-tracing pass.
  return `
    uniform vec4 uColor;
    uniform float uCoeffs[${OPNS_MAX_COEFFS}];
    uniform int uGrade;
    uniform float uThresh;
    uniform int uMaxSteps;
    uniform float uStepSize;
    uniform int uIsIPNS;
    uniform float uSimTime;
    varying vec3 vWorldPos;
    varying vec3 vLocalPos;

    ${rawGlsl}

    vec3 estimateNormal(vec3 p) {
      float e = max(uThresh, 0.0025);
      return normalize(vec3(
        evalField(p + vec3(e, 0.0, 0.0)) - evalField(p - vec3(e, 0.0, 0.0)),
        evalField(p + vec3(0.0, e, 0.0)) - evalField(p - vec3(0.0, e, 0.0)),
        evalField(p + vec3(0.0, 0.0, e)) - evalField(p - vec3(0.0, 0.0, e))
      ));
    }

    void main() {
      vec3 ro = cameraPosition;
      vec3 rd = normalize(vWorldPos - cameraPosition);
      float t = max(0.0, length(vWorldPos - ro) - 3.5);
      float tMax = t + 7.5;
      float dt = max(uStepSize, 0.02);
      bool hit = false;
      vec3 hitPos = vec3(0.0);
      for (int i = 0; i < 128; i++) {
        if (i >= uMaxSteps || t > tMax) break;
        vec3 p = ro + rd * t;
        float val = abs(evalField(p));
        if (val < max(uThresh, 0.004)) {
          hit = true;
          hitPos = p;
          break;
        }
        t += clamp(val * 0.5, dt * 0.25, dt * 1.5);
      }
      if (!hit) discard;
      vec3 n = estimateNormal(hitPos);
      vec3 l = normalize(vec3(0.5, 0.8, 0.6));
      float diff = max(dot(n, l), 0.18);
      float fres = pow(1.0 - abs(dot(n, -rd)), 2.5);
      vec3 col = uColor.rgb * diff + mix(uColor.rgb, vec3(1.0), 0.65) * fres * 0.7;
      gl_FragColor = vec4(col, clamp(uColor.a, 0.2, 0.95));
    }
  `;
}

/**
 * Caches compiled OPNS/IPNS ShaderMaterials by Lean's shader.hash so live
 * coefficient updates never trigger GLSL recompilation.
 */
export class OpnsShaderCache {
  private readonly materials = new Map<string, THREE.ShaderMaterial>();

  getOrCreate(meta: OpnsShaderMeta): THREE.ShaderMaterial | null {
    const existing = this.materials.get(meta.hash);
    if (existing) return existing;
    if (!meta.glsl) return null;

    const glsl3 = isGlsl3Shader(meta.glsl);
    const coeffsBuf = new Float32Array(OPNS_MAX_COEFFS);
    const mat = new THREE.ShaderMaterial({
      glslVersion: glsl3 ? THREE.GLSL3 : THREE.GLSL1,
      transparent: true,
      depthWrite: false,
      side: THREE.BackSide,
      uniforms: {
        uColor: { value: new THREE.Vector4(0.35, 0.8, 1.0, 0.75) },
        uCoeffs: { value: coeffsBuf },
        uGrade: { value: 4 },
        uThresh: { value: 0.003 },
        uMaxSteps: { value: 80 },
        uStepSize: { value: 0.05 },
        uIsIPNS: { value: 0 },
        uSimTime: { value: 0 },
      },
      vertexShader: glsl3 ? OPNS_VERTEX_SHADER_GLSL3 : OPNS_VERTEX_SHADER_GLSL1,
      fragmentShader: glsl3 ? stripVersionDirective(meta.glsl) : wrapLeanOpnsGlsl(meta.glsl),
    });

    this.materials.set(meta.hash, mat);
    return mat;
  }

  updateUniforms(mat: THREE.ShaderMaterial, item: GsirOpnsUniform, simTime: number): void {
    const u = mat.uniforms;
    if (u.uColor) (u.uColor.value as THREE.Vector4).set(item.rgba[0], item.rgba[1], item.rgba[2], item.rgba[3]);
    if (u.uCoeffs) {
      const dst = u.uCoeffs.value as Float32Array;
      dst.fill(0);
      dst.set(item.coeffs.subarray(0, Math.min(item.coeffs.length, OPNS_MAX_COEFFS)));
    }
    if (u.uGrade) u.uGrade.value = item.grade;
    if (u.uThresh) u.uThresh.value = item.thresh;
    if (u.uMaxSteps) u.uMaxSteps.value = item.maxSteps;
    if (u.uStepSize) u.uStepSize.value = item.stepSize;
    if (u.uIsIPNS) u.uIsIPNS.value = item.isIPNS ? 1 : 0;
    if (u.uSimTime) u.uSimTime.value = simTime;
  }

  dispose(): void {
    for (const mat of this.materials.values()) {
      mat.dispose();
    }
    this.materials.clear();
  }
}

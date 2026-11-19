// Obsidian Studio Environment:
// - Procedural PMREMGenerator studio softbox IBL (zero external HDRI fetch!)
// - Deep charcoal-indigo radial backdrop dome (plus Gallery Alabaster light theme)
// - Analytical screen-space anti-aliased infinite coordinate grid (XZ in 3D, XY in 2D ortho)

import * as THREE from 'three';

/**
 * Generates a procedural 3-point softbox studio environment map using PMREMGenerator.
 * Gives Fresnel spheres, glass planes, and metallic handles museum-grade reflections.
 */
export function createStudioEnvironmentMap(
  renderer: THREE.WebGLRenderer,
  darkTheme: boolean
): THREE.Texture {
  const pmrem = new THREE.PMREMGenerator(renderer);
  pmrem.compileEquirectangularShader();

  const envScene = new THREE.Scene();
  envScene.background = new THREE.Color(darkTheme ? 0x090d18 : 0xe9eef6);

  // Soft studio box walls
  const roomGeo = new THREE.BoxGeometry(24, 16, 24);
  const roomMat = new THREE.MeshBasicMaterial({
    color: darkTheme ? 0x0d1324 : 0xdce4f0,
    side: THREE.BackSide,
  });
  envScene.add(new THREE.Mesh(roomGeo, roomMat));

  // Overhead warm-white key softbox
  const keyPanel = new THREE.Mesh(
    new THREE.PlaneGeometry(10, 10),
    new THREE.MeshBasicMaterial({ color: darkTheme ? 0xfff4e6 : 0xffffff, side: THREE.DoubleSide })
  );
  keyPanel.position.set(4, 7.5, 4);
  keyPanel.lookAt(0, 0, 0);
  envScene.add(keyPanel);

  // Cool cyan fill softbox
  const fillPanel = new THREE.Mesh(
    new THREE.PlaneGeometry(9, 6),
    new THREE.MeshBasicMaterial({ color: darkTheme ? 0x5cc8ff : 0x99d6ff, side: THREE.DoubleSide })
  );
  fillPanel.position.set(-9, 3.5, 4);
  fillPanel.lookAt(0, 0, 0);
  envScene.add(fillPanel);

  // Indigo-violet rim light strip
  const rimPanel = new THREE.Mesh(
    new THREE.PlaneGeometry(12, 3),
    new THREE.MeshBasicMaterial({ color: darkTheme ? 0x8b6dff : 0xc4b5fd, side: THREE.DoubleSide })
  );
  rimPanel.position.set(0, 4.5, -10);
  rimPanel.lookAt(0, 0, 0);
  envScene.add(rimPanel);

  // Warm amber accent strip for metallic highlights
  const warmAccent = new THREE.Mesh(
    new THREE.PlaneGeometry(5, 3),
    new THREE.MeshBasicMaterial({ color: darkTheme ? 0xff9f5a : 0xffcfa3, side: THREE.DoubleSide })
  );
  warmAccent.position.set(9, 1.5, -5);
  warmAccent.lookAt(0, 0, 0);
  envScene.add(warmAccent);

  const renderTarget = pmrem.fromScene(envScene, 0.04);
  pmrem.dispose();
  roomGeo.dispose();
  roomMat.dispose();
  for (const panel of [keyPanel, fillPanel, rimPanel, warmAccent]) {
    panel.geometry.dispose();
    (panel.material as THREE.Material).dispose();
  }
  return renderTarget.texture;
}

/**
 * Obsidian / Gallery radial sky backdrop dome.
 */
export function createBackdropDome(): {
  mesh: THREE.Mesh;
  setTheme: (dark: boolean) => void;
  dispose: () => void;
} {
  const geo = new THREE.SphereGeometry(140, 32, 24);
  const uniforms = {
    uZenith: { value: new THREE.Color(0x05070e) },
    uHorizon: { value: new THREE.Color(0x10182b) },
    uNadir: { value: new THREE.Color(0x060911) },
    uGlow: { value: new THREE.Color(0x1b2b4d) },
  };

  const mat = new THREE.ShaderMaterial({
    side: THREE.BackSide,
    depthWrite: false,
    depthTest: false,
    uniforms,
    vertexShader: `
      varying vec3 vDir;
      void main() {
        vDir = normalize(position);
        gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0);
      }
    `,
    fragmentShader: `
      uniform vec3 uZenith;
      uniform vec3 uHorizon;
      uniform vec3 uNadir;
      uniform vec3 uGlow;
      varying vec3 vDir;
      void main() {
        float y = clamp(vDir.y, -1.0, 1.0);
        vec3 col = y >= 0.0
          ? mix(uHorizon, uZenith, pow(y, 0.65))
          : mix(uHorizon, uNadir, pow(-y, 0.75));
        float horizonBand = exp(-abs(y) * 5.5);
        col += uGlow * horizonBand * 0.22;
        gl_FragColor = vec4(col, 1.0);
      }
    `,
  });

  const mesh = new THREE.Mesh(geo, mat);
  mesh.renderOrder = -1000;
  mesh.frustumCulled = false;

  const setTheme = (dark: boolean) => {
    if (dark) {
      uniforms.uZenith.value.setHex(0x05070e);
      uniforms.uHorizon.value.setHex(0x111a2e);
      uniforms.uNadir.value.setHex(0x060810);
      uniforms.uGlow.value.setHex(0x223866);
    } else {
      uniforms.uZenith.value.setHex(0xe8eef7);
      uniforms.uHorizon.value.setHex(0xf7f9fc);
      uniforms.uNadir.value.setHex(0xe2e8f2);
      uniforms.uGlow.value.setHex(0xdbeafe);
    }
  };

  return {
    mesh,
    setTheme,
    dispose: () => {
      geo.dispose();
      mat.dispose();
    },
  };
}

/**
 * Analytical anti-aliased infinite coordinate grid shader.
 * Switches smoothly between XZ ground plane (3D) and XY plane (2D ortho).
 */
export function createInfiniteGrid(): {
  mesh: THREE.Mesh;
  update: (opts: { visible: boolean; gridSize: number; is2D: boolean; darkTheme: boolean }) => void;
  dispose: () => void;
} {
  const geo = new THREE.PlaneGeometry(2, 2, 1, 1);
  const uniforms = {
    uGridSize: { value: 6.0 },
    uIs2D: { value: 0.0 },
    uMinorColor: { value: new THREE.Color(0x283552) },
    uMajorColor: { value: new THREE.Color(0x425680) },
    uAxisAColor: { value: new THREE.Color(0xe05d72) }, // X
    uAxisBColor: { value: new THREE.Color(0x46b89a) }, // Z (3D) or Y (2D)
    uOpacity: { value: 0.72 },
  };

  const mat = new THREE.ShaderMaterial({
    transparent: true,
    depthWrite: false,
    side: THREE.DoubleSide,
    uniforms,
    vertexShader: `
      uniform float uGridSize;
      uniform float uIs2D;
      varying vec2 vCoord;
      void main() {
        float extent = max(uGridSize * 1.35, 2.0);
        vec2 p = position.xy * extent;
        vCoord = p;
        vec3 worldPos = uIs2D > 0.5 ? vec3(p.x, p.y, -0.002) : vec3(p.x, -0.002, p.y);
        gl_Position = projectionMatrix * modelViewMatrix * vec4(worldPos, 1.0);
      }
    `,
    fragmentShader: `
      uniform float uGridSize;
      uniform vec3 uMinorColor;
      uniform vec3 uMajorColor;
      uniform vec3 uAxisAColor;
      uniform vec3 uAxisBColor;
      uniform float uOpacity;
      varying vec2 vCoord;

      float gridLine(vec2 coord, float scale) {
        vec2 p = coord / scale;
        vec2 grid = abs(fract(p - 0.5) - 0.5) / max(fwidth(p), vec2(0.0001));
        float line = min(grid.x, grid.y);
        return 1.0 - min(line, 1.0);
      }

      void main() {
        float minor = gridLine(vCoord, 0.25) * 0.24;
        float major = gridLine(vCoord, 1.0) * 0.62;

        vec2 fw = max(fwidth(vCoord), vec2(0.0001));
        float axisX = 1.0 - min(abs(vCoord.y) / (fw.y * 1.45), 1.0);
        float axisY = 1.0 - min(abs(vCoord.x) / (fw.x * 1.45), 1.0);

        float dist = length(vCoord) / max(uGridSize * 1.15, 1.0);
        float radialFade = 1.0 - smoothstep(0.55, 1.05, dist);

        vec3 col = mix(uMinorColor, uMajorColor, clamp(major * 1.4, 0.0, 1.0));
        float alpha = max(minor, major);

        if (axisX > 0.01) {
          col = mix(col, uAxisAColor, axisX * 0.9);
          alpha = max(alpha, axisX * 0.85);
        }
        if (axisY > 0.01) {
          col = mix(col, uAxisBColor, axisY * 0.9);
          alpha = max(alpha, axisY * 0.85);
        }

        alpha *= radialFade * uOpacity;
        if (alpha < 0.004) discard;
        gl_FragColor = vec4(col, alpha);
      }
    `,
  });

  const mesh = new THREE.Mesh(geo, mat);
  mesh.renderOrder = -50;
  mesh.frustumCulled = false;

  const update = (opts: { visible: boolean; gridSize: number; is2D: boolean; darkTheme: boolean }) => {
    mesh.visible = opts.visible;
    uniforms.uGridSize.value = Math.max(opts.gridSize || 5, 1);
    uniforms.uIs2D.value = opts.is2D ? 1.0 : 0.0;
    if (opts.darkTheme) {
      uniforms.uMinorColor.value.setHex(0x283552);
      uniforms.uMajorColor.value.setHex(0x4b6294);
      uniforms.uOpacity.value = 0.72;
    } else {
      uniforms.uMinorColor.value.setHex(0xc8d2e2);
      uniforms.uMajorColor.value.setHex(0x94a3b8);
      uniforms.uOpacity.value = 0.85;
    }
  };

  return {
    mesh,
    update,
    dispose: () => {
      geo.dispose();
      mat.dispose();
    },
  };
}

/**
 * Subtle studio floor radial contact shadow & depth cue beneath 3D scenes.
 * Automatically disabled in 2D ortho mode, WebXR passthrough, and full-screen OPNS passes.
 */
export function createStudioContactShadow(): {
  mesh: THREE.Mesh;
  update: (opts: {
    visible: boolean;
    centerX: number;
    centerZ: number;
    floorY: number;
    radius: number;
    darkTheme: boolean;
  }) => void;
  dispose: () => void;
} {
  const geo = new THREE.PlaneGeometry(2, 2, 1, 1);
  geo.rotateX(-Math.PI / 2);

  const uniforms = {
    uColor: { value: new THREE.Color(0x020612) },
    uRimTint: { value: new THREE.Color(0x1e3a5f) },
    uOpacity: { value: 0.48 },
    uDarkTheme: { value: 1.0 },
  };

  const mat = new THREE.ShaderMaterial({
    transparent: true,
    depthWrite: false,
    side: THREE.DoubleSide,
    uniforms,
    vertexShader: `
      varying vec2 vUv;
      void main() {
        vUv = uv * 2.0 - 1.0;
        gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0);
      }
    `,
    fragmentShader: `
      uniform vec3 uColor;
      uniform vec3 uRimTint;
      uniform float uOpacity;
      uniform float uDarkTheme;
      varying vec2 vUv;

      void main() {
        float r2 = dot(vUv, vUv);
        if (r2 >= 1.0) discard;
        // Soft Gaussian contact core + gentle plinth halo falloff
        float core = exp(-r2 * 4.2);
        float halo = exp(-r2 * 1.9) * (1.0 - smoothstep(0.68, 1.0, sqrt(r2)));
        float strength = core * 0.62 + halo * 0.38;
        vec3 col = uDarkTheme > 0.5
          ? mix(uRimTint, uColor, clamp(core * 1.15, 0.0, 1.0))
          : uColor;
        float alpha = strength * uOpacity;
        if (alpha < 0.004) discard;
        gl_FragColor = vec4(col, alpha);
      }
    `,
  });

  const mesh = new THREE.Mesh(geo, mat);
  mesh.renderOrder = -60;
  mesh.frustumCulled = false;

  const update = (opts: {
    visible: boolean;
    centerX: number;
    centerZ: number;
    floorY: number;
    radius: number;
    darkTheme: boolean;
  }) => {
    mesh.visible = opts.visible;
    if (!opts.visible) return;
    const r = Math.max(1.25, Math.min(8.5, opts.radius));
    mesh.position.set(opts.centerX, opts.floorY, opts.centerZ);
    mesh.scale.set(r, 1, r);
    uniforms.uDarkTheme.value = opts.darkTheme ? 1.0 : 0.0;
    if (opts.darkTheme) {
      uniforms.uColor.value.setHex(0x02050d);
      uniforms.uRimTint.value.setHex(0x16294a);
      uniforms.uOpacity.value = 0.52;
    } else {
      uniforms.uColor.value.setHex(0x0f172a);
      uniforms.uRimTint.value.setHex(0x475569);
      uniforms.uOpacity.value = 0.22;
    }
  };

  return {
    mesh,
    update,
    dispose: () => {
      geo.dispose();
      mat.dispose();
    },
  };
}

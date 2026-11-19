// Museum-Grade Three.js 3D PBR + Custom Shader Renderer for Binary GSIR v1 Frames
// STRICT PURITY: Zero GA math, zero normal computation, zero mesh slicing, zero Wedge game logic.
// Strictly consumes Lean-produced GSIR v1 frames and forwards raw pointer/XR gestures to Lean.

import katex from 'katex';
import * as THREE from 'three';
import { OrbitControls } from 'three/examples/jsm/controls/OrbitControls.js';
import { Line2 } from 'three/examples/jsm/lines/Line2.js';
import { LineGeometry } from 'three/examples/jsm/lines/LineGeometry.js';
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js';
import { EffectComposer } from 'three/examples/jsm/postprocessing/EffectComposer.js';
import { OutputPass } from 'three/examples/jsm/postprocessing/OutputPass.js';
import { RenderPass } from 'three/examples/jsm/postprocessing/RenderPass.js';
import { UnrealBloomPass } from 'three/examples/jsm/postprocessing/UnrealBloomPass.js';
import { CSS2DObject, CSS2DRenderer } from 'three/examples/jsm/renderers/CSS2DRenderer.js';

import type { GsirSessionDecoder } from '../gsir/decoder';
import {
  GSIR_NO_LABEL,
  HeaderFlag,
  ModeKind,
  type GsirFrame,
  type GsirMeshAsset,
  type RgbaTuple,
  type Vec3Tuple,
} from '../gsir/types';
import { AxisTriadGizmo, type AxisSnapPreset } from './axisGizmo';
import { ContourOverlayRenderer } from './contourOverlay';
import { createBackdropDome, createInfiniteGrid, createStudioEnvironmentMap } from './environment';
import {
  OpnsShaderCache,
  createBivectorMaterial,
  createFlowParticleMaterial,
  createFresnelPlaneMaterial,
  createFresnelSphereMaterial,
} from './materials';
import { WebXrManager, type XrPinchDragEvent } from './webxr';

export type AccessibleWedgeOp = 'join' | 'meet' | 'add' | 'dot';

export interface ArmedWedgePair {
  idA: number;
  idB: number;
  labelA: string;
  labelB: string;
}

export interface RendererCallbacks {
  onDragHandle?: (handleId: number, pos: Vec3Tuple) => void;
  onSelectObject?: (info: { handleId: number; kind: string; label?: string }) => void;
  onWedgeGesture?: (
    idA: number,
    idB: number,
    dirA: Vec3Tuple,
    dirB: Vec3Tuple,
    isPreview: boolean
  ) => void;
  onWedgePairArmed?: (pair: ArmedWedgePair | null) => void;
  onWedgeSelectSound?: () => void;
  onCameraChange?: (motor: Float32Array, fovDeg: number, distance: number) => void;
  onTelemetry?: (stats: {
    fps: number;
    renderUs: number;
    p95InputToPresentMs: number;
    droppedFrames: number;
    cachedMeshes: number;
    xrActive: boolean;
  }) => void;
}

interface CachedGpuMesh {
  dirtyHash: bigint;
  geometry: THREE.BufferGeometry;
}

interface InteractiveMeta {
  handleId: number;
  anchor: THREE.Vector3;
  kind: 'point' | 'segment' | 'line' | 'plane';
  label?: string;
}

interface WedgePickSlot {
  handleId: number;
  label: string;
  anchorWorld: THREE.Vector3;
  currentWorld: THREE.Vector3;
}

function toColor(rgba: RgbaTuple): THREE.Color {
  return new THREE.Color(rgba[0], rgba[1], rgba[2]);
}

function makePlaneQuadGeometry(
  center: Vec3Tuple,
  u: Vec3Tuple,
  v: Vec3Tuple,
  extent: number
): THREE.BufferGeometry {
  const cx = center[0], cy = center[1], cz = center[2];
  const ux = u[0] * extent, uy = u[1] * extent, uz = u[2] * extent;
  const vx = v[0] * extent, vy = v[1] * extent, vz = v[2] * extent;

  const positions = new Float32Array([
    cx - ux - vx, cy - uy - vy, cz - uz - vz,
    cx + ux - vx, cy + uy - vy, cz + uz - vz,
    cx + ux + vx, cy + uy + vy, cz + uz + vz,
    cx - ux + vx, cy - uy + vy, cz - uz + vz,
  ]);

  // Display normal purely for quad lighting orientation from Lean's orthonormal (u, v) basis
  const nx = u[1] * v[2] - u[2] * v[1];
  const ny = u[2] * v[0] - u[0] * v[2];
  const nz = u[0] * v[1] - u[1] * v[0];
  const normals = new Float32Array([nx, ny, nz, nx, ny, nz, nx, ny, nz, nx, ny, nz]);
  const uvs = new Float32Array([0, 0, 1, 0, 1, 1, 0, 1]);

  const geo = new THREE.BufferGeometry();
  geo.setAttribute('position', new THREE.BufferAttribute(positions, 3));
  geo.setAttribute('normal', new THREE.BufferAttribute(normals, 3));
  geo.setAttribute('uv', new THREE.BufferAttribute(uvs, 2));
  geo.setIndex([0, 1, 2, 0, 2, 3]);
  return geo;
}

function makeBivectorGeometry(
  origin: Vec3Tuple,
  u: Vec3Tuple,
  v: Vec3Tuple,
  isDisk: boolean
): THREE.BufferGeometry {
  const ox = origin[0], oy = origin[1], oz = origin[2];
  let positions: Float32Array;
  if (isDisk) {
    // Centered quad [-1..1] along u, v masked to circle in fragment shader
    positions = new Float32Array([
      ox - u[0] - v[0], oy - u[1] - v[1], oz - u[2] - v[2],
      ox + u[0] - v[0], oy + u[1] - v[1], oz + u[2] - v[2],
      ox + u[0] + v[0], oy + u[1] + v[1], oz + u[2] + v[2],
      ox - u[0] + v[0], oy - u[1] + v[1], oz - u[2] + v[2],
    ]);
  } else {
    // Parallelogram from origin spanned by u and v
    positions = new Float32Array([
      ox, oy, oz,
      ox + u[0], oy + u[1], oz + u[2],
      ox + u[0] + v[0], oy + u[1] + v[1], oz + u[2] + v[2],
      ox + v[0], oy + v[1], oz + v[2],
    ]);
  }
  const uvs = new Float32Array([0, 0, 1, 0, 1, 1, 0, 1]);
  const geo = new THREE.BufferGeometry();
  geo.setAttribute('position', new THREE.BufferAttribute(positions, 3));
  geo.setAttribute('uv', new THREE.BufferAttribute(uvs, 2));
  geo.setIndex([0, 1, 2, 0, 2, 3]);
  return geo;
}

export class GrassmannSceneRenderer {
  private readonly container: HTMLElement;
  private readonly callbacks: RendererCallbacks;
  private readonly renderer: THREE.WebGLRenderer;
  private readonly labelRenderer: CSS2DRenderer;
  private readonly scene: THREE.Scene;
  private readonly perspCamera: THREE.PerspectiveCamera;
  private readonly orthoCamera: THREE.OrthographicCamera;
  private activeCamera: THREE.PerspectiveCamera | THREE.OrthographicCamera;
  private readonly controls: OrbitControls;
  private readonly composer: EffectComposer;
  private readonly renderPass: RenderPass;
  private readonly bloomPass: UnrealBloomPass;

  private readonly backdrop: ReturnType<typeof createBackdropDome>;
  private readonly grid: ReturnType<typeof createInfiniteGrid>;
  private envMapDark: THREE.Texture;
  private envMapLight: THREE.Texture;

  private readonly dynamicGroup = new THREE.Group();
  private readonly labelGroup = new THREE.Group();
  private readonly opnsGroup = new THREE.Group();
  private readonly contourOverlay: ContourOverlayRenderer;
  private readonly axisGizmo: AxisTriadGizmo;
  private readonly opnsCache = new OpnsShaderCache();
  private readonly opnsResolution = new THREE.Vector2(800, 600);
  private readonly opnsInvViewProj = new THREE.Matrix4();
  private readonly meshGeoCache = new Map<bigint, CachedGpuMesh>();
  private readonly lineMaterials: LineMaterial[] = [];
  private readonly flowMaterials: THREE.ShaderMaterial[] = [];
  private readonly interactiveObjects: THREE.Object3D[] = [];

  // Shared unit geometries
  private readonly unitSphereGeo = new THREE.SphereGeometry(1, 28, 20);
  private readonly fresnelSphereGeo = new THREE.SphereGeometry(1, 48, 32);
  private readonly imaginarySphereGeo = new THREE.IcosahedronGeometry(1, 2);
  private readonly ringTorusGeo = new THREE.TorusGeometry(1.45, 0.12, 12, 36);
  private readonly hollowTorusGeo = new THREE.TorusGeometry(1.0, 0.22, 14, 36);
  private readonly arrowConeGeo = new THREE.ConeGeometry(0.065, 0.2, 16);
  private readonly opnsBoxGeo = new THREE.BoxGeometry(8, 8, 8);
  private readonly opnsQuadGeo = new THREE.PlaneGeometry(2, 2);

  // Wedge 2D/3D green rubber-band SVG overlay
  private readonly wedgeSvg: SVGSVGElement;

  // WebXR support
  readonly xr: WebXrManager;

  // Interaction state
  private readonly raycaster = new THREE.Raycaster();
  private readonly pointerNdc = new THREE.Vector2();
  private readonly dragPlane = new THREE.Plane();
  private readonly dragHitPoint = new THREE.Vector3();
  private activeDrag: {
    handleId: number;
    offset: THREE.Vector3;
    startClientX: number;
    startClientY: number;
    moved: boolean;
    meta: InteractiveMeta;
  } | null = null;
  private hoveredHandleId: number | null = null;
  private wedgeFirst: WedgePickSlot | null = null;
  private wedgeSecond: WedgePickSlot | null = null;
  private wedgeDraggingSlot: 1 | 2 | null = null;
  private lastWedgePreviewMs = 0;
  private winPulses: Array<{ mesh: THREE.Mesh; mat: THREE.MeshBasicMaterial; startMs: number; durationMs: number }> = [];

  // True input-to-present latency + dropped frame telemetry
  private pendingInputTsMs: number | null = null;
  private readonly inputToPresentSamples: number[] = [];
  private lastRafMs = performance.now();
  private droppedFrames = 0;

  // Frame / UI state
  private currentFrame: GsirFrame | null = null;
  private darkTheme = true;
  private themeOverride: boolean | null = null;
  private forceGridOverride: boolean | null = null;
  private forceWireframeOverride = false;
  private isOrtho = false;
  private orthoScale = 3.0;
  private lastCameraSyncMs = 0;
  private suppressCameraSync = false;
  private cameraTransition: {
    startPos: THREE.Vector3;
    endPos: THREE.Vector3;
    startTarget: THREE.Vector3;
    endTarget: THREE.Vector3;
    startMs: number;
    durationMs: number;
  } | null = null;
  private width = 800;
  private height = 600;
  private simTime = 0;
  private resizeObserver: ResizeObserver;
  private rafFrames = 0;
  private fpsWindowStart = performance.now();
  private lastFps = 60;
  private disposed = false;

  constructor(container: HTMLElement, callbacks: RendererCallbacks = {}) {
    this.container = container;
    this.callbacks = callbacks;

    this.width = Math.max(container.clientWidth, 320);
    this.height = Math.max(container.clientHeight, 240);

    // WebGL2 Renderer with ACES Filmic tone mapping + crisp antialiasing
    this.renderer = new THREE.WebGLRenderer({
      antialias: true,
      alpha: false,
      powerPreference: 'high-performance',
      preserveDrawingBuffer: true, // enables clean PNG export at any moment
    });
    this.renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
    this.renderer.setSize(this.width, this.height);
    this.renderer.toneMapping = THREE.ACESFilmicToneMapping;
    this.renderer.toneMappingExposure = 1.12;
    this.renderer.outputColorSpace = THREE.SRGBColorSpace;
    this.renderer.domElement.className = 'gs-webgl-canvas';
    container.appendChild(this.renderer.domElement);

    // CSS2D Label Layer (KaTeX + crisp typography)
    this.labelRenderer = new CSS2DRenderer();
    this.labelRenderer.setSize(this.width, this.height);
    this.labelRenderer.domElement.className = 'gs-label-layer';
    container.appendChild(this.labelRenderer.domElement);

    // Wedge green rubber-band gesture SVG overlay
    this.wedgeSvg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    this.wedgeSvg.setAttribute('class', 'gs-wedge-svg');
    container.appendChild(this.wedgeSvg);

    // 2D Contour PiP Inset (0x0F CONTOUR_OVERLAY)
    this.contourOverlay = new ContourOverlayRenderer();
    container.appendChild(this.contourOverlay.element);

    // Interactive 3D Axis Triad Gizmo (bottom-right)
    this.axisGizmo = new AxisTriadGizmo((preset) => this.snapCamera(preset));
    container.appendChild(this.axisGizmo.element);

    // Scene & Studio IBL
    this.scene = new THREE.Scene();
    this.envMapDark = createStudioEnvironmentMap(this.renderer, true);
    this.envMapLight = createStudioEnvironmentMap(this.renderer, false);
    this.scene.environment = this.envMapDark;

    // 3-Point Studio Lighting
    const hemi = new THREE.HemisphereLight(0xdbeafe, 0x161c2e, 0.72);
    this.scene.add(hemi);
    const keyLight = new THREE.DirectionalLight(0xfff6eb, 1.45);
    keyLight.position.set(6, 9, 7);
    this.scene.add(keyLight);
    const fillLight = new THREE.DirectionalLight(0x60a5fa, 0.65);
    fillLight.position.set(-7, 4, -5);
    this.scene.add(fillLight);
    const rimLight = new THREE.DirectionalLight(0x93c5fd, 0.38);
    rimLight.position.set(-5, 5, -7);
    this.scene.add(rimLight);

    // Backdrop & Infinite AA Grid
    this.backdrop = createBackdropDome();
    this.scene.add(this.backdrop.mesh);
    this.grid = createInfiniteGrid();
    this.scene.add(this.grid.mesh);

    this.scene.add(this.dynamicGroup);
    this.scene.add(this.opnsGroup);
    this.scene.add(this.labelGroup);

    // Cameras (Perspective + 2D Ortho)
    const aspect = this.width / this.height;
    this.perspCamera = new THREE.PerspectiveCamera(45, aspect, 0.05, 400);
    this.perspCamera.position.set(3.8, 2.8, 4.8);
    this.perspCamera.lookAt(0, 0, 0);

    this.orthoCamera = new THREE.OrthographicCamera(
      -this.orthoScale * aspect,
      this.orthoScale * aspect,
      this.orthoScale,
      -this.orthoScale,
      -50,
      50
    );
    this.orthoCamera.position.set(0, 0, 10);
    this.orthoCamera.lookAt(0, 0, 0);
    this.activeCamera = this.perspCamera;

    // Smooth Damped OrbitControls
    this.controls = new OrbitControls(this.activeCamera, this.renderer.domElement);
    this.controls.enableDamping = true;
    this.controls.dampingFactor = 0.08;
    this.controls.rotateSpeed = 0.85;
    this.controls.zoomSpeed = 1.05;
    this.controls.addEventListener('start', () => {
      this.cameraTransition = null;
    });
    this.controls.addEventListener('change', () => this.maybeEmitCameraChange());

    // Post-processing Composer with calibrated subtle bloom (no surface hotspot glare)
    this.composer = new EffectComposer(this.renderer);
    this.renderPass = new RenderPass(this.scene, this.activeCamera);
    this.bloomPass = new UnrealBloomPass(new THREE.Vector2(this.width, this.height), 0.2, 0.32, 0.96);
    this.composer.addPass(this.renderPass);
    this.composer.addPass(this.bloomPass);
    this.composer.addPass(new OutputPass());

    // WebXR Manager (4-slot gaze+pinch + 1.5x framebuffer cap)
    this.xr = new WebXrManager(this.renderer, this.scene, {
      onPinch: (ev) => this.handleXrPinch(ev),
      onTwoHandPinch: (a, b, commit) => this.handleXrTwoHandPinch(a, b, commit),
    });

    // Pointer listeners on canvas
    const dom = this.renderer.domElement;
    dom.addEventListener('pointerdown', this.onPointerDown);
    window.addEventListener('pointermove', this.onPointerMove);
    window.addEventListener('pointerup', this.onPointerUp);

    // Resize observer
    this.resizeObserver = new ResizeObserver(() => this.handleResize());
    this.resizeObserver.observe(container);

    // Start XR-compatible animation loop
    this.renderer.setAnimationLoop(this.renderLoop);
  }

  /**
   * Apply a decoded GSIR v1 frame + session mesh cache into the Three.js scene.
   */
  applyFrame(
    frame: GsirFrame,
    decoder: GsirSessionDecoder,
    syncCamera = false,
    inputTimestampMs?: number
  ): void {
    this.currentFrame = frame;
    this.simTime = frame.header.simTime;
    if (typeof inputTimestampMs === 'number' && Number.isFinite(inputTimestampMs)) {
      this.pendingInputTsMs = inputTimestampMs;
    }

    // 1. Update cached MeshAsset BufferGeometries ONLY when dirtyHash changes (#17 Fix #1 CCW winding)
    for (const asset of frame.meshAssets) {
      this.ensureCachedMeshGeometry(asset);
    }

    // 2. Theme, grid, and 2D/3D Ortho camera mode (#17 Fix #5)
    const frameDark = (frame.header.flags & HeaderFlag.DARK_THEME) !== 0;
    const is2D = (frame.header.flags & HeaderFlag.IS_2D) !== 0;
    const wantOrtho = is2D || Boolean(frame.camera?.isOrtho);
    const gridVisible =
      this.forceGridOverride !== null
        ? this.forceGridOverride
        : (frame.header.flags & HeaderFlag.GRID_ENABLED) !== 0;

    if (frame.camera) {
      this.orthoScale = Math.max(0.25, frame.camera.orthoScale || 3.0);
      if (frame.camera.fovDeg > 5 && frame.camera.fovDeg < 150) {
        this.perspCamera.fov = frame.camera.fovDeg;
        this.perspCamera.updateProjectionMatrix();
      }
      if (syncCamera) {
        this.applyLeanCamera(frame.camera.viewMat4, frame.camera.distance, wantOrtho);
      }
    }

    this.setOrthoMode(wantOrtho);
    this.setDarkTheme(this.themeOverride !== null ? this.themeOverride : frameDark);
    this.grid.update({
      visible: gridVisible,
      gridSize: frame.header.gridSize || 5,
      is2D: wantOrtho,
      darkTheme: this.darkTheme,
    });

    // 3. Rebuild dynamic primitives (reusing cached mesh BufferGeometries & OPNS ShaderMaterials!)
    this.clearDynamicGroup();
    const labelTexts = frame.meta?.labels ?? [];
    const renderedLabelIndices = new Set<number>();
    const dedicatedLabelIndices = new Set<number>(frame.labels.map((l) => l.textIdx));

    // 0x02 POINTS (strictly gated on pt.draggable; handleId = 0 is valid!)
    for (const pt of frame.points) {
      const r = Math.max(0.03, pt.radius || 0.08);
      const col = toColor(pt.rgba);
      const isHovered = pt.draggable && this.hoveredHandleId === pt.handleId;

      const geo = pt.hollow ? this.hollowTorusGeo : this.unitSphereGeo;
      const mat = new THREE.MeshPhysicalMaterial({
        color: col,
        roughness: pt.draggable ? 0.16 : 0.32,
        metalness: pt.draggable ? 0.25 : 0.1,
        clearcoat: 0.9,
        clearcoatRoughness: 0.1,
        transparent: pt.rgba[3] < 0.99 || pt.hint,
        opacity: pt.hint ? Math.min(0.45, pt.rgba[3]) : pt.rgba[3],
        emissive: pt.selected
          ? new THREE.Color(0x22c55e)
          : pt.target
            ? new THREE.Color(0xf43f5e)
            : isHovered
              ? col
              : new THREE.Color(0x000000),
        emissiveIntensity: pt.selected ? 0.85 : pt.target ? 0.65 : isHovered ? 0.55 : 0.08,
      });

      const mesh = new THREE.Mesh(geo, mat);
      mesh.position.set(pt.pos[0], pt.pos[1], pt.pos[2]);
      mesh.scale.setScalar(isHovered ? r * 1.18 : r);
      this.dynamicGroup.add(mesh);

      if (pt.draggable) {
        mesh.userData.interactive = {
          handleId: pt.handleId,
          anchor: new THREE.Vector3(pt.pos[0], pt.pos[1], pt.pos[2]),
          kind: 'point',
          label: pt.labelIdx !== GSIR_NO_LABEL ? labelTexts[pt.labelIdx] : undefined,
        } satisfies InteractiveMeta;
        this.interactiveObjects.push(mesh);
      }

      // Selection / target / hover halo ring
      if (pt.selected || pt.target || isHovered) {
        const ringMat = new THREE.MeshBasicMaterial({
          color: pt.selected ? 0x4ade80 : pt.target ? 0xfb7185 : 0x7dd3fc,
          transparent: true,
          opacity: pt.selected ? 0.92 : 0.72,
          side: THREE.DoubleSide,
        });
        const ring = new THREE.Mesh(this.ringTorusGeo, ringMat);
        ring.position.copy(mesh.position);
        ring.scale.setScalar(r * 1.12);
        ring.lookAt(this.activeCamera.position);
        this.dynamicGroup.add(ring);
      }

      if (
        pt.labelIdx !== GSIR_NO_LABEL &&
        labelTexts[pt.labelIdx] &&
        !dedicatedLabelIndices.has(pt.labelIdx) &&
        !renderedLabelIndices.has(pt.labelIdx)
      ) {
        renderedLabelIndices.add(pt.labelIdx);
        this.addLabelObject(
          [pt.pos[0], pt.pos[1] + r * 1.9, pt.pos[2]],
          labelTexts[pt.labelIdx]!,
          pt.rgba,
          false
        );
      }
    }

    // 0x03 SEGMENTS (Screen-space AA Line2 + optional arrowhead + dashed)
    for (const seg of frame.segments) {
      this.addThickPolyline(
        [seg.a[0], seg.a[1], seg.a[2], seg.b[0], seg.b[1], seg.b[2]],
        seg.width,
        seg.rgba,
        seg.dashed,
        seg.draggable ? seg.handleId : null,
        'segment',
        [
          (seg.a[0] + seg.b[0]) * 0.5,
          (seg.a[1] + seg.b[1]) * 0.5,
          (seg.a[2] + seg.b[2]) * 0.5,
        ]
      );

      if (seg.arrow) {
        const start = new THREE.Vector3(seg.a[0], seg.a[1], seg.a[2]);
        const end = new THREE.Vector3(seg.b[0], seg.b[1], seg.b[2]);
        const dir = end.clone().sub(start);
        if (dir.lengthSq() > 1e-8) {
          dir.normalize();
          const coneMat = new THREE.MeshStandardMaterial({
            color: toColor(seg.rgba),
            emissive: toColor(seg.rgba),
            emissiveIntensity: 0.25,
            roughness: 0.25,
            metalness: 0.2,
          });
          const cone = new THREE.Mesh(this.arrowConeGeo, coneMat);
          cone.position.copy(end);
          cone.quaternion.setFromUnitVectors(new THREE.Vector3(0, 1, 0), dir);
          this.dynamicGroup.add(cone);
        }
      }
    }

    // 0x04 LINES (Infinite clipped lines: origin ± dir * clip)
    for (const ln of frame.lines) {
      const clip = Math.max(0.5, ln.clip || 6.0);
      const ax = ln.origin[0] - ln.dir[0] * clip;
      const ay = ln.origin[1] - ln.dir[1] * clip;
      const az = ln.origin[2] - ln.dir[2] * clip;
      const bx = ln.origin[0] + ln.dir[0] * clip;
      const by = ln.origin[1] + ln.dir[1] * clip;
      const bz = ln.origin[2] + ln.dir[2] * clip;
      const rgba: RgbaTuple = ln.selected
        ? [0.3, 0.96, 0.55, 1]
        : ln.target
          ? [1.0, 0.36, 0.44, 1]
          : ln.rgba;
      this.addThickPolyline(
        [ax, ay, az, bx, by, bz],
        ln.selected ? Math.max(3.2, ln.width * 1.4) : ln.width,
        rgba,
        ln.dashed || ln.hint,
        ln.draggable ? ln.handleId : null,
        'line',
        ln.origin
      );
    }

    // 0x05 PLANES (Fresnel glass translucent quads spanned by Lean's u, v)
    for (const pl of frame.planes) {
      const geo = makePlaneQuadGeometry(pl.center, pl.u, pl.v, Math.max(0.1, pl.extent || 2.0));
      const mat = createFresnelPlaneMaterial(pl.rgba, {
        gridLines: pl.gridLines,
        selected: pl.selected,
        target: pl.target,
        hint: pl.hint,
        darkTheme: this.darkTheme,
      });
      const mesh = new THREE.Mesh(geo, mat);
      mesh.renderOrder = 2;
      this.dynamicGroup.add(mesh);

      if (pl.draggable) {
        mesh.userData.interactive = {
          handleId: pl.handleId,
          anchor: new THREE.Vector3(pl.center[0], pl.center[1], pl.center[2]),
          kind: 'plane',
          label: pl.labelIdx !== GSIR_NO_LABEL ? labelTexts[pl.labelIdx] : undefined,
        } satisfies InteractiveMeta;
        this.interactiveObjects.push(mesh);
      }

      if (
        pl.labelIdx !== GSIR_NO_LABEL &&
        labelTexts[pl.labelIdx] &&
        !dedicatedLabelIndices.has(pl.labelIdx) &&
        !renderedLabelIndices.has(pl.labelIdx)
      ) {
        renderedLabelIndices.add(pl.labelIdx);
        // Place plane label near a clean front edge/corner so it never collides with center handles or intersection circles!
        const ext = Math.max(0.1, pl.extent || 2.0) * 0.62;
        const labelPos: Vec3Tuple = [
          pl.center[0] + pl.u[0] * ext + pl.v[0] * ext,
          pl.center[1] + pl.u[1] * ext + pl.v[1] * ext,
          pl.center[2] + pl.u[2] * ext + pl.v[2] * ext,
        ];
        this.addLabelObject(labelPos, labelTexts[pl.labelIdx]!, pl.rgba, false);
      }
    }

    // 0x06 CIRCLES (96-segment smooth Line2 rings; dashed when imaginary)
    const CIRCLE_SEGS = 96;
    for (const c of frame.circles) {
      const pts: number[] = [];
      for (let i = 0; i <= CIRCLE_SEGS; i++) {
        const theta = (i / CIRCLE_SEGS) * Math.PI * 2;
        const ct = Math.cos(theta) * c.radius;
        const st = Math.sin(theta) * c.radius;
        pts.push(
          c.center[0] + ct * c.u[0] + st * c.v[0],
          c.center[1] + ct * c.u[1] + st * c.v[1],
          c.center[2] + ct * c.u[2] + st * c.v[2]
        );
      }
      this.addThickPolyline(pts, c.width || 2.2, c.rgba, c.imaginary, null, 'segment', c.center);
      if (c.labelIdx !== GSIR_NO_LABEL && labelTexts[c.labelIdx]) {
        this.addLabelObject(c.center, labelTexts[c.labelIdx]!, c.rgba, false);
      }
    }

    // 0x07 SPHERES (Fresnel glass spheres; wireframe geodesic when imaginary)
    for (const sp of frame.spheres) {
      const geo = sp.imaginary ? this.imaginarySphereGeo : this.fresnelSphereGeo;
      const mat = createFresnelSphereMaterial(sp.rgba, sp.imaginary);
      const mesh = new THREE.Mesh(geo, mat);
      mesh.position.set(sp.center[0], sp.center[1], sp.center[2]);
      mesh.scale.setScalar(Math.max(0.01, sp.radius));
      mesh.renderOrder = 3;
      this.dynamicGroup.add(mesh);

      if (sp.labelIdx !== GSIR_NO_LABEL && labelTexts[sp.labelIdx]) {
        this.addLabelObject(
          [sp.center[0], sp.center[1] + sp.radius + 0.14, sp.center[2]],
          labelTexts[sp.labelIdx]!,
          sp.rgba,
          false
        );
      }
    }

    // 0x08 POINT_PAIRS (Twin glowing endpoints + dashed dipole connector)
    for (const pp of frame.pointPairs) {
      const r = Math.max(0.035, pp.radius || 0.08);
      const geo = pp.imaginary ? this.hollowTorusGeo : this.unitSphereGeo;
      for (const pos of [pp.p1, pp.p2]) {
        const mat = new THREE.MeshPhysicalMaterial({
          color: toColor(pp.rgba),
          roughness: 0.18,
          metalness: 0.25,
          clearcoat: 1.0,
          emissive: toColor(pp.rgba),
          emissiveIntensity: 0.35,
          transparent: pp.rgba[3] < 0.99,
          opacity: pp.rgba[3],
        });
        const m = new THREE.Mesh(geo, mat);
        m.position.set(pos[0], pos[1], pos[2]);
        m.scale.setScalar(r);
        this.dynamicGroup.add(m);
      }
      if (pp.showLink) {
        this.addThickPolyline(
          [pp.p1[0], pp.p1[1], pp.p1[2], pp.p2[0], pp.p2[1], pp.p2[2]],
          1.8,
          [pp.rgba[0], pp.rgba[1], pp.rgba[2], Math.min(0.75, pp.rgba[3])],
          true,
          null,
          'segment',
          pp.p1
        );
      }
    }

    // 0x09 BIVECTOR_DISKS (Oriented translucent parallelogram / disk + perimeter arrow)
    for (const bv of frame.bivectorDisks) {
      const geo = makeBivectorGeometry(bv.origin, bv.u, bv.v, bv.isDisk);
      const mat = createBivectorMaterial(bv.rgba, bv.isDisk);
      const mesh = new THREE.Mesh(geo, mat);
      mesh.renderOrder = 2;
      this.dynamicGroup.add(mesh);

      if (bv.orientationArrow) {
        const tipPos = bv.isDisk
          ? new THREE.Vector3(
              bv.origin[0] + bv.u[0],
              bv.origin[1] + bv.u[1],
              bv.origin[2] + bv.u[2]
            )
          : new THREE.Vector3(
              bv.origin[0] + bv.u[0] + bv.v[0] * 0.5,
              bv.origin[1] + bv.u[1] + bv.v[1] * 0.5,
              bv.origin[2] + bv.u[2] + bv.v[2] * 0.5
            );
        const tangent = new THREE.Vector3(bv.v[0], bv.v[1], bv.v[2]);
        if (tangent.lengthSq() > 1e-8) {
          tangent.normalize();
          const coneMat = new THREE.MeshBasicMaterial({ color: toColor(bv.rgba) });
          const cone = new THREE.Mesh(this.arrowConeGeo, coneMat);
          cone.position.copy(tipPos);
          cone.quaternion.setFromUnitVectors(new THREE.Vector3(0, 1, 0), tangent);
          cone.scale.setScalar(0.58);
          this.dynamicGroup.add(cone);
        }
      }
    }

    // 0x0A MESH_REFS (Uses cached zero-copy BufferGeometry from 0x0B MESH_ASSETS!)
    for (const mr of frame.meshRefs) {
      const asset = decoder.getCachedMesh(mr.meshId);
      if (asset) {
        this.ensureCachedMeshGeometry(asset);
      }
      const cached = this.meshGeoCache.get(mr.meshId);
      if (!cached) continue;

      const wantWire = mr.wireframe || this.forceWireframeOverride;
      const isGhost = mr.rgba[3] < 0.99;
      const baseColor = mr.useVertexColors ? new THREE.Color(0xffffff) : toColor(mr.rgba);
      if (!this.darkTheme && isGhost && !mr.useVertexColors) {
        // Keep translucent ghost halves crisp and legible against bright Gallery Daylight backdrops
        baseColor.multiplyScalar(0.42);
      }
      const mat = new THREE.MeshPhysicalMaterial({
        color: baseColor,
        vertexColors: mr.useVertexColors && cached.geometry.hasAttribute('color'),
        roughness: isGhost ? 0.18 : 0.28,
        metalness: isGhost ? 0.08 : 0.14,
        clearcoat: isGhost ? 0.85 : 0.36,
        clearcoatRoughness: isGhost ? 0.14 : 0.22,
        sheen: isGhost ? 0.55 : 0.32,
        sheenRoughness: 0.45,
        sheenColor: new THREE.Color(this.darkTheme ? 0x93c5fd : 0x334155),
        envMapIntensity: this.darkTheme ? 1.18 : 0.95,
        transparent: isGhost,
        opacity: !this.darkTheme && isGhost ? Math.max(mr.rgba[3], 0.34) : mr.rgba[3],
        depthWrite: !isGhost,
        side: mr.doubleSided ? THREE.DoubleSide : THREE.FrontSide,
        wireframe: wantWire,
      });

      const mesh = new THREE.Mesh(cached.geometry, mat);
      mesh.matrixAutoUpdate = false;
      mesh.matrix.fromArray(mr.modelMat4);
      mesh.matrixWorldNeedsUpdate = true;
      mesh.userData.sharedGeometry = true; // DO NOT dispose cached BufferGeometry on frame clear!
      this.dynamicGroup.add(mesh);

      // Subtle wireframe sheen overlay when requested via override on solid mesh
      if (mr.wireframe && !this.forceWireframeOverride) {
        // Already rendered wireframe via mat.wireframe
      }
    }

    // 0x0C CURVES (Thick Line2 polylines directly from curve.xyz)
    for (const curve of frame.curves) {
      if (curve.ptCount < 2) continue;
      const coords = Array.from(curve.xyz);
      if (curve.closed) {
        coords.push(curve.xyz[0]!, curve.xyz[1]!, curve.xyz[2]!);
      }
      this.addThickPolyline(coords, curve.width || 2.2, curve.rgba, curve.dashed, null, 'segment', [
        curve.xyz[0]!,
        curve.xyz[1]!,
        curve.xyz[2]!,
      ]);
    }

    // 0x0D FLOW_PARTICLES (GPU-instanced velocity-colored luminous tapered ribbons)
    for (const fp of frame.flowParticles) {
      if (fp.particleCount === 0) continue;
      // Unit 4-segment tapered strip quad along uv.x ∈ [0,1], uv.y ∈ [0,1]
      const basePlane = new THREE.PlaneGeometry(1, 1, 4, 1);
      const instGeo = new THREE.InstancedBufferGeometry();
      instGeo.index = basePlane.index;
      instGeo.setAttribute('position', basePlane.getAttribute('position'));
      instGeo.setAttribute('uv', basePlane.getAttribute('uv'));
      instGeo.instanceCount = fp.particleCount;

      instGeo.setAttribute('aStart', new THREE.InstancedBufferAttribute(new Float32Array(fp.starts), 3));
      instGeo.setAttribute('aEnd', new THREE.InstancedBufferAttribute(new Float32Array(fp.ends), 3));
      const seeds = new Float32Array(fp.particleCount);
      for (let i = 0; i < fp.particleCount; i++) {
        seeds[i] = (i * 0.61803398875) % 1;
      }
      instGeo.setAttribute('aSeed', new THREE.InstancedBufferAttribute(seeds, 1));

      const mat = createFlowParticleMaterial(fp.rgba, fp.pointSize);
      mat.uniforms.uSpeed!.value = fp.speed || 0.6;
      mat.uniforms.uTime!.value = this.simTime;
      this.flowMaterials.push(mat);

      const ribbons = new THREE.Mesh(instGeo, mat);
      ribbons.frustumCulled = false;
      ribbons.renderOrder = 4;
      this.dynamicGroup.add(ribbons);
    }

    // 0x0E LABELS (CSS2DRenderer + KaTeX typography)
    for (const lb of frame.labels) {
      const text = labelTexts[lb.textIdx];
      if (!text) continue;
      this.addLabelObject(lb.pos, text, lb.rgba, lb.isLatex);
    }

    // 0x0F CONTOUR_OVERLAY (2D Picture-in-Picture Canvas)
    this.contourOverlay.update(frame.contourOverlay, labelTexts, this.darkTheme);

    // 0x10 OPNS_UNIFORMS (Cached Lean-emitted GLSL ShaderMaterial pass)
    this.updateOpnsGroup(frame);
  }

  setThemeOverride(dark: boolean | null): void {
    this.themeOverride = dark;
    if (dark !== null) {
      this.setDarkTheme(dark);
    } else if (this.currentFrame) {
      this.setDarkTheme((this.currentFrame.header.flags & HeaderFlag.DARK_THEME) !== 0);
    }
  }

  setDarkTheme(dark: boolean): void {
    if (this.darkTheme === dark) return;
    this.darkTheme = dark;
    this.scene.environment = dark ? this.envMapDark : this.envMapLight;
    this.backdrop.setTheme(dark);
    for (const child of this.dynamicGroup.children) {
      if (child instanceof THREE.Mesh && child.material instanceof THREE.ShaderMaterial && child.material.uniforms.uDarkTheme) {
        child.material.uniforms.uDarkTheme.value = dark ? 1.0 : 0.0;
      }
    }
    if (this.currentFrame) {
      this.grid.update({
        visible:
          this.forceGridOverride !== null
            ? this.forceGridOverride
            : (this.currentFrame.header.flags & HeaderFlag.GRID_ENABLED) !== 0,
        gridSize: this.currentFrame.header.gridSize || 5,
        is2D: this.isOrtho,
        darkTheme: dark,
      });
      this.contourOverlay.update(
        this.currentFrame.contourOverlay,
        this.currentFrame.meta?.labels ?? [],
        dark
      );
    }
  }

  setGridVisible(visible: boolean | null): void {
    this.forceGridOverride = visible;
    this.grid.update({
      visible: visible ?? ((this.currentFrame?.header.flags ?? HeaderFlag.GRID_ENABLED) & HeaderFlag.GRID_ENABLED) !== 0,
      gridSize: this.currentFrame?.header.gridSize || 5,
      is2D: this.isOrtho,
      darkTheme: this.darkTheme,
    });
  }

  setWireframeOverride(wireframe: boolean): void {
    this.forceWireframeOverride = wireframe;
  }

  resetCamera(): void {
    this.snapCamera('iso');
  }

  getCanvas(): HTMLCanvasElement {
    return this.renderer.domElement;
  }

  snapCamera(preset: AxisSnapPreset): void {
    if (this.isOrtho) {
      this.cameraTransition = null;
      this.orthoCamera.position.set(0, 0, 10);
      this.orthoCamera.zoom = 1;
      this.orthoCamera.updateProjectionMatrix();
      this.controls.target.set(0, 0, 0);
      this.controls.update();
      this.maybeEmitCameraChange(true);
      return;
    }

    const d = Math.max(3.2, this.perspCamera.position.distanceTo(this.controls.target) || 6.4);
    let endPos: THREE.Vector3;
    switch (preset) {
      case '+x':
        endPos = new THREE.Vector3(d, 0.01, 0);
        break;
      case '-x':
        endPos = new THREE.Vector3(-d, 0.01, 0);
        break;
      case '+y':
        endPos = new THREE.Vector3(0.01, d, 0.01);
        break;
      case '-y':
        endPos = new THREE.Vector3(0.01, -d, 0.01);
        break;
      case '+z':
        endPos = new THREE.Vector3(0, 0.01, d);
        break;
      case '-z':
        endPos = new THREE.Vector3(0, 0.01, -d);
        break;
      case 'iso':
      default:
        endPos = new THREE.Vector3(d * 0.58, d * 0.46, d * 0.68);
        break;
    }
    this.startCameraTransition(endPos, new THREE.Vector3(0, 0, 0), 420);
    this.maybeEmitCameraChange(true);
  }

  getCameraState(): { pos: Vec3Tuple; target: Vec3Tuple; isOrtho: boolean } {
    const cam = this.isOrtho ? this.orthoCamera : this.perspCamera;
    const t = this.controls.target;
    return {
      pos: [cam.position.x, cam.position.y, cam.position.z],
      target: [t.x, t.y, t.z],
      isOrtho: this.isOrtho,
    };
  }

  setCameraState(pos: Vec3Tuple, target: Vec3Tuple, isOrtho: boolean): void {
    this.setOrthoMode(isOrtho);
    this.cameraTransition = null;
    this.suppressCameraSync = true;
    try {
      const cam = isOrtho ? this.orthoCamera : this.perspCamera;
      cam.position.set(pos[0], pos[1], pos[2]);
      this.controls.target.set(target[0], target[1], target[2]);
      this.controls.update();
    } finally {
      this.suppressCameraSync = false;
    }
  }

  frameRadius(radius: number): void {
    if (this.isOrtho) return;
    const d = Math.max(4.8, radius * 2.75);
    this.startCameraTransition(
      new THREE.Vector3(d * 0.62, d * 0.48, d * 0.72),
      new THREE.Vector3(0, 0.05, 0),
      380
    );
  }

  /**
   * Read-only screen-space projection helper for deterministic E2E handle drag testing.
   */
  getInteractiveHandleScreenPos(handleId?: number): { handleId: number; clientX: number; clientY: number; world: Vec3Tuple } | null {
    const rect = this.renderer.domElement.getBoundingClientRect();
    for (const obj of this.interactiveObjects) {
      const meta = obj.userData.interactive as InteractiveMeta | undefined;
      if (!meta) continue;
      if (handleId !== undefined && meta.handleId !== handleId) continue;
      const p = meta.anchor.clone().project(this.activeCamera);
      return {
        handleId: meta.handleId,
        clientX: rect.left + ((p.x + 1) * 0.5) * rect.width,
        clientY: rect.top + ((1 - p.y) * 0.5) * rect.height,
        world: [meta.anchor.x, meta.anchor.y, meta.anchor.z],
      };
    }
    return null;
  }

  private startCameraTransition(endPos: THREE.Vector3, endTarget: THREE.Vector3, durationMs = 460): void {
    this.cameraTransition = {
      startPos: this.perspCamera.position.clone(),
      endPos: endPos.clone(),
      startTarget: this.controls.target.clone(),
      endTarget: endTarget.clone(),
      startMs: performance.now(),
      durationMs,
    };
  }

  clearWedgeSelection(): void {
    this.wedgeFirst = null;
    this.wedgeSecond = null;
    this.wedgeDraggingSlot = null;
    this.callbacks.onWedgePairArmed?.(null);
    this.renderWedgeOverlay();
  }

  /**
   * Accessible single-hand / keyboard Wedge operation on an armed (A, B) pair.
   * Sends ONLY raw unit separation direction vectors to Lean — ZERO GA math in JS!
   */
  commitArmedWedgeOp(op: AccessibleWedgeOp): boolean {
    if (!this.wedgeFirst || !this.wedgeSecond) return false;
    const u = this.wedgeFirst.anchorWorld.clone().sub(this.wedgeSecond.anchorWorld);
    if (u.lengthSq() < 1e-6) {
      u.set(1, 0, 0);
    } else {
      u.normalize();
    }

    let dirA: Vec3Tuple;
    let dirB: Vec3Tuple;
    switch (op) {
      case 'join':
      case 'add':
        // Pull apart along separation axis (aOut && bOut)
        dirA = [u.x, u.y, u.z];
        dirB = [-u.x, -u.y, -u.z];
        break;
      case 'meet':
        // Push together along separation axis (aIn && bIn)
        dirA = [-u.x, -u.y, -u.z];
        dirB = [u.x, u.y, u.z];
        break;
      case 'dot':
        // Hold A stationary (dirA = 0), push B toward A (holdA && bIn)
        dirA = [0, 0, 0];
        dirB = [u.x, u.y, u.z];
        break;
    }

    const idA = this.wedgeFirst.handleId;
    const idB = this.wedgeSecond.handleId;
    this.clearWedgeSelection();
    this.callbacks.onWedgeGesture?.(idA, idB, dirA, dirB, false);
    return true;
  }

  /**
   * Spawns a crisp expanding luminous emerald-gold ring pulse when Lean reports Wedge solved.
   */
  triggerWedgeWinPulse(): void {
    const geo = new THREE.RingGeometry(0.18, 0.28, 64);
    const mat = new THREE.MeshBasicMaterial({
      color: 0x34d399,
      transparent: true,
      opacity: 0.92,
      side: THREE.DoubleSide,
      depthWrite: false,
      blending: THREE.AdditiveBlending,
    });
    const mesh = new THREE.Mesh(geo, mat);
    mesh.position.set(0, 0, this.isOrtho ? 0.05 : 0);
    if (!this.isOrtho) {
      mesh.lookAt(this.activeCamera.position);
    }
    mesh.renderOrder = 8;
    this.scene.add(mesh);
    this.winPulses.push({ mesh, mat, startMs: performance.now(), durationMs: 820 });
  }

  /**
   * Captures the current 3D viewport as a crisp PNG data URL at custom resolution.
   */
  exportPng(width = 1600, height = 1000): string {
    const prevW = this.width;
    const prevH = this.height;
    const prevPixelRatio = this.renderer.getPixelRatio();

    this.renderer.setPixelRatio(1);
    this.renderer.setSize(width, height, false);
    this.updateCameraProjection(width, height);
    this.composer.setSize(width, height);
    for (const lm of this.lineMaterials) lm.resolution.set(width, height);
    this.composer.render();

    const dataUrl = this.renderer.domElement.toDataURL('image/png');

    this.renderer.setPixelRatio(prevPixelRatio);
    this.renderer.setSize(prevW, prevH, false);
    this.updateCameraProjection(prevW, prevH);
    this.composer.setSize(prevW, prevH);
    for (const lm of this.lineMaterials) lm.resolution.set(prevW, prevH);
    return dataUrl;
  }

  /**
   * Exports current projected GSIR 2D/3D primitives to a clean standalone SVG document.
   */
  exportSvg(width = 1200, height = 800): string {
    const bg = this.darkTheme ? '#090d18' : '#f8fafc';
    const parts: string[] = [
      `<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" viewBox="0 0 ${width} ${height}">`,
      `<rect width="100%" height="100%" fill="${bg}"/>`,
    ];

    const project = (p: Vec3Tuple): [number, number] => {
      const v = new THREE.Vector3(p[0], p[1], p[2]).project(this.activeCamera);
      return [((v.x + 1) * 0.5) * width, ((1 - v.y) * 0.5) * height];
    };

    const hex = (rgba: RgbaTuple) =>
      `rgba(${Math.round(rgba[0] * 255)},${Math.round(rgba[1] * 255)},${Math.round(rgba[2] * 255)},${rgba[3].toFixed(2)})`;

    const frame = this.currentFrame;
    if (frame) {
      const labelTexts = frame.meta?.labels ?? [];

      // Planes (translucent quads)
      for (const pl of frame.planes) {
        const e = pl.extent || 2.0;
        const corners: Vec3Tuple[] = [
          [pl.center[0] - pl.u[0] * e - pl.v[0] * e, pl.center[1] - pl.u[1] * e - pl.v[1] * e, pl.center[2] - pl.u[2] * e - pl.v[2] * e],
          [pl.center[0] + pl.u[0] * e - pl.v[0] * e, pl.center[1] + pl.u[1] * e - pl.v[1] * e, pl.center[2] + pl.u[2] * e - pl.v[2] * e],
          [pl.center[0] + pl.u[0] * e + pl.v[0] * e, pl.center[1] + pl.u[1] * e + pl.v[1] * e, pl.center[2] + pl.u[2] * e + pl.v[2] * e],
          [pl.center[0] - pl.u[0] * e + pl.v[0] * e, pl.center[1] - pl.u[1] * e + pl.v[1] * e, pl.center[2] - pl.u[2] * e + pl.v[2] * e],
        ];
        const pts = corners.map((c) => project(c).map((v) => v.toFixed(1)).join(',')).join(' ');
        parts.push(`<polygon points="${pts}" fill="${hex([pl.rgba[0], pl.rgba[1], pl.rgba[2], Math.min(0.32, pl.rgba[3])])}" stroke="${hex([pl.rgba[0], pl.rgba[1], pl.rgba[2], 0.85])}" stroke-width="1.5"/>`);
      }

      // Bivector disks / parallelograms
      for (const bv of frame.bivectorDisks) {
        if (bv.isDisk) {
          const pts: string[] = [];
          for (let i = 0; i < 48; i++) {
            const a = (i / 48) * Math.PI * 2;
            const c = Math.cos(a), s = Math.sin(a);
            const [px, py] = project([
              bv.origin[0] + c * bv.u[0] + s * bv.v[0],
              bv.origin[1] + c * bv.u[1] + s * bv.v[1],
              bv.origin[2] + c * bv.u[2] + s * bv.v[2],
            ]);
            pts.push(`${px.toFixed(1)},${py.toFixed(1)}`);
          }
          parts.push(`<polygon points="${pts.join(' ')}" fill="${hex([bv.rgba[0], bv.rgba[1], bv.rgba[2], Math.min(0.45, bv.rgba[3])])}" stroke="${hex([bv.rgba[0], bv.rgba[1], bv.rgba[2], 0.95])}" stroke-width="1.8"/>`);
        } else {
          const quad: Vec3Tuple[] = [
            bv.origin,
            [bv.origin[0] + bv.u[0], bv.origin[1] + bv.u[1], bv.origin[2] + bv.u[2]],
            [bv.origin[0] + bv.u[0] + bv.v[0], bv.origin[1] + bv.u[1] + bv.v[1], bv.origin[2] + bv.u[2] + bv.v[2]],
            [bv.origin[0] + bv.v[0], bv.origin[1] + bv.v[1], bv.origin[2] + bv.v[2]],
          ];
          const pts = quad.map((c) => project(c).map((v) => v.toFixed(1)).join(',')).join(' ');
          parts.push(`<polygon points="${pts}" fill="${hex([bv.rgba[0], bv.rgba[1], bv.rgba[2], Math.min(0.45, bv.rgba[3])])}" stroke="${hex([bv.rgba[0], bv.rgba[1], bv.rgba[2], 0.95])}" stroke-width="1.8"/>`);
        }
      }

      // Circles
      for (const cir of frame.circles) {
        const pts: string[] = [];
        for (let i = 0; i <= 64; i++) {
          const a = (i / 64) * Math.PI * 2;
          const ct = Math.cos(a) * cir.radius;
          const st = Math.sin(a) * cir.radius;
          const [px, py] = project([
            cir.center[0] + ct * cir.u[0] + st * cir.v[0],
            cir.center[1] + ct * cir.u[1] + st * cir.v[1],
            cir.center[2] + ct * cir.u[2] + st * cir.v[2],
          ]);
          pts.push(`${px.toFixed(1)},${py.toFixed(1)}`);
        }
        const dash = cir.imaginary ? ' stroke-dasharray="6,5"' : '';
        parts.push(`<polyline fill="none" points="${pts.join(' ')}" stroke="${hex(cir.rgba)}" stroke-width="${Math.max(1.6, cir.width)}"${dash}/>`);
      }

      for (const ln of frame.lines) {
        const c = ln.clip || 6;
        const [x1, y1] = project([ln.origin[0] - ln.dir[0] * c, ln.origin[1] - ln.dir[1] * c, ln.origin[2] - ln.dir[2] * c]);
        const [x2, y2] = project([ln.origin[0] + ln.dir[0] * c, ln.origin[1] + ln.dir[1] * c, ln.origin[2] + ln.dir[2] * c]);
        const dash = ln.dashed ? ' stroke-dasharray="6,6"' : '';
        parts.push(`<line x1="${x1.toFixed(1)}" y1="${y1.toFixed(1)}" x2="${x2.toFixed(1)}" y2="${y2.toFixed(1)}" stroke="${hex(ln.rgba)}" stroke-width="${Math.max(1.5, ln.width)}"${dash}/>`);
      }
      for (const seg of frame.segments) {
        const [x1, y1] = project(seg.a);
        const [x2, y2] = project(seg.b);
        const dash = seg.dashed ? ' stroke-dasharray="6,5"' : '';
        parts.push(`<line x1="${x1.toFixed(1)}" y1="${y1.toFixed(1)}" x2="${x2.toFixed(1)}" y2="${y2.toFixed(1)}" stroke="${hex(seg.rgba)}" stroke-width="${Math.max(1.5, seg.width)}"${dash}/>`);
      }
      for (const curve of frame.curves) {
        if (curve.ptCount < 2) continue;
        const pts: string[] = [];
        for (let i = 0; i < curve.ptCount; i++) {
          const [px, py] = project([curve.xyz[i * 3]!, curve.xyz[i * 3 + 1]!, curve.xyz[i * 3 + 2]!]);
          pts.push(`${px.toFixed(1)},${py.toFixed(1)}`);
        }
        const tag = curve.closed ? 'polygon' : 'polyline';
        const dash = curve.dashed ? ' stroke-dasharray="6,5"' : '';
        parts.push(`<${tag} fill="none" points="${pts.join(' ')}" stroke="${hex(curve.rgba)}" stroke-width="${Math.max(1.5, curve.width)}"${dash}/>`);
      }
      for (const pt of frame.points) {
        const [cx, cy] = project(pt.pos);
        const r = Math.max(4, pt.radius * 55);
        parts.push(
          `<circle cx="${cx.toFixed(1)}" cy="${cy.toFixed(1)}" r="${r.toFixed(1)}" fill="${pt.hollow ? 'none' : hex(pt.rgba)}" stroke="${hex(pt.rgba)}" stroke-width="2"/>`
        );
      }

      // Labels
      for (const lb of frame.labels) {
        const txt = labelTexts[lb.textIdx];
        if (!txt) continue;
        const [lx, ly] = project(lb.pos);
        const safe = txt.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
        parts.push(
          `<text x="${lx.toFixed(1)}" y="${ly.toFixed(1)}" fill="${hex(lb.rgba)}" font-family="ui-monospace,Menlo,monospace" font-size="13">${safe}</text>`
        );
      }

      // 2D Contour Overlay inset (0x0F)
      if (frame.contourOverlay && (frame.contourOverlay.curves.length > 0 || frame.contourOverlay.intersections.length > 0)) {
        const co = frame.contourOverlay;
        const boxW = Math.round(width * 0.24);
        const boxH = Math.round(height * 0.26);
        const ox = 20;
        const oy = height - boxH - 20;
        const pad = 16;
        const spanX = Math.max(1e-5, co.maxX - co.minX);
        const spanY = Math.max(1e-5, co.maxY - co.minY);
        const mx = (x: number) => ox + pad + ((x - co.minX) / spanX) * (boxW - pad * 2);
        const my = (y: number) => oy + pad + (1 - (y - co.minY) / spanY) * (boxH - pad * 2);

        parts.push(`<rect x="${ox}" y="${oy}" width="${boxW}" height="${boxH}" rx="10" fill="${this.darkTheme ? '#0b1222' : '#ffffff'}" stroke="rgba(148,175,224,0.45)" stroke-width="1.2"/>`);
        for (const c of co.curves) {
          if (c.ptCount < 2) continue;
          const pts: string[] = [];
          for (let i = 0; i < c.ptCount; i++) {
            pts.push(`${mx(c.xy[i * 2]!).toFixed(1)},${my(c.xy[i * 2 + 1]!).toFixed(1)}`);
          }
          parts.push(`<polyline fill="none" points="${pts.join(' ')}" stroke="${hex(c.rgba)}" stroke-width="${Math.max(1.4, c.width)}"/>`);
        }
        for (const pt of co.intersections) {
          parts.push(`<circle cx="${mx(pt.x).toFixed(1)}" cy="${my(pt.y).toFixed(1)}" r="3.5" fill="${hex(pt.rgba)}"/>`);
        }
      }
    }

    parts.push('</svg>');
    return parts.join('\n');
  }

  private ensureCachedMeshGeometry(asset: GsirMeshAsset): void {
    const existing = this.meshGeoCache.get(asset.meshId);
    if (existing && existing.dirtyHash === asset.dirtyHash) return;

    if (existing) {
      existing.geometry.dispose();
    }

    const geo = new THREE.BufferGeometry();
    // Strictly consume Lean's precomputed positions, normals, optional vertex colors, and CCW indices
    geo.setAttribute('position', new THREE.BufferAttribute(new Float32Array(asset.positions), 3));
    geo.setAttribute('normal', new THREE.BufferAttribute(new Float32Array(asset.normals), 3));
    if (asset.hasColors && asset.colors) {
      geo.setAttribute('color', new THREE.BufferAttribute(new Float32Array(asset.colors), 4));
    }
    geo.setIndex(new THREE.BufferAttribute(new Uint32Array(asset.indices), 1));
    geo.computeBoundingSphere();

    this.meshGeoCache.set(asset.meshId, {
      dirtyHash: asset.dirtyHash,
      geometry: geo,
    });
  }

  private addThickPolyline(
    positions: number[],
    width: number,
    rgba: RgbaTuple,
    dashed: boolean,
    draggableHandleId: number | null,
    kind: 'segment' | 'line',
    anchor: Vec3Tuple
  ): void {
    const geo = new LineGeometry();
    geo.setPositions(positions);

    const mat = new LineMaterial({
      color: toColor(rgba).getHex(),
      linewidth: Math.max(1.2, width || 2.0),
      transparent: rgba[3] < 0.99,
      opacity: rgba[3],
      dashed,
      dashSize: 0.16,
      gapSize: 0.11,
      worldUnits: false,
      resolution: new THREE.Vector2(this.width, this.height),
    });
    this.lineMaterials.push(mat);

    const line = new Line2(geo, mat);
    if (dashed) {
      line.computeLineDistances();
    }
    this.dynamicGroup.add(line);

    // Invisible wide hit cylinder for smooth Wedge 2D/3D line selection when draggable
    if (draggableHandleId !== null && positions.length >= 6) {
      const a = new THREE.Vector3(positions[0], positions[1], positions[2]);
      const b = new THREE.Vector3(
        positions[positions.length - 3],
        positions[positions.length - 2],
        positions[positions.length - 1]
      );
      const span = b.clone().sub(a);
      const len = span.length();
      if (len > 1e-4) {
        const hitGeo = new THREE.CylinderGeometry(0.14, 0.14, len, 6, 1, true);
        const hitMat = new THREE.MeshBasicMaterial({ visible: false });
        const hitMesh = new THREE.Mesh(hitGeo, hitMat);
        hitMesh.position.copy(a).add(b).multiplyScalar(0.5);
        hitMesh.quaternion.setFromUnitVectors(new THREE.Vector3(0, 1, 0), span.normalize());
        hitMesh.userData.interactive = {
          handleId: draggableHandleId,
          anchor: new THREE.Vector3(anchor[0], anchor[1], anchor[2]),
          kind,
        } satisfies InteractiveMeta;
        this.dynamicGroup.add(hitMesh);
        this.interactiveObjects.push(hitMesh);
      }
    }
  }

  private addLabelObject(pos: Vec3Tuple, text: string, rgba: RgbaTuple, isLatex: boolean): void {
    const el = document.createElement('div');
    el.className = 'gs-scene-label';
    el.style.color = `rgba(${Math.round(rgba[0] * 255)}, ${Math.round(rgba[1] * 255)}, ${Math.round(rgba[2] * 255)}, ${Math.max(0.75, rgba[3])})`;

    if (isLatex) {
      try {
        el.innerHTML = katex.renderToString(text, { throwOnError: false, displayMode: false });
      } catch {
        el.textContent = text;
      }
    } else {
      el.textContent = text;
    }

    const obj = new CSS2DObject(el);
    obj.position.set(pos[0], pos[1], pos[2]);
    this.labelGroup.add(obj);
  }

  private updateOpnsGroup(frame: GsirFrame): void {
    while (this.opnsGroup.children.length > 0) {
      this.opnsGroup.remove(this.opnsGroup.children[0]!);
    }

    const shaders = frame.meta?.opnsShaders ?? [];
    this.opnsResolution.set(this.width, this.height);
    this.opnsInvViewProj
      .multiplyMatrices(this.activeCamera.projectionMatrix, this.activeCamera.matrixWorldInverse)
      .invert();

    for (const item of frame.opnsUniforms) {
      const shaderMeta = shaders[item.shaderIdx];
      if (!shaderMeta) continue;
      const entry = this.opnsCache.getOrCreate(shaderMeta);
      if (!entry) continue;
      this.opnsCache.updateUniforms(entry, item, this.simTime, this.opnsResolution, this.opnsInvViewProj);
      const mesh = new THREE.Mesh(
        entry.isFullScreenQuad ? this.opnsQuadGeo : this.opnsBoxGeo,
        entry.material
      );
      mesh.frustumCulled = false;
      mesh.renderOrder = entry.isFullScreenQuad ? 1 : entry.material.depthWrite ? 1 : 4;
      this.opnsGroup.add(mesh);
    }
  }

  private clearDynamicGroup(): void {
    this.interactiveObjects.length = 0;
    this.lineMaterials.length = 0;
    this.flowMaterials.length = 0;

    while (this.dynamicGroup.children.length > 0) {
      const child = this.dynamicGroup.children[0]!;
      this.dynamicGroup.remove(child);
      if (child instanceof THREE.Mesh || child instanceof THREE.Points || child instanceof Line2) {
        if (
          !child.userData.sharedGeometry &&
          child.geometry !== this.unitSphereGeo &&
          child.geometry !== this.fresnelSphereGeo &&
          child.geometry !== this.imaginarySphereGeo &&
          child.geometry !== this.ringTorusGeo &&
          child.geometry !== this.hollowTorusGeo &&
          child.geometry !== this.arrowConeGeo &&
          child.geometry !== this.opnsBoxGeo
        ) {
          child.geometry.dispose();
        }
        if (Array.isArray(child.material)) {
          for (const m of child.material) m.dispose();
        } else {
          child.material.dispose();
        }
      }
    }

    while (this.labelGroup.children.length > 0) {
      const child = this.labelGroup.children[0]!;
      this.labelGroup.remove(child);
      if (child instanceof CSS2DObject) {
        child.element.remove();
      }
    }
  }

  private setOrthoMode(wantOrtho: boolean): void {
    if (this.isOrtho === wantOrtho) {
      if (wantOrtho) this.updateCameraProjection(this.width, this.height);
      return;
    }
    this.suppressCameraSync = true;
    try {
      this.isOrtho = wantOrtho;
      this.activeCamera = wantOrtho ? this.orthoCamera : this.perspCamera;
      this.controls.object = this.activeCamera;
      this.controls.enableRotate = !wantOrtho;
      this.renderPass.camera = this.activeCamera;
      this.updateCameraProjection(this.width, this.height);
      if (wantOrtho) {
        this.orthoCamera.position.set(0, 0, 10);
        this.controls.target.set(0, 0, 0);
      }
      this.controls.update();
    } finally {
      this.suppressCameraSync = false;
    }
  }

  private applyLeanCamera(viewMat4: Float32Array, distance: number, wantOrtho: boolean): void {
    this.suppressCameraSync = true;
    try {
      if (wantOrtho) {
        this.orthoCamera.position.set(0, 0, 10);
        this.controls.target.set(0, 0, 0);
        this.controls.update();
        return;
      }
      // Check if viewMat4 is non-degenerate (invertible) and not identity
      const m = new THREE.Matrix4().fromArray(viewMat4);
      const det = m.determinant();
      if (Math.abs(det) > 1e-5) {
        const inv = m.clone().invert();
        const pos = new THREE.Vector3();
        const quat = new THREE.Quaternion();
        const scale = new THREE.Vector3();
        inv.decompose(pos, quat, scale);
        const dist = Math.max(2.6, distance || pos.length() || 5.0);
        // Elevate flat eye-level Z-axis defaults OR inverted-pitch view matrices (pos.y < 0) to a hero 3/4 studio angle
        if ((Math.abs(pos.x) < 1e-2 && Math.abs(pos.y) < 1e-2) || pos.y < -0.05) {
          const heroX = Math.abs(pos.x) > 0.2 ? Math.abs(pos.x) : dist * 0.65;
          const heroY = Math.max(Math.abs(pos.y) * 1.15, dist * 0.45);
          const heroZ = Math.max(Math.abs(pos.z), dist * 0.72);
          this.startCameraTransition(
            new THREE.Vector3(heroX, heroY, heroZ),
            new THREE.Vector3(0, 0.15, 0),
            440
          );
        } else if (pos.lengthSq() > 1e-4) {
          const forward = new THREE.Vector3(0, 0, -1).applyQuaternion(quat);
          const nextTarget = pos.clone().addScaledVector(forward, dist);
          this.startCameraTransition(pos, nextTarget, 460);
        }
      }
    } finally {
      this.suppressCameraSync = false;
    }
  }

  private isWedgeMode(): boolean {
    const mode = this.currentFrame?.header.modeKind;
    return mode === ModeKind.Wedge2D || mode === ModeKind.Wedge3D;
  }

  private updatePointerNdc(ev: PointerEvent): void {
    const rect = this.renderer.domElement.getBoundingClientRect();
    this.pointerNdc.x = ((ev.clientX - rect.left) / rect.width) * 2 - 1;
    this.pointerNdc.y = -((ev.clientY - rect.top) / rect.height) * 2 + 1;
  }

  private raycastInteractive(): { meta: InteractiveMeta; hitPoint: THREE.Vector3 } | null {
    this.raycaster.setFromCamera(this.pointerNdc, this.activeCamera);
    const hits = this.raycaster.intersectObjects(this.interactiveObjects, false);
    for (const h of hits) {
      const meta = h.object.userData.interactive as InteractiveMeta | undefined;
      if (meta) {
        return { meta, hitPoint: h.point.clone() };
      }
    }
    return null;
  }

  private setCameraDragPlane(anchor: THREE.Vector3): void {
    const camDir = new THREE.Vector3();
    this.activeCamera.getWorldDirection(camDir);
    if (this.isOrtho) {
      this.dragPlane.setFromNormalAndCoplanarPoint(new THREE.Vector3(0, 0, 1), new THREE.Vector3(0, 0, 0));
    } else {
      this.dragPlane.setFromNormalAndCoplanarPoint(camDir.negate(), anchor);
    }
  }

  private readonly onPointerDown = (ev: PointerEvent): void => {
    if (ev.button !== 0) return;
    this.updatePointerNdc(ev);
    const hit = this.raycastInteractive();
    if (!hit) return;

    this.controls.enabled = false;
    this.setCameraDragPlane(hit.meta.anchor);

    if (this.isWedgeMode()) {
      this.callbacks.onWedgeSelectSound?.();
      const slotLabel = hit.meta.label || `#${hit.meta.handleId}`;
      if (!this.wedgeFirst || (this.wedgeFirst && this.wedgeSecond)) {
        this.wedgeFirst = {
          handleId: hit.meta.handleId,
          label: slotLabel,
          anchorWorld: hit.meta.anchor.clone(),
          currentWorld: hit.meta.anchor.clone(),
        };
        this.wedgeSecond = null;
        this.wedgeDraggingSlot = 1;
        this.callbacks.onWedgePairArmed?.(null);
      } else if (hit.meta.handleId === this.wedgeFirst.handleId) {
        this.wedgeFirst.currentWorld.copy(hit.meta.anchor);
        this.wedgeDraggingSlot = 1;
      } else {
        this.wedgeSecond = {
          handleId: hit.meta.handleId,
          label: slotLabel,
          anchorWorld: hit.meta.anchor.clone(),
          currentWorld: hit.meta.anchor.clone(),
        };
        this.wedgeDraggingSlot = 2;
      }
      this.renderWedgeOverlay();
      return;
    }

    // Standard CoffeeShop / Calculator draggable handle raycast
    if (hit.meta.kind === 'point') {
      this.raycaster.ray.intersectPlane(this.dragPlane, this.dragHitPoint);
      this.activeDrag = {
        handleId: hit.meta.handleId,
        offset: hit.meta.anchor.clone().sub(this.dragHitPoint),
        startClientX: ev.clientX,
        startClientY: ev.clientY,
        moved: false,
        meta: hit.meta,
      };
    } else {
      // Clicking a plane/segment/line immediately selects it in Inspect Stash
      this.controls.enabled = true;
      this.callbacks.onSelectObject?.({
        handleId: hit.meta.handleId,
        kind: hit.meta.kind,
        label: hit.meta.label,
      });
    }
  };

  private readonly onPointerMove = (ev: PointerEvent): void => {
    this.updatePointerNdc(ev);

    if (this.activeDrag) {
      const dx = ev.clientX - this.activeDrag.startClientX;
      const dy = ev.clientY - this.activeDrag.startClientY;
      if (dx * dx + dy * dy > 16) {
        this.activeDrag.moved = true;
      }
      this.raycaster.setFromCamera(this.pointerNdc, this.activeCamera);
      if (this.raycaster.ray.intersectPlane(this.dragPlane, this.dragHitPoint)) {
        const nextPos = this.dragHitPoint.clone().add(this.activeDrag.offset);
        this.callbacks.onDragHandle?.(this.activeDrag.handleId, [nextPos.x, nextPos.y, nextPos.z]);
      }
      return;
    }

    if (this.wedgeDraggingSlot !== null) {
      this.raycaster.setFromCamera(this.pointerNdc, this.activeCamera);
      if (this.raycaster.ray.intersectPlane(this.dragPlane, this.dragHitPoint)) {
        const slot = this.wedgeDraggingSlot === 1 ? this.wedgeFirst : this.wedgeSecond;
        if (slot) {
          slot.currentWorld.copy(this.dragHitPoint);
          this.renderWedgeOverlay();

          // Live Wedge preview (isPreview = true) while dragging second element (#17 Fix #3)
          if (this.wedgeDraggingSlot === 2 && this.wedgeFirst && this.wedgeSecond) {
            const now = performance.now();
            if (now - this.lastWedgePreviewMs > 32) {
              this.lastWedgePreviewMs = now;
              const dA = this.wedgeFirst.currentWorld.clone().sub(this.wedgeFirst.anchorWorld);
              const dB = this.wedgeSecond.currentWorld.clone().sub(this.wedgeSecond.anchorWorld);
              this.callbacks.onWedgeGesture?.(
                this.wedgeFirst.handleId,
                this.wedgeSecond.handleId,
                [dA.x, dA.y, dA.z],
                [dB.x, dB.y, dB.z],
                true
              );
            }
          }
        }
      }
      return;
    }

    // Hover cursor feedback
    const hit = this.raycastInteractive();
    const nextHover = hit ? hit.meta.handleId : null;
    if (nextHover !== this.hoveredHandleId) {
      this.hoveredHandleId = nextHover;
      this.renderer.domElement.style.cursor = nextHover !== null ? 'grab' : 'default';
    }
  };

  private readonly onPointerUp = (): void => {
    if (this.activeDrag) {
      const finished = this.activeDrag;
      this.activeDrag = null;
      this.controls.enabled = true;
      if (!finished.moved) {
        this.callbacks.onSelectObject?.({
          handleId: finished.meta.handleId,
          kind: finished.meta.kind,
          label: finished.meta.label,
        });
      }
      return;
    }

    if (this.wedgeDraggingSlot !== null) {
      this.controls.enabled = true;
      if (this.wedgeDraggingSlot === 2 && this.wedgeFirst && this.wedgeSecond) {
        const dA = this.wedgeFirst.currentWorld.clone().sub(this.wedgeFirst.anchorWorld);
        const dB = this.wedgeSecond.currentWorld.clone().sub(this.wedgeSecond.anchorWorld);
        const dragged = dA.length() >= 0.1 || dB.length() >= 0.1;
        if (dragged) {
          // Commit real drag gesture to Lean (isPreview = false; Lean derives hold from raw vectors!)
          this.callbacks.onWedgeGesture?.(
            this.wedgeFirst.handleId,
            this.wedgeSecond.handleId,
            [dA.x, dA.y, dA.z],
            [dB.x, dB.y, dB.z],
            false
          );
          this.wedgeFirst = null;
          this.wedgeSecond = null;
          this.callbacks.onWedgePairArmed?.(null);
        } else {
          // Accessible single-hand / tap-tap mode: keep A & B armed for Join/Meet/Add/Dot action buttons!
          this.callbacks.onWedgePairArmed?.({
            idA: this.wedgeFirst.handleId,
            idB: this.wedgeSecond.handleId,
            labelA: this.wedgeFirst.label,
            labelB: this.wedgeSecond.label,
          });
        }
      }
      this.wedgeDraggingSlot = null;
      this.renderWedgeOverlay();
    }
  };

  private renderWedgeOverlay(): void {
    const svg = this.wedgeSvg;
    svg.innerHTML = '';
    const slots = [this.wedgeFirst, this.wedgeSecond].filter((s): s is WedgePickSlot => s !== null);
    if (slots.length === 0) return;

    const toScreen = (v: THREE.Vector3): [number, number] => {
      const p = v.clone().project(this.activeCamera);
      return [((p.x + 1) * 0.5) * this.width, ((1 - p.y) * 0.5) * this.height];
    };

    for (const slot of slots) {
      const [x1, y1] = toScreen(slot.anchorWorld);
      const [x2, y2] = toScreen(slot.currentWorld);
      const g = document.createElementNS('http://www.w3.org/2000/svg', 'g');

      const halo = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
      halo.setAttribute('cx', x1.toFixed(1));
      halo.setAttribute('cy', y1.toFixed(1));
      halo.setAttribute('r', '14');
      halo.setAttribute('fill', 'rgba(74, 222, 128, 0.16)');
      halo.setAttribute('stroke', '#4ADE80');
      halo.setAttribute('stroke-width', '2');
      g.appendChild(halo);

      const line = document.createElementNS('http://www.w3.org/2000/svg', 'line');
      line.setAttribute('x1', x1.toFixed(1));
      line.setAttribute('y1', y1.toFixed(1));
      line.setAttribute('x2', x2.toFixed(1));
      line.setAttribute('y2', y2.toFixed(1));
      line.setAttribute('stroke', '#4ADE80');
      line.setAttribute('stroke-width', '3');
      line.setAttribute('stroke-linecap', 'round');
      line.setAttribute('stroke-dasharray', '6 4');
      g.appendChild(line);

      const tip = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
      tip.setAttribute('cx', x2.toFixed(1));
      tip.setAttribute('cy', y2.toFixed(1));
      tip.setAttribute('r', '5');
      tip.setAttribute('fill', '#4ADE80');
      g.appendChild(tip);

      svg.appendChild(g);
    }
  }

  private handleXrPinch(ev: XrPinchDragEvent): void {
    this.raycaster.set(ev.rayOrigin, ev.rayDirection);
    const hits = this.raycaster.intersectObjects(this.interactiveObjects, false);
    const hitMeta = hits[0]?.object.userData.interactive as InteractiveMeta | undefined;
    if (!hitMeta) return;
    if (ev.phase === 'move') {
      const next = hitMeta.anchor.clone().add(ev.deltaWorld);
      this.callbacks.onDragHandle?.(hitMeta.handleId, [next.x, next.y, next.z]);
    }
  }

  private handleXrTwoHandPinch(a: XrPinchDragEvent, b: XrPinchDragEvent, commit: boolean): void {
    if (!this.isWedgeMode()) return;
    this.raycaster.set(a.rayOrigin, a.rayDirection);
    const hitA = this.raycaster.intersectObjects(this.interactiveObjects, false)[0]?.object.userData
      .interactive as InteractiveMeta | undefined;
    this.raycaster.set(b.rayOrigin, b.rayDirection);
    const hitB = this.raycaster.intersectObjects(this.interactiveObjects, false)[0]?.object.userData
      .interactive as InteractiveMeta | undefined;
    if (!hitA || !hitB || hitA.handleId === hitB.handleId) return;

    this.callbacks.onWedgeGesture?.(
      hitA.handleId,
      hitB.handleId,
      [a.deltaWorld.x, a.deltaWorld.y, a.deltaWorld.z],
      [b.deltaWorld.x, b.deltaWorld.y, b.deltaWorld.z],
      !commit
    );
  }

  private maybeEmitCameraChange(force = false): void {
    if (this.suppressCameraSync) return;
    const now = performance.now();
    if (!force && now - this.lastCameraSyncMs < 50) return;
    this.lastCameraSyncMs = now;

    // Pack Three.js camera unit orientation quaternion + distance into the 8-float wire slot
    // (ganja motor order [s, e01, e02, e03, e12, e13, e23, e0123])
    const q = this.activeCamera.quaternion;
    const t = this.controls.target;
    const dist = this.activeCamera.position.distanceTo(t);
    const tx = -0.5 * t.x, ty = -0.5 * t.y, tz = -0.5 * t.z;
    const rw = q.w, r12 = -q.z, r13 = q.y, r23 = -q.x;
    const e01 = tx * rw + ty * r12 + tz * r13;
    const e02 = -tx * r12 + ty * rw + tz * r23;
    const e03 = -tx * r13 - ty * r23 + tz * rw;
    const e0123 = tx * r23 - ty * r13 + tz * r12;
    const motor = new Float32Array([rw, e01, e02, e03, r12, r13, r23, e0123]);
    this.callbacks.onCameraChange?.(motor, this.perspCamera.fov, dist);
  }

  private updateCameraProjection(w: number, h: number): void {
    const aspect = Math.max(0.1, w / Math.max(1, h));
    this.perspCamera.aspect = aspect;
    this.perspCamera.updateProjectionMatrix();

    this.orthoCamera.left = -this.orthoScale * aspect;
    this.orthoCamera.right = this.orthoScale * aspect;
    this.orthoCamera.top = this.orthoScale;
    this.orthoCamera.bottom = -this.orthoScale;
    this.orthoCamera.updateProjectionMatrix();
  }

  private handleResize(): void {
    const w = Math.max(this.container.clientWidth, 160);
    const h = Math.max(this.container.clientHeight, 160);
    if (w === this.width && h === this.height) return;
    this.width = w;
    this.height = h;
    this.renderer.setSize(w, h);
    this.labelRenderer.setSize(w, h);
    this.composer.setSize(w, h);
    this.updateCameraProjection(w, h);
    for (const lm of this.lineMaterials) lm.resolution.set(w, h);
    this.renderWedgeOverlay();
  }

  private readonly renderLoop = (): void => {
    if (this.disposed) return;
    const t0 = performance.now();

    if (!this.xr.isActive()) {
      if (this.cameraTransition && !this.isOrtho) {
        const tr = this.cameraTransition;
        const u = Math.min(1, (t0 - tr.startMs) / tr.durationMs);
        const ease = 1 - Math.pow(1 - u, 3);
        this.suppressCameraSync = true;
        this.perspCamera.position.lerpVectors(tr.startPos, tr.endPos, ease);
        this.controls.target.lerpVectors(tr.startTarget, tr.endTarget, ease);
        this.controls.update();
        this.suppressCameraSync = false;
        if (u >= 1) this.cameraTransition = null;
      } else {
        this.controls.update();
      }
    } else {
      this.xr.updateFrame();
    }

    // Advance Wedge win celebration ring pulses cleanly
    if (this.winPulses.length > 0) {
      for (let i = this.winPulses.length - 1; i >= 0; i--) {
        const p = this.winPulses[i]!;
        const u = (t0 - p.startMs) / p.durationMs;
        if (u >= 1) {
          this.scene.remove(p.mesh);
          p.mesh.geometry.dispose();
          p.mat.dispose();
          this.winPulses.splice(i, 1);
        } else {
          const ease = 1 - Math.pow(1 - u, 3);
          p.mesh.scale.setScalar(1 + ease * 11);
          p.mat.opacity = 0.88 * (1 - u);
          if (!this.isOrtho) p.mesh.lookAt(this.activeCamera.position);
        }
      }
    }

    // Advance particle flow uniform clock smoothly
    const sec = t0 * 0.001;
    for (const fm of this.flowMaterials) {
      fm.uniforms.uTime!.value = sec;
    }

    // Sync OPNS camera basis/matrices & corner 3D axis gizmo smoothly
    if (this.opnsGroup.children.length > 0) {
      this.opnsInvViewProj
        .multiplyMatrices(this.activeCamera.projectionMatrix, this.activeCamera.matrixWorldInverse)
        .invert();
      const aspect = Math.max(0.1, this.width / Math.max(1, this.height));
      const fovRad = THREE.MathUtils.degToRad(this.perspCamera.fov);
      const tanHalf = Math.tan(fovRad * 0.5);
      const camFwd = new THREE.Vector3();
      this.activeCamera.getWorldDirection(camFwd);
      const camRight = new THREE.Vector3().setFromMatrixColumn(this.activeCamera.matrixWorld, 0).normalize();
      const camUp = new THREE.Vector3().setFromMatrixColumn(this.activeCamera.matrixWorld, 1).normalize();

      for (const child of this.opnsGroup.children) {
        if (child instanceof THREE.Mesh && child.material instanceof THREE.ShaderMaterial) {
          const u = child.material.uniforms;
          if (u.uInvViewProj) (u.uInvViewProj.value as THREE.Matrix4).copy(this.opnsInvViewProj);
          if (u.uResolution) (u.uResolution.value as THREE.Vector2).set(this.width, this.height);
          if (u.uCamPos) (u.uCamPos.value as THREE.Vector3).copy(this.activeCamera.position);
          if (u.uCamFwd) (u.uCamFwd.value as THREE.Vector3).copy(camFwd);
          if (u.uCamRight) (u.uCamRight.value as THREE.Vector3).copy(camRight).multiplyScalar(tanHalf * aspect);
          if (u.uCamUp) (u.uCamUp.value as THREE.Vector3).copy(camUp).multiplyScalar(tanHalf);
          if (u.uSimTime) u.uSimTime.value = sec;
        }
      }
    }
    this.axisGizmo.update(this.activeCamera, this.isOrtho);

    const dtFrameMs = t0 - this.lastRafMs;
    this.lastRafMs = t0;
    if (dtFrameMs > 25 && dtFrameMs < 250) {
      this.droppedFrames++;
    }

    if (this.xr.isActive()) {
      // During WebXR sessions render straight to the XR framebuffer (per RayTrace4D #8)
      this.renderer.render(this.scene, this.activeCamera);
    } else {
      this.composer.render();
      this.labelRenderer.render(this.scene, this.activeCamera);
    }

    const tEnd = performance.now();
    if (this.pendingInputTsMs !== null) {
      const i2p = Math.max(0, tEnd - this.pendingInputTsMs);
      this.pendingInputTsMs = null;
      this.inputToPresentSamples.push(i2p);
      if (this.inputToPresentSamples.length > 60) {
        this.inputToPresentSamples.shift();
      }
    }

    const renderUs = Math.max(0, (tEnd - t0) * 1000);
    this.rafFrames++;
    if (t0 - this.fpsWindowStart >= 500) {
      this.lastFps = Math.round((this.rafFrames * 1000) / (t0 - this.fpsWindowStart));
      this.rafFrames = 0;
      this.fpsWindowStart = t0;
      let p95 = renderUs / 1000;
      if (this.inputToPresentSamples.length > 0) {
        const sorted = [...this.inputToPresentSamples].sort((a, b) => a - b);
        p95 = sorted[Math.min(sorted.length - 1, Math.floor(sorted.length * 0.95))]!;
      }
      this.callbacks.onTelemetry?.({
        fps: this.lastFps,
        renderUs,
        p95InputToPresentMs: p95,
        droppedFrames: this.droppedFrames,
        cachedMeshes: this.meshGeoCache.size,
        xrActive: this.xr.isActive(),
      });
    }
  };

  dispose(): void {
    this.disposed = true;
    this.renderer.setAnimationLoop(null);
    this.resizeObserver.disconnect();
    this.renderer.domElement.removeEventListener('pointerdown', this.onPointerDown);
    window.removeEventListener('pointermove', this.onPointerMove);
    window.removeEventListener('pointerup', this.onPointerUp);

    this.clearDynamicGroup();
    for (const cached of this.meshGeoCache.values()) {
      cached.geometry.dispose();
    }
    this.meshGeoCache.clear();
    this.opnsCache.dispose();
    this.backdrop.dispose();
    this.grid.dispose();
    this.envMapDark.dispose();
    this.envMapLight.dispose();
    this.unitSphereGeo.dispose();
    this.fresnelSphereGeo.dispose();
    this.imaginarySphereGeo.dispose();
    this.ringTorusGeo.dispose();
    this.hollowTorusGeo.dispose();
    this.arrowConeGeo.dispose();
    this.opnsBoxGeo.dispose();
    this.opnsQuadGeo.dispose();
    this.xr.dispose();
    this.axisGizmo.dispose();
    this.contourOverlay.dispose();
    this.controls.dispose();
    this.composer.dispose();
    this.renderer.dispose();
    this.renderer.domElement.remove();
    this.labelRenderer.domElement.remove();
    this.wedgeSvg.remove();
  }
}

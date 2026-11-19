// Canonical GSIR v1 Wire Protocol Types
// Conforms strictly to docs/SCENE_IR_V1.md + all 5 fixes from verifier-core (#17):
//  1. 8-byte alignment for all section byteOffsets & 0x0B MESH_ASSETS records + CCW winding
//  2. grassmann_studio_get_frame & InputEvent.flags bit0 = forceFullSnapshot
//  3. WedgeGesture flags bit0 = isPreview, Lean-derived hold, draggable bit gating (handleId=0 valid)
//  4. metaJsonLen = 0 unchanged delta & opnsShaders hash cache
//  5. CAMERA.flags b0 = isOrtho, ganja motor wire order, evalSurface JSON event

export const GSIR_MAGIC = 0x52495347; // "GSIR" ASCII little-endian
export const GSIR_VERSION = 1;
export const GSIR_HEADER_SIZE = 64;
export const GSIR_DIR_ENTRY_SIZE = 16;
export const GSIR_NO_LABEL = 0xffffffff;

export const HeaderFlag = {
  IS_2D: 1 << 0,
  GRID_ENABLED: 1 << 1,
  DARK_THEME: 1 << 2,
  HAS_WEDGE_HUD: 1 << 3,
  HAS_CALC_STATE: 1 << 4,
  HAS_CONTOUR_OVERLAY: 1 << 5,
  HAS_OPNS_SHADER: 1 << 6,
} as const;

export const ModeKind = {
  CoffeeShop: 0,
  Wedge2D: 1,
  Wedge3D: 2,
  Calculator: 3,
  Surface: 4,
} as const;
export type ModeKindValue = (typeof ModeKind)[keyof typeof ModeKind];

export const SectionKind = {
  CAMERA: 0x01,
  POINTS: 0x02,
  SEGMENTS: 0x03,
  LINES: 0x04,
  PLANES: 0x05,
  CIRCLES: 0x06,
  SPHERES: 0x07,
  POINT_PAIRS: 0x08,
  BIVECTOR_DISKS: 0x09,
  MESH_REFS: 0x0a,
  MESH_ASSETS: 0x0b,
  CURVES: 0x0c,
  FLOW_PARTICLES: 0x0d,
  LABELS: 0x0e,
  CONTOUR_OVERLAY: 0x0f,
  OPNS_UNIFORMS: 0x10,
  INSPECT_COEFFS: 0x11,
} as const;
export type SectionKindValue = (typeof SectionKind)[keyof typeof SectionKind];

export const CameraFlag = {
  IS_ORTHO: 1 << 0,
} as const;

export const PointFlag = {
  DRAGGABLE: 1 << 0,
  SELECTED: 1 << 1,
  TARGET: 1 << 2,
  HINT: 1 << 3,
  HOLLOW: 1 << 4,
} as const;

export const SegmentFlag = {
  DASHED: 1 << 0,
  ARROW: 1 << 1,
  DRAGGABLE: 1 << 2,
  SELECTED: 1 << 3,
  TARGET: 1 << 4,
  HINT: 1 << 5,
} as const;

export const LineFlag = {
  DASHED: 1 << 0,
  DRAGGABLE: 1 << 1,
  SELECTED: 1 << 2,
  TARGET: 1 << 3,
  HINT: 1 << 4,
} as const;

export const PlaneFlag = {
  GRID_LINES: 1 << 0,
  DRAGGABLE: 1 << 1,
  SELECTED: 1 << 2,
  TARGET: 1 << 3,
  HINT: 1 << 4,
} as const;

export const CircleFlag = {
  IMAGINARY: 1 << 0,
} as const;

export const SphereFlag = {
  IMAGINARY: 1 << 0,
} as const;

export const PointPairFlag = {
  IMAGINARY: 1 << 0,
  SHOW_LINK: 1 << 1,
} as const;

export const BivectorFlag = {
  DISK: 1 << 0, // 0 = parallelogram, 1 = disk
  ORIENTATION_ARROW: 1 << 1,
} as const;

export const MeshRefFlag = {
  WIREFRAME: 1 << 0,
  DOUBLE_SIDED: 1 << 1,
  USE_VERTEX_COLORS: 1 << 2,
} as const;

export const MeshAssetFlag = {
  HAS_COLORS: 1 << 0,
} as const;

export const CurveFlag = {
  CLOSED: 1 << 0,
  DASHED: 1 << 1,
} as const;

export const LabelFlag = {
  IS_LATEX: 1 << 0,
  BILLBOARD: 1 << 1,
} as const;

export const OpnsFlag = {
  IS_IPNS: 1 << 0,
} as const;

export type Vec3Tuple = readonly [number, number, number];
export type RgbaTuple = readonly [number, number, number, number];

export interface GsirHeader {
  magic: number;
  version: number;
  flags: number;
  frameSeq: bigint;
  simTime: number;
  p: number;
  q: number;
  r: number;
  modeKind: ModeKindValue;
  gridSize: number;
  sectionCount: number;
  totalByteLen: number;
  metaJsonOffset: number;
  metaJsonLen: number;
}

export interface GsirSectionDirEntry {
  kind: number;
  count: number;
  byteOffset: number;
  byteLen: number;
}

export interface GsirCamera {
  /** Ganja order: (s, e01, e02, e03, e12, e13, e23, e0123) */
  motor: Float32Array;
  /** Column-major 4x4 view matrix */
  viewMat4: Float32Array;
  fovDeg: number;
  distance: number;
  orthoScale: number;
  flags: number;
  isOrtho: boolean;
}

export interface GsirPoint {
  handleId: number;
  flags: number;
  draggable: boolean;
  selected: boolean;
  target: boolean;
  hint: boolean;
  hollow: boolean;
  pos: Vec3Tuple;
  radius: number;
  rgba: RgbaTuple;
  labelIdx: number;
}

export interface GsirSegment {
  a: Vec3Tuple;
  b: Vec3Tuple;
  width: number;
  rgba: RgbaTuple;
  flags: number;
  handleId: number;
  dashed: boolean;
  arrow: boolean;
  draggable: boolean;
  selected: boolean;
  target: boolean;
  hint: boolean;
}

export interface GsirLine {
  origin: Vec3Tuple;
  dir: Vec3Tuple;
  clip: number;
  width: number;
  rgba: RgbaTuple;
  flags: number;
  handleId: number;
  dashed: boolean;
  draggable: boolean;
  selected: boolean;
  target: boolean;
  hint: boolean;
}

export interface GsirPlane {
  center: Vec3Tuple;
  u: Vec3Tuple;
  v: Vec3Tuple;
  extent: number;
  rgba: RgbaTuple;
  flags: number;
  handleId: number;
  gridLines: boolean;
  draggable: boolean;
  selected: boolean;
  target: boolean;
  hint: boolean;
  labelIdx: number;
}

export interface GsirCircle {
  center: Vec3Tuple;
  u: Vec3Tuple;
  v: Vec3Tuple;
  radius: number;
  width: number;
  rgba: RgbaTuple;
  flags: number;
  imaginary: boolean;
  labelIdx: number;
}

export interface GsirSphere {
  center: Vec3Tuple;
  radius: number;
  rgba: RgbaTuple;
  flags: number;
  imaginary: boolean;
  labelIdx: number;
}

export interface GsirPointPair {
  p1: Vec3Tuple;
  p2: Vec3Tuple;
  radius: number;
  rgba: RgbaTuple;
  flags: number;
  imaginary: boolean;
  showLink: boolean;
}

export interface GsirBivectorDisk {
  origin: Vec3Tuple;
  u: Vec3Tuple;
  v: Vec3Tuple;
  area: number;
  rgba: RgbaTuple;
  flags: number;
  isDisk: boolean;
  orientationArrow: boolean;
}

export interface GsirMeshRef {
  meshId: bigint;
  dirtyHash: bigint;
  motor: Float32Array;
  modelMat4: Float32Array;
  rgba: RgbaTuple;
  flags: number;
  wireframe: boolean;
  doubleSided: boolean;
  useVertexColors: boolean;
}

export interface GsirMeshAsset {
  meshId: bigint;
  dirtyHash: bigint;
  vertCount: number;
  idxCount: number;
  flags: number;
  hasColors: boolean;
  /** Zero-copy view of f32[vertCount * 3] */
  positions: Float32Array;
  /** Zero-copy view of f32[vertCount * 3] */
  normals: Float32Array;
  /** Zero-copy view of f32[vertCount * 4] when hasColors is true */
  colors: Float32Array | null;
  /** Zero-copy view of u32[idxCount], CCW front-face winding */
  indices: Uint32Array;
}

export interface GsirCurve {
  ptCount: number;
  width: number;
  rgba: RgbaTuple;
  flags: number;
  closed: boolean;
  dashed: boolean;
  /** Zero-copy view of f32[ptCount * 3] */
  xyz: Float32Array;
}

export interface GsirFlowParticles {
  particleCount: number;
  pointSize: number;
  rgba: RgbaTuple;
  speed: number;
  /** Zero-copy view of f32[particleCount * 3] */
  starts: Float32Array;
  /** Zero-copy view of f32[particleCount * 3] */
  ends: Float32Array;
}

export interface GsirLabel {
  pos: Vec3Tuple;
  rgba: RgbaTuple;
  textIdx: number;
  flags: number;
  isLatex: boolean;
  billboard: boolean;
}

export interface GsirContourCurve {
  ptCount: number;
  rgba: RgbaTuple;
  width: number;
  flags: number;
  /** Zero-copy view of f32[ptCount * 2] */
  xy: Float32Array;
}

export interface GsirContourIntersection {
  x: number;
  y: number;
  rgba: RgbaTuple;
  labelIdx: number;
}

export interface GsirContourOverlay {
  minX: number;
  maxX: number;
  minY: number;
  maxY: number;
  curves: GsirContourCurve[];
  intersections: GsirContourIntersection[];
}

export interface GsirOpnsUniform {
  shaderIdx: number;
  grade: number;
  coeffCount: number;
  thresh: number;
  maxSteps: number;
  stepSize: number;
  rgba: RgbaTuple;
  flags: number;
  isIPNS: boolean;
  /** Zero-copy view of f32[coeffCount] */
  coeffs: Float32Array;
}

export interface GsirInspectCoeffs {
  entryIdx: number;
  grade: number;
  coeffCount: number;
  /** Zero-copy view of f32[coeffCount] */
  coeffs: Float32Array;
}

export interface AlgebraMeta {
  name: string;
  p: number;
  q: number;
  r: number;
  conformalWitt?: boolean;
  basisNames: string[];
  basisMetric: number[];
}

export interface InspectMetaEntry {
  idx: number;
  name: string;
  grade: number;
  formatted: string;
  editable?: boolean;
}

export interface OpnsShaderMeta {
  hash: string;
  wgsl?: string;
  glsl?: string;
  msl?: string;
}

export interface CalcRegisterMeta {
  slot: string;
  formatted: string;
}

export interface CalcMeta {
  mode: string;
  display: string;
  history: string[];
  registers: CalcRegisterMeta[];
}

export interface WedgeHudState {
  is3D: boolean;
  level: number;
  totalLevels: number;
  title: string;
  goal: string;
  tutorialText: string;
  moves: number;
  score: number;
  elapsedMs: number;
  lastOp: string;
  previewOp: string;
  hintText: string;
  solved: boolean;
  canUndo: boolean;
}

export interface DiagnosticItem {
  severity?: 'error' | 'warning' | 'info';
  line?: number;
  col?: number;
  message: string;
}

export interface ParamSpec {
  name: string;
  label?: string;
  value: number;
  min: number;
  max: number;
  step?: number;
}

export interface GsirMetaJson {
  version: number;
  algebra?: AlgebraMeta;
  presetId?: string;
  title?: string;
  /** Live editable CoffeeShop LiveScript v2 source emitted by Lean for the active preset/frame */
  script?: string;
  /** Optional KaTeX LaTeX formula describing the active geometric algebra identity */
  formula?: string;
  /** Optional concise human explanation of the active 3D scene */
  summary?: string;
  /** Optional interactive @param sliders exposed by Lean presets or LiveScript `slider(...)` */
  params?: ParamSpec[];
  labels?: string[];
  inspect?: InspectMetaEntry[];
  opnsShaders?: OpnsShaderMeta[];
  calc?: CalcMeta;
  wedge?: WedgeHudState;
  diagnostics?: Array<string | DiagnosticItem>;
}

export interface GsirFrame {
  header: GsirHeader;
  camera: GsirCamera | null;
  points: GsirPoint[];
  segments: GsirSegment[];
  lines: GsirLine[];
  planes: GsirPlane[];
  circles: GsirCircle[];
  spheres: GsirSphere[];
  pointPairs: GsirPointPair[];
  bivectorDisks: GsirBivectorDisk[];
  meshRefs: GsirMeshRef[];
  meshAssets: GsirMeshAsset[];
  curves: GsirCurve[];
  flowParticles: GsirFlowParticles[];
  labels: GsirLabel[];
  contourOverlay: GsirContourOverlay | null;
  opnsUniforms: GsirOpnsUniform[];
  inspectCoeffs: GsirInspectCoeffs[];
  meta: GsirMetaJson | null;
  /** True when metaJsonLen === 0 and decoder reused previous frame metadata */
  metaReused: boolean;
  /** Unknown section kinds encountered and safely skipped */
  skippedSections: number[];
  /** Decode duration in microseconds */
  decodeTimeUs: number;
}

// ============================================================================
// Client -> Lean InputEvent Protocol
// ============================================================================

export const InputEventKind = {
  DRAG_HANDLE: 0x01,
  TICK: 0x02,
  EDIT_COEFF: 0x04,
  WEDGE_GESTURE: 0x06,
  WEDGE_ACTION: 0x07,
  SET_CAMERA: 0x09,
  SLICE_PLANE: 0x0a,
} as const;
export type InputEventKindValue = (typeof InputEventKind)[keyof typeof InputEventKind];

export const InputEventFlag = {
  NONE: 0,
  FORCE_FULL_SNAPSHOT: 1 << 0,
} as const;

export const WedgeGestureFlag = {
  NONE: 0,
  IS_PREVIEW: 1 << 0,
} as const;

export const WedgeActionCode = {
  UNDO: 0,
  RESET: 1,
  NEXT: 2,
  PREV: 3,
  TOGGLE_3D: 4,
  HINT: 5,
  GOTO_LEVEL: 6,
} as const;
export type WedgeActionCodeValue = (typeof WedgeActionCode)[keyof typeof WedgeActionCode];

export type BinaryInputEvent =
  | { kind: typeof InputEventKind.DRAG_HANDLE; handleId: number; x: number; y: number; z: number; forceFullSnapshot?: boolean }
  | { kind: typeof InputEventKind.TICK; dt: number; timeSec: number; forceFullSnapshot?: boolean }
  | { kind: typeof InputEventKind.EDIT_COEFF; entryIdx: number; bladeIdx: number; value: number; forceFullSnapshot?: boolean }
  | {
      kind: typeof InputEventKind.WEDGE_GESTURE;
      idA: number;
      idB: number;
      dirA: Vec3Tuple;
      dirB: Vec3Tuple;
      holdA?: number;
      holdB?: number;
      isPreview: boolean;
      forceFullSnapshot?: boolean;
    }
  | { kind: typeof InputEventKind.WEDGE_ACTION; action: WedgeActionCodeValue; arg?: number; forceFullSnapshot?: boolean }
  | { kind: typeof InputEventKind.SET_CAMERA; motor: ArrayLike<number>; fovDeg: number; distance: number; forceFullSnapshot?: boolean }
  | { kind: typeof InputEventKind.SLICE_PLANE; motor: ArrayLike<number>; forceFullSnapshot?: boolean };

export type JsonInputEvent =
  | { op: 'dragHandle'; id: number; pos: [number, number, number]; forceFullSnapshot?: boolean }
  | { op: 'tick'; dt: number; t: number; forceFullSnapshot?: boolean }
  | { op: 'evalScript'; algebra: string; code: string; forceFullSnapshot?: boolean }
  | { op: 'editCoeff'; entryIdx: number; bladeIdx: number; val: number; forceFullSnapshot?: boolean }
  | { op: 'loadPreset'; id: string; forceFullSnapshot?: boolean }
  | {
      op: 'wedgeGesture';
      idA: number;
      idB: number;
      dirA: [number, number, number];
      dirB: [number, number, number];
      holdA?: boolean;
      holdB?: boolean;
      isPreview?: boolean;
      forceFullSnapshot?: boolean;
    }
  | { op: 'wedgeAction'; action: 'undo' | 'reset' | 'next' | 'prev' | 'toggle3D' | 'hint' | 'goto'; arg?: number; forceFullSnapshot?: boolean }
  | { op: 'calcKey'; key: string; forceFullSnapshot?: boolean }
  | { op: 'calcEval'; mode: string; expr: string; forceFullSnapshot?: boolean }
  | { op: 'setCamera'; motor: number[]; fovDeg: number; distance: number; forceFullSnapshot?: boolean }
  | { op: 'slicePlane'; motor: number[]; forceFullSnapshot?: boolean }
  | { op: 'evalEquations'; equations: string[]; bounds: [number, number, number, number]; gridN: number; forceFullSnapshot?: boolean }
  | { op: 'evalSurface'; expr: string; bounds: [number, number, number, number]; gridN: number; forceFullSnapshot?: boolean }
  | {
      op: 'evalImplicit';
      expr: string;
      gpuRaymarch: boolean;
      bounds?: [number, number, number, number, number, number];
      gridN?: number;
      forceFullSnapshot?: boolean;
    }
  | {
      op: 'evalParametric';
      fx: string;
      fy: string;
      fz: string;
      uRange?: [number, number];
      vRange?: [number, number];
      gridN?: number;
      forceFullSnapshot?: boolean;
    }
  | { op: 'wedgeTutorial'; id: 'T1' | 'T2' | 'T3' | 'T4' | 'T5' | 'T6'; forceFullSnapshot?: boolean }
  | { op: 'wedgeRandom'; dim: 2 | 3; difficulty: 0 | 1 | 2; seed: number; forceFullSnapshot?: boolean }
  | { op: 'setParam'; name: string; value: number };

// C ABI return status codes (§5)
export const GsirStatus = {
  OK: 0,
  ERR_BAD_HANDLE: -1,
  ERR_BAD_INPUT: -2,
  ERR_BUF_SMALL: -3,
} as const;

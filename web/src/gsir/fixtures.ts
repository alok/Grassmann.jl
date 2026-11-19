// Static pre-encoded binary GSIR v1 fixtures for offline unit tests and static .gsir inspection.
// ZERO Geometric Algebra math, ZERO normal computation, ZERO mesh slicing, ZERO Wedge logic here:
// these are strictly hardcoded static byte-level wire test vectors.

import { encodeGsirFrame } from './encoder';
import {
  BivectorFlag,
  CameraFlag,
  CircleFlag,
  CurveFlag,
  GSIR_NO_LABEL,
  HeaderFlag,
  LabelFlag,
  LineFlag,
  MeshAssetFlag,
  MeshRefFlag,
  ModeKind,
  OpnsFlag,
  PlaneFlag,
  PointFlag,
  PointPairFlag,
  SegmentFlag,
  SphereFlag,
} from './types';

function identityMat4(): Float32Array {
  return new Float32Array([
    1, 0, 0, 0,
    0, 1, 0, 0,
    0, 0, 1, 0,
    0, 0, 0, 1,
  ]);
}

function identityMotor(): Float32Array {
  return new Float32Array([1, 0, 0, 0, 0, 0, 0, 0]);
}

/**
 * Full-coverage static binary GSIR v1 fixture containing EVERY section 0x01..0x11,
 * including odd-idxCount MESH_ASSETS (testing 8-byte record padding), handleId = 0 draggable point,
 * imaginary circles/spheres/point-pairs, bivector disks, contour overlay, OPNS uniforms, and inspect coeffs.
 */
export function buildAllSectionsFixtureBytes(): Uint8Array {
  // Static unit tetrahedron (4 verts, 12 indices = even) + static single triangle (3 verts, 3 indices = ODD to verify 8B pad!)
  const triPositions = new Float32Array([
    -0.8, -0.5, 0.0,
     0.8, -0.5, 0.0,
     0.0,  0.9, 0.0,
  ]);
  const triNormals = new Float32Array([
    0, 0, 1,
    0, 0, 1,
    0, 0, 1,
  ]);
  const triColors = new Float32Array([
    0.25, 0.72, 1.0, 1.0,
    0.96, 0.48, 0.25, 1.0,
    0.42, 0.94, 0.72, 1.0,
  ]);
  // ODD index count = 3 (CCW front-face winding) -> forces 4B zero pad before next mesh asset!
  const triIndices = new Uint32Array([0, 1, 2]);

  const quadPositions = new Float32Array([
    -0.6, -0.6, -0.6,
     0.6, -0.6, -0.6,
     0.6,  0.6, -0.6,
    -0.6,  0.6, -0.6,
  ]);
  const quadNormals = new Float32Array([
    0, 0, 1,
    0, 0, 1,
    0, 0, 1,
    0, 0, 1,
  ]);
  const quadIndices = new Uint32Array([0, 1, 2, 0, 2, 3]);

  const sampleGlsl = `
// Static fixture OPNS test shader (emitted by Lean in live mode)
uniform vec4 uColor;
uniform float uCoeffs[16];
uniform float uThresh;
uniform int uMaxSteps;
uniform float uStepSize;
uniform int uIsIPNS;
varying vec3 vWorldPos;
varying vec3 vLocalPos;
void main() {
  float d = length(vLocalPos) - 0.55;
  if (abs(d) > 0.45) discard;
  vec3 n = normalize(vLocalPos + vec3(0.0001));
  float rim = pow(1.0 - abs(dot(n, vec3(0.0, 0.0, 1.0))), 2.0);
  vec3 col = mix(uColor.rgb * 0.6, vec3(0.95, 0.98, 1.0), rim * 0.65);
  gl_FragColor = vec4(col, uColor.a * (0.35 + 0.55 * rim));
}
`;

  return encodeGsirFrame({
    flags:
      HeaderFlag.GRID_ENABLED |
      HeaderFlag.DARK_THEME |
      HeaderFlag.HAS_CONTOUR_OVERLAY |
      HeaderFlag.HAS_OPNS_SHADER |
      HeaderFlag.HAS_CALC_STATE,
    frameSeq: 42n,
    simTime: 1.5,
    p: 3,
    q: 0,
    r: 1,
    modeKind: ModeKind.CoffeeShop,
    gridSize: 6.0,
    camera: {
      motor: identityMotor(),
      viewMat4: identityMat4(),
      fovDeg: 45,
      distance: 5.5,
      orthoScale: 3.0,
      flags: 0,
    },
    points: [
      {
        // handleId = 0 MUST be valid & draggable when PointFlag.DRAGGABLE is set (#17 Fix #3)
        handleId: 0,
        flags: PointFlag.DRAGGABLE | PointFlag.SELECTED,
        pos: [-1.2, 0.8, 0.4],
        radius: 0.11,
        rgba: [0.35, 0.88, 1.0, 1.0],
        labelIdx: 0,
      },
      {
        handleId: 1,
        flags: PointFlag.DRAGGABLE,
        pos: [1.3, 0.4, -0.5],
        radius: 0.1,
        rgba: [1.0, 0.64, 0.28, 1.0],
        labelIdx: 1,
      },
      {
        handleId: 2,
        flags: PointFlag.TARGET | PointFlag.HOLLOW,
        pos: [0.0, 1.4, 0.0],
        radius: 0.12,
        rgba: [1.0, 0.32, 0.42, 1.0],
        labelIdx: GSIR_NO_LABEL,
      },
    ],
    segments: [
      {
        a: [-1.2, 0.8, 0.4],
        b: [1.3, 0.4, -0.5],
        width: 3.0,
        rgba: [0.45, 0.95, 0.78, 1.0],
        flags: SegmentFlag.ARROW | (10 << 16),
      },
      {
        a: [0.0, 0.0, 0.0],
        b: [0.0, 1.4, 0.0],
        width: 2.0,
        rgba: [0.72, 0.78, 0.92, 0.75],
        flags: SegmentFlag.DASHED | SegmentFlag.HINT,
      },
    ],
    lines: [
      {
        origin: [0.0, 0.2, 0.0],
        dir: [0.8, 0.6, 0.0],
        clip: 4.0,
        width: 2.5,
        rgba: [0.56, 0.78, 1.0, 0.92],
        flags: LineFlag.DRAGGABLE | (20 << 16),
      },
    ],
    planes: [
      {
        center: [0.0, 0.0, 0.0],
        u: [1.0, 0.0, 0.0],
        v: [0.0, 0.0, 1.0],
        extent: 1.8,
        rgba: [0.22, 0.66, 0.98, 0.24],
        flags: PlaneFlag.GRID_LINES | PlaneFlag.DRAGGABLE | (30 << 16),
        labelIdx: 2,
      },
    ],
    circles: [
      {
        center: [0.0, 0.5, 0.0],
        u: [1.0, 0.0, 0.0],
        v: [0.0, 1.0, 0.0],
        radius: 1.15,
        width: 2.5,
        rgba: [0.98, 0.76, 0.3, 0.95],
        flags: 0,
        labelIdx: GSIR_NO_LABEL,
      },
      {
        center: [0.0, 0.5, 0.0],
        u: [0.0, 0.0, 1.0],
        v: [0.0, 1.0, 0.0],
        radius: 0.75,
        width: 2.0,
        rgba: [0.98, 0.35, 0.58, 0.85],
        flags: CircleFlag.IMAGINARY,
        labelIdx: GSIR_NO_LABEL,
      },
    ],
    spheres: [
      {
        center: [-0.9, 0.4, 0.1],
        radius: 0.7,
        rgba: [0.28, 0.78, 1.0, 0.28],
        flags: 0,
        labelIdx: GSIR_NO_LABEL,
      },
      {
        center: [1.1, 0.4, 0.1],
        radius: 0.55,
        rgba: [0.98, 0.42, 0.62, 0.4],
        flags: SphereFlag.IMAGINARY,
        labelIdx: GSIR_NO_LABEL,
      },
    ],
    pointPairs: [
      {
        p1: [-0.6, -0.4, 0.7],
        p2: [0.6, -0.4, 0.7],
        radius: 0.08,
        rgba: [0.76, 0.55, 1.0, 1.0],
        flags: PointPairFlag.SHOW_LINK,
      },
    ],
    bivectorDisks: [
      {
        origin: [0.0, 0.0, 0.0],
        u: [0.9, 0.2, 0.0],
        v: [0.1, 0.85, 0.2],
        area: 0.745,
        rgba: [0.98, 0.56, 0.24, 0.48],
        flags: BivectorFlag.ORIENTATION_ARROW,
      },
      {
        origin: [0.0, -0.6, 0.0],
        u: [0.6, 0.0, 0.0],
        v: [0.0, 0.0, 0.6],
        area: 0.36,
        rgba: [0.24, 0.88, 0.76, 0.42],
        flags: BivectorFlag.DISK | BivectorFlag.ORIENTATION_ARROW,
      },
    ],
    meshAssets: [
      {
        meshId: 101n,
        dirtyHash: 0xabc123n,
        positions: triPositions,
        normals: triNormals,
        colors: triColors,
        indices: triIndices,
        flags: MeshAssetFlag.HAS_COLORS,
      },
      {
        meshId: 102n,
        dirtyHash: 0xdef456n,
        positions: quadPositions,
        normals: quadNormals,
        colors: null,
        indices: quadIndices,
        flags: 0,
      },
    ],
    meshRefs: [
      {
        meshId: 101n,
        dirtyHash: 0xabc123n,
        motor: identityMotor(),
        modelMat4: identityMat4(),
        rgba: [1.0, 1.0, 1.0, 1.0],
        flags: MeshRefFlag.USE_VERTEX_COLORS | MeshRefFlag.DOUBLE_SIDED,
      },
      {
        meshId: 102n,
        dirtyHash: 0xdef456n,
        motor: identityMotor(),
        modelMat4: identityMat4(),
        rgba: [0.55, 0.72, 1.0, 0.6],
        flags: MeshRefFlag.WIREFRAME,
      },
    ],
    curves: [
      {
        width: 2.2,
        rgba: [0.95, 0.85, 0.35, 0.95],
        flags: CurveFlag.CLOSED,
        xyz: new Float32Array([
          -1.0, -0.8, 0.2,
           0.0, -1.1, 0.5,
           1.0, -0.8, 0.2,
           0.0, -0.5, -0.1,
        ]),
      },
    ],
    flowParticles: [
      {
        pointSize: 0.06,
        rgba: [0.32, 0.95, 0.92, 0.9],
        speed: 0.75,
        starts: new Float32Array([
          -1.5, 0.2, -0.5,
          -1.5, 0.5, 0.0,
          -1.5, 0.8, 0.5,
        ]),
        ends: new Float32Array([
          1.5, 0.6, -0.5,
          1.5, 0.9, 0.0,
          1.5, 1.2, 0.5,
        ]),
      },
    ],
    labels: [
      {
        pos: [-1.2, 1.0, 0.4],
        rgba: [0.88, 0.95, 1.0, 1.0],
        textIdx: 0,
        flags: LabelFlag.IS_LATEX | LabelFlag.BILLBOARD,
      },
    ],
    contourOverlay: {
      minX: -2,
      maxX: 2,
      minY: -2,
      maxY: 2,
      curves: [
        {
          ptCount: 5,
          rgba: [0.35, 0.92, 1.0, 1.0],
          width: 2.0,
          flags: 0,
          xy: new Float32Array([-1.2, 0.0, 0.0, 1.2, 1.2, 0.0, 0.0, -1.2, -1.2, 0.0]),
        },
        {
          ptCount: 2,
          rgba: [1.0, 0.64, 0.28, 1.0],
          width: 1.8,
          flags: 0,
          xy: new Float32Array([-1.6, -1.6, 1.6, 1.6]),
        },
      ],
      intersections: [
        { x: 0.6, y: 0.6, rgba: [1.0, 0.32, 0.42, 1.0], labelIdx: 0 },
        { x: -0.6, y: -0.6, rgba: [1.0, 0.32, 0.42, 1.0], labelIdx: 1 },
      ],
    },
    opnsUniforms: [
      {
        shaderIdx: 0,
        grade: 4,
        thresh: 0.002,
        maxSteps: 64,
        stepSize: 0.05,
        rgba: [0.38, 0.82, 1.0, 0.72],
        flags: OpnsFlag.IS_IPNS,
        coeffs: new Float32Array([1, 0, 0, 0, 0.5, 0, 0, 0]),
      },
    ],
    inspectCoeffs: [
      {
        entryIdx: 0,
        grade: 1,
        coeffs: new Float32Array([0, 0.5, 0.0, 1.0, 0.0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
      },
    ],
    meta: {
      version: 1,
      algebra: {
        name: 'PGA3',
        p: 3,
        q: 0,
        r: 1,
        conformalWitt: false,
        basisNames: [
          '1', 'e0', 'e1', 'e2', 'e3',
          'e01', 'e02', 'e03', 'e12', 'e13', 'e23',
          'e012', 'e013', 'e023', 'e123', 'e0123',
        ],
        basisMetric: [1, 0, 1, 1, 1, 0, 0, 0, -1, -1, -1, 0, 0, 0, -1, 0],
      },
      presetId: 'fixture_all_sections',
      title: 'GSIR v1 Static Wire Fixture (All Sections)',
      labels: ['P_0 = e_{123}', 'P_1', 'Cut Plane'],
      inspect: [
        {
          idx: 0,
          name: 'cut',
          grade: 1,
          formatted: '0.5e0 + 1.0e2',
          editable: true,
        },
      ],
      opnsShaders: [
        {
          hash: 'fixture_opns_v1',
          glsl: sampleGlsl,
        },
      ],
      calc: {
        mode: 'STA',
        display: '1.00 + 0.75e12',
        history: ['A = e1 + 0.5e2', 'A ∧ B'],
        registers: [
          { slot: 'x1', formatted: 'e1 + 0.5e2' },
          { slot: 'x2', formatted: '0.2e1 + e2' },
        ],
      },
      diagnostics: [],
    },
  });
}

/**
 * Static binary delta frame with metaJsonLen = 0 and 2D ortho camera flag (#17 Fix #4 & #5).
 */
export function buildOrthoDeltaFixtureBytes(frameSeq = 43n): Uint8Array {
  return encodeGsirFrame({
    flags: HeaderFlag.IS_2D | HeaderFlag.GRID_ENABLED | HeaderFlag.DARK_THEME | HeaderFlag.HAS_WEDGE_HUD,
    frameSeq,
    simTime: 2.0,
    p: 2,
    q: 0,
    r: 1,
    modeKind: ModeKind.Wedge2D,
    gridSize: 4.0,
    camera: {
      motor: identityMotor(),
      viewMat4: identityMat4(),
      fovDeg: 45,
      distance: 5.0,
      orthoScale: 2.5,
      flags: CameraFlag.IS_ORTHO,
    },
    points: [
      {
        handleId: 0,
        flags: PointFlag.DRAGGABLE,
        pos: [-1.0, 0.0, 0.0],
        radius: 0.09,
        rgba: [1.0, 1.0, 1.0, 1.0],
        labelIdx: GSIR_NO_LABEL,
      },
      {
        handleId: 1,
        flags: PointFlag.DRAGGABLE,
        pos: [1.0, 0.5, 0.0],
        radius: 0.09,
        rgba: [1.0, 1.0, 1.0, 1.0],
        labelIdx: GSIR_NO_LABEL,
      },
    ],
    meta: null, // metaJsonLen = 0 (unchanged)
  });
}

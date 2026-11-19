// Binary InputEvent Encoder + Strict GSIR v1 Frame Encoder (for tests & static binary fixtures)
// Conforms strictly to docs/SCENE_IR_V1.md + all 5 fixes from verifier-core (#17).

import {
  GSIR_DIR_ENTRY_SIZE,
  GSIR_HEADER_SIZE,
  GSIR_MAGIC,
  GSIR_VERSION,
  InputEventFlag,
  InputEventKind,
  MeshAssetFlag,
  SectionKind,
  WedgeGestureFlag,
  type BinaryInputEvent,
  type GsirBivectorDisk,
  type GsirCamera,
  type GsirCircle,
  type GsirContourOverlay,
  type GsirCurve,
  type GsirFlowParticles,
  type GsirInspectCoeffs,
  type GsirLabel,
  type GsirLine,
  type GsirMeshAsset,
  type GsirMeshRef,
  type GsirMetaJson,
  type GsirOpnsUniform,
  type GsirPlane,
  type GsirPoint,
  type GsirPointPair,
  type GsirSegment,
  type GsirSphere,
  type ModeKindValue,
  type Vec3Tuple,
  type WedgeActionCodeValue,
} from './types';

const textEncoder = new TextEncoder();

function align8(n: number): number {
  return (n + 7) & ~7;
}

// ============================================================================
// Binary InputEvent Encoders (4B Header: { kind: u8, flags: u8, payloadLen: u16 })
// ============================================================================

export function encodeDragHandle(
  handleId: number,
  x: number,
  y: number,
  z: number,
  forceFullSnapshot = false
): Uint8Array {
  const buf = new ArrayBuffer(20);
  const dv = new DataView(buf);
  dv.setUint8(0, InputEventKind.DRAG_HANDLE);
  dv.setUint8(1, forceFullSnapshot ? InputEventFlag.FORCE_FULL_SNAPSHOT : InputEventFlag.NONE);
  dv.setUint16(2, 16, true);
  dv.setUint32(4, handleId >>> 0, true);
  dv.setFloat32(8, x, true);
  dv.setFloat32(12, y, true);
  dv.setFloat32(16, z, true);
  return new Uint8Array(buf);
}

export function encodeTick(dt: number, timeSec: number, forceFullSnapshot = false): Uint8Array {
  const buf = new ArrayBuffer(12);
  const dv = new DataView(buf);
  dv.setUint8(0, InputEventKind.TICK);
  dv.setUint8(1, forceFullSnapshot ? InputEventFlag.FORCE_FULL_SNAPSHOT : InputEventFlag.NONE);
  dv.setUint16(2, 8, true);
  dv.setFloat32(4, dt, true);
  dv.setFloat32(8, timeSec, true);
  return new Uint8Array(buf);
}

export function encodeEditCoeff(
  entryIdx: number,
  bladeIdx: number,
  value: number,
  forceFullSnapshot = false
): Uint8Array {
  const buf = new ArrayBuffer(16);
  const dv = new DataView(buf);
  dv.setUint8(0, InputEventKind.EDIT_COEFF);
  dv.setUint8(1, forceFullSnapshot ? InputEventFlag.FORCE_FULL_SNAPSHOT : InputEventFlag.NONE);
  dv.setUint16(2, 12, true);
  dv.setUint32(4, entryIdx >>> 0, true);
  dv.setUint32(8, bladeIdx >>> 0, true);
  dv.setFloat32(12, value, true);
  return new Uint8Array(buf);
}

/**
 * Encodes 0x06 WedgeGesture (36 B payload, 40 B total).
 * #17 Fix #3: tail u16 is gestureFlags (b0 = isPreview); Lean derives hold from raw dirA/dirB.
 */
export function encodeWedgeGesture(
  idA: number,
  idB: number,
  dirA: Vec3Tuple,
  dirB: Vec3Tuple,
  isPreview: boolean,
  holdA = 0,
  holdB = 0,
  forceFullSnapshot = false
): Uint8Array {
  const buf = new ArrayBuffer(40);
  const dv = new DataView(buf);
  dv.setUint8(0, InputEventKind.WEDGE_GESTURE);
  dv.setUint8(1, forceFullSnapshot ? InputEventFlag.FORCE_FULL_SNAPSHOT : InputEventFlag.NONE);
  dv.setUint16(2, 36, true);
  dv.setUint32(4, idA >>> 0, true);
  dv.setUint32(8, idB >>> 0, true);
  dv.setFloat32(12, dirA[0], true);
  dv.setFloat32(16, dirA[1], true);
  dv.setFloat32(20, dirA[2], true);
  dv.setFloat32(24, dirB[0], true);
  dv.setFloat32(28, dirB[1], true);
  dv.setFloat32(32, dirB[2], true);
  dv.setUint8(36, holdA & 0xff);
  dv.setUint8(37, holdB & 0xff);
  dv.setUint16(38, isPreview ? WedgeGestureFlag.IS_PREVIEW : WedgeGestureFlag.NONE, true);
  return new Uint8Array(buf);
}

export function encodeWedgeAction(
  action: WedgeActionCodeValue,
  arg = 0,
  forceFullSnapshot = false
): Uint8Array {
  const buf = new ArrayBuffer(12);
  const dv = new DataView(buf);
  dv.setUint8(0, InputEventKind.WEDGE_ACTION);
  dv.setUint8(1, forceFullSnapshot ? InputEventFlag.FORCE_FULL_SNAPSHOT : InputEventFlag.NONE);
  dv.setUint16(2, 8, true);
  dv.setUint8(4, action & 0xff);
  dv.setUint8(5, 0);
  dv.setUint8(6, 0);
  dv.setUint8(7, 0);
  dv.setUint32(8, arg >>> 0, true);
  return new Uint8Array(buf);
}

export function encodeSetCamera(
  motor: ArrayLike<number>,
  fovDeg: number,
  distance: number,
  forceFullSnapshot = false
): Uint8Array {
  const buf = new ArrayBuffer(44);
  const dv = new DataView(buf);
  dv.setUint8(0, InputEventKind.SET_CAMERA);
  dv.setUint8(1, forceFullSnapshot ? InputEventFlag.FORCE_FULL_SNAPSHOT : InputEventFlag.NONE);
  dv.setUint16(2, 40, true);
  for (let i = 0; i < 8; i++) {
    dv.setFloat32(4 + i * 4, motor[i] ?? (i === 0 ? 1 : 0), true);
  }
  dv.setFloat32(36, fovDeg, true);
  dv.setFloat32(40, distance, true);
  return new Uint8Array(buf);
}

export function encodeSlicePlane(motor: ArrayLike<number>, forceFullSnapshot = false): Uint8Array {
  const buf = new ArrayBuffer(36);
  const dv = new DataView(buf);
  dv.setUint8(0, InputEventKind.SLICE_PLANE);
  dv.setUint8(1, forceFullSnapshot ? InputEventFlag.FORCE_FULL_SNAPSHOT : InputEventFlag.NONE);
  dv.setUint16(2, 32, true);
  for (let i = 0; i < 8; i++) {
    dv.setFloat32(4 + i * 4, motor[i] ?? (i === 0 ? 1 : 0), true);
  }
  return new Uint8Array(buf);
}

export function encodeBinaryInputEvent(ev: BinaryInputEvent): Uint8Array {
  switch (ev.kind) {
    case InputEventKind.DRAG_HANDLE:
      return encodeDragHandle(ev.handleId, ev.x, ev.y, ev.z, ev.forceFullSnapshot);
    case InputEventKind.TICK:
      return encodeTick(ev.dt, ev.timeSec, ev.forceFullSnapshot);
    case InputEventKind.EDIT_COEFF:
      return encodeEditCoeff(ev.entryIdx, ev.bladeIdx, ev.value, ev.forceFullSnapshot);
    case InputEventKind.WEDGE_GESTURE:
      return encodeWedgeGesture(
        ev.idA,
        ev.idB,
        ev.dirA,
        ev.dirB,
        ev.isPreview,
        ev.holdA ?? 0,
        ev.holdB ?? 0,
        ev.forceFullSnapshot
      );
    case InputEventKind.WEDGE_ACTION:
      return encodeWedgeAction(ev.action, ev.arg ?? 0, ev.forceFullSnapshot);
    case InputEventKind.SET_CAMERA:
      return encodeSetCamera(ev.motor, ev.fovDeg, ev.distance, ev.forceFullSnapshot);
    case InputEventKind.SLICE_PLANE:
      return encodeSlicePlane(ev.motor, ev.forceFullSnapshot);
  }
}

// ============================================================================
// GSIR v1 Binary Frame Encoder (strict 8-byte aligned sections & mesh records)
// Used for round-trip unit tests and static binary fixtures.
// ============================================================================

export interface EncodeGsirFrameInput {
  flags?: number;
  frameSeq?: bigint;
  simTime?: number;
  p?: number;
  q?: number;
  r?: number;
  modeKind?: ModeKindValue;
  gridSize?: number;
  camera?: Omit<GsirCamera, 'isOrtho'> & { isOrtho?: boolean };
  points?: Array<Pick<GsirPoint, 'handleId' | 'flags' | 'pos' | 'radius' | 'rgba' | 'labelIdx'>>;
  segments?: Array<Pick<GsirSegment, 'a' | 'b' | 'width' | 'rgba' | 'flags'>>;
  lines?: Array<Pick<GsirLine, 'origin' | 'dir' | 'clip' | 'width' | 'rgba' | 'flags'>>;
  planes?: Array<Pick<GsirPlane, 'center' | 'u' | 'v' | 'extent' | 'rgba' | 'flags' | 'labelIdx'>>;
  circles?: Array<Pick<GsirCircle, 'center' | 'u' | 'v' | 'radius' | 'width' | 'rgba' | 'flags' | 'labelIdx'>>;
  spheres?: Array<Pick<GsirSphere, 'center' | 'radius' | 'rgba' | 'flags' | 'labelIdx'>>;
  pointPairs?: Array<Pick<GsirPointPair, 'p1' | 'p2' | 'radius' | 'rgba' | 'flags'>>;
  bivectorDisks?: Array<Pick<GsirBivectorDisk, 'origin' | 'u' | 'v' | 'area' | 'rgba' | 'flags'>>;
  meshRefs?: Array<Pick<GsirMeshRef, 'meshId' | 'dirtyHash' | 'motor' | 'modelMat4' | 'rgba' | 'flags'>>;
  meshAssets?: Array<
    Pick<GsirMeshAsset, 'meshId' | 'dirtyHash' | 'positions' | 'normals' | 'colors' | 'indices'> & { flags?: number }
  >;
  curves?: Array<Pick<GsirCurve, 'width' | 'rgba' | 'flags' | 'xyz'>>;
  flowParticles?: Array<Pick<GsirFlowParticles, 'pointSize' | 'rgba' | 'speed' | 'starts' | 'ends'>>;
  labels?: Array<Pick<GsirLabel, 'pos' | 'rgba' | 'textIdx' | 'flags'>>;
  contourOverlay?: GsirContourOverlay | null;
  opnsUniforms?: Array<Pick<GsirOpnsUniform, 'shaderIdx' | 'grade' | 'thresh' | 'maxSteps' | 'stepSize' | 'rgba' | 'flags' | 'coeffs'>>;
  inspectCoeffs?: Array<Pick<GsirInspectCoeffs, 'entryIdx' | 'grade' | 'coeffs'>>;
  extraSections?: Array<{ kind: number; count: number; data: Uint8Array }>;
  /** Omit or pass null to emit metaJsonLen = 0 (unchanged delta frame) */
  meta?: GsirMetaJson | null;
}

interface EncodedSection {
  kind: number;
  count: number;
  bytes: Uint8Array;
}

export function encodeGsirFrame(spec: EncodeGsirFrameInput): Uint8Array {
  const sections: EncodedSection[] = [];

  if (spec.camera) {
    const b = new Uint8Array(112);
    const dv = new DataView(b.buffer);
    for (let i = 0; i < 8; i++) dv.setFloat32(i * 4, spec.camera.motor[i] ?? 0, true);
    for (let i = 0; i < 16; i++) dv.setFloat32(32 + i * 4, spec.camera.viewMat4[i] ?? 0, true);
    dv.setFloat32(96, spec.camera.fovDeg, true);
    dv.setFloat32(100, spec.camera.distance, true);
    dv.setFloat32(104, spec.camera.orthoScale, true);
    dv.setUint32(108, spec.camera.flags >>> 0, true);
    sections.push({ kind: SectionKind.CAMERA, count: 1, bytes: b });
  }

  if (spec.points && spec.points.length > 0) {
    const b = new Uint8Array(spec.points.length * 44);
    const dv = new DataView(b.buffer);
    spec.points.forEach((pt, i) => {
      const o = i * 44;
      dv.setUint32(o, pt.handleId >>> 0, true);
      dv.setUint32(o + 4, pt.flags >>> 0, true);
      dv.setFloat32(o + 8, pt.pos[0], true);
      dv.setFloat32(o + 12, pt.pos[1], true);
      dv.setFloat32(o + 16, pt.pos[2], true);
      dv.setFloat32(o + 20, pt.radius, true);
      dv.setFloat32(o + 24, pt.rgba[0], true);
      dv.setFloat32(o + 28, pt.rgba[1], true);
      dv.setFloat32(o + 32, pt.rgba[2], true);
      dv.setFloat32(o + 36, pt.rgba[3], true);
      dv.setUint32(o + 40, pt.labelIdx >>> 0, true);
    });
    sections.push({ kind: SectionKind.POINTS, count: spec.points.length, bytes: b });
  }

  if (spec.segments && spec.segments.length > 0) {
    const b = new Uint8Array(spec.segments.length * 48);
    const dv = new DataView(b.buffer);
    spec.segments.forEach((seg, i) => {
      const o = i * 48;
      dv.setFloat32(o, seg.a[0], true);
      dv.setFloat32(o + 4, seg.a[1], true);
      dv.setFloat32(o + 8, seg.a[2], true);
      dv.setFloat32(o + 12, seg.b[0], true);
      dv.setFloat32(o + 16, seg.b[1], true);
      dv.setFloat32(o + 20, seg.b[2], true);
      dv.setFloat32(o + 24, seg.width, true);
      dv.setFloat32(o + 28, seg.rgba[0], true);
      dv.setFloat32(o + 32, seg.rgba[1], true);
      dv.setFloat32(o + 36, seg.rgba[2], true);
      dv.setFloat32(o + 40, seg.rgba[3], true);
      dv.setUint32(o + 44, seg.flags >>> 0, true);
    });
    sections.push({ kind: SectionKind.SEGMENTS, count: spec.segments.length, bytes: b });
  }

  if (spec.lines && spec.lines.length > 0) {
    const b = new Uint8Array(spec.lines.length * 52);
    const dv = new DataView(b.buffer);
    spec.lines.forEach((ln, i) => {
      const o = i * 52;
      dv.setFloat32(o, ln.origin[0], true);
      dv.setFloat32(o + 4, ln.origin[1], true);
      dv.setFloat32(o + 8, ln.origin[2], true);
      dv.setFloat32(o + 12, ln.dir[0], true);
      dv.setFloat32(o + 16, ln.dir[1], true);
      dv.setFloat32(o + 20, ln.dir[2], true);
      dv.setFloat32(o + 24, ln.clip, true);
      dv.setFloat32(o + 28, ln.width, true);
      dv.setFloat32(o + 32, ln.rgba[0], true);
      dv.setFloat32(o + 36, ln.rgba[1], true);
      dv.setFloat32(o + 40, ln.rgba[2], true);
      dv.setFloat32(o + 44, ln.rgba[3], true);
      dv.setUint32(o + 48, ln.flags >>> 0, true);
    });
    sections.push({ kind: SectionKind.LINES, count: spec.lines.length, bytes: b });
  }

  if (spec.planes && spec.planes.length > 0) {
    const b = new Uint8Array(spec.planes.length * 64);
    const dv = new DataView(b.buffer);
    spec.planes.forEach((pl, i) => {
      const o = i * 64;
      dv.setFloat32(o, pl.center[0], true);
      dv.setFloat32(o + 4, pl.center[1], true);
      dv.setFloat32(o + 8, pl.center[2], true);
      dv.setFloat32(o + 12, pl.u[0], true);
      dv.setFloat32(o + 16, pl.u[1], true);
      dv.setFloat32(o + 20, pl.u[2], true);
      dv.setFloat32(o + 24, pl.v[0], true);
      dv.setFloat32(o + 28, pl.v[1], true);
      dv.setFloat32(o + 32, pl.v[2], true);
      dv.setFloat32(o + 36, pl.extent, true);
      dv.setFloat32(o + 40, pl.rgba[0], true);
      dv.setFloat32(o + 44, pl.rgba[1], true);
      dv.setFloat32(o + 48, pl.rgba[2], true);
      dv.setFloat32(o + 52, pl.rgba[3], true);
      dv.setUint32(o + 56, pl.flags >>> 0, true);
      dv.setUint32(o + 60, pl.labelIdx >>> 0, true);
    });
    sections.push({ kind: SectionKind.PLANES, count: spec.planes.length, bytes: b });
  }

  if (spec.circles && spec.circles.length > 0) {
    const b = new Uint8Array(spec.circles.length * 68);
    const dv = new DataView(b.buffer);
    spec.circles.forEach((c, i) => {
      const o = i * 68;
      dv.setFloat32(o, c.center[0], true);
      dv.setFloat32(o + 4, c.center[1], true);
      dv.setFloat32(o + 8, c.center[2], true);
      dv.setFloat32(o + 12, c.u[0], true);
      dv.setFloat32(o + 16, c.u[1], true);
      dv.setFloat32(o + 20, c.u[2], true);
      dv.setFloat32(o + 24, c.v[0], true);
      dv.setFloat32(o + 28, c.v[1], true);
      dv.setFloat32(o + 32, c.v[2], true);
      dv.setFloat32(o + 36, c.radius, true);
      dv.setFloat32(o + 40, c.width, true);
      dv.setFloat32(o + 44, c.rgba[0], true);
      dv.setFloat32(o + 48, c.rgba[1], true);
      dv.setFloat32(o + 52, c.rgba[2], true);
      dv.setFloat32(o + 56, c.rgba[3], true);
      dv.setUint32(o + 60, c.flags >>> 0, true);
      dv.setUint32(o + 64, c.labelIdx >>> 0, true);
    });
    sections.push({ kind: SectionKind.CIRCLES, count: spec.circles.length, bytes: b });
  }

  if (spec.spheres && spec.spheres.length > 0) {
    const b = new Uint8Array(spec.spheres.length * 40);
    const dv = new DataView(b.buffer);
    spec.spheres.forEach((s, i) => {
      const o = i * 40;
      dv.setFloat32(o, s.center[0], true);
      dv.setFloat32(o + 4, s.center[1], true);
      dv.setFloat32(o + 8, s.center[2], true);
      dv.setFloat32(o + 12, s.radius, true);
      dv.setFloat32(o + 16, s.rgba[0], true);
      dv.setFloat32(o + 20, s.rgba[1], true);
      dv.setFloat32(o + 24, s.rgba[2], true);
      dv.setFloat32(o + 28, s.rgba[3], true);
      dv.setUint32(o + 32, s.flags >>> 0, true);
      dv.setUint32(o + 36, s.labelIdx >>> 0, true);
    });
    sections.push({ kind: SectionKind.SPHERES, count: spec.spheres.length, bytes: b });
  }

  if (spec.pointPairs && spec.pointPairs.length > 0) {
    const b = new Uint8Array(spec.pointPairs.length * 48);
    const dv = new DataView(b.buffer);
    spec.pointPairs.forEach((pp, i) => {
      const o = i * 48;
      dv.setFloat32(o, pp.p1[0], true);
      dv.setFloat32(o + 4, pp.p1[1], true);
      dv.setFloat32(o + 8, pp.p1[2], true);
      dv.setFloat32(o + 12, pp.p2[0], true);
      dv.setFloat32(o + 16, pp.p2[1], true);
      dv.setFloat32(o + 20, pp.p2[2], true);
      dv.setFloat32(o + 24, pp.radius, true);
      dv.setFloat32(o + 28, pp.rgba[0], true);
      dv.setFloat32(o + 32, pp.rgba[1], true);
      dv.setFloat32(o + 36, pp.rgba[2], true);
      dv.setFloat32(o + 40, pp.rgba[3], true);
      dv.setUint32(o + 44, pp.flags >>> 0, true);
    });
    sections.push({ kind: SectionKind.POINT_PAIRS, count: spec.pointPairs.length, bytes: b });
  }

  if (spec.bivectorDisks && spec.bivectorDisks.length > 0) {
    const b = new Uint8Array(spec.bivectorDisks.length * 60);
    const dv = new DataView(b.buffer);
    spec.bivectorDisks.forEach((bv, i) => {
      const o = i * 60;
      dv.setFloat32(o, bv.origin[0], true);
      dv.setFloat32(o + 4, bv.origin[1], true);
      dv.setFloat32(o + 8, bv.origin[2], true);
      dv.setFloat32(o + 12, bv.u[0], true);
      dv.setFloat32(o + 16, bv.u[1], true);
      dv.setFloat32(o + 20, bv.u[2], true);
      dv.setFloat32(o + 24, bv.v[0], true);
      dv.setFloat32(o + 28, bv.v[1], true);
      dv.setFloat32(o + 32, bv.v[2], true);
      dv.setFloat32(o + 36, bv.area, true);
      dv.setFloat32(o + 40, bv.rgba[0], true);
      dv.setFloat32(o + 44, bv.rgba[1], true);
      dv.setFloat32(o + 48, bv.rgba[2], true);
      dv.setFloat32(o + 52, bv.rgba[3], true);
      dv.setUint32(o + 56, bv.flags >>> 0, true);
    });
    sections.push({ kind: SectionKind.BIVECTOR_DISKS, count: spec.bivectorDisks.length, bytes: b });
  }

  if (spec.meshRefs && spec.meshRefs.length > 0) {
    const b = new Uint8Array(spec.meshRefs.length * 136);
    const dv = new DataView(b.buffer);
    spec.meshRefs.forEach((mr, i) => {
      const o = i * 136;
      dv.setBigUint64(o, mr.meshId, true);
      dv.setBigUint64(o + 8, mr.dirtyHash, true);
      for (let k = 0; k < 8; k++) dv.setFloat32(o + 16 + k * 4, mr.motor[k] ?? 0, true);
      for (let k = 0; k < 16; k++) dv.setFloat32(o + 48 + k * 4, mr.modelMat4[k] ?? 0, true);
      dv.setFloat32(o + 112, mr.rgba[0], true);
      dv.setFloat32(o + 116, mr.rgba[1], true);
      dv.setFloat32(o + 120, mr.rgba[2], true);
      dv.setFloat32(o + 124, mr.rgba[3], true);
      dv.setUint32(o + 128, mr.flags >>> 0, true);
      dv.setUint32(o + 132, 0, true);
    });
    sections.push({ kind: SectionKind.MESH_REFS, count: spec.meshRefs.length, bytes: b });
  }

  if (spec.meshAssets && spec.meshAssets.length > 0) {
    // Each mesh record is 8-byte aligned (4B zero pad when idxCount is odd per #17 Fix #1)
    let total = 0;
    const recordSizes = spec.meshAssets.map((m) => {
      const vertCount = Math.floor(m.positions.length / 3);
      const hasColors = m.colors !== null && m.colors.length > 0;
      const raw =
        32 +
        vertCount * 3 * 4 +
        vertCount * 3 * 4 +
        (hasColors ? vertCount * 4 * 4 : 0) +
        m.indices.length * 4;
      const padded = align8(raw);
      total += padded;
      return padded;
    });

    const b = new Uint8Array(total);
    const dv = new DataView(b.buffer);
    let cursor = 0;
    spec.meshAssets.forEach((m, idx) => {
      const vertCount = Math.floor(m.positions.length / 3);
      const idxCount = m.indices.length;
      const hasColors = m.colors !== null && m.colors.length > 0;
      const flags = (m.flags ?? 0) | (hasColors ? MeshAssetFlag.HAS_COLORS : 0);

      dv.setBigUint64(cursor, m.meshId, true);
      dv.setBigUint64(cursor + 8, m.dirtyHash, true);
      dv.setUint32(cursor + 16, vertCount, true);
      dv.setUint32(cursor + 20, idxCount, true);
      dv.setUint32(cursor + 24, flags >>> 0, true);
      dv.setUint32(cursor + 28, 0, true);
      let p = cursor + 32;

      new Float32Array(b.buffer, p, vertCount * 3).set(m.positions.subarray(0, vertCount * 3));
      p += vertCount * 3 * 4;

      new Float32Array(b.buffer, p, vertCount * 3).set(m.normals.subarray(0, vertCount * 3));
      p += vertCount * 3 * 4;

      if (hasColors && m.colors) {
        new Float32Array(b.buffer, p, vertCount * 4).set(m.colors.subarray(0, vertCount * 4));
        p += vertCount * 4 * 4;
      }

      new Uint32Array(b.buffer, p, idxCount).set(m.indices);
      cursor += recordSizes[idx]!;
    });

    sections.push({ kind: SectionKind.MESH_ASSETS, count: spec.meshAssets.length, bytes: b });
  }

  if (spec.curves && spec.curves.length > 0) {
    let total = 0;
    for (const c of spec.curves) total += 28 + c.xyz.length * 4;
    const b = new Uint8Array(total);
    const dv = new DataView(b.buffer);
    let cursor = 0;
    for (const c of spec.curves) {
      const ptCount = Math.floor(c.xyz.length / 3);
      dv.setUint32(cursor, ptCount, true);
      dv.setFloat32(cursor + 4, c.width, true);
      dv.setFloat32(cursor + 8, c.rgba[0], true);
      dv.setFloat32(cursor + 12, c.rgba[1], true);
      dv.setFloat32(cursor + 16, c.rgba[2], true);
      dv.setFloat32(cursor + 20, c.rgba[3], true);
      dv.setUint32(cursor + 24, c.flags >>> 0, true);
      cursor += 28;
      new Float32Array(b.buffer, cursor, ptCount * 3).set(c.xyz.subarray(0, ptCount * 3));
      cursor += ptCount * 3 * 4;
    }
    sections.push({ kind: SectionKind.CURVES, count: spec.curves.length, bytes: b });
  }

  if (spec.flowParticles && spec.flowParticles.length > 0) {
    let total = 0;
    for (const fp of spec.flowParticles) {
      const count = Math.floor(fp.starts.length / 3);
      total += 28 + count * 3 * 4 * 2;
    }
    const b = new Uint8Array(total);
    const dv = new DataView(b.buffer);
    let cursor = 0;
    for (const fp of spec.flowParticles) {
      const count = Math.floor(fp.starts.length / 3);
      dv.setUint32(cursor, count, true);
      dv.setFloat32(cursor + 4, fp.pointSize, true);
      dv.setFloat32(cursor + 8, fp.rgba[0], true);
      dv.setFloat32(cursor + 12, fp.rgba[1], true);
      dv.setFloat32(cursor + 16, fp.rgba[2], true);
      dv.setFloat32(cursor + 20, fp.rgba[3], true);
      dv.setFloat32(cursor + 24, fp.speed, true);
      cursor += 28;
      new Float32Array(b.buffer, cursor, count * 3).set(fp.starts.subarray(0, count * 3));
      cursor += count * 3 * 4;
      new Float32Array(b.buffer, cursor, count * 3).set(fp.ends.subarray(0, count * 3));
      cursor += count * 3 * 4;
    }
    sections.push({ kind: SectionKind.FLOW_PARTICLES, count: spec.flowParticles.length, bytes: b });
  }

  if (spec.labels && spec.labels.length > 0) {
    const b = new Uint8Array(spec.labels.length * 36);
    const dv = new DataView(b.buffer);
    spec.labels.forEach((lb, i) => {
      const o = i * 36;
      dv.setFloat32(o, lb.pos[0], true);
      dv.setFloat32(o + 4, lb.pos[1], true);
      dv.setFloat32(o + 8, lb.pos[2], true);
      dv.setFloat32(o + 12, lb.rgba[0], true);
      dv.setFloat32(o + 16, lb.rgba[1], true);
      dv.setFloat32(o + 20, lb.rgba[2], true);
      dv.setFloat32(o + 24, lb.rgba[3], true);
      dv.setUint32(o + 28, lb.textIdx >>> 0, true);
      dv.setUint32(o + 32, lb.flags >>> 0, true);
    });
    sections.push({ kind: SectionKind.LABELS, count: spec.labels.length, bytes: b });
  }

  if (spec.contourOverlay) {
    const co = spec.contourOverlay;
    let total = 24;
    for (const c of co.curves) total += 28 + Math.floor(c.xy.length / 2) * 2 * 4;
    total += co.intersections.length * 28;
    const b = new Uint8Array(total);
    const dv = new DataView(b.buffer);
    dv.setFloat32(0, co.minX, true);
    dv.setFloat32(4, co.maxX, true);
    dv.setFloat32(8, co.minY, true);
    dv.setFloat32(12, co.maxY, true);
    dv.setUint32(16, co.curves.length, true);
    dv.setUint32(20, co.intersections.length, true);
    let cursor = 24;
    for (const c of co.curves) {
      const ptCount = Math.floor(c.xy.length / 2);
      dv.setUint32(cursor, ptCount, true);
      dv.setFloat32(cursor + 4, c.rgba[0], true);
      dv.setFloat32(cursor + 8, c.rgba[1], true);
      dv.setFloat32(cursor + 12, c.rgba[2], true);
      dv.setFloat32(cursor + 16, c.rgba[3], true);
      dv.setFloat32(cursor + 20, c.width, true);
      dv.setUint32(cursor + 24, c.flags >>> 0, true);
      cursor += 28;
      new Float32Array(b.buffer, cursor, ptCount * 2).set(c.xy.subarray(0, ptCount * 2));
      cursor += ptCount * 2 * 4;
    }
    for (const pt of co.intersections) {
      dv.setFloat32(cursor, pt.x, true);
      dv.setFloat32(cursor + 4, pt.y, true);
      dv.setFloat32(cursor + 8, pt.rgba[0], true);
      dv.setFloat32(cursor + 12, pt.rgba[1], true);
      dv.setFloat32(cursor + 16, pt.rgba[2], true);
      dv.setFloat32(cursor + 20, pt.rgba[3], true);
      dv.setUint32(cursor + 24, pt.labelIdx >>> 0, true);
      cursor += 28;
    }
    sections.push({ kind: SectionKind.CONTOUR_OVERLAY, count: 1, bytes: b });
  }

  if (spec.opnsUniforms && spec.opnsUniforms.length > 0) {
    let total = 0;
    for (const u of spec.opnsUniforms) total += 44 + u.coeffs.length * 4;
    const b = new Uint8Array(total);
    const dv = new DataView(b.buffer);
    let cursor = 0;
    for (const u of spec.opnsUniforms) {
      dv.setUint32(cursor, u.shaderIdx >>> 0, true);
      dv.setUint32(cursor + 4, u.grade >>> 0, true);
      dv.setUint32(cursor + 8, u.coeffs.length >>> 0, true);
      dv.setFloat32(cursor + 12, u.thresh, true);
      dv.setUint32(cursor + 16, u.maxSteps >>> 0, true);
      dv.setFloat32(cursor + 20, u.stepSize, true);
      dv.setFloat32(cursor + 24, u.rgba[0], true);
      dv.setFloat32(cursor + 28, u.rgba[1], true);
      dv.setFloat32(cursor + 32, u.rgba[2], true);
      dv.setFloat32(cursor + 36, u.rgba[3], true);
      dv.setUint32(cursor + 40, u.flags >>> 0, true);
      cursor += 44;
      new Float32Array(b.buffer, cursor, u.coeffs.length).set(u.coeffs);
      cursor += u.coeffs.length * 4;
    }
    sections.push({ kind: SectionKind.OPNS_UNIFORMS, count: spec.opnsUniforms.length, bytes: b });
  }

  if (spec.inspectCoeffs && spec.inspectCoeffs.length > 0) {
    let total = 0;
    for (const ic of spec.inspectCoeffs) total += 12 + ic.coeffs.length * 4;
    const b = new Uint8Array(total);
    const dv = new DataView(b.buffer);
    let cursor = 0;
    for (const ic of spec.inspectCoeffs) {
      dv.setUint32(cursor, ic.entryIdx >>> 0, true);
      dv.setUint32(cursor + 4, ic.grade >>> 0, true);
      dv.setUint32(cursor + 8, ic.coeffs.length >>> 0, true);
      cursor += 12;
      new Float32Array(b.buffer, cursor, ic.coeffs.length).set(ic.coeffs);
      cursor += ic.coeffs.length * 4;
    }
    sections.push({ kind: SectionKind.INSPECT_COEFFS, count: spec.inspectCoeffs.length, bytes: b });
  }

  if (spec.extraSections) {
    for (const ex of spec.extraSections) {
      sections.push({ kind: ex.kind, count: ex.count, bytes: ex.data });
    }
  }

  // Compute 8-byte aligned layout (#17 Fix #1)
  const dirEnd = GSIR_HEADER_SIZE + sections.length * GSIR_DIR_ENTRY_SIZE;
  let offset = align8(dirEnd);
  const offsets: number[] = [];
  for (const sec of sections) {
    offset = align8(offset);
    offsets.push(offset);
    offset += sec.bytes.byteLength;
  }

  const metaBytes = spec.meta ? textEncoder.encode(JSON.stringify(spec.meta)) : new Uint8Array(0);
  const metaJsonOffset = metaBytes.byteLength > 0 ? align8(offset) : 0;
  const metaJsonLen = metaBytes.byteLength;
  const totalByteLen = metaBytes.byteLength > 0 ? align8(metaJsonOffset + metaJsonLen) : align8(offset);

  const out = new Uint8Array(totalByteLen);
  const dv = new DataView(out.buffer);

  // Header
  dv.setUint32(0, GSIR_MAGIC, true);
  dv.setUint16(4, GSIR_VERSION, true);
  dv.setUint16(6, (spec.flags ?? 0) & 0xffff, true);
  dv.setBigUint64(8, spec.frameSeq ?? 1n, true);
  dv.setFloat32(16, spec.simTime ?? 0, true);
  dv.setUint8(20, (spec.p ?? 3) & 0xff);
  dv.setUint8(21, (spec.q ?? 0) & 0xff);
  dv.setUint8(22, (spec.r ?? 1) & 0xff);
  dv.setUint8(23, (spec.modeKind ?? 0) & 0xff);
  dv.setFloat32(24, spec.gridSize ?? 5, true);
  dv.setUint32(28, sections.length, true);
  dv.setUint32(32, totalByteLen, true);
  dv.setUint32(36, metaJsonOffset, true);
  dv.setUint32(40, metaJsonLen, true);

  // Directory
  for (let i = 0; i < sections.length; i++) {
    const o = GSIR_HEADER_SIZE + i * GSIR_DIR_ENTRY_SIZE;
    dv.setUint32(o, sections[i]!.kind >>> 0, true);
    dv.setUint32(o + 4, sections[i]!.count >>> 0, true);
    dv.setUint32(o + 8, offsets[i]! >>> 0, true);
    dv.setUint32(o + 12, sections[i]!.bytes.byteLength >>> 0, true);
  }

  // Payloads
  for (let i = 0; i < sections.length; i++) {
    out.set(sections[i]!.bytes, offsets[i]!);
  }

  if (metaJsonLen > 0) {
    out.set(metaBytes, metaJsonOffset);
  }

  return out;
}

// Strict Zero-Copy Binary GSIR v1 Decoder
// Enforces 8-byte alignment for sections & 0x0B mesh records (#17 Fix #1),
// preserves handleId = 0 gated on draggable flag (#17 Fix #3),
// supports metaJsonLen = 0 unchanged delta & opnsShaders hash cache (#17 Fix #4),
// reads CAMERA.flags b0=isOrtho (#17 Fix #5), and safely skips unknown sections.

import {
  BivectorFlag,
  CameraFlag,
  CircleFlag,
  CurveFlag,
  GSIR_DIR_ENTRY_SIZE,
  GSIR_HEADER_SIZE,
  GSIR_MAGIC,
  GSIR_VERSION,
  LabelFlag,
  LineFlag,
  MeshAssetFlag,
  MeshRefFlag,
  ModeKindValue,
  OpnsFlag,
  PlaneFlag,
  PointFlag,
  PointPairFlag,
  SectionKind,
  SegmentFlag,
  SphereFlag,
  type GsirBivectorDisk,
  type GsirCamera,
  type GsirCircle,
  type GsirContourCurve,
  type GsirContourIntersection,
  type GsirContourOverlay,
  type GsirCurve,
  type GsirFlowParticles,
  type GsirFrame,
  type GsirHeader,
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
  type GsirSectionDirEntry,
  type GsirSegment,
  type GsirSphere,
  type OpnsShaderMeta,
} from './types';

export class GsirDecodeError extends Error {
  constructor(message: string) {
    super(`GSIR decode error: ${message}`);
    this.name = 'GsirDecodeError';
  }
}

const textDecoder = new TextDecoder('utf-8', { fatal: true });

function align8(offset: number): number {
  return (offset + 7) & ~7;
}

function nowUs(): number {
  return typeof performance !== 'undefined' ? performance.now() * 1000 : Date.now() * 1000;
}

/**
 * Ensures we have an ArrayBuffer and 8-byte aligned baseOffset so zero-copy
 * Float32Array / Uint32Array / BigUint64Array views never throw RangeError.
 */
function normalizeAlignedView(input: ArrayBuffer | Uint8Array): {
  buffer: ArrayBuffer;
  byteOffset: number;
  byteLength: number;
} {
  if (input instanceof ArrayBuffer) {
    return { buffer: input, byteOffset: 0, byteLength: input.byteLength };
  }
  if (input.byteOffset % 8 === 0 && input.buffer instanceof ArrayBuffer) {
    return {
      buffer: input.buffer,
      byteOffset: input.byteOffset,
      byteLength: input.byteLength,
    };
  }
  // Sub-slice was not 8-byte aligned (or backed by SharedArrayBuffer): copy once into aligned ArrayBuffer
  const copy = new Uint8Array(input.byteLength);
  copy.set(input);
  return { buffer: copy.buffer, byteOffset: 0, byteLength: copy.byteLength };
}

function assertBounds(offset: number, needed: number, limit: number, context: string): void {
  if (offset < 0 || needed < 0 || offset + needed > limit) {
    throw new GsirDecodeError(`${context} out of bounds (offset=${offset}, needed=${needed}, limit=${limit})`);
  }
}

export interface DecodeOptions {
  /** Require strict 8-byte section offsets (default true per #17 Fix #1) */
  strictAlignment?: boolean;
  /** Previous frame's metadata to reuse when metaJsonLen === 0 */
  previousMeta?: GsirMetaJson | null;
  /** Shader cache keyed by OpnsShaderMeta.hash to hydrate omitted bodies */
  shaderCache?: Map<string, OpnsShaderMeta>;
}

/**
 * Stateless single-frame decoder (accepts optional previousMeta + shaderCache for delta frames).
 */
export function decodeGsirFrame(input: ArrayBuffer | Uint8Array, options: DecodeOptions = {}): GsirFrame {
  const startUs = nowUs();
  const strictAlignment = options.strictAlignment ?? true;
  const { buffer, byteOffset: baseOffset, byteLength } = normalizeAlignedView(input);

  if (byteLength < GSIR_HEADER_SIZE) {
    throw new GsirDecodeError(`Frame too small for header (${byteLength} < ${GSIR_HEADER_SIZE})`);
  }

  const dv = new DataView(buffer, baseOffset, byteLength);

  // 1. Parse 64-byte fixed header
  const magic = dv.getUint32(0, true);
  if (magic !== GSIR_MAGIC) {
    throw new GsirDecodeError(`Invalid magic 0x${magic.toString(16)} (expected 0x${GSIR_MAGIC.toString(16)})`);
  }
  const version = dv.getUint16(4, true);
  if (version !== GSIR_VERSION) {
    throw new GsirDecodeError(`Unsupported GSIR version ${version} (expected ${GSIR_VERSION})`);
  }

  const flags = dv.getUint16(6, true);
  const frameSeq = dv.getBigUint64(8, true);
  const simTime = dv.getFloat32(16, true);
  const p = dv.getUint8(20);
  const q = dv.getUint8(21);
  const r = dv.getUint8(22);
  const modeKind = dv.getUint8(23) as ModeKindValue;
  const gridSize = dv.getFloat32(24, true);
  const sectionCount = dv.getUint32(28, true);
  const totalByteLen = dv.getUint32(32, true);
  const metaJsonOffset = dv.getUint32(36, true);
  const metaJsonLen = dv.getUint32(40, true);

  if (totalByteLen < GSIR_HEADER_SIZE || totalByteLen > byteLength) {
    throw new GsirDecodeError(`Invalid totalByteLen=${totalByteLen} for buffer length=${byteLength}`);
  }

  const header: GsirHeader = {
    magic,
    version,
    flags,
    frameSeq,
    simTime,
    p,
    q,
    r,
    modeKind,
    gridSize,
    sectionCount,
    totalByteLen,
    metaJsonOffset,
    metaJsonLen,
  };

  // 2. Parse Section Directory
  const dirByteLen = sectionCount * GSIR_DIR_ENTRY_SIZE;
  assertBounds(GSIR_HEADER_SIZE, dirByteLen, totalByteLen, 'section directory');

  const dir: GsirSectionDirEntry[] = new Array(sectionCount);
  for (let i = 0; i < sectionCount; i++) {
    const off = GSIR_HEADER_SIZE + i * GSIR_DIR_ENTRY_SIZE;
    const entry: GsirSectionDirEntry = {
      kind: dv.getUint32(off, true),
      count: dv.getUint32(off + 4, true),
      byteOffset: dv.getUint32(off + 8, true),
      byteLen: dv.getUint32(off + 12, true),
    };
    if (strictAlignment && entry.byteOffset % 8 !== 0) {
      throw new GsirDecodeError(
        `Section 0x${entry.kind.toString(16)} byteOffset=${entry.byteOffset} is not 8-byte aligned`
      );
    }
    assertBounds(entry.byteOffset, entry.byteLen, totalByteLen, `section 0x${entry.kind.toString(16)}`);
    dir[i] = entry;
  }

  // 3. Parse sections
  let camera: GsirCamera | null = null;
  const points: GsirPoint[] = [];
  const segments: GsirSegment[] = [];
  const lines: GsirLine[] = [];
  const planes: GsirPlane[] = [];
  const circles: GsirCircle[] = [];
  const spheres: GsirSphere[] = [];
  const pointPairs: GsirPointPair[] = [];
  const bivectorDisks: GsirBivectorDisk[] = [];
  const meshRefs: GsirMeshRef[] = [];
  const meshAssets: GsirMeshAsset[] = [];
  const curves: GsirCurve[] = [];
  const flowParticles: GsirFlowParticles[] = [];
  const labels: GsirLabel[] = [];
  let contourOverlay: GsirContourOverlay | null = null;
  const opnsUniforms: GsirOpnsUniform[] = [];
  const inspectCoeffs: GsirInspectCoeffs[] = [];
  const skippedSections: number[] = [];

  for (const sec of dir) {
    const start = sec.byteOffset;
    const end = sec.byteOffset + sec.byteLen;

    switch (sec.kind) {
      case SectionKind.CAMERA: {
        if (sec.count > 0) {
          assertBounds(start, 112, end, 'CAMERA');
          const motor = new Float32Array(buffer, baseOffset + start, 8);
          const viewMat4 = new Float32Array(buffer, baseOffset + start + 32, 16);
          const fovDeg = dv.getFloat32(start + 96, true);
          const distance = dv.getFloat32(start + 100, true);
          const orthoScale = dv.getFloat32(start + 104, true);
          const camFlags = dv.getUint32(start + 108, true);
          camera = {
            motor,
            viewMat4,
            fovDeg,
            distance,
            orthoScale,
            flags: camFlags,
            isOrtho: (camFlags & CameraFlag.IS_ORTHO) !== 0,
          };
        }
        break;
      }

      case SectionKind.POINTS: {
        const stride = 44;
        assertBounds(start, sec.count * stride, end, 'POINTS');
        for (let i = 0; i < sec.count; i++) {
          const o = start + i * stride;
          const handleId = dv.getUint32(o, true);
          const pFlags = dv.getUint32(o + 4, true);
          points.push({
            handleId,
            flags: pFlags,
            draggable: (pFlags & PointFlag.DRAGGABLE) !== 0,
            selected: (pFlags & PointFlag.SELECTED) !== 0,
            target: (pFlags & PointFlag.TARGET) !== 0,
            hint: (pFlags & PointFlag.HINT) !== 0,
            hollow: (pFlags & PointFlag.HOLLOW) !== 0,
            pos: [dv.getFloat32(o + 8, true), dv.getFloat32(o + 12, true), dv.getFloat32(o + 16, true)],
            radius: dv.getFloat32(o + 20, true),
            rgba: [
              dv.getFloat32(o + 24, true),
              dv.getFloat32(o + 28, true),
              dv.getFloat32(o + 32, true),
              dv.getFloat32(o + 36, true),
            ],
            labelIdx: dv.getUint32(o + 40, true),
          });
        }
        break;
      }

      case SectionKind.SEGMENTS: {
        const stride = 48;
        assertBounds(start, sec.count * stride, end, 'SEGMENTS');
        for (let i = 0; i < sec.count; i++) {
          const o = start + i * stride;
          const sFlags = dv.getUint32(o + 44, true);
          segments.push({
            a: [dv.getFloat32(o, true), dv.getFloat32(o + 4, true), dv.getFloat32(o + 8, true)],
            b: [dv.getFloat32(o + 12, true), dv.getFloat32(o + 16, true), dv.getFloat32(o + 20, true)],
            width: dv.getFloat32(o + 24, true),
            rgba: [
              dv.getFloat32(o + 28, true),
              dv.getFloat32(o + 32, true),
              dv.getFloat32(o + 36, true),
              dv.getFloat32(o + 40, true),
            ],
            flags: sFlags,
            handleId: sFlags >>> 16,
            dashed: (sFlags & SegmentFlag.DASHED) !== 0,
            arrow: (sFlags & SegmentFlag.ARROW) !== 0,
            draggable: (sFlags & SegmentFlag.DRAGGABLE) !== 0,
            selected: (sFlags & SegmentFlag.SELECTED) !== 0,
            target: (sFlags & SegmentFlag.TARGET) !== 0,
            hint: (sFlags & SegmentFlag.HINT) !== 0,
          });
        }
        break;
      }

      case SectionKind.LINES: {
        const stride = 52;
        assertBounds(start, sec.count * stride, end, 'LINES');
        for (let i = 0; i < sec.count; i++) {
          const o = start + i * stride;
          const lFlags = dv.getUint32(o + 48, true);
          lines.push({
            origin: [dv.getFloat32(o, true), dv.getFloat32(o + 4, true), dv.getFloat32(o + 8, true)],
            dir: [dv.getFloat32(o + 12, true), dv.getFloat32(o + 16, true), dv.getFloat32(o + 20, true)],
            clip: dv.getFloat32(o + 24, true),
            width: dv.getFloat32(o + 28, true),
            rgba: [
              dv.getFloat32(o + 32, true),
              dv.getFloat32(o + 36, true),
              dv.getFloat32(o + 40, true),
              dv.getFloat32(o + 44, true),
            ],
            flags: lFlags,
            handleId: lFlags >>> 16,
            dashed: (lFlags & LineFlag.DASHED) !== 0,
            draggable: (lFlags & LineFlag.DRAGGABLE) !== 0,
            selected: (lFlags & LineFlag.SELECTED) !== 0,
            target: (lFlags & LineFlag.TARGET) !== 0,
            hint: (lFlags & LineFlag.HINT) !== 0,
          });
        }
        break;
      }

      case SectionKind.PLANES: {
        const stride = 64;
        assertBounds(start, sec.count * stride, end, 'PLANES');
        for (let i = 0; i < sec.count; i++) {
          const o = start + i * stride;
          const pFlags = dv.getUint32(o + 56, true);
          planes.push({
            center: [dv.getFloat32(o, true), dv.getFloat32(o + 4, true), dv.getFloat32(o + 8, true)],
            u: [dv.getFloat32(o + 12, true), dv.getFloat32(o + 16, true), dv.getFloat32(o + 20, true)],
            v: [dv.getFloat32(o + 24, true), dv.getFloat32(o + 28, true), dv.getFloat32(o + 32, true)],
            extent: dv.getFloat32(o + 36, true),
            rgba: [
              dv.getFloat32(o + 40, true),
              dv.getFloat32(o + 44, true),
              dv.getFloat32(o + 48, true),
              dv.getFloat32(o + 52, true),
            ],
            flags: pFlags,
            handleId: pFlags >>> 16,
            gridLines: (pFlags & PlaneFlag.GRID_LINES) !== 0,
            draggable: (pFlags & PlaneFlag.DRAGGABLE) !== 0,
            selected: (pFlags & PlaneFlag.SELECTED) !== 0,
            target: (pFlags & PlaneFlag.TARGET) !== 0,
            hint: (pFlags & PlaneFlag.HINT) !== 0,
            labelIdx: dv.getUint32(o + 60, true),
          });
        }
        break;
      }

      case SectionKind.CIRCLES: {
        const stride = 68;
        assertBounds(start, sec.count * stride, end, 'CIRCLES');
        for (let i = 0; i < sec.count; i++) {
          const o = start + i * stride;
          const cFlags = dv.getUint32(o + 60, true);
          circles.push({
            center: [dv.getFloat32(o, true), dv.getFloat32(o + 4, true), dv.getFloat32(o + 8, true)],
            u: [dv.getFloat32(o + 12, true), dv.getFloat32(o + 16, true), dv.getFloat32(o + 20, true)],
            v: [dv.getFloat32(o + 24, true), dv.getFloat32(o + 28, true), dv.getFloat32(o + 32, true)],
            radius: dv.getFloat32(o + 36, true),
            width: dv.getFloat32(o + 40, true),
            rgba: [
              dv.getFloat32(o + 44, true),
              dv.getFloat32(o + 48, true),
              dv.getFloat32(o + 52, true),
              dv.getFloat32(o + 56, true),
            ],
            flags: cFlags,
            imaginary: (cFlags & CircleFlag.IMAGINARY) !== 0,
            labelIdx: dv.getUint32(o + 64, true),
          });
        }
        break;
      }

      case SectionKind.SPHERES: {
        const stride = 40;
        assertBounds(start, sec.count * stride, end, 'SPHERES');
        for (let i = 0; i < sec.count; i++) {
          const o = start + i * stride;
          const sFlags = dv.getUint32(o + 32, true);
          spheres.push({
            center: [dv.getFloat32(o, true), dv.getFloat32(o + 4, true), dv.getFloat32(o + 8, true)],
            radius: dv.getFloat32(o + 12, true),
            rgba: [
              dv.getFloat32(o + 16, true),
              dv.getFloat32(o + 20, true),
              dv.getFloat32(o + 24, true),
              dv.getFloat32(o + 28, true),
            ],
            flags: sFlags,
            imaginary: (sFlags & SphereFlag.IMAGINARY) !== 0,
            labelIdx: dv.getUint32(o + 36, true),
          });
        }
        break;
      }

      case SectionKind.POINT_PAIRS: {
        const stride = 48;
        assertBounds(start, sec.count * stride, end, 'POINT_PAIRS');
        for (let i = 0; i < sec.count; i++) {
          const o = start + i * stride;
          const ppFlags = dv.getUint32(o + 44, true);
          pointPairs.push({
            p1: [dv.getFloat32(o, true), dv.getFloat32(o + 4, true), dv.getFloat32(o + 8, true)],
            p2: [dv.getFloat32(o + 12, true), dv.getFloat32(o + 16, true), dv.getFloat32(o + 20, true)],
            radius: dv.getFloat32(o + 24, true),
            rgba: [
              dv.getFloat32(o + 28, true),
              dv.getFloat32(o + 32, true),
              dv.getFloat32(o + 36, true),
              dv.getFloat32(o + 40, true),
            ],
            flags: ppFlags,
            imaginary: (ppFlags & PointPairFlag.IMAGINARY) !== 0,
            showLink: (ppFlags & PointPairFlag.SHOW_LINK) !== 0,
          });
        }
        break;
      }

      case SectionKind.BIVECTOR_DISKS: {
        const stride = 60;
        assertBounds(start, sec.count * stride, end, 'BIVECTOR_DISKS');
        for (let i = 0; i < sec.count; i++) {
          const o = start + i * stride;
          const bFlags = dv.getUint32(o + 56, true);
          bivectorDisks.push({
            origin: [dv.getFloat32(o, true), dv.getFloat32(o + 4, true), dv.getFloat32(o + 8, true)],
            u: [dv.getFloat32(o + 12, true), dv.getFloat32(o + 16, true), dv.getFloat32(o + 20, true)],
            v: [dv.getFloat32(o + 24, true), dv.getFloat32(o + 28, true), dv.getFloat32(o + 32, true)],
            area: dv.getFloat32(o + 36, true),
            rgba: [
              dv.getFloat32(o + 40, true),
              dv.getFloat32(o + 44, true),
              dv.getFloat32(o + 48, true),
              dv.getFloat32(o + 52, true),
            ],
            flags: bFlags,
            isDisk: (bFlags & BivectorFlag.DISK) !== 0,
            orientationArrow: (bFlags & BivectorFlag.ORIENTATION_ARROW) !== 0,
          });
        }
        break;
      }

      case SectionKind.MESH_REFS: {
        const stride = 136; // 136 is a multiple of 8
        assertBounds(start, sec.count * stride, end, 'MESH_REFS');
        for (let i = 0; i < sec.count; i++) {
          const o = start + i * stride;
          const ids = new BigUint64Array(buffer, baseOffset + o, 2);
          const meshId = ids[0]!;
          const dirtyHash = ids[1]!;
          const motor = new Float32Array(buffer, baseOffset + o + 16, 8);
          const modelMat4 = new Float32Array(buffer, baseOffset + o + 48, 16);
          const rgba: [number, number, number, number] = [
            dv.getFloat32(o + 112, true),
            dv.getFloat32(o + 116, true),
            dv.getFloat32(o + 120, true),
            dv.getFloat32(o + 124, true),
          ];
          const mFlags = dv.getUint32(o + 128, true);
          meshRefs.push({
            meshId,
            dirtyHash,
            motor,
            modelMat4,
            rgba,
            flags: mFlags,
            wireframe: (mFlags & MeshRefFlag.WIREFRAME) !== 0,
            doubleSided: (mFlags & MeshRefFlag.DOUBLE_SIDED) !== 0,
            useVertexColors: (mFlags & MeshRefFlag.USE_VERTEX_COLORS) !== 0,
          });
        }
        break;
      }

      case SectionKind.MESH_ASSETS: {
        let cursor = start;
        for (let i = 0; i < sec.count; i++) {
          if (strictAlignment && cursor % 8 !== 0) {
            throw new GsirDecodeError(`MESH_ASSETS[${i}] offset=${cursor} is not 8-byte aligned`);
          }
          assertBounds(cursor, 32, end, `MESH_ASSETS[${i}] header`);
          const ids = new BigUint64Array(buffer, baseOffset + cursor, 2);
          const meshId = ids[0]!;
          const dirtyHash = ids[1]!;
          const vertCount = dv.getUint32(cursor + 16, true);
          const idxCount = dv.getUint32(cursor + 20, true);
          const mFlags = dv.getUint32(cursor + 24, true);
          const hasColors = (mFlags & MeshAssetFlag.HAS_COLORS) !== 0;
          cursor += 32;

          const posBytes = vertCount * 3 * 4;
          assertBounds(cursor, posBytes, end, `MESH_ASSETS[${i}] positions`);
          const positions = new Float32Array(buffer, baseOffset + cursor, vertCount * 3);
          cursor += posBytes;

          const normBytes = vertCount * 3 * 4;
          assertBounds(cursor, normBytes, end, `MESH_ASSETS[${i}] normals`);
          const normals = new Float32Array(buffer, baseOffset + cursor, vertCount * 3);
          cursor += normBytes;

          let colors: Float32Array | null = null;
          if (hasColors) {
            const colBytes = vertCount * 4 * 4;
            assertBounds(cursor, colBytes, end, `MESH_ASSETS[${i}] colors`);
            colors = new Float32Array(buffer, baseOffset + cursor, vertCount * 4);
            cursor += colBytes;
          }

          const idxBytes = idxCount * 4;
          assertBounds(cursor, idxBytes, end, `MESH_ASSETS[${i}] indices`);
          const indices = new Uint32Array(buffer, baseOffset + cursor, idxCount);
          cursor += idxBytes;

          // #17 Fix #1: Pad each MESH_ASSETS record to an 8-byte boundary (4B pad when idxCount is odd)
          const alignedCursor = align8(cursor);
          if (alignedCursor <= end) {
            cursor = alignedCursor;
          } else if (i < sec.count - 1) {
            throw new GsirDecodeError(
              `MESH_ASSETS[${i}] missing 8-byte tail alignment pad before next mesh (cursor=${cursor}, end=${end})`
            );
          }

          meshAssets.push({
            meshId,
            dirtyHash,
            vertCount,
            idxCount,
            flags: mFlags,
            hasColors,
            positions,
            normals,
            colors,
            indices,
          });
        }
        break;
      }

      case SectionKind.CURVES: {
        let cursor = start;
        for (let i = 0; i < sec.count; i++) {
          assertBounds(cursor, 28, end, `CURVES[${i}] header`);
          const ptCount = dv.getUint32(cursor, true);
          const width = dv.getFloat32(cursor + 4, true);
          const rgba: [number, number, number, number] = [
            dv.getFloat32(cursor + 8, true),
            dv.getFloat32(cursor + 12, true),
            dv.getFloat32(cursor + 16, true),
            dv.getFloat32(cursor + 20, true),
          ];
          const cFlags = dv.getUint32(cursor + 24, true);
          cursor += 28;
          const ptsBytes = ptCount * 3 * 4;
          assertBounds(cursor, ptsBytes, end, `CURVES[${i}] xyz`);
          const xyz = new Float32Array(buffer, baseOffset + cursor, ptCount * 3);
          cursor += ptsBytes;
          curves.push({
            ptCount,
            width,
            rgba,
            flags: cFlags,
            closed: (cFlags & CurveFlag.CLOSED) !== 0,
            dashed: (cFlags & CurveFlag.DASHED) !== 0,
            xyz,
          });
        }
        break;
      }

      case SectionKind.FLOW_PARTICLES: {
        let cursor = start;
        for (let i = 0; i < sec.count; i++) {
          assertBounds(cursor, 28, end, `FLOW_PARTICLES[${i}] header`);
          const particleCount = dv.getUint32(cursor, true);
          const pointSize = dv.getFloat32(cursor + 4, true);
          const rgba: [number, number, number, number] = [
            dv.getFloat32(cursor + 8, true),
            dv.getFloat32(cursor + 12, true),
            dv.getFloat32(cursor + 16, true),
            dv.getFloat32(cursor + 20, true),
          ];
          const speed = dv.getFloat32(cursor + 24, true);
          cursor += 28;
          const vecBytes = particleCount * 3 * 4;
          assertBounds(cursor, vecBytes * 2, end, `FLOW_PARTICLES[${i}] starts+ends`);
          const starts = new Float32Array(buffer, baseOffset + cursor, particleCount * 3);
          cursor += vecBytes;
          const ends = new Float32Array(buffer, baseOffset + cursor, particleCount * 3);
          cursor += vecBytes;
          flowParticles.push({ particleCount, pointSize, rgba, speed, starts, ends });
        }
        break;
      }

      case SectionKind.LABELS: {
        const stride = 36;
        assertBounds(start, sec.count * stride, end, 'LABELS');
        for (let i = 0; i < sec.count; i++) {
          const o = start + i * stride;
          const lFlags = dv.getUint32(o + 32, true);
          labels.push({
            pos: [dv.getFloat32(o, true), dv.getFloat32(o + 4, true), dv.getFloat32(o + 8, true)],
            rgba: [
              dv.getFloat32(o + 12, true),
              dv.getFloat32(o + 16, true),
              dv.getFloat32(o + 20, true),
              dv.getFloat32(o + 24, true),
            ],
            textIdx: dv.getUint32(o + 28, true),
            flags: lFlags,
            isLatex: (lFlags & LabelFlag.IS_LATEX) !== 0,
            billboard: (lFlags & LabelFlag.BILLBOARD) !== 0,
          });
        }
        break;
      }

      case SectionKind.CONTOUR_OVERLAY: {
        let cursor = start;
        assertBounds(cursor, 24, end, 'CONTOUR_OVERLAY header');
        const minX = dv.getFloat32(cursor, true);
        const maxX = dv.getFloat32(cursor + 4, true);
        const minY = dv.getFloat32(cursor + 8, true);
        const maxY = dv.getFloat32(cursor + 12, true);
        const curveCount = dv.getUint32(cursor + 16, true);
        const intersectionCount = dv.getUint32(cursor + 20, true);
        cursor += 24;

        const cCurves: GsirContourCurve[] = [];
        for (let i = 0; i < curveCount; i++) {
          assertBounds(cursor, 28, end, `CONTOUR_OVERLAY curve[${i}] header`);
          const ptCount = dv.getUint32(cursor, true);
          const rgba: [number, number, number, number] = [
            dv.getFloat32(cursor + 4, true),
            dv.getFloat32(cursor + 8, true),
            dv.getFloat32(cursor + 12, true),
            dv.getFloat32(cursor + 16, true),
          ];
          const width = dv.getFloat32(cursor + 20, true);
          const cFlags = dv.getUint32(cursor + 24, true);
          cursor += 28;
          const xyBytes = ptCount * 2 * 4;
          assertBounds(cursor, xyBytes, end, `CONTOUR_OVERLAY curve[${i}] xy`);
          const xy = new Float32Array(buffer, baseOffset + cursor, ptCount * 2);
          cursor += xyBytes;
          cCurves.push({ ptCount, rgba, width, flags: cFlags, xy });
        }

        const intersections: GsirContourIntersection[] = [];
        for (let i = 0; i < intersectionCount; i++) {
          assertBounds(cursor, 28, end, `CONTOUR_OVERLAY intersection[${i}]`);
          intersections.push({
            x: dv.getFloat32(cursor, true),
            y: dv.getFloat32(cursor + 4, true),
            rgba: [
              dv.getFloat32(cursor + 8, true),
              dv.getFloat32(cursor + 12, true),
              dv.getFloat32(cursor + 16, true),
              dv.getFloat32(cursor + 20, true),
            ],
            labelIdx: dv.getUint32(cursor + 24, true),
          });
          cursor += 28;
        }

        contourOverlay = { minX, maxX, minY, maxY, curves: cCurves, intersections };
        break;
      }

      case SectionKind.OPNS_UNIFORMS: {
        let cursor = start;
        for (let i = 0; i < sec.count; i++) {
          assertBounds(cursor, 44, end, `OPNS_UNIFORMS[${i}] header`);
          const shaderIdx = dv.getUint32(cursor, true);
          const grade = dv.getUint32(cursor + 4, true);
          const coeffCount = dv.getUint32(cursor + 8, true);
          const thresh = dv.getFloat32(cursor + 12, true);
          const maxSteps = dv.getUint32(cursor + 16, true);
          const stepSize = dv.getFloat32(cursor + 20, true);
          const rgba: [number, number, number, number] = [
            dv.getFloat32(cursor + 24, true),
            dv.getFloat32(cursor + 28, true),
            dv.getFloat32(cursor + 32, true),
            dv.getFloat32(cursor + 36, true),
          ];
          const oFlags = dv.getUint32(cursor + 40, true);
          cursor += 44;
          const coeffBytes = coeffCount * 4;
          assertBounds(cursor, coeffBytes, end, `OPNS_UNIFORMS[${i}] coeffs`);
          const coeffs = new Float32Array(buffer, baseOffset + cursor, coeffCount);
          cursor += coeffBytes;
          opnsUniforms.push({
            shaderIdx,
            grade,
            coeffCount,
            thresh,
            maxSteps,
            stepSize,
            rgba,
            flags: oFlags,
            isIPNS: (oFlags & OpnsFlag.IS_IPNS) !== 0,
            coeffs,
          });
        }
        break;
      }

      case SectionKind.INSPECT_COEFFS: {
        let cursor = start;
        for (let i = 0; i < sec.count; i++) {
          assertBounds(cursor, 12, end, `INSPECT_COEFFS[${i}] header`);
          const entryIdx = dv.getUint32(cursor, true);
          const grade = dv.getUint32(cursor + 4, true);
          const coeffCount = dv.getUint32(cursor + 8, true);
          cursor += 12;
          const coeffBytes = coeffCount * 4;
          assertBounds(cursor, coeffBytes, end, `INSPECT_COEFFS[${i}] coeffs`);
          const coeffs = new Float32Array(buffer, baseOffset + cursor, coeffCount);
          cursor += coeffBytes;
          inspectCoeffs.push({ entryIdx, grade, coeffCount, coeffs });
        }
        break;
      }

      default: {
        // Spec §2.2: Unknown section kinds MUST be safely skipped by clients.
        skippedSections.push(sec.kind);
        break;
      }
    }
  }

  // 4. Parse UTF-8 JSON metadata chunk (or reuse previous when metaJsonLen === 0 per #17 Fix #4)
  let meta: GsirMetaJson | null = null;
  let metaReused = false;
  if (metaJsonLen === 0) {
    meta = options.previousMeta ?? null;
    metaReused = meta !== null;
  } else {
    assertBounds(metaJsonOffset, metaJsonLen, totalByteLen, 'metaJson');
    const jsonBytes = new Uint8Array(buffer, baseOffset + metaJsonOffset, metaJsonLen);
    const jsonStr = textDecoder.decode(jsonBytes);
    try {
      meta = JSON.parse(jsonStr) as GsirMetaJson;
    } catch (err) {
      throw new GsirDecodeError(`Invalid metaJson UTF-8 JSON: ${(err as Error).message}`);
    }

    // Hydrate / update opnsShaders hash cache (#17 Fix #4)
    if (options.shaderCache && meta.opnsShaders) {
      meta.opnsShaders = meta.opnsShaders.map((shader) => {
        const existing = options.shaderCache!.get(shader.hash);
        const merged: OpnsShaderMeta = {
          hash: shader.hash,
          glsl: shader.glsl || existing?.glsl,
          wgsl: shader.wgsl || existing?.wgsl,
          msl: shader.msl || existing?.msl,
        };
        options.shaderCache!.set(shader.hash, merged);
        return merged;
      });
    }
  }

  const decodeTimeUs = Math.max(0, nowUs() - startUs);

  return {
    header,
    camera,
    points,
    segments,
    lines,
    planes,
    circles,
    spheres,
    pointPairs,
    bivectorDisks,
    meshRefs,
    meshAssets,
    curves,
    flowParticles,
    labels,
    contourOverlay,
    opnsUniforms,
    inspectCoeffs,
    meta,
    metaReused,
    skippedSections,
    decodeTimeUs,
  };
}

/**
 * Stateful session decoder that caches:
 * - Mesh assets by meshId + dirtyHash (preventing redundant GPU buffer uploads)
 * - Previous metaJson for zero-alloc metaJsonLen === 0 frames
 * - opnsShaders bodies keyed by hash
 */
export class GsirSessionDecoder {
  private lastMeta: GsirMetaJson | null = null;
  private readonly meshCache = new Map<bigint, GsirMeshAsset>();
  private readonly shaderCache = new Map<string, OpnsShaderMeta>();

  decode(input: ArrayBuffer | Uint8Array, strictAlignment = true): GsirFrame {
    const frame = decodeGsirFrame(input, {
      strictAlignment,
      previousMeta: this.lastMeta,
      shaderCache: this.shaderCache,
    });

    if (!frame.metaReused && frame.meta !== null) {
      this.lastMeta = frame.meta;
    }

    // Update persistent mesh asset cache on new or changed dirtyHash.
    // Note: clone typed arrays when storing across frames so caller's reusable WASM buffer can be overwritten safely.
    for (const asset of frame.meshAssets) {
      const prev = this.meshCache.get(asset.meshId);
      if (!prev || prev.dirtyHash !== asset.dirtyHash) {
        this.meshCache.set(asset.meshId, {
          ...asset,
          positions: new Float32Array(asset.positions),
          normals: new Float32Array(asset.normals),
          colors: asset.colors ? new Float32Array(asset.colors) : null,
          indices: new Uint32Array(asset.indices),
        });
      }
    }

    return frame;
  }

  getCachedMesh(meshId: bigint): GsirMeshAsset | undefined {
    return this.meshCache.get(meshId);
  }

  getCachedMeshCount(): number {
    return this.meshCache.size;
  }

  getCachedShader(hash: string): OpnsShaderMeta | undefined {
    return this.shaderCache.get(hash);
  }

  getCachedShaderCount(): number {
    return this.shaderCache.size;
  }

  reset(): void {
    this.lastMeta = null;
    this.meshCache.clear();
    this.shaderCache.clear();
  }
}

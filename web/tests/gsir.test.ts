import { describe, expect, it } from 'vitest';
import {
  CameraFlag,
  GSIR_MAGIC,
  GSIR_NO_LABEL,
  GSIR_VERSION,
  GsirDecodeError,
  GsirSessionDecoder,
  HeaderFlag,
  InputEventFlag,
  InputEventKind,
  ModeKind,
  PointFlag,
  SectionKind,
  WedgeActionCode,
  WedgeGestureFlag,
  buildAllSectionsFixtureBytes,
  buildOrthoDeltaFixtureBytes,
  decodeGsirFrame,
  encodeBinaryInputEvent,
  encodeDragHandle,
  encodeEditCoeff,
  encodeGsirFrame,
  encodeSetCamera,
  encodeSlicePlane,
  encodeTick,
  encodeWedgeAction,
  encodeWedgeGesture,
} from '../src/gsir';

describe('GSIR v1 Binary Wire Protocol', () => {
  it('round-trips all 17 sections (0x01..0x11) with zero-copy typed-array views', () => {
    const bytes = buildAllSectionsFixtureBytes();
    const frame = decodeGsirFrame(bytes);

    expect(frame.header.magic).toBe(GSIR_MAGIC);
    expect(frame.header.version).toBe(GSIR_VERSION);
    expect(frame.header.frameSeq).toBe(42n);
    expect(frame.header.simTime).toBeCloseTo(1.5, 5);
    expect(frame.header.p).toBe(3);
    expect(frame.header.q).toBe(0);
    expect(frame.header.r).toBe(1);
    expect(frame.header.modeKind).toBe(ModeKind.CoffeeShop);
    expect(frame.header.gridSize).toBeCloseTo(6.0, 5);
    expect(frame.header.totalByteLen).toBe(bytes.byteLength);

    // 0x01 CAMERA
    expect(frame.camera).not.toBeNull();
    expect(frame.camera!.fovDeg).toBeCloseTo(45, 5);
    expect(frame.camera!.distance).toBeCloseTo(5.5, 5);
    expect(frame.camera!.orthoScale).toBeCloseTo(3.0, 5);
    expect(frame.camera!.isOrtho).toBe(false);
    expect(frame.camera!.motor.buffer).toBe(bytes.buffer);
    expect(frame.camera!.viewMat4.buffer).toBe(bytes.buffer);

    // 0x02 POINTS (verifies handleId = 0 is valid and draggable gated by flag bit0!)
    expect(frame.points).toHaveLength(3);
    expect(frame.points[0]!.handleId).toBe(0);
    expect(frame.points[0]!.draggable).toBe(true);
    expect(frame.points[0]!.selected).toBe(true);
    expect(frame.points[0]!.pos[0]).toBeCloseTo(-1.2, 5);
    expect(frame.points[2]!.target).toBe(true);
    expect(frame.points[2]!.hollow).toBe(true);
    expect(frame.points[2]!.draggable).toBe(false);
    expect(frame.points[2]!.labelIdx).toBe(GSIR_NO_LABEL);

    // 0x03 SEGMENTS, 0x04 LINES, 0x05 PLANES
    expect(frame.segments).toHaveLength(2);
    expect(frame.segments[0]!.arrow).toBe(true);
    expect(frame.segments[0]!.handleId).toBe(10);
    expect(frame.segments[1]!.dashed).toBe(true);
    expect(frame.segments[1]!.hint).toBe(true);

    expect(frame.lines).toHaveLength(1);
    expect(frame.lines[0]!.handleId).toBe(20);
    expect(frame.lines[0]!.draggable).toBe(true);
    expect(frame.lines[0]!.clip).toBeCloseTo(4.0, 5);

    expect(frame.planes).toHaveLength(1);
    expect(frame.planes[0]!.handleId).toBe(30);
    expect(frame.planes[0]!.gridLines).toBe(true);
    expect(frame.planes[0]!.draggable).toBe(true);
    expect(frame.planes[0]!.labelIdx).toBe(2);

    // 0x06 CIRCLES, 0x07 SPHERES, 0x08 POINT_PAIRS, 0x09 BIVECTOR_DISKS
    expect(frame.circles).toHaveLength(2);
    expect(frame.circles[0]!.imaginary).toBe(false);
    expect(frame.circles[1]!.imaginary).toBe(true);

    expect(frame.spheres).toHaveLength(2);
    expect(frame.spheres[0]!.imaginary).toBe(false);
    expect(frame.spheres[1]!.imaginary).toBe(true);

    expect(frame.pointPairs).toHaveLength(1);
    expect(frame.pointPairs[0]!.showLink).toBe(true);

    expect(frame.bivectorDisks).toHaveLength(2);
    expect(frame.bivectorDisks[0]!.isDisk).toBe(false);
    expect(frame.bivectorDisks[0]!.orientationArrow).toBe(true);
    expect(frame.bivectorDisks[1]!.isDisk).toBe(true);

    // 0x0A MESH_REFS & 0x0B MESH_ASSETS (including odd idxCount = 3 followed by second mesh!)
    expect(frame.meshRefs).toHaveLength(2);
    expect(frame.meshRefs[0]!.meshId).toBe(101n);
    expect(frame.meshRefs[0]!.dirtyHash).toBe(0xabc123n);
    expect(frame.meshRefs[0]!.useVertexColors).toBe(true);
    expect(frame.meshRefs[1]!.wireframe).toBe(true);

    expect(frame.meshAssets).toHaveLength(2);
    expect(frame.meshAssets[0]!.meshId).toBe(101n);
    expect(frame.meshAssets[0]!.idxCount).toBe(3); // odd idxCount
    expect(frame.meshAssets[0]!.hasColors).toBe(true);
    expect(frame.meshAssets[0]!.positions.buffer).toBe(bytes.buffer); // zero-copy!
    expect(frame.meshAssets[0]!.indices.buffer).toBe(bytes.buffer); // zero-copy!
    expect(Array.from(frame.meshAssets[0]!.indices)).toEqual([0, 1, 2]);
    // Second mesh immediately after odd idxCount MUST decode cleanly on 8-byte boundary!
    expect(frame.meshAssets[1]!.meshId).toBe(102n);
    expect(frame.meshAssets[1]!.dirtyHash).toBe(0xdef456n);
    expect(frame.meshAssets[1]!.hasColors).toBe(false);
    expect(frame.meshAssets[1]!.colors).toBeNull();
    expect(Array.from(frame.meshAssets[1]!.indices)).toEqual([0, 1, 2, 0, 2, 3]);

    // 0x0C CURVES, 0x0D FLOW_PARTICLES, 0x0E LABELS
    expect(frame.curves).toHaveLength(1);
    expect(frame.curves[0]!.closed).toBe(true);
    expect(frame.curves[0]!.ptCount).toBe(4);
    expect(frame.curves[0]!.xyz.buffer).toBe(bytes.buffer);

    expect(frame.flowParticles).toHaveLength(1);
    expect(frame.flowParticles[0]!.particleCount).toBe(3);
    expect(frame.flowParticles[0]!.starts.buffer).toBe(bytes.buffer);
    expect(frame.flowParticles[0]!.ends.buffer).toBe(bytes.buffer);

    expect(frame.labels).toHaveLength(1);
    expect(frame.labels[0]!.isLatex).toBe(true);
    expect(frame.labels[0]!.billboard).toBe(true);

    // 0x0F CONTOUR_OVERLAY
    expect(frame.contourOverlay).not.toBeNull();
    expect(frame.contourOverlay!.curves).toHaveLength(2);
    expect(frame.contourOverlay!.intersections).toHaveLength(2);
    expect(frame.contourOverlay!.intersections[0]!.x).toBeCloseTo(0.6, 5);

    // 0x10 OPNS_UNIFORMS & 0x11 INSPECT_COEFFS
    expect(frame.opnsUniforms).toHaveLength(1);
    expect(frame.opnsUniforms[0]!.isIPNS).toBe(true);
    expect(frame.opnsUniforms[0]!.coeffs.length).toBe(8);
    expect(frame.opnsUniforms[0]!.coeffs[4]).toBeCloseTo(0.5, 5);

    expect(frame.inspectCoeffs).toHaveLength(1);
    expect(frame.inspectCoeffs[0]!.entryIdx).toBe(0);
    expect(frame.inspectCoeffs[0]!.coeffs[1]).toBeCloseTo(0.5, 5);

    // metaJson
    expect(frame.metaReused).toBe(false);
    expect(frame.meta?.algebra?.name).toBe('PGA3');
    expect(frame.meta?.opnsShaders?.[0]?.hash).toBe('fixture_opns_v1');
  });

  it('enforces 8-byte alignment for every section offset (#17 Fix #1)', () => {
    const bytes = buildAllSectionsFixtureBytes();
    const dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
    const sectionCount = dv.getUint32(28, true);
    expect(sectionCount).toBe(17);
    for (let i = 0; i < sectionCount; i++) {
      const byteOffset = dv.getUint32(64 + i * 16 + 8, true);
      expect(byteOffset % 8).toBe(0);
    }

    // Corrupt a section offset to be only 4-byte aligned and confirm strict decoder rejects it
    const bad = new Uint8Array(bytes);
    const badDv = new DataView(bad.buffer);
    const origOff = badDv.getUint32(64 + 8, true);
    badDv.setUint32(64 + 8, origOff + 4, true);
    expect(() => decodeGsirFrame(bad, { strictAlignment: true })).toThrow(GsirDecodeError);
  });

  it('handles unaligned input Uint8Array subviews cleanly without RangeError', () => {
    const bytes = buildAllSectionsFixtureBytes();
    const padded = new Uint8Array(bytes.byteLength + 5);
    padded.set(bytes, 3); // byteOffset = 3 (not 8-byte aligned!)
    const unalignedView = padded.subarray(3, 3 + bytes.byteLength);
    expect(unalignedView.byteOffset % 8).toBe(3);

    const frame = decodeGsirFrame(unalignedView);
    expect(frame.header.frameSeq).toBe(42n);
    expect(frame.meshAssets).toHaveLength(2);
    expect(frame.meshAssets[1]!.meshId).toBe(102n);
  });

  it('supports metaJsonLen = 0 delta reuse, opnsShaders hash cache, and CAMERA.isOrtho (#17 Fixes #4 & #5)', () => {
    const session = new GsirSessionDecoder();

    // Frame 1: full snapshot with opnsShader GLSL body + mesh assets
    const f1 = session.decode(buildAllSectionsFixtureBytes());
    expect(f1.metaReused).toBe(false);
    expect(f1.meta?.opnsShaders?.[0]?.glsl).toContain('gl_FragColor');
    expect(session.getCachedMeshCount()).toBe(2);
    expect(session.getCachedShaderCount()).toBe(1);

    // Frame 2: metaJsonLen = 0 delta frame + CAMERA.flags b0=isOrtho
    const f2 = session.decode(buildOrthoDeltaFixtureBytes(43n));
    expect(f2.header.metaJsonLen).toBe(0);
    expect(f2.metaReused).toBe(true);
    expect(f2.meta?.algebra?.name).toBe('PGA3'); // reused from f1!
    expect(f2.camera?.isOrtho).toBe(true);
    expect((f2.camera?.flags ?? 0) & CameraFlag.IS_ORTHO).toBe(CameraFlag.IS_ORTHO);
    // Mesh assets from Frame 1 stay cached!
    expect(session.getCachedMesh(101n)?.dirtyHash).toBe(0xabc123n);
    expect(session.getCachedMesh(102n)?.dirtyHash).toBe(0xdef456n);

    // Frame 3: new metaJson omitting opnsShader GLSL body (hash-only delta) -> hydrated from shader cache!
    const f3Bytes = encodeGsirFrame({
      frameSeq: 44n,
      meta: {
        version: 1,
        presetId: 'opns_delta',
        opnsShaders: [{ hash: 'fixture_opns_v1' }],
      },
    });
    const f3 = session.decode(f3Bytes);
    expect(f3.metaReused).toBe(false);
    expect(f3.meta?.opnsShaders?.[0]?.hash).toBe('fixture_opns_v1');
    expect(f3.meta?.opnsShaders?.[0]?.glsl).toContain('gl_FragColor');
  });

  it('safely skips unknown section kinds without failing decode', () => {
    const frameBytes = encodeGsirFrame({
      frameSeq: 99n,
      points: [
        {
          handleId: 0,
          flags: PointFlag.DRAGGABLE,
          pos: [1, 2, 3],
          radius: 0.1,
          rgba: [1, 1, 1, 1],
          labelIdx: GSIR_NO_LABEL,
        },
      ],
      extraSections: [
        { kind: 0xfe, count: 2, data: new Uint8Array(24) },
        { kind: 0xff, count: 1, data: new Uint8Array(16) },
      ],
      meta: { version: 1, title: 'Future Extension' },
    });

    const decoded = decodeGsirFrame(frameBytes);
    expect(decoded.points).toHaveLength(1);
    expect(decoded.skippedSections).toEqual([0xfe, 0xff]);
    expect(decoded.meta?.title).toBe('Future Extension');
  });

  it('rejects bad magic, bad version, and truncated frames with GsirDecodeError', () => {
    const bytes = buildAllSectionsFixtureBytes();

    const badMagic = new Uint8Array(bytes);
    badMagic[0] = 0x00;
    expect(() => decodeGsirFrame(badMagic)).toThrow(GsirDecodeError);

    const badVersion = new Uint8Array(bytes);
    new DataView(badVersion.buffer).setUint16(4, 2, true);
    expect(() => decodeGsirFrame(badVersion)).toThrow(GsirDecodeError);

    const truncated = bytes.subarray(0, 32);
    expect(() => decodeGsirFrame(truncated)).toThrow(GsirDecodeError);
  });

  it('updates cached mesh ONLY when dirtyHash changes', () => {
    const session = new GsirSessionDecoder();
    const f1 = encodeGsirFrame({
      frameSeq: 1n,
      meshAssets: [
        {
          meshId: 7n,
          dirtyHash: 100n,
          positions: new Float32Array([0, 0, 0, 1, 0, 0, 0, 1, 0]),
          normals: new Float32Array([0, 0, 1, 0, 0, 1, 0, 0, 1]),
          colors: null,
          indices: new Uint32Array([0, 1, 2]),
        },
      ],
    });
    session.decode(f1);
    const cached1 = session.getCachedMesh(7n)!;
    expect(cached1.positions[3]).toBe(1);

    // Same dirtyHash -> cached object reference stays unchanged
    const f2 = encodeGsirFrame({
      frameSeq: 2n,
      meshAssets: [
        {
          meshId: 7n,
          dirtyHash: 100n,
          positions: new Float32Array([0, 0, 0, 9, 0, 0, 0, 1, 0]),
          normals: new Float32Array([0, 0, 1, 0, 0, 1, 0, 0, 1]),
          colors: null,
          indices: new Uint32Array([0, 1, 2]),
        },
      ],
    });
    session.decode(f2);
    expect(session.getCachedMesh(7n)).toBe(cached1);

    // New dirtyHash -> mesh replaced
    const f3 = encodeGsirFrame({
      frameSeq: 3n,
      meshAssets: [
        {
          meshId: 7n,
          dirtyHash: 101n,
          positions: new Float32Array([0, 0, 0, 5, 0, 0, 0, 1, 0]),
          normals: new Float32Array([0, 0, 1, 0, 0, 1, 0, 0, 1]),
          colors: null,
          indices: new Uint32Array([0, 1, 2]),
        },
      ],
    });
    session.decode(f3);
    expect(session.getCachedMesh(7n)).not.toBe(cached1);
    expect(session.getCachedMesh(7n)!.positions[3]).toBe(5);
  });
});

describe('GSIR Binary InputEvent Encoders', () => {
  it('encodes DragHandle (0x01) including handleId = 0 and forceFullSnapshot', () => {
    const buf = encodeDragHandle(0, 1.25, -2.5, 3.75, true);
    expect(buf.byteLength).toBe(20);
    const dv = new DataView(buf.buffer);
    expect(dv.getUint8(0)).toBe(InputEventKind.DRAG_HANDLE);
    expect(dv.getUint8(1)).toBe(InputEventFlag.FORCE_FULL_SNAPSHOT);
    expect(dv.getUint16(2, true)).toBe(16);
    expect(dv.getUint32(4, true)).toBe(0);
    expect(dv.getFloat32(8, true)).toBeCloseTo(1.25, 6);
    expect(dv.getFloat32(12, true)).toBeCloseTo(-2.5, 6);
    expect(dv.getFloat32(16, true)).toBeCloseTo(3.75, 6);
  });

  it('encodes Tick (0x02), EditCoeff (0x04), WedgeAction (0x07), SetCamera (0x09), SlicePlane (0x0A)', () => {
    const tick = encodeTick(0.016, 12.5);
    expect(tick.byteLength).toBe(12);
    expect(new DataView(tick.buffer).getUint8(0)).toBe(InputEventKind.TICK);
    expect(new DataView(tick.buffer).getFloat32(4, true)).toBeCloseTo(0.016, 5);
    expect(new DataView(tick.buffer).getFloat32(8, true)).toBeCloseTo(12.5, 5);

    const edit = encodeEditCoeff(2, 5, -0.75);
    expect(edit.byteLength).toBe(16);
    expect(new DataView(edit.buffer).getUint32(4, true)).toBe(2);
    expect(new DataView(edit.buffer).getUint32(8, true)).toBe(5);
    expect(new DataView(edit.buffer).getFloat32(12, true)).toBeCloseTo(-0.75, 6);

    const act = encodeWedgeAction(WedgeActionCode.GOTO_LEVEL, 12);
    expect(act.byteLength).toBe(12);
    expect(new DataView(act.buffer).getUint8(4)).toBe(WedgeActionCode.GOTO_LEVEL);
    expect(new DataView(act.buffer).getUint32(8, true)).toBe(12);

    const cam = encodeSetCamera([1, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7], 50, 6.5);
    expect(cam.byteLength).toBe(44);
    expect(new DataView(cam.buffer).getFloat32(36, true)).toBeCloseTo(50, 5);
    expect(new DataView(cam.buffer).getFloat32(40, true)).toBeCloseTo(6.5, 5);

    const slice = encodeSlicePlane([1, 0, 0.5, 0, 0, 0, 0, 0]);
    expect(slice.byteLength).toBe(36);
    expect(new DataView(slice.buffer).getUint8(0)).toBe(InputEventKind.SLICE_PLANE);
    expect(new DataView(slice.buffer).getFloat32(12, true)).toBeCloseTo(0.5, 5);
  });

  it('encodes WedgeGesture (0x06) with isPreview flag bit0 and raw drag vectors (#17 Fix #3)', () => {
    const preview = encodeWedgeGesture(0, 1, [0.4, -0.2, 0.1], [-0.5, 0.3, 0.0], true);
    expect(preview.byteLength).toBe(40);
    const dv = new DataView(preview.buffer);
    expect(dv.getUint8(0)).toBe(InputEventKind.WEDGE_GESTURE);
    expect(dv.getUint16(2, true)).toBe(36);
    expect(dv.getUint32(4, true)).toBe(0);
    expect(dv.getUint32(8, true)).toBe(1);
    expect(dv.getFloat32(12, true)).toBeCloseTo(0.4, 5);
    expect(dv.getFloat32(24, true)).toBeCloseTo(-0.5, 5);
    expect(dv.getUint8(36)).toBe(0); // holdA = 0 (Lean derives hold)
    expect(dv.getUint8(37)).toBe(0); // holdB = 0 (Lean derives hold)
    expect(dv.getUint16(38, true)).toBe(WedgeGestureFlag.IS_PREVIEW);

    const commit = encodeBinaryInputEvent({
      kind: InputEventKind.WEDGE_GESTURE,
      idA: 3,
      idB: 4,
      dirA: [0, 0, 0],
      dirB: [1, 0, 0],
      isPreview: false,
    });
    expect(new DataView(commit.buffer).getUint16(38, true)).toBe(0);
  });
});

// Sanity check enum values match SCENE_IR_V1.md table exactly
describe('GSIR Spec Constants', () => {
  it('matches SectionKind hex IDs from SCENE_IR_V1.md', () => {
    expect(SectionKind.CAMERA).toBe(0x01);
    expect(SectionKind.POINTS).toBe(0x02);
    expect(SectionKind.SEGMENTS).toBe(0x03);
    expect(SectionKind.LINES).toBe(0x04);
    expect(SectionKind.PLANES).toBe(0x05);
    expect(SectionKind.CIRCLES).toBe(0x06);
    expect(SectionKind.SPHERES).toBe(0x07);
    expect(SectionKind.POINT_PAIRS).toBe(0x08);
    expect(SectionKind.BIVECTOR_DISKS).toBe(0x09);
    expect(SectionKind.MESH_REFS).toBe(0x0a);
    expect(SectionKind.MESH_ASSETS).toBe(0x0b);
    expect(SectionKind.CURVES).toBe(0x0c);
    expect(SectionKind.FLOW_PARTICLES).toBe(0x0d);
    expect(SectionKind.LABELS).toBe(0x0e);
    expect(SectionKind.CONTOUR_OVERLAY).toBe(0x0f);
    expect(SectionKind.OPNS_UNIFORMS).toBe(0x10);
    expect(SectionKind.INSPECT_COEFFS).toBe(0x11);
    expect(HeaderFlag.HAS_OPNS_SHADER).toBe(1 << 6);
  });
});

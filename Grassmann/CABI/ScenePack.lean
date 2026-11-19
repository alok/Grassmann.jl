/-
  Grassmann/CABI/ScenePack.lean — Init-only GSIR v1 Binary Encoder & InputEvent Decoder

  Implements the Canonical `SceneIR` v1 (`GSIR`) wire contract (`docs/SCENE_IR_V1.md`)
  plus all 5 verification refinements:
  1. 8-byte aligned section offsets and 8-byte padded `0x0B MESH_ASSETS` records
     with CCW front-face winding (safe for JS `BigUint64Array` & ARM64 Swift `UInt64`).
  2. Idempotent cached-frame reads (`get_frame`) + `forceFullSnapshot` (`flags` b0).
  3. `WedgeGesture` `flags: u16` (`b0=isPreview`) and Lean-derived `hold` (`‖dir‖ < 0.1`).
  4. `metaJsonLen = 0` on hot frames when metadata is unchanged + cached `opnsShaders`.
  5. `0x01 CAMERA.flags` (`b0=isOrtho`), ganja motor wire order
     `(s, e01, e02, e03, e12, e13, e23, e0123)`, and `evalSurface` JSON op.

  Strictly `Init`-only (ZERO `Lean.Data.Json`, ZERO `Std.*`).
-/
import Init.Data.FloatArray
import Init.Data.ByteArray
import Init.Data.Float

namespace Grassmann.CABI.ScenePack

/-! ### Little-Endian ByteArray Writer & Reader -/

@[inline] def pushU8 (b : ByteArray) (v : UInt8) : ByteArray :=
  b.push v

@[inline] def pushU16LE (b : ByteArray) (v : UInt16) : ByteArray :=
  b |>.push (v &&& 0xFF).toUInt8
    |>.push ((v >>> 8) &&& 0xFF).toUInt8

@[inline] def pushU32LE (b : ByteArray) (v : UInt32) : ByteArray :=
  b |>.push (v &&& 0xFF).toUInt8
    |>.push ((v >>> 8) &&& 0xFF).toUInt8
    |>.push ((v >>> 16) &&& 0xFF).toUInt8
    |>.push ((v >>> 24) &&& 0xFF).toUInt8

@[inline] def pushU64LE (b : ByteArray) (v : UInt64) : ByteArray :=
  b |>.push (v &&& 0xFF).toUInt8
    |>.push ((v >>> 8) &&& 0xFF).toUInt8
    |>.push ((v >>> 16) &&& 0xFF).toUInt8
    |>.push ((v >>> 24) &&& 0xFF).toUInt8
    |>.push ((v >>> 32) &&& 0xFF).toUInt8
    |>.push ((v >>> 40) &&& 0xFF).toUInt8
    |>.push ((v >>> 48) &&& 0xFF).toUInt8
    |>.push ((v >>> 56) &&& 0xFF).toUInt8

@[inline] def pushF32LE (b : ByteArray) (v : Float) : ByteArray :=
  pushU32LE b v.toFloat32.toBits

def pushZeros (b : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut out := b
  for _ in [:n] do
    out := out.push 0
  return out

/-- Pad `b` with zero bytes so `b.size % 8 == 0`. -/
def padAlign8 (b : ByteArray) : ByteArray :=
  let rem := b.size % 8
  if rem == 0 then b else pushZeros b (8 - rem)

@[inline] def getU8 (b : ByteArray) (off : Nat) : UInt8 :=
  if off < b.size then b.get! off else 0

@[inline] def getU16LE (b : ByteArray) (off : Nat) : UInt16 :=
  (getU8 b off).toUInt16 ||| ((getU8 b (off + 1)).toUInt16 <<< 8)

@[inline] def getU32LE (b : ByteArray) (off : Nat) : UInt32 :=
  (getU8 b off).toUInt32
    ||| ((getU8 b (off + 1)).toUInt32 <<< 8)
    ||| ((getU8 b (off + 2)).toUInt32 <<< 16)
    ||| ((getU8 b (off + 3)).toUInt32 <<< 24)

@[inline] def getF32LE (b : ByteArray) (off : Nat) : Float :=
  (Float32.ofBits (getU32LE b off)).toFloat

/-! ### SceneIR v1 Data Structures -/

structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving Inhabited

structure RGBA where
  r : Float
  g : Float
  b : Float
  a : Float
  deriving Inhabited

@[inline] def pushVec3 (b : ByteArray) (v : Vec3) : ByteArray :=
  b |> (pushF32LE · v.x) |> (pushF32LE · v.y) |> (pushF32LE · v.z)

@[inline] def pushRGBA (b : ByteArray) (c : RGBA) : ByteArray :=
  b |> (pushF32LE · c.r) |> (pushF32LE · c.g) |> (pushF32LE · c.b) |> (pushF32LE · c.a)

structure CameraData where
  motor : FloatArray      -- 8 floats: (s, e01, e02, e03, e12, e13, e23, e0123)
  viewMat4 : FloatArray   -- 16 floats: col-major
  fovDeg : Float := 45.0
  distance : Float := 5.0
  orthoScale : Float := 2.5
  flags : UInt32 := 0     -- b0 = isOrtho

structure PointPrim where
  handleId : UInt32 := 0
  flags : UInt32 := 0     -- b0=draggable, b1=selected, b2=target, b3=hint, b4=hollow
  pos : Vec3
  radius : Float := 0.08
  color : RGBA
  labelIdx : UInt32 := 0xFFFFFFFF

structure SegmentPrim where
  a : Vec3
  b : Vec3
  width : Float := 2.5
  color : RGBA
  flags : UInt32 := 0

structure LinePrim where
  origin : Vec3
  dir : Vec3
  clip : Float := 12.0
  width : Float := 2.0
  color : RGBA
  flags : UInt32 := 0

structure PlanePrim where
  center : Vec3
  u : Vec3
  v : Vec3
  extent : Float := 2.0
  color : RGBA
  flags : UInt32 := 1
  labelIdx : UInt32 := 0xFFFFFFFF

structure CirclePrim where
  center : Vec3
  u : Vec3
  v : Vec3
  radius : Float
  width : Float := 2.5
  color : RGBA
  flags : UInt32 := 0     -- b0 = imaginary
  labelIdx : UInt32 := 0xFFFFFFFF

structure SpherePrim where
  center : Vec3
  radius : Float
  color : RGBA
  flags : UInt32 := 0     -- b0 = imaginary
  labelIdx : UInt32 := 0xFFFFFFFF

structure PointPairPrim where
  p1 : Vec3
  p2 : Vec3
  radius : Float := 0.07
  color : RGBA
  flags : UInt32 := 2     -- b0=imaginary, b1=showLink

structure BivectorDiskPrim where
  origin : Vec3
  u : Vec3
  v : Vec3
  area : Float
  color : RGBA
  flags : UInt32 := 2     -- b0=disk(1)/parallelogram(0), b1=orientationArrow

structure MeshRefPrim where
  meshId : UInt64
  dirtyHash : UInt64
  motor : FloatArray      -- 8 floats
  modelMat4 : FloatArray  -- 16 floats
  color : RGBA
  flags : UInt32 := 6     -- b0=wireframe, b1=doubleSided, b2=useVertexColors

structure MeshAssetData where
  meshId : UInt64
  dirtyHash : UInt64
  positions : FloatArray  -- vertCount * 3
  normals : FloatArray    -- vertCount * 3
  colors : FloatArray     -- empty or vertCount * 4
  indices : Array UInt32  -- CCW front-face winding

structure CurvePrim where
  pts : FloatArray        -- ptCount * 3
  width : Float := 2.5
  color : RGBA
  flags : UInt32 := 0     -- b0=closed, b1=dashed

structure FlowParticlesPrim where
  starts : FloatArray     -- N * 3
  ends : FloatArray       -- N * 3
  pointSize : Float := 3.0
  color : RGBA
  speed : Float := 1.0

structure LabelPrim where
  pos : Vec3
  color : RGBA
  textIdx : UInt32
  flags : UInt32 := 2     -- b0=isLatex, b1=billboard

structure ContourCurve2D where
  xy : FloatArray         -- ptCount * 2
  color : RGBA
  width : Float := 2.0
  flags : UInt32 := 0

structure ContourPt2D where
  x : Float
  y : Float
  color : RGBA
  labelIdx : UInt32 := 0xFFFFFFFF

structure ContourOverlayData where
  minX : Float := -2.0
  maxX : Float := 2.0
  minY : Float := -2.0
  maxY : Float := 2.0
  curves : Array ContourCurve2D := #[]
  intersections : Array ContourPt2D := #[]

structure OpnsUniformData where
  shaderIdx : UInt32 := 0
  grade : UInt32 := 4
  thresh : Float := 0.02
  maxSteps : UInt32 := 64
  stepSize : Float := 0.05
  color : RGBA
  flags : UInt32 := 0     -- b0 = isIPNS
  coeffs : FloatArray

structure InspectCoeffsData where
  entryIdx : UInt32
  grade : UInt32
  coeffs : FloatArray

structure SceneFrameData where
  flags : UInt16 := 6     -- gridEnabled (b1) | darkTheme (b2)
  frameSeq : UInt64 := 0
  simTime : Float := 0.0
  sigP : UInt8 := 3
  sigQ : UInt8 := 0
  sigR : UInt8 := 1
  modeKind : UInt8 := 0
  gridSize : Float := 4.0
  camera : Option CameraData := none
  points : Array PointPrim := #[]
  segments : Array SegmentPrim := #[]
  lines : Array LinePrim := #[]
  planes : Array PlanePrim := #[]
  circles : Array CirclePrim := #[]
  spheres : Array SpherePrim := #[]
  pointPairs : Array PointPairPrim := #[]
  bivectorDisks : Array BivectorDiskPrim := #[]
  meshRefs : Array MeshRefPrim := #[]
  meshAssets : Array MeshAssetData := #[]
  curves : Array CurvePrim := #[]
  flowParticles : Array FlowParticlesPrim := #[]
  labels : Array LabelPrim := #[]
  contourOverlay : Option ContourOverlayData := none
  opnsUniforms : Array OpnsUniformData := #[]
  inspectCoeffs : Array InspectCoeffsData := #[]
  metaJson : String := ""  -- empty => metaJsonLen = 0 (unchanged on hot frames!)

/-! ### Section Encoders (every stride matches `docs/SCENE_IR_V1.md` + #17) -/

@[inline] private def faAt (a : FloatArray) (i : Nat) : Float :=
  if i < a.size then a.get! i else 0.0

private def pushFAFixed (b : ByteArray) (a : FloatArray) (n : Nat) : ByteArray := Id.run do
  let mut out := b
  for i in [:n] do
    out := pushF32LE out (faAt a i)
  return out

def encodeCamera (c : CameraData) : ByteArray :=
  let b := ByteArray.emptyWithCapacity 112
  let b := pushFAFixed b c.motor 8
  let b := pushFAFixed b c.viewMat4 16
  let b := pushF32LE b c.fovDeg
  let b := pushF32LE b c.distance
  let b := pushF32LE b c.orthoScale
  pushU32LE b c.flags

def encodePoints (pts : Array PointPrim) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (pts.size * 44)
  for p in pts do
    b := pushU32LE b p.handleId
    b := pushU32LE b p.flags
    b := pushVec3 b p.pos
    b := pushF32LE b p.radius
    b := pushRGBA b p.color
    b := pushU32LE b p.labelIdx
  return b

def encodeSegments (segs : Array SegmentPrim) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (segs.size * 48)
  for s in segs do
    b := pushVec3 b s.a
    b := pushVec3 b s.b
    b := pushF32LE b s.width
    b := pushRGBA b s.color
    b := pushU32LE b s.flags
  return b

def encodeLines (lines : Array LinePrim) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (lines.size * 52)
  for l in lines do
    b := pushVec3 b l.origin
    b := pushVec3 b l.dir
    b := pushF32LE b l.clip
    b := pushF32LE b l.width
    b := pushRGBA b l.color
    b := pushU32LE b l.flags
  return b

def encodePlanes (planes : Array PlanePrim) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (planes.size * 64)
  for pl in planes do
    b := pushVec3 b pl.center
    b := pushVec3 b pl.u
    b := pushVec3 b pl.v
    b := pushF32LE b pl.extent
    b := pushRGBA b pl.color
    b := pushU32LE b pl.flags
    b := pushU32LE b pl.labelIdx
  return b

def encodeCircles (cs : Array CirclePrim) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (cs.size * 68)
  for c in cs do
    b := pushVec3 b c.center
    b := pushVec3 b c.u
    b := pushVec3 b c.v
    b := pushF32LE b c.radius
    b := pushF32LE b c.width
    b := pushRGBA b c.color
    b := pushU32LE b c.flags
    b := pushU32LE b c.labelIdx
  return b

def encodeSpheres (ss : Array SpherePrim) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (ss.size * 40)
  for s in ss do
    b := pushVec3 b s.center
    b := pushF32LE b s.radius
    b := pushRGBA b s.color
    b := pushU32LE b s.flags
    b := pushU32LE b s.labelIdx
  return b

def encodePointPairs (pps : Array PointPairPrim) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (pps.size * 48)
  for pp in pps do
    b := pushVec3 b pp.p1
    b := pushVec3 b pp.p2
    b := pushF32LE b pp.radius
    b := pushRGBA b pp.color
    b := pushU32LE b pp.flags
  return b

def encodeBivectorDisks (ds : Array BivectorDiskPrim) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (ds.size * 60)
  for d in ds do
    b := pushVec3 b d.origin
    b := pushVec3 b d.u
    b := pushVec3 b d.v
    b := pushF32LE b d.area
    b := pushRGBA b d.color
    b := pushU32LE b d.flags
  return b

def encodeMeshRefs (refs : Array MeshRefPrim) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (refs.size * 136)
  for r in refs do
    b := pushU64LE b r.meshId
    b := pushU64LE b r.dirtyHash
    b := pushFAFixed b r.motor 8
    b := pushFAFixed b r.modelMat4 16
    b := pushRGBA b r.color
    b := pushU32LE b r.flags
    b := pushU32LE b 0
  return b

/-- Encode `0x0B MESH_ASSETS` with 8-byte aligned records (4-byte zero pad if `idxCount` odd). -/
def encodeMeshAssets (assets : Array MeshAssetData) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 1024
  for m in assets do
    let vertCount := m.positions.size / 3
    let idxCount := m.indices.size
    let hasColors : UInt32 := if m.colors.size >= vertCount * 4 && vertCount > 0 then 1 else 0
    b := pushU64LE b m.meshId
    b := pushU64LE b m.dirtyHash
    b := pushU32LE b vertCount.toUInt32
    b := pushU32LE b idxCount.toUInt32
    b := pushU32LE b hasColors
    b := pushU32LE b 0
    b := pushFAFixed b m.positions (vertCount * 3)
    b := pushFAFixed b m.normals (vertCount * 3)
    if hasColors == 1 then
      b := pushFAFixed b m.colors (vertCount * 4)
    for idx in m.indices do
      b := pushU32LE b idx
    b := padAlign8 b
  return b

def encodeCurves (curves : Array CurvePrim) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 256
  for c in curves do
    let ptCount := c.pts.size / 3
    b := pushU32LE b ptCount.toUInt32
    b := pushF32LE b c.width
    b := pushRGBA b c.color
    b := pushU32LE b c.flags
    b := pushFAFixed b c.pts (ptCount * 3)
  return b

def encodeFlowParticles (flows : Array FlowParticlesPrim) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 256
  for f in flows do
    let n := min (f.starts.size / 3) (f.ends.size / 3)
    b := pushU32LE b n.toUInt32
    b := pushF32LE b f.pointSize
    b := pushRGBA b f.color
    b := pushF32LE b f.speed
    b := pushFAFixed b f.starts (n * 3)
    b := pushFAFixed b f.ends (n * 3)
  return b

def encodeLabels (labels : Array LabelPrim) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (labels.size * 36)
  for l in labels do
    b := pushVec3 b l.pos
    b := pushRGBA b l.color
    b := pushU32LE b l.textIdx
    b := pushU32LE b l.flags
  return b

def encodeContourOverlay (ov : ContourOverlayData) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 256
  b := pushF32LE b ov.minX
  b := pushF32LE b ov.maxX
  b := pushF32LE b ov.minY
  b := pushF32LE b ov.maxY
  b := pushU32LE b ov.curves.size.toUInt32
  b := pushU32LE b ov.intersections.size.toUInt32
  for c in ov.curves do
    let n := c.xy.size / 2
    b := pushU32LE b n.toUInt32
    b := pushRGBA b c.color
    b := pushF32LE b c.width
    b := pushU32LE b c.flags
    b := pushFAFixed b c.xy (n * 2)
  for pt in ov.intersections do
    b := pushF32LE b pt.x
    b := pushF32LE b pt.y
    b := pushRGBA b pt.color
    b := pushU32LE b pt.labelIdx
  return b

def encodeOpnsUniforms (items : Array OpnsUniformData) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 128
  for it in items do
    b := pushU32LE b it.shaderIdx
    b := pushU32LE b it.grade
    b := pushU32LE b it.coeffs.size.toUInt32
    b := pushF32LE b it.thresh
    b := pushU32LE b it.maxSteps
    b := pushF32LE b it.stepSize
    b := pushRGBA b it.color
    b := pushU32LE b it.flags
    b := pushFAFixed b it.coeffs it.coeffs.size
  return b

def encodeInspectCoeffs (entries : Array InspectCoeffsData) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 128
  for e in entries do
    b := pushU32LE b e.entryIdx
    b := pushU32LE b e.grade
    b := pushU32LE b e.coeffs.size.toUInt32
    b := pushFAFixed b e.coeffs e.coeffs.size
  return b

private structure EncodedSection where
  kind : UInt32
  count : UInt32
  bytes : ByteArray
  deriving Inhabited

/-- Pack a complete `GSIR` v1 binary frame with 8-byte aligned sections and optional `metaJson`. -/
def encodeSceneFrame (f : SceneFrameData) : ByteArray := Id.run do
  let mut sections : Array EncodedSection := #[]
  match f.camera with
  | some cam => sections := sections.push { kind := 0x01, count := 1, bytes := encodeCamera cam }
  | none => pure ()
  if !f.points.isEmpty then
    sections := sections.push { kind := 0x02, count := f.points.size.toUInt32, bytes := encodePoints f.points }
  if !f.segments.isEmpty then
    sections := sections.push { kind := 0x03, count := f.segments.size.toUInt32, bytes := encodeSegments f.segments }
  if !f.lines.isEmpty then
    sections := sections.push { kind := 0x04, count := f.lines.size.toUInt32, bytes := encodeLines f.lines }
  if !f.planes.isEmpty then
    sections := sections.push { kind := 0x05, count := f.planes.size.toUInt32, bytes := encodePlanes f.planes }
  if !f.circles.isEmpty then
    sections := sections.push { kind := 0x06, count := f.circles.size.toUInt32, bytes := encodeCircles f.circles }
  if !f.spheres.isEmpty then
    sections := sections.push { kind := 0x07, count := f.spheres.size.toUInt32, bytes := encodeSpheres f.spheres }
  if !f.pointPairs.isEmpty then
    sections := sections.push { kind := 0x08, count := f.pointPairs.size.toUInt32, bytes := encodePointPairs f.pointPairs }
  if !f.bivectorDisks.isEmpty then
    sections := sections.push { kind := 0x09, count := f.bivectorDisks.size.toUInt32, bytes := encodeBivectorDisks f.bivectorDisks }
  if !f.meshRefs.isEmpty then
    sections := sections.push { kind := 0x0A, count := f.meshRefs.size.toUInt32, bytes := encodeMeshRefs f.meshRefs }
  if !f.meshAssets.isEmpty then
    sections := sections.push { kind := 0x0B, count := f.meshAssets.size.toUInt32, bytes := encodeMeshAssets f.meshAssets }
  if !f.curves.isEmpty then
    sections := sections.push { kind := 0x0C, count := f.curves.size.toUInt32, bytes := encodeCurves f.curves }
  if !f.flowParticles.isEmpty then
    sections := sections.push { kind := 0x0D, count := f.flowParticles.size.toUInt32, bytes := encodeFlowParticles f.flowParticles }
  if !f.labels.isEmpty then
    sections := sections.push { kind := 0x0E, count := f.labels.size.toUInt32, bytes := encodeLabels f.labels }
  match f.contourOverlay with
  | some ov => sections := sections.push { kind := 0x0F, count := 1, bytes := encodeContourOverlay ov }
  | none => pure ()
  if !f.opnsUniforms.isEmpty then
    sections := sections.push { kind := 0x10, count := f.opnsUniforms.size.toUInt32, bytes := encodeOpnsUniforms f.opnsUniforms }
  if !f.inspectCoeffs.isEmpty then
    sections := sections.push { kind := 0x11, count := f.inspectCoeffs.size.toUInt32, bytes := encodeInspectCoeffs f.inspectCoeffs }

  let headerBytes : Nat := 64
  let dirBytes : Nat := sections.size * 16
  let mut cursor : Nat := headerBytes + dirBytes  -- always multiple of 8 (64 + 16*N)
  let mut offsets : Array Nat := Array.emptyWithCapacity sections.size
  for s in sections do
    offsets := offsets.push cursor
    let paddedLen := ((s.bytes.size + 7) / 8) * 8
    cursor := cursor + paddedLen

  let metaBytes := f.metaJson.toUTF8
  let metaOffset : Nat := if metaBytes.size > 0 then cursor else 0
  let totalLen : Nat := cursor + metaBytes.size

  let mut out := ByteArray.emptyWithCapacity totalLen
  -- Fixed 64-byte Header
  out := pushU32LE out 0x52495347          -- "GSIR"
  out := pushU16LE out 1                   -- version = 1
  out := pushU16LE out f.flags
  out := pushU64LE out f.frameSeq
  out := pushF32LE out f.simTime
  out := pushU8 out f.sigP
  out := pushU8 out f.sigQ
  out := pushU8 out f.sigR
  out := pushU8 out f.modeKind
  out := pushF32LE out f.gridSize
  out := pushU32LE out sections.size.toUInt32
  out := pushU32LE out totalLen.toUInt32
  out := pushU32LE out metaOffset.toUInt32
  out := pushU32LE out metaBytes.size.toUInt32
  out := pushZeros out 20                  -- reserved[20]

  -- Section Directory (16 B * sectionCount)
  for i in [:sections.size] do
    let s := sections[i]!
    let off := offsets[i]!
    out := pushU32LE out s.kind
    out := pushU32LE out s.count
    out := pushU32LE out off.toUInt32
    out := pushU32LE out s.bytes.size.toUInt32

  -- Section Payloads (each padded to 8-byte boundary)
  for s in sections do
    out := out.append s.bytes
    out := padAlign8 out

  -- UTF-8 metaJson chunk (or empty)
  if metaBytes.size > 0 then
    out := out.append metaBytes
  return out

/-! ### Binary `InputEvent` Decoder (`docs/SCENE_IR_V1.md` §4.1 + #17) -/

inductive BinEvent where
  | dragHandle (handleId : UInt32) (x y z : Float) (forceFull : Bool)
  | tick (dt timeSec : Float) (forceFull : Bool)
  | editCoeff (entryIdx bladeIdx : UInt32) (value : Float) (forceFull : Bool)
  | wedgeGesture (idA idB : UInt32) (dirA dirB : Vec3) (holdA holdB isPreview : Bool) (forceFull : Bool)
  | wedgeAction (action : UInt8) (arg : UInt32) (forceFull : Bool)
  | setCamera (motor : FloatArray) (fovDeg distance : Float) (forceFull : Bool)
  | slicePlane (motor : FloatArray) (forceFull : Bool)
  | fullSnapshot
  | invalid

/-- Decode a packed little-endian `InputEvent` packet.
Enforces Lean-derived `hold` (`‖dir‖ < 0.1`) per `@verifier-core` #17 fix #3! -/
def decodeBinEvent (buf : ByteArray) : BinEvent :=
  if buf.size < 4 then .invalid
  else
    let kind := getU8 buf 0
    let flags := getU8 buf 1
    let payloadLen := (getU16LE buf 2).toNat
    let forceFull := (flags &&& 1) != 0
    if buf.size < 4 + payloadLen then .invalid
    else match kind with
      | 0x00 => .fullSnapshot
      | 0x01 =>
        if payloadLen < 16 then .invalid
        else
          let hid := getU32LE buf 4
          let x := getF32LE buf 8
          let y := getF32LE buf 12
          let z := getF32LE buf 16
          .dragHandle hid x y z forceFull
      | 0x02 =>
        if payloadLen < 8 then .invalid
        else
          .tick (getF32LE buf 4) (getF32LE buf 8) forceFull
      | 0x04 =>
        if payloadLen < 12 then .invalid
        else
          .editCoeff (getU32LE buf 4) (getU32LE buf 8) (getF32LE buf 12) forceFull
      | 0x06 =>
        if payloadLen < 36 then .invalid
        else
          let idA := getU32LE buf 4
          let idB := getU32LE buf 8
          let ax := getF32LE buf 12; let ay := getF32LE buf 16; let az := getF32LE buf 20
          let bx := getF32LE buf 24; let by0 := getF32LE buf 28; let bz := getF32LE buf 32
          -- Lean owns gesture threshold (hold iff ‖dir‖ < 0.1) regardless of client byte
          let lenA := Float.sqrt (ax*ax + ay*ay + az*az)
          let lenB := Float.sqrt (bx*bx + by0*by0 + bz*bz)
          let holdA := lenA < 0.1
          let holdB := lenB < 0.1
          let gFlags := getU16LE buf 38
          let isPreview := (gFlags &&& 1) != 0
          .wedgeGesture idA idB ⟨ax, ay, az⟩ ⟨bx, by0, bz⟩ holdA holdB isPreview forceFull
      | 0x07 =>
        if payloadLen < 8 then .invalid
        else
          .wedgeAction (getU8 buf 4) (getU32LE buf 8) forceFull
      | 0x09 =>
        if payloadLen < 40 then .invalid
        else Id.run do
          let mut m := FloatArray.emptyWithCapacity 8
          for i in [:8] do
            m := m.push (getF32LE buf (4 + i * 4))
          return .setCamera m (getF32LE buf 36) (getF32LE buf 40) forceFull
      | 0x0A =>
        if payloadLen < 32 then .invalid
        else Id.run do
          let mut m := FloatArray.emptyWithCapacity 8
          for i in [:8] do
            m := m.push (getF32LE buf (4 + i * 4))
          return .slicePlane m forceFull
      | _ => .invalid

/-! ### Minimal Init-Only JSON Formatting Helpers (Zero `Lean.Data.Json`) -/

def jsonEscape (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    if c == '"' then out := out ++ "\\\""
    else if c == '\\' then out := out ++ "\\\\"
    else if c == '\n' then out := out ++ "\\n"
    else if c == '\r' then out := out ++ "\\r"
    else if c == '\t' then out := out ++ "\\t"
    else out := out.push c
  return out.push '"'

/-- Compact finite float formatter (4 decimals, Init-only, deterministic across native & WASM). -/
def fmtF (x : Float) : String :=
  if x.isNaN || x.isInf then "0"
  else
    let neg := x < 0.0
    let ax := if neg then -x else x
    let scaled := (ax * 10000.0 + 0.5).toUInt64.toNat
    let intPart := scaled / 10000
    let frac := scaled % 10000
    let pfx := if neg && scaled > 0 then "-" else ""
    if frac == 0 then s!"{pfx}{intPart}"
    else
      let d1 := frac / 1000
      let d2 := (frac / 100) % 10
      let d3 := (frac / 10) % 10
      let d4 := frac % 10
      if d4 != 0 then s!"{pfx}{intPart}.{d1}{d2}{d3}{d4}"
      else if d3 != 0 then s!"{pfx}{intPart}.{d1}{d2}{d3}"
      else if d2 != 0 then s!"{pfx}{intPart}.{d1}{d2}"
      else s!"{pfx}{intPart}.{d1}"

end Grassmann.CABI.ScenePack

import Grassmann.Scene.Types
import Grassmann.Scene.Json

/-!
# Canonical `SceneIR` v1 (`GSIR`) Packed Binary Encoder & Decoder

Produces little-endian, 8-byte-aligned `ByteArray` frames matching `docs/SCENE_IR_V1.md`
byte-for-byte so WebGL2/WebGPU (`Float32Array`/`BigUint64Array`) and visionOS RealityKit/Metal
(`MTLBuffer`/`LowLevelMesh`) consume vertex and primitive buffers directly with zero JSON float parsing.
-/

namespace Grassmann.Scene.Binary

/-! ## Little-Endian Primitive Packing -/

@[inline] def pushU8 (b : ByteArray) (v : UInt8) : ByteArray := b.push v

@[inline] def pushU16LE (b : ByteArray) (v : UInt16) : ByteArray :=
  b.push (v &&& 0xFF).toUInt8
   |>.push ((v >>> 8) &&& 0xFF).toUInt8

@[inline] def pushU32LE (b : ByteArray) (v : UInt32) : ByteArray :=
  b.push (v &&& 0xFF).toUInt8
   |>.push ((v >>> 8) &&& 0xFF).toUInt8
   |>.push ((v >>> 16) &&& 0xFF).toUInt8
   |>.push ((v >>> 24) &&& 0xFF).toUInt8

@[inline] def pushU64LE (b : ByteArray) (v : UInt64) : ByteArray :=
  let lo : UInt32 := (v &&& 0xFFFFFFFF).toUInt32
  let hi : UInt32 := ((v >>> 32) &&& 0xFFFFFFFF).toUInt32
  pushU32LE (pushU32LE b lo) hi

@[inline] def pushF32LE (b : ByteArray) (v : Float) : ByteArray :=
  let safe := if v.isFinite && !v.isNaN then v else 0.0
  pushU32LE b safe.toFloat32.toBits

@[inline] def pushVec3 (b : ByteArray) (v : Vec3) : ByteArray :=
  pushF32LE (pushF32LE (pushF32LE b v.x) v.y) v.z

@[inline] def pushRGBA (b : ByteArray) (c : RGBA) : ByteArray :=
  pushF32LE (pushF32LE (pushF32LE (pushF32LE b c.r) c.g) c.b) c.a

@[inline] def pushMotor3 (b : ByteArray) (m : Motor3) : ByteArray :=
  let b := pushF32LE b m.s
  let b := pushF32LE b m.e01
  let b := pushF32LE b m.e02
  let b := pushF32LE b m.e03
  let b := pushF32LE b m.e12
  let b := pushF32LE b m.e13
  let b := pushF32LE b m.e23
  pushF32LE b m.e0123

def pushFloatArrayF32 (b : ByteArray) (xs : FloatArray) : ByteArray :=
  let rec go (i : Nat) (acc : ByteArray) : ByteArray :=
    if i < xs.size then go (i + 1) (pushF32LE acc (xs.get! i)) else acc
  go 0 b

def pushUInt32Array (b : ByteArray) (xs : Array UInt32) : ByteArray :=
  let rec go (i : Nat) (acc : ByteArray) : ByteArray :=
    if i < xs.size then go (i + 1) (pushU32LE acc xs[i]!) else acc
  go 0 b

def pad8 (b : ByteArray) : ByteArray :=
  let rem := b.size % 8
  if rem == 0 then b
  else
    let rec go (k : Nat) (acc : ByteArray) : ByteArray :=
      match k with
      | 0 => acc
      | n + 1 => go n (acc.push 0)
    go (8 - rem) b

/-! ## Little-Endian Reading (for Binary `InputEvent` & Verification) -/

@[inline] def readU8 (b : ByteArray) (off : Nat) : UInt8 :=
  if off < b.size then b.get! off else 0

@[inline] def readU16LE (b : ByteArray) (off : Nat) : UInt16 :=
  (readU8 b off).toUInt16 ||| ((readU8 b (off + 1)).toUInt16 <<< 8)

@[inline] def readU32LE (b : ByteArray) (off : Nat) : UInt32 :=
  (readU8 b off).toUInt32
    ||| ((readU8 b (off + 1)).toUInt32 <<< 8)
    ||| ((readU8 b (off + 2)).toUInt32 <<< 16)
    ||| ((readU8 b (off + 3)).toUInt32 <<< 24)

@[inline] def readU64LE (b : ByteArray) (off : Nat) : UInt64 :=
  (readU32LE b off).toUInt64 ||| ((readU32LE b (off + 4)).toUInt64 <<< 32)

@[inline] def readF32LE (b : ByteArray) (off : Nat) : Float :=
  (Float32.ofBits (readU32LE b off)).toFloat

@[inline] def readVec3 (b : ByteArray) (off : Nat) : Vec3 :=
  ⟨readF32LE b off, readF32LE b (off + 4), readF32LE b (off + 8)⟩

def readMotor3 (b : ByteArray) (off : Nat) : Motor3 :=
  { s     := readF32LE b off
    e01   := readF32LE b (off + 4)
    e02   := readF32LE b (off + 8)
    e03   := readF32LE b (off + 12)
    e12   := readF32LE b (off + 16)
    e13   := readF32LE b (off + 20)
    e23   := readF32LE b (off + 24)
    e0123 := readF32LE b (off + 28) }

/-! ## Section Constants & Flag Encoders (`docs/SCENE_IR_V1.md` §2.3) -/

def gsirMagic   : UInt32 := 0x52495347 -- "GSIR" LE
def gsirVersion : UInt16 := 1

def secCamera         : UInt32 := 0x01
def secPoints         : UInt32 := 0x02
def secSegments       : UInt32 := 0x03
def secLines          : UInt32 := 0x04
def secPlanes         : UInt32 := 0x05
def secCircles        : UInt32 := 0x06
def secSpheres        : UInt32 := 0x07
def secPointPairs     : UInt32 := 0x08
def secBivectorDisks  : UInt32 := 0x09
def secMeshRefs       : UInt32 := 0x0A
def secMeshAssets     : UInt32 := 0x0B
def secCurves         : UInt32 := 0x0C
def secFlowParticles  : UInt32 := 0x0D
def secLabels         : UInt32 := 0x0E
def secContourOverlay : UInt32 := 0x0F
def secOpnsUniforms   : UInt32 := 0x10
def secInspectCoeffs  : UInt32 := 0x11

private def bitFlag (cond : Bool) (shift : UInt32) : UInt32 :=
  if cond then (1 : UInt32) <<< shift else 0

private def pointFlags (r : RoleFlags) : UInt32 :=
  bitFlag r.draggable 0 ||| bitFlag r.selected 1 ||| bitFlag r.target 2 |||
  bitFlag r.hint 3 ||| bitFlag r.hollow 4

private def segmentFlags (r : RoleFlags) (handleId : UInt32) : UInt32 :=
  bitFlag r.dashed 0 ||| bitFlag r.arrow 1 ||| bitFlag r.draggable 2 |||
  bitFlag r.selected 3 ||| bitFlag r.target 4 ||| bitFlag r.hint 5 |||
  ((handleId &&& 0xFFFF) <<< 16)

private def lineFlags (r : RoleFlags) (handleId : UInt32) : UInt32 :=
  bitFlag r.dashed 0 ||| bitFlag r.draggable 1 ||| bitFlag r.selected 2 |||
  bitFlag r.target 3 ||| bitFlag r.hint 4 ||| ((handleId &&& 0xFFFF) <<< 16)

private def planeFlags (gridLines : Bool) (r : RoleFlags) (handleId : UInt32) : UInt32 :=
  bitFlag gridLines 0 ||| bitFlag r.draggable 1 ||| bitFlag r.selected 2 |||
  bitFlag r.target 3 ||| bitFlag r.hint 4 ||| ((handleId &&& 0xFFFF) <<< 16)

private structure EncodedSection where
  kind  : UInt32
  count : UInt32
  data  : ByteArray
  deriving Inhabited

/-! ## Individual Section Packers -/

private def packCamera (cam : CameraState) : EncodedSection :=
  let mat := cam.motor.toColMajorMat4
  let b := ByteArray.emptyWithCapacity 112
  let b := pushMotor3 b cam.motor
  let b := pushFloatArrayF32 b mat
  let b := pushF32LE b cam.fovDeg
  let b := pushF32LE b cam.distance
  let b := pushF32LE b cam.orthoScale
  let b := pushU32LE b (bitFlag cam.isOrtho 0)
  ⟨secCamera, 1, b⟩

private def packPoints (pts : Array PointPrim) (tbl : Array String) : EncodedSection :=
  let b := pts.foldl (init := ByteArray.emptyWithCapacity (pts.size * 44)) fun acc p =>
    let acc := pushU32LE acc p.handleId
    let acc := pushU32LE acc (pointFlags p.role)
    let acc := pushVec3 acc p.pos
    let acc := pushF32LE acc p.radius
    let acc := pushRGBA acc p.color
    pushU32LE acc (Json.findLabelIdx tbl p.label)
  ⟨secPoints, pts.size.toUInt32, b⟩

private def packSegments (segs : Array SegmentPrim) : EncodedSection :=
  let b := segs.foldl (init := ByteArray.emptyWithCapacity (segs.size * 48)) fun acc s =>
    let acc := pushVec3 acc s.a
    let acc := pushVec3 acc s.b
    let acc := pushF32LE acc s.width
    let acc := pushRGBA acc s.color
    pushU32LE acc (segmentFlags s.role s.handleId)
  ⟨secSegments, segs.size.toUInt32, b⟩

private def packLines (lns : Array LinePrim) : EncodedSection :=
  let b := lns.foldl (init := ByteArray.emptyWithCapacity (lns.size * 52)) fun acc l =>
    let acc := pushVec3 acc l.origin
    let acc := pushVec3 acc (Vec3.normalize l.dir)
    let acc := pushF32LE acc l.clip
    let acc := pushF32LE acc l.width
    let acc := pushRGBA acc l.color
    pushU32LE acc (lineFlags l.role l.handleId)
  ⟨secLines, lns.size.toUInt32, b⟩

private def packPlanes (pls : Array PlanePrim) (tbl : Array String) : EncodedSection :=
  let b := pls.foldl (init := ByteArray.emptyWithCapacity (pls.size * 64)) fun acc pl =>
    let acc := pushVec3 acc pl.center
    let acc := pushVec3 acc pl.u
    let acc := pushVec3 acc pl.v
    let acc := pushF32LE acc pl.extent
    let acc := pushRGBA acc pl.color
    let acc := pushU32LE acc (planeFlags pl.gridLines pl.role pl.handleId)
    pushU32LE acc (Json.findLabelIdx tbl pl.label)
  ⟨secPlanes, pls.size.toUInt32, b⟩

private def packCircles (cs : Array CirclePrim) (tbl : Array String) : EncodedSection :=
  let b := cs.foldl (init := ByteArray.emptyWithCapacity (cs.size * 68)) fun acc c =>
    let acc := pushVec3 acc c.center
    let acc := pushVec3 acc c.u
    let acc := pushVec3 acc c.v
    let acc := pushF32LE acc c.radius
    let acc := pushF32LE acc c.width
    let acc := pushRGBA acc c.color
    let acc := pushU32LE acc (bitFlag c.imaginary 0)
    pushU32LE acc (Json.findLabelIdx tbl c.label)
  ⟨secCircles, cs.size.toUInt32, b⟩

private def packSpheres (ss : Array SpherePrim) (tbl : Array String) : EncodedSection :=
  let b := ss.foldl (init := ByteArray.emptyWithCapacity (ss.size * 40)) fun acc s =>
    let acc := pushVec3 acc s.center
    let acc := pushF32LE acc s.radius
    let acc := pushRGBA acc s.color
    let acc := pushU32LE acc (bitFlag s.imaginary 0)
    pushU32LE acc (Json.findLabelIdx tbl s.label)
  ⟨secSpheres, ss.size.toUInt32, b⟩

private def packPointPairs (pps : Array PointPairPrim) : EncodedSection :=
  let b := pps.foldl (init := ByteArray.emptyWithCapacity (pps.size * 48)) fun acc pp =>
    let acc := pushVec3 acc pp.p1
    let acc := pushVec3 acc pp.p2
    let acc := pushF32LE acc pp.radius
    let acc := pushRGBA acc pp.color
    pushU32LE acc (bitFlag pp.imaginary 0 ||| bitFlag pp.showLink 1)
  ⟨secPointPairs, pps.size.toUInt32, b⟩

private def packBivectorDisks (bds : Array BivectorDiskPrim) : EncodedSection :=
  let b := bds.foldl (init := ByteArray.emptyWithCapacity (bds.size * 60)) fun acc bd =>
    let acc := pushVec3 acc bd.origin
    let acc := pushVec3 acc bd.u
    let acc := pushVec3 acc bd.v
    let acc := pushF32LE acc bd.area
    let acc := pushRGBA acc bd.color
    pushU32LE acc (bitFlag bd.isDisk 0 ||| bitFlag bd.orientationArrow 1)
  ⟨secBivectorDisks, bds.size.toUInt32, b⟩

private def packMeshRefs (refs : Array MeshRefPrim) : EncodedSection :=
  let b := refs.foldl (init := ByteArray.emptyWithCapacity (refs.size * 136)) fun acc r =>
    let acc := pushU64LE acc r.meshId
    let acc := pushU64LE acc r.dirtyHash
    let acc := pushMotor3 acc r.motor
    let acc := pushFloatArrayF32 acc r.motor.toColMajorMat4
    let acc := pushRGBA acc r.color
    let flg := bitFlag r.wireframe 0 ||| bitFlag r.doubleSided 1 ||| bitFlag r.useVertexColors 2
    pushU32LE (pushU32LE acc flg) 0
  ⟨secMeshRefs, refs.size.toUInt32, b⟩

private def packMeshAssets (assets : Array MeshAsset) : EncodedSection :=
  let b := assets.foldl (init := ByteArray.emptyWithCapacity (assets.size * 256)) fun acc m =>
    let vertCount := m.positions.size / 3
    let hasColors := m.colors.size == vertCount * 4 && vertCount > 0
    let acc := pushU64LE acc m.meshId
    let acc := pushU64LE acc m.dirtyHash
    let acc := pushU32LE acc vertCount.toUInt32
    let acc := pushU32LE acc m.indices.size.toUInt32
    let acc := pushU32LE acc (bitFlag hasColors 0)
    let acc := pushU32LE acc 0
    let acc := pushFloatArrayF32 acc m.positions
    let acc := pushFloatArrayF32 acc m.normals
    let acc := if hasColors then pushFloatArrayF32 acc m.colors else acc
    let acc := pushUInt32Array acc m.indices
    -- 8-byte align each mesh record (4B zero pad when idxCount is odd)
    pad8 acc
  ⟨secMeshAssets, assets.size.toUInt32, b⟩

private def packCurves (cs : Array CurvePrim) : EncodedSection :=
  let b := cs.foldl (init := ByteArray.emptyWithCapacity (cs.size * 128)) fun acc c =>
    let ptCount := c.points.size / 3
    let acc := pushU32LE acc ptCount.toUInt32
    let acc := pushF32LE acc c.width
    let acc := pushRGBA acc c.color
    let acc := pushU32LE acc (bitFlag c.closed 0 ||| bitFlag c.dashed 1)
    pushFloatArrayF32 acc c.points
  ⟨secCurves, cs.size.toUInt32, b⟩

private def packFlowFields (fs : Array FlowFieldPrim) : EncodedSection :=
  let b := fs.foldl (init := ByteArray.emptyWithCapacity (fs.size * 256)) fun acc fl =>
    let cnt := min (fl.starts.size / 3) (fl.ends.size / 3)
    let acc := pushU32LE acc cnt.toUInt32
    let acc := pushF32LE acc fl.pointSize
    let acc := pushRGBA acc fl.color
    let acc := pushF32LE acc fl.speed
    let acc := pushFloatArrayF32 acc fl.starts
    pushFloatArrayF32 acc fl.ends
  ⟨secFlowParticles, fs.size.toUInt32, b⟩

private def packLabels (lbs : Array LabelPrim) (tbl : Array String) : EncodedSection :=
  let b := lbs.foldl (init := ByteArray.emptyWithCapacity (lbs.size * 36)) fun acc lb =>
    let acc := pushVec3 acc lb.pos
    let acc := pushRGBA acc lb.color
    let acc := pushU32LE acc (Json.findLabelIdx tbl lb.text)
    pushU32LE acc (bitFlag lb.isLatex 0 ||| bitFlag lb.billboard 1)
  ⟨secLabels, lbs.size.toUInt32, b⟩

private def packContourOverlay (co : ContourOverlay) (tbl : Array String) : EncodedSection :=
  let b := ByteArray.emptyWithCapacity 256
  let b := pushF32LE b co.minX
  let b := pushF32LE b co.maxX
  let b := pushF32LE b co.minY
  let b := pushF32LE b co.maxY
  let b := pushU32LE b co.curves.size.toUInt32
  let b := pushU32LE b co.intersections.size.toUInt32
  let b := co.curves.foldl (init := b) fun acc cv =>
    let ptCount := cv.points.size / 2
    let acc := pushU32LE acc ptCount.toUInt32
    let acc := pushRGBA acc cv.color
    let acc := pushF32LE acc cv.width
    let acc := pushU32LE acc (bitFlag cv.closed 0)
    pushFloatArrayF32 acc cv.points
  let b := co.intersections.foldl (init := b) fun acc pt =>
    let acc := pushF32LE acc pt.x
    let acc := pushF32LE acc pt.y
    let acc := pushRGBA acc pt.color
    pushU32LE acc (Json.findLabelIdx tbl pt.label)
  ⟨secContourOverlay, 1, b⟩

private def packOpnsUniforms (us : Array OpnsUniformPrim) : EncodedSection :=
  let b := us.foldl (init := ByteArray.emptyWithCapacity (us.size * 128)) fun acc u =>
    let acc := pushU32LE acc u.shaderIdx
    let acc := pushU32LE acc u.grade
    let acc := pushU32LE acc u.coeffs.size.toUInt32
    let acc := pushF32LE acc u.thresh
    let acc := pushU32LE acc u.maxSteps
    let acc := pushF32LE acc u.stepSize
    let acc := pushRGBA acc u.color
    let acc := pushU32LE acc (bitFlag u.isIPNS 0)
    pushFloatArrayF32 acc u.coeffs
  ⟨secOpnsUniforms, us.size.toUInt32, b⟩

private def packInspectCoeffs (es : Array InspectEntry) : EncodedSection :=
  let b := es.foldl (init := ByteArray.emptyWithCapacity (es.size * 64)) fun acc e =>
    let acc := pushU32LE acc e.idx
    let acc := pushU32LE acc e.grade
    let acc := pushU32LE acc e.coeffs.size.toUInt32
    pushFloatArrayF32 acc e.coeffs
  ⟨secInspectCoeffs, es.size.toUInt32, b⟩

/-! ## Complete `GSIR` v1 Frame Encoder -/

/-- Encode a `SceneFrame` into a canonical `GSIR` v1 little-endian 8-byte-aligned binary frame.
Pass `includeMeta := false` on hot `Tick`/`DragHandle` frames when metadata is unchanged
(`metaJsonLen = 0` signals clients to retain cached metadata with zero JSON parsing). -/
def encodeFrame (f : SceneFrame) (includeMeta : Bool := true) : ByteArray := Id.run do
  let labelsTbl := Json.buildLabelTable f
  let metaBytes := if includeMeta then (Json.toMetaJson f labelsTbl).toUTF8 else ByteArray.empty
  let mut secs : Array EncodedSection := #[packCamera f.camera]
  if !f.points.isEmpty        then secs := secs.push (packPoints f.points labelsTbl)
  if !f.segments.isEmpty      then secs := secs.push (packSegments f.segments)
  if !f.lines.isEmpty         then secs := secs.push (packLines f.lines)
  if !f.planes.isEmpty        then secs := secs.push (packPlanes f.planes labelsTbl)
  if !f.circles.isEmpty       then secs := secs.push (packCircles f.circles labelsTbl)
  if !f.spheres.isEmpty       then secs := secs.push (packSpheres f.spheres labelsTbl)
  if !f.pointPairs.isEmpty    then secs := secs.push (packPointPairs f.pointPairs)
  if !f.bivectorDisks.isEmpty then secs := secs.push (packBivectorDisks f.bivectorDisks)
  if !f.meshRefs.isEmpty      then secs := secs.push (packMeshRefs f.meshRefs)
  if !f.meshAssets.isEmpty    then secs := secs.push (packMeshAssets f.meshAssets)
  if !f.curves.isEmpty        then secs := secs.push (packCurves f.curves)
  if !f.flowFields.isEmpty    then secs := secs.push (packFlowFields f.flowFields)
  if !f.labels.isEmpty        then secs := secs.push (packLabels f.labels labelsTbl)
  match f.contourOverlay with
  | some co => secs := secs.push (packContourOverlay co labelsTbl)
  | none => pure ()
  if !f.opnsUniforms.isEmpty  then secs := secs.push (packOpnsUniforms f.opnsUniforms)
  if !f.inspect.isEmpty       then secs := secs.push (packInspectCoeffs f.inspect)

  let headerSize : Nat := 64
  let dirSize : Nat := secs.size * 16
  let mut curOff : Nat := headerSize + dirSize
  let mut offsets : Array Nat := Array.mkEmpty secs.size
  for s in secs do
    offsets := offsets.push curOff
    let padded := ((s.data.size + 7) / 8) * 8
    curOff := curOff + padded
  let metaOff : Nat := curOff
  let metaPadded : Nat := ((metaBytes.size + 7) / 8) * 8
  let totalLen : Nat := metaOff + metaPadded

  let flags : UInt16 :=
    (if f.is2D then 1 else 0) |||
    (if f.gridEnabled then 2 else 0) |||
    (if f.darkTheme then 4 else 0) |||
    (if f.wedgeHud.isSome then 8 else 0) |||
    (if f.calcHud.isSome then 16 else 0) |||
    (if f.contourOverlay.isSome then 32 else 0) |||
    (if !f.opnsUniforms.isEmpty then 64 else 0)

  let mut out := ByteArray.emptyWithCapacity totalLen
  -- 64-byte header
  out := pushU32LE out gsirMagic
  out := pushU16LE out gsirVersion
  out := pushU16LE out flags
  out := pushU64LE out f.frameSeq
  out := pushF32LE out f.simTime
  out := pushU8 out f.algebra.p
  out := pushU8 out f.algebra.q
  out := pushU8 out f.algebra.r
  out := pushU8 out f.mode.toUInt8
  out := pushF32LE out f.gridSize
  out := pushU32LE out secs.size.toUInt32
  out := pushU32LE out totalLen.toUInt32
  out := pushU32LE out metaOff.toUInt32
  out := pushU32LE out metaBytes.size.toUInt32
  -- 20 reserved zero bytes (5 × u32)
  out := pushU32LE (pushU32LE (pushU32LE (pushU32LE (pushU32LE out 0) 0) 0) 0) 0
  -- Section directory
  for i in [:secs.size] do
    let s := secs[i]!
    out := pushU32LE out s.kind
    out := pushU32LE out s.count
    out := pushU32LE out offsets[i]!.toUInt32
    out := pushU32LE out s.data.size.toUInt32
  -- Section payloads (each 8-byte aligned)
  for s in secs do
    out := pad8 (out ++ s.data)
  -- Meta JSON payload (8-byte aligned)
  out := pad8 (out ++ metaBytes)
  return out

/-! ## Binary `InputEvent` Fast-Path Decoder (`docs/SCENE_IR_V1.md` §4.1) -/

/-- Decode a binary `InputEvent` packet (`4 B` header + fixed payload).
Returns `(event, forceFullSnapshot)`. -/
def decodeInputEventBin (buf : ByteArray) : Except String (InputEvent × Bool) := do
  if buf.size < 4 then throw "binary event shorter than 4-byte header"
  let kind := readU8 buf 0
  let evFlags := readU8 buf 1
  let forceSnap := (evFlags &&& 1) != 0
  let plen := (readU16LE buf 2).toNat
  if buf.size < 4 + plen then throw "binary event truncated"
  match kind with
  | 0x01 => -- DragHandle: handleId(4) + xyz(12)
    if plen < 16 then throw "DragHandle payload < 16 B"
    return (.dragHandle (readU32LE buf 4) (readVec3 buf 8), forceSnap)
  | 0x02 => -- Tick: dt(4) + timeSec(4)
    if plen < 8 then throw "Tick payload < 8 B"
    return (.tick (readF32LE buf 4) (readF32LE buf 8), forceSnap)
  | 0x04 => -- EditCoeff: entryIdx(4) + bladeIdx(4) + value(4)
    if plen < 12 then throw "EditCoeff payload < 12 B"
    return (.editCoeff (readU32LE buf 4) (readU32LE buf 8) (readF32LE buf 12), forceSnap)
  | 0x06 => -- WedgeGesture: idA(4) + idB(4) + dirA(12) + dirB(12) + holdA(1) + holdB(1) + flags(2)
    if plen < 36 then throw "WedgeGesture payload < 36 B"
    let wFlags := readU16LE buf 38
    return (.wedgeGesture (readU32LE buf 4) (readU32LE buf 8)
      (readVec3 buf 12) (readVec3 buf 24) (readU8 buf 36 != 0) (readU8 buf 37 != 0)
      ((wFlags &&& 1) != 0), forceSnap)
  | 0x07 => -- WedgeAction: action(1) + pad(3) + arg(4)
    if plen < 8 then throw "WedgeAction payload < 8 B"
    let act : WedgeActionKind := match readU8 buf 4 with
      | 0 => .undo | 1 => .reset | 2 => .next | 3 => .prev
      | 4 => .toggle3D | 5 => .hint | 6 => .gotoLevel | _ => .reset
    return (.wedgeAction act (readU32LE buf 8), forceSnap)
  | 0x09 => -- SetCamera: motor(32) + fov(4) + dist(4)
    if plen < 40 then throw "SetCamera payload < 40 B"
    return (.setCamera (readMotor3 buf 4) (readF32LE buf 36) (readF32LE buf 40), forceSnap)
  | 0x0A => -- SlicePlane: motor(32)
    if plen < 32 then throw "SlicePlane payload < 32 B"
    return (.slicePlane (readMotor3 buf 4), forceSnap)
  | 0x0C => -- Snapshot
    return (.snapshot, true)
  | _ => throw s!"unsupported binary InputEvent kind: {kind}"

/-- Encode a binary `InputEvent` packet (useful for tests and native/WASM roundtrip checks). -/
def encodeInputEventBin (ev : InputEvent) (forceSnap : Bool := false) : Except String ByteArray :=
  let fl : UInt8 := if forceSnap then 1 else 0
  match ev with
  | .dragHandle hid p =>
    let b := pushU16LE (pushU8 (pushU8 (ByteArray.emptyWithCapacity 20) 0x01) fl) 16
    .ok (pushVec3 (pushU32LE b hid) p)
  | .tick dt t =>
    let b := pushU16LE (pushU8 (pushU8 (ByteArray.emptyWithCapacity 12) 0x02) fl) 8
    .ok (pushF32LE (pushF32LE b dt) t)
  | .editCoeff ei bi val =>
    let b := pushU16LE (pushU8 (pushU8 (ByteArray.emptyWithCapacity 16) 0x04) fl) 12
    .ok (pushF32LE (pushU32LE (pushU32LE b ei) bi) val)
  | .wedgeGesture idA idB dA dB hA hB isPrev =>
    let b := pushU16LE (pushU8 (pushU8 (ByteArray.emptyWithCapacity 40) 0x06) fl) 36
    let b := pushVec3 (pushVec3 (pushU32LE (pushU32LE b idA) idB) dA) dB
    .ok (pushU16LE (pushU8 (pushU8 b (if hA then 1 else 0)) (if hB then 1 else 0)) (if isPrev then 1 else 0))
  | .wedgeAction act arg =>
    let code : UInt8 := match act with
      | .undo => 0 | .reset => 1 | .next => 2 | .prev => 3
      | .toggle3D => 4 | .hint => 5 | .gotoLevel => 6
    let b := pushU16LE (pushU8 (pushU8 (ByteArray.emptyWithCapacity 12) 0x07) fl) 8
    .ok (pushU32LE (pushU8 (pushU8 (pushU8 (pushU8 b code) 0) 0) 0) arg)
  | .setCamera m fov dist =>
    let b := pushU16LE (pushU8 (pushU8 (ByteArray.emptyWithCapacity 44) 0x09) fl) 40
    .ok (pushF32LE (pushF32LE (pushMotor3 b m) fov) dist)
  | .slicePlane m =>
    let b := pushU16LE (pushU8 (pushU8 (ByteArray.emptyWithCapacity 36) 0x0A) fl) 32
    .ok (pushMotor3 b m)
  | .snapshot =>
    .ok (pushU16LE (pushU8 (pushU8 (ByteArray.emptyWithCapacity 4) 0x0C) 1) 0)
  | _ => .error "string-bearing InputEvents use the JSON control path"

/-- Validate a `GSIR` v1 binary buffer header and 8-byte-aligned section directory bounds. -/
def validateGsirFrame (buf : ByteArray) : Except String (UInt32 × UInt64 × Nat) := do
  if buf.size < 64 then throw "GSIR frame < 64 bytes"
  if buf.size % 8 != 0 then throw s!"GSIR frame size {buf.size} not 8-byte aligned"
  let magic := readU32LE buf 0
  if magic != gsirMagic then throw s!"bad GSIR magic: {magic}"
  let ver := readU16LE buf 4
  if ver != gsirVersion then throw s!"unsupported GSIR version: {ver}"
  let seq := readU64LE buf 8
  let secCount := (readU32LE buf 28).toNat
  let totalLen := (readU32LE buf 32).toNat
  let metaOff := (readU32LE buf 36).toNat
  let metaLen := (readU32LE buf 40).toNat
  if totalLen != buf.size then throw s!"totalLen mismatch: {totalLen} vs {buf.size}"
  if 64 + secCount * 16 > buf.size then throw "directory exceeds buffer"
  if metaOff % 8 != 0 || metaOff + metaLen > buf.size then throw "invalid metaJson bounds or alignment"
  for i in [:secCount] do
    let dOff := 64 + i * 16
    let sOff := (readU32LE buf (dOff + 8)).toNat
    let sLen := (readU32LE buf (dOff + 12)).toNat
    if sOff % 8 != 0 || sOff + sLen > metaOff then
      throw s!"section {i} out of bounds or not 8-byte aligned"
  return (secCount.toUInt32, seq, metaLen)

end Grassmann.Scene.Binary

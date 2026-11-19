/-!
# Canonical `SceneIR` v1 (`GSIR`) Types & PGA3 Motor Helpers

Zero-dependency (`Init`-only) scene intermediate representation shared by:
- `Grassmann/Eval` (GA expressions, GAlculator, scalar surfaces, marching-triangles contours)
- `Grassmann/Wedge` (Wedge 2D & Wedge 3D coordinate-free PGA game)
- `Grassmann/CoffeeShop` (interactive GA studio presets)
- `Grassmann/Codegen/GPU` (WGSL/GLSL/MSL OPNS raymarching shaders)
- Native C ABI (visionOS/macOS RealityKit/Metal) and WASM/HTTP WebGPU/WebGL2 clients.

All geometry, normals, motor matrices, contours, and game rules are computed in Lean.
Clients only upload packed little-endian `Float32`/`UInt32` buffers and forward `InputEvent`s.

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) and Steven De Keninck (`enkimute` / `ganja.js`).
-/

namespace Grassmann.Scene

/-! ## Basic Geometric Primitives -/

/-- 2D point / vector in screen or contour coordinates. -/
structure Vec2 where
  x : Float := 0.0
  y : Float := 0.0
  deriving Repr, Inhabited, BEq

/-- 3D right-handed Euclidean point / vector. -/
structure Vec3 where
  x : Float := 0.0
  y : Float := 0.0
  z : Float := 0.0
  deriving Repr, Inhabited, BEq

namespace Vec3

@[inline] def zero : Vec3 := ⟨0.0, 0.0, 0.0⟩
@[inline] def add (a b : Vec3) : Vec3 := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩
@[inline] def sub (a b : Vec3) : Vec3 := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩
@[inline] def scale (s : Float) (a : Vec3) : Vec3 := ⟨s * a.x, s * a.y, s * a.z⟩
@[inline] def neg (a : Vec3) : Vec3 := ⟨-a.x, -a.y, -a.z⟩
@[inline] def dot (a b : Vec3) : Float := a.x * b.x + a.y * b.y + a.z * b.z
@[inline] def cross (a b : Vec3) : Vec3 :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩
@[inline] def normSq (a : Vec3) : Float := a.x * a.x + a.y * a.y + a.z * a.z
@[inline] def norm (a : Vec3) : Float := Float.sqrt (normSq a)
@[inline] def normalize (a : Vec3) : Vec3 :=
  let n := norm a
  if n < 1e-12 then ⟨0.0, 0.0, 1.0⟩ else scale (1.0 / n) a
@[inline] def lerp (a b : Vec3) (t : Float) : Vec3 :=
  ⟨a.x + (b.x - a.x) * t, a.y + (b.y - a.y) * t, a.z + (b.z - a.z) * t⟩

instance : Add Vec3 := ⟨add⟩
instance : Sub Vec3 := ⟨sub⟩
instance : Neg Vec3 := ⟨neg⟩

/-- Construct an orthonormal tangent basis `(u, v)` orthogonal to `n`. -/
def orthonormalBasis (n : Vec3) : Vec3 × Vec3 :=
  let nn := normalize n
  let ref := if Float.abs nn.y < 0.9 then ⟨0.0, 1.0, 0.0⟩ else ⟨1.0, 0.0, 0.0⟩
  let u := normalize (cross ref nn)
  let v := normalize (cross nn u)
  (u, v)

end Vec3

/-- Color in `[0, 1]` RGBA. -/
structure RGBA where
  r : Float := 1.0
  g : Float := 1.0
  b : Float := 1.0
  a : Float := 1.0
  deriving Repr, Inhabited, BEq

namespace RGBA

/-- Construct from `0xRRGGBB` and alpha `[0..1]`. -/
def ofHex (hex : UInt32) (alpha : Float := 1.0) : RGBA :=
  let r := ((hex >>> 16) &&& 0xFF).toNat.toFloat / 255.0
  let g := ((hex >>> 8) &&& 0xFF).toNat.toFloat / 255.0
  let b := (hex &&& 0xFF).toNat.toFloat / 255.0
  ⟨r, g, b, alpha⟩

def white  : RGBA := ⟨1.0, 1.0, 1.0, 1.0⟩
def red    : RGBA := ⟨1.0, 0.42, 0.42, 1.0⟩
def coral  : RGBA := ⟨1.0, 0.53, 0.53, 1.0⟩
def green  : RGBA := ⟨0.32, 0.92, 0.58, 1.0⟩
def blue   : RGBA := ⟨0.30, 0.62, 1.0, 1.0⟩
def cyan   : RGBA := ⟨0.22, 0.88, 0.95, 1.0⟩
def amber  : RGBA := ⟨1.0, 0.72, 0.22, 1.0⟩
def violet : RGBA := ⟨0.72, 0.45, 1.0, 1.0⟩
def ghost  : RGBA := ⟨0.42, 0.44, 0.54, 0.45⟩

end RGBA

/-! ## Compact PGA3 Even Motor (`Cl(3,0,1)` Rigid Transformation) -/

/-- Even subalgebra element of 3D PGA `Cl(3,0,1)` (`e₀²=0, e₁²=e₂²=e₃²=+1`):
`M = s + e01·e₀₁ + e02·e₀₂ + e03·e₀₃ + e12·e₁₂ + e13·e₁₃ + e23·e₂₃ + e0123·e₀₁₂₃`.
Represents any 3D rigid motion (rotation + translation / screw motion). -/
structure Motor3 where
  s     : Float := 1.0
  e01   : Float := 0.0
  e02   : Float := 0.0
  e03   : Float := 0.0
  e12   : Float := 0.0
  e13   : Float := 0.0
  e23   : Float := 0.0
  e0123 : Float := 0.0
  deriving Repr, Inhabited, BEq

namespace Motor3

@[inline] def identity : Motor3 := {}

/-- Geometric product of two PGA3 even motors (unrolled straight-line, zero alloc).
Basis rules: `e₀²=0`, `eᵢ²=+1`, `e₁₂²=e₁₃²=e₂₃²=-1`, `e₁₂e₁₃=-e₂₃`, `e₁₂e₂₃=e₁₃`, `e₁₃e₂₃=-e₁₂`. -/
@[inline] def mul (a b : Motor3) : Motor3 :=
  { s     := a.s * b.s - a.e12 * b.e12 - a.e13 * b.e13 - a.e23 * b.e23
    e01   := a.s * b.e01 + a.e01 * b.s - a.e02 * b.e12 - a.e03 * b.e13
             + a.e12 * b.e02 + a.e13 * b.e03 - a.e23 * b.e0123 - a.e0123 * b.e23
    e02   := a.s * b.e02 + a.e02 * b.s + a.e01 * b.e12 - a.e03 * b.e23
             - a.e12 * b.e01 + a.e23 * b.e03 + a.e13 * b.e0123 + a.e0123 * b.e13
    e03   := a.s * b.e03 + a.e03 * b.s + a.e01 * b.e13 + a.e02 * b.e23
             - a.e13 * b.e01 - a.e23 * b.e02 - a.e12 * b.e0123 - a.e0123 * b.e12
    e12   := a.s * b.e12 + a.e12 * b.s - a.e13 * b.e23 + a.e23 * b.e13
    e13   := a.s * b.e13 + a.e13 * b.s + a.e12 * b.e23 - a.e23 * b.e12
    e23   := a.s * b.e23 + a.e23 * b.s - a.e12 * b.e13 + a.e13 * b.e12
    e0123 := a.s * b.e0123 + a.e0123 * b.s + a.e01 * b.e23 - a.e02 * b.e13
             + a.e03 * b.e12 + a.e12 * b.e03 - a.e13 * b.e02 + a.e23 * b.e01 }

/-- Reverse `~M`: negates grade-2 bivector parts, preserves scalar and grade-4 `e0123`. -/
@[inline] def rev (m : Motor3) : Motor3 :=
  { s := m.s, e01 := -m.e01, e02 := -m.e02, e03 := -m.e03,
    e12 := -m.e12, e13 := -m.e13, e23 := -m.e23, e0123 := m.e0123 }

/-- Study-preserving normalization `M / ‖M‖` ensuring `M ~M = 1`. -/
def normalize (m : Motor3) : Motor3 :=
  let n2 := m.s * m.s + m.e12 * m.e12 + m.e13 * m.e13 + m.e23 * m.e23
  if n2 < 1e-24 then identity
  else
    let invN := 1.0 / Float.sqrt n2
    let invN3 := invN / n2
    let study := m.s * m.e0123 - m.e01 * m.e23 + m.e02 * m.e13 - m.e03 * m.e12
    let k := study * invN3
    { s     := m.s * invN
      e01   := m.e01 * invN + m.e23 * k
      e02   := m.e02 * invN - m.e13 * k
      e03   := m.e03 * invN + m.e12 * k
      e12   := m.e12 * invN
      e13   := m.e13 * invN
      e23   := m.e23 * invN
      e0123 := m.e0123 * invN - m.s * k }

/-- Pure translator by `(dx, dy, dz)`: `T = 1 - ½(dx·e₀₁ + dy·e₀₂ + dz·e₀₃)`. -/
@[inline] def translator (dx dy dz : Float) : Motor3 :=
  { s := 1.0, e01 := -0.5 * dx, e02 := -0.5 * dy, e03 := -0.5 * dz }

/-- Pure rotor around unit axis `(ax, ay, az)` by `angle` radians.
In PGA3: rotation around `e₁` is in `e₂₃` plane, around `e₂` is `-e₁₃`, around `e₃` is `e₁₂`. -/
@[inline] def rotorAxis (axis : Vec3) (angle : Float) : Motor3 :=
  let u := Vec3.normalize axis
  let half := 0.5 * angle
  let c := Float.cos half
  let s := Float.sin half
  { s := c, e23 := -s * u.x, e13 := s * u.y, e12 := -s * u.z }

/-- Closed-form O(1) PGA3 exponential `exp(B)` of a bivector `(e01,e02,e03,e12,e13,e23)`. -/
def expBivector (b01 b02 b03 b12 b13 b23 : Float) : Motor3 :=
  let l2 := b12 * b12 + b13 * b13 + b23 * b23
  if l2 < 1e-18 then
    { s := 1.0, e01 := b01, e02 := b02, e03 := b03 }
  else
    let a := Float.sqrt l2
    let c := Float.cos a
    let sinc := Float.sin a / a
    let m := b01 * b23 - b02 * b13 + b03 * b12
    let t := (m / l2) * (c - sinc)
    { s     := c
      e01   := sinc * b01 + t * b23
      e02   := sinc * b02 - t * b13
      e03   := sinc * b03 + t * b12
      e12   := sinc * b12
      e13   := sinc * b13
      e23   := sinc * b23
      e0123 := sinc * m }

/-- Closed-form O(1) PGA3 logarithm `log(M)` returning the 6 bivector coefficients
`(e01, e02, e03, e12, e13, e23)` such that `expBivector (log M) = M`. -/
def logBivector (m : Motor3) : Float × Float × Float × Float × Float × Float :=
  let mn := normalize m
  let l2 := mn.e12 * mn.e12 + mn.e13 * mn.e13 + mn.e23 * mn.e23
  if l2 < 1e-18 then
    let sgn := if mn.s < 0.0 then -1.0 else 1.0
    (sgn * mn.e01, sgn * mn.e02, sgn * mn.e03, 0.0, 0.0, 0.0)
  else
    let a := Float.acos (max (-1.0) (min 1.0 mn.s))
    let invL := 1.0 / Float.sqrt l2
    let b := a * invL
    let c := (mn.e0123 / l2) * (1.0 - mn.s * b)
    (b * mn.e01 + c * mn.e23, b * mn.e02 - c * mn.e13, b * mn.e03 + c * mn.e12,
     b * mn.e12, b * mn.e13, b * mn.e23)

/-- Screw-linear interpolation `SLERP(a, b, t) = a * exp(t * log(~a * b))`. -/
def slerp (a b : Motor3) (t : Float) : Motor3 :=
  let d := mul (rev a) b
  let (b01, b02, b03, b12, b13, b23) := logBivector d
  mul a (expBivector (t * b01) (t * b02) (t * b03) (t * b12) (t * b13) (t * b23))

/-- Extract the 3×3 rotation matrix (row vectors `rx, ry, rz`) and translation `(tx, ty, tz)`
of normalized motor `M` acting on 3D Euclidean points `p ↦ R p + t`. -/
def toAffine (m : Motor3) : Vec3 × Vec3 × Vec3 × Vec3 :=
  let mn := normalize m
  -- Map PGA3 rotor (s, e23, e13, e12) to unit quaternion (w, qx, qy, qz) with q = (s, -e23, e13, -e12)
  let w := mn.s
  let x := -mn.e23
  let y := mn.e13
  let z := -mn.e12
  let xx := x * x; let yy := y * y; let zz := z * z
  let xy := x * y; let xz := x * z; let yz := y * z
  let wx := w * x; let wy := w * y; let wz := w * z
  let r0 : Vec3 := ⟨1.0 - 2.0 * (yy + zz), 2.0 * (xy - wz),       2.0 * (xz + wy)⟩
  let r1 : Vec3 := ⟨2.0 * (xy + wz),       1.0 - 2.0 * (xx + zz), 2.0 * (yz - wx)⟩
  let r2 : Vec3 := ⟨2.0 * (xz - wy),       2.0 * (yz + wx),       1.0 - 2.0 * (xx + yy)⟩
  -- Translation from ideal part: T = M * ~R => t = -2 * (T.e01, T.e02, T.e03)
  let tx := -2.0 * (mn.s * mn.e01 + mn.e02 * mn.e12 + mn.e03 * mn.e13 + mn.e0123 * mn.e23)
  let ty := -2.0 * (mn.s * mn.e02 - mn.e01 * mn.e12 + mn.e03 * mn.e23 - mn.e0123 * mn.e13)
  let tz := -2.0 * (mn.s * mn.e03 - mn.e01 * mn.e13 - mn.e02 * mn.e23 + mn.e0123 * mn.e12)
  (r0, r1, r2, ⟨tx, ty, tz⟩)

/-- Apply motor `m` to a 3D point `p`. -/
@[inline] def applyPoint (m : Motor3) (p : Vec3) : Vec3 :=
  let (r0, r1, r2, t) := toAffine m
  ⟨Vec3.dot r0 p + t.x, Vec3.dot r1 p + t.y, Vec3.dot r2 p + t.z⟩

/-- Apply only the rotational part of motor `m` to a 3D direction vector `v`. -/
@[inline] def applyDir (m : Motor3) (v : Vec3) : Vec3 :=
  let (r0, r1, r2, _) := toAffine m
  ⟨Vec3.dot r0 v, Vec3.dot r1 v, Vec3.dot r2 v⟩

/-- Column-major 4×4 affine matrix (16 `Float`s) ready for WebGL2/WebGPU/Metal/RealityKit. -/
def toColMajorMat4 (m : Motor3) : FloatArray :=
  let (r0, r1, r2, t) := toAffine m
  let out := FloatArray.emptyWithCapacity 16
  let out := out.push r0.x |>.push r1.x |>.push r2.x |>.push 0.0
  let out := out.push r0.y |>.push r1.y |>.push r2.y |>.push 0.0
  let out := out.push r0.z |>.push r1.z |>.push r2.z |>.push 0.0
  out.push t.x |>.push t.y |>.push t.z |>.push 1.0

/-- Pack the 8 motor coefficients into a `FloatArray`. -/
def toFloatArray (m : Motor3) : FloatArray :=
  (FloatArray.emptyWithCapacity 8)
    |>.push m.s |>.push m.e01 |>.push m.e02 |>.push m.e03
    |>.push m.e12 |>.push m.e13 |>.push m.e23 |>.push m.e0123

/-- Unpack 8 motor coefficients from a `FloatArray` (identity fallback if shorter). -/
def ofFloatArray (xs : FloatArray) : Motor3 :=
  if xs.size < 8 then identity
  else
    { s := xs.get! 0, e01 := xs.get! 1, e02 := xs.get! 2, e03 := xs.get! 3
      e12 := xs.get! 4, e13 := xs.get! 5, e23 := xs.get! 6, e0123 := xs.get! 7 }

/-- Build an orbit view motor from heading `yaw`, pitch `pitch`, and target `distance`. -/
def orbitCamera (yaw pitch distance : Float) : Motor3 :=
  let rYaw := rotorAxis ⟨0.0, 1.0, 0.0⟩ yaw
  let rPitch := rotorAxis ⟨1.0, 0.0, 0.0⟩ pitch
  let tBack := translator 0.0 0.0 (-distance)
  mul tBack (mul rPitch rYaw)

end Motor3

/-! ## `SceneIR` v1 Primitives & Metadata -/

/-- Workspace mode encoded in header byte `sigMode[3]`. -/
inductive StudioMode where
  | coffeeShop
  | wedge2D
  | wedge3D
  | calculator
  | surface
  deriving Repr, Inhabited, BEq

def StudioMode.toUInt8 : StudioMode → UInt8
  | .coffeeShop => 0
  | .wedge2D    => 1
  | .wedge3D    => 2
  | .calculator => 3
  | .surface    => 4

/-- Camera specification (`0x01 CAMERA`). `isOrtho` sets `flags` bit 0. -/
structure CameraState where
  motor      : Motor3 := Motor3.orbitCamera 0.55 (-0.32) 5.2
  fovDeg     : Float  := 45.0
  distance   : Float  := 5.2
  orthoScale : Float  := 1.0
  isOrtho    : Bool   := false
  deriving Repr, Inhabited

/-- Role flags shared by points, segments, lines, and planes. -/
structure RoleFlags where
  draggable : Bool := false
  selected  : Bool := false
  target    : Bool := false
  hint      : Bool := false
  hollow    : Bool := false
  dashed    : Bool := false
  arrow     : Bool := false
  deriving Repr, Inhabited, BEq

/-- Interactive or static 3D/2D point (`0x02 POINTS`). -/
structure PointPrim where
  handleId : UInt32 := 0
  pos      : Vec3   := Vec3.zero
  radius   : Float  := 0.06
  color    : RGBA   := RGBA.white
  role     : RoleFlags := {}
  label    : String := ""
  deriving Repr, Inhabited

/-- Finite 3D/2D line segment (`0x03 SEGMENTS`). -/
structure SegmentPrim where
  a        : Vec3   := Vec3.zero
  b        : Vec3   := ⟨1.0, 0.0, 0.0⟩
  width    : Float  := 2.0
  color    : RGBA   := RGBA.white
  handleId : UInt32 := 0
  role     : RoleFlags := {}
  deriving Repr, Inhabited

/-- Infinite line clipped to `origin ± clip * dir` (`0x04 LINES`). -/
structure LinePrim where
  origin   : Vec3   := Vec3.zero
  dir      : Vec3   := ⟨1.0, 0.0, 0.0⟩
  clip     : Float  := 3.5
  width    : Float  := 2.0
  color    : RGBA   := RGBA.cyan
  handleId : UInt32 := 0
  role     : RoleFlags := {}
  label    : String := ""
  deriving Repr, Inhabited

/-- Oriented finite plane quad `center ± extent·u ± extent·v` (`0x05 PLANES`). -/
structure PlanePrim where
  center    : Vec3   := Vec3.zero
  u         : Vec3   := ⟨1.0, 0.0, 0.0⟩
  v         : Vec3   := ⟨0.0, 0.0, 1.0⟩
  extent    : Float  := 2.0
  color     : RGBA   := ⟨0.25, 0.55, 0.95, 0.25⟩
  gridLines : Bool   := true
  handleId  : UInt32 := 0
  role      : RoleFlags := {}
  label     : String := ""
  deriving Repr, Inhabited

/-- 3D/2D circle (`0x06 CIRCLES`, `imaginary = true` renders dashed). -/
structure CirclePrim where
  center    : Vec3   := Vec3.zero
  u         : Vec3   := ⟨1.0, 0.0, 0.0⟩
  v         : Vec3   := ⟨0.0, 1.0, 0.0⟩
  radius    : Float  := 1.0
  width     : Float  := 2.2
  color     : RGBA   := RGBA.cyan
  imaginary : Bool   := false
  label     : String := ""
  deriving Repr, Inhabited

/-- 3D sphere (`0x07 SPHERES`, `imaginary = true` renders wireframe/dashed). -/
structure SpherePrim where
  center    : Vec3   := Vec3.zero
  radius    : Float  := 1.0
  color     : RGBA   := ⟨0.30, 0.65, 1.0, 0.28⟩
  imaginary : Bool   := false
  label     : String := ""
  deriving Repr, Inhabited

/-- CGA point pair (`0x08 POINT_PAIRS`). -/
structure PointPairPrim where
  p1        : Vec3   := Vec3.zero
  p2        : Vec3   := ⟨1.0, 0.0, 0.0⟩
  radius    : Float  := 0.06
  color     : RGBA   := RGBA.amber
  imaginary : Bool   := false
  showLink  : Bool   := true
  label     : String := ""
  deriving Repr, Inhabited

/-- Oriented bivector parallelogram or disk (`0x09 BIVECTOR_DISKS`, STA & R3 wedge). -/
structure BivectorDiskPrim where
  origin           : Vec3  := Vec3.zero
  u                : Vec3  := ⟨1.0, 0.0, 0.0⟩
  v                : Vec3  := ⟨0.0, 1.0, 0.0⟩
  area             : Float := 1.0
  color            : RGBA  := ⟨0.95, 0.58, 0.22, 0.35⟩
  isDisk           : Bool  := false
  orientationArrow : Bool  := true
  deriving Repr, Inhabited

/-- Triangle mesh geometry asset uploaded delta-wise by `(meshId, dirtyHash)` (`0x0B MESH_ASSETS`).
`positions` and `normals` hold `3 * vertCount` packed `Float`s; `colors` holds either `0` or
`4 * vertCount` packed RGBA `Float`s; `indices` holds `3 * triCount` vertex indices. -/
structure MeshAsset where
  meshId    : UInt64
  dirtyHash : UInt64
  positions : FloatArray
  normals   : FloatArray
  colors    : FloatArray := FloatArray.empty
  indices   : Array UInt32
  deriving Inhabited

/-- Compute deterministic 64-bit FNV-1a dirty hash for a `MeshAsset`'s geometry. -/
def computeMeshHash (meshId : UInt64) (positions : FloatArray) (indices : Array UInt32) : UInt64 :=
  let h0 : UInt64 := 14695981039346656037 ^^^ meshId
  let prime : UInt64 := 1099511628211
  let rec loopP (i : Nat) (h : UInt64) : UInt64 :=
    if i < positions.size then
      let bits := (positions.get! i).toFloat32.toBits.toUInt64
      loopP (i + 1) ((h ^^^ bits) * prime)
    else h
  let h1 := loopP 0 h0
  let rec loopI (i : Nat) (h : UInt64) : UInt64 :=
    if i < indices.size then
      loopI (i + 1) ((h ^^^ indices[i]!.toUInt64) * prime)
    else h
  loopI 0 h1

/-- Instance reference to a cached `MeshAsset` transformed by a PGA3 `Motor3` (`0x0A MESH_REFS`). -/
structure MeshRefPrim where
  meshId          : UInt64
  dirtyHash       : UInt64
  motor           : Motor3 := Motor3.identity
  color           : RGBA   := RGBA.white
  wireframe       : Bool   := false
  doubleSided     : Bool   := true
  useVertexColors : Bool   := false
  deriving Repr, Inhabited

/-- Packed 3D polyline curve (`0x0C CURVES`, `points` has `3 * ptCount` floats). -/
structure CurvePrim where
  points : FloatArray
  width  : Float := 2.0
  color  : RGBA  := RGBA.cyan
  closed : Bool  := false
  dashed : Bool  := false
  deriving Inhabited

/-- Motor-flow particle field (`0x0D FLOW_PARTICLES`, `starts`/`ends` have `3 * count` floats). -/
structure FlowFieldPrim where
  starts    : FloatArray
  ends      : FloatArray
  pointSize : Float := 4.0
  color     : RGBA  := RGBA.cyan
  speed     : Float := 1.0
  deriving Inhabited

/-- Anchored 3D/2D text or LaTeX label (`0x0E LABELS`). -/
structure LabelPrim where
  pos       : Vec3   := Vec3.zero
  text      : String := ""
  color     : RGBA   := RGBA.white
  isLatex   : Bool   := false
  billboard : Bool   := true
  deriving Repr, Inhabited

/-- 2D polyline inside a `ContourOverlay` (`points` has `2 * ptCount` floats `[x0,y0,...]`). -/
structure ContourPolyline where
  points : FloatArray
  color  : RGBA  := RGBA.cyan
  width  : Float := 2.0
  closed : Bool  := false
  deriving Inhabited

/-- Common intersection point highlighted in a `ContourOverlay`. -/
structure ContourIntersection where
  x     : Float
  y     : Float
  color : RGBA   := RGBA.amber
  label : String := ""
  deriving Repr, Inhabited

/-- 2D contour inset (`0x0F CONTOUR_OVERLAY`) for `#pga3d_slicing` and implicit equation systems. -/
structure ContourOverlay where
  minX          : Float := -2.0
  maxX          : Float := 2.0
  minY          : Float := -2.0
  maxY          : Float := 2.0
  curves        : Array ContourPolyline := #[]
  intersections : Array ContourIntersection := #[]
  deriving Inhabited

/-- Lean-emitted OPNS/IPNS GPU raymarching shader triplet cached by `hash`. -/
structure OpnsShaderSource where
  hash : String
  wgsl : String
  glsl : String
  msl  : String
  deriving Repr, Inhabited

/-- Implicit OPNS/IPNS blade uniform payload (`0x10 OPNS_UNIFORMS`). -/
structure OpnsUniformPrim where
  shaderIdx : UInt32     := 0
  grade     : UInt32     := 4
  coeffs    : FloatArray := FloatArray.empty
  thresh    : Float      := 0.04
  maxSteps  : UInt32     := 80
  stepSize  : Float      := 0.0002
  color     : RGBA       := RGBA.violet
  isIPNS    : Bool       := false
  deriving Inhabited

/-- Live multivector inspector entry (CoffeeShop `inspect stash`). -/
structure InspectEntry where
  idx       : UInt32     := 0
  name      : String     := ""
  grade     : UInt32     := 0
  formatted : String     := "0"
  coeffs    : FloatArray := FloatArray.empty
  editable  : Bool       := false
  deriving Inhabited

/-- GAlculator memory slot (`x1..x10`). -/
structure CalcRegister where
  slot      : String
  formatted : String
  deriving Repr, Inhabited

/-- GAlculator / LeanCalculator HUD metadata. -/
structure CalcHudState where
  mode      : String := "STA"
  display   : String := "0"
  history   : Array String := #[]
  registers : Array CalcRegister := #[]
  deriving Repr, Inhabited

/-- Wedge 2D/3D game HUD metadata. -/
structure WedgeHudState where
  is3D         : Bool   := false
  level        : UInt32 := 1
  totalLevels  : UInt32 := 16
  title        : String := ""
  goal         : String := ""
  tutorialText : String := ""
  moves        : UInt32 := 0
  score        : UInt32 := 1000
  elapsedMs    : UInt32 := 0
  lastOp       : String := ""
  previewOp    : String := ""
  hintText     : String := ""
  solved       : Bool   := false
  canUndo      : Bool   := false
  isRandom     : Bool   := false
  seedStr      : String := ""
  difficulty   : UInt32 := 0
  dim          : UInt32 := 2
  tutorialId   : String := ""
  deriving Repr, Inhabited

/-- Algebra signature & basis metadata. -/
structure AlgebraMeta where
  name          : String       := "PGA3"
  p             : UInt8        := 3
  q             : UInt8        := 0
  r             : UInt8        := 1
  conformalWitt : Bool         := false
  basisNames    : Array String := #[]
  basisMetric   : Array Int8   := #[]
  deriving Repr, Inhabited

/-- Interactive `@param` slider specification emitted in `metaJson.params[]`. -/
structure ParamSpec where
  name  : String := ""
  label : String := ""
  value : Float  := 0.0
  min   : Float  := 0.0
  max   : Float  := 1.0
  step  : Float  := 0.01
  deriving Repr, Inhabited, BEq

/-- Complete canonical `SceneIR` v1 frame produced purely in Lean. -/
structure SceneFrame where
  frameSeq       : UInt64                := 0
  simTime        : Float                 := 0.0
  mode           : StudioMode            := .coffeeShop
  is2D           : Bool                  := false
  gridEnabled    : Bool                  := true
  darkTheme      : Bool                  := true
  gridSize       : Float                 := 2.0
  algebra        : AlgebraMeta           := {}
  presetId       : String                := ""
  title          : String                := ""
  script         : String                := ""
  params         : Array ParamSpec       := #[]
  formula        : String                := ""
  summary        : String                := ""
  camera         : CameraState           := {}
  points         : Array PointPrim       := #[]
  segments       : Array SegmentPrim     := #[]
  lines          : Array LinePrim        := #[]
  planes         : Array PlanePrim       := #[]
  circles        : Array CirclePrim      := #[]
  spheres        : Array SpherePrim      := #[]
  pointPairs     : Array PointPairPrim   := #[]
  bivectorDisks  : Array BivectorDiskPrim := #[]
  meshRefs       : Array MeshRefPrim     := #[]
  meshAssets     : Array MeshAsset       := #[]
  curves         : Array CurvePrim       := #[]
  flowFields     : Array FlowFieldPrim   := #[]
  labels         : Array LabelPrim       := #[]
  contourOverlay : Option ContourOverlay := none
  opnsShaders    : Array OpnsShaderSource := #[]
  opnsUniforms   : Array OpnsUniformPrim := #[]
  inspect        : Array InspectEntry    := #[]
  calcHud        : Option CalcHudState   := none
  wedgeHud       : Option WedgeHudState  := none
  diagnostics    : Array String          := #[]
  deriving Inhabited

/-- Wedge control actions. -/
inductive WedgeActionKind where
  | undo
  | reset
  | next
  | prev
  | toggle3D
  | hint
  | gotoLevel
  deriving Repr, Inhabited, BEq

/-- Typed client → Lean input event union (zero logic in JS/Swift). -/
inductive InputEvent where
  | dragHandle    (handleId : UInt32) (pos : Vec3)
  | tick          (dt : Float) (timeSec : Float)
  | evalScript    (algebra : String) (code : String)
  | evalSurface   (expr : String) (minX maxX minY maxY : Float) (gridN : UInt32)
  | editCoeff     (entryIdx : UInt32) (bladeIdx : UInt32) (value : Float)
  | loadPreset    (presetId : String)
  | wedgeGesture  (idA idB : UInt32) (dirA dirB : Vec3) (holdA holdB : Bool) (isPreview : Bool := false)
  | wedgeAction   (action : WedgeActionKind) (arg : UInt32 := 0)
  | calcKey       (key : String)
  | calcEval      (mode : String) (expr : String)
  | setCamera     (motor : Motor3) (fovDeg : Float) (distance : Float)
  | slicePlane    (motor : Motor3)
  | evalEquations  (equations : Array String) (minX maxX minY maxY : Float) (gridN : UInt32)
  | evalImplicit   (expr : String) (gpuRaymarch : Bool := false) (bound : Float := 1.6) (gridN : UInt32 := 18)
  | evalParametric (fx fy fz : String) (uMin uMax vMin vMax : Float) (nu nv : UInt32)
  | wedgeTutorial  (id : String)
  | wedgeRandom    (is3D : Bool) (difficulty : UInt32) (seed : UInt64)
  | setParam       (name : String) (value : Float)
  | loadTourStop   (index : UInt32)
  | resetTime
  | seekTime       (timeSec : Float)
  | snapshot
  deriving Repr, Inhabited

end Grassmann.Scene

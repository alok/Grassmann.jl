/-
Projective Geometric Algebra (`PGA2 := D!"0,1,1"`, `PGA3 := D!"0,1,1,1"`) utilities:
points, Plücker lines, planes, join (`&` / `∨`), meet (`^` / `∧`), closed-form `O(1)`
`motorExp`/`motorLog`/SLERP, Study normalization, column-major 4×4 affine matrix extraction,
flat XYZ batch transforms, rigid-body dynamics Euler/RK4 steps, and exact PGA3 triangle-mesh
plane slicing (clipped 3D half-meshes + projected 2D contour polylines for `#pga3d_slicing`).

Credits:
- Michael Reed (`chakravala` / `Grassmann.jl`): core Grassmann-Clifford algebra engine.
- Steven De Keninck (`enkimute` / `ganja.js`): PGA2/PGA3 geometry, motors, slicing & physics demos.

## Storage & Wire Order Alignment

`PGA3 := D!"0,1,1,1"` has generators `[e0, e1, e2, e3]` (`e0² = 0`, `e1² = e2² = e3² = 1`).
In Grassmann.jl's grade-major lex order, `Spinor PGA3 Float` stores its 8 coefficients in
**exact `ganja.js` / `GSIR` v1 wire order**:
  `[s, e01, e02, e03, e12, e13, e23, e0123]` (indices `0..7`).
-/
module

public import Grassmann.GanjaCompat
public import Grassmann.Kernel.Generated.PGA2
public import Grassmann.Kernel.Generated.PGA3

public section

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors GanjaCompat

namespace Projective

/-! ## Module-Level Float Constants & Compact Unboxed Constructors

Hoisting constants to top-level `def`s avoids Lean's per-call `Float.ofScientific` / atomic
once-cell overhead (especially for exponents beyond `10⁻²²` like `1e-24`). Building fixed-size
`Values` via `Values.set` on a cached zero template does a single copy + inline unboxed stores
instead of out-of-line `lean_float_array_push` calls. -/

private def f0 : Float := 0.0
private def f1 : Float := 1.0
private def f2 : Float := 2.0
private def fNeg2 : Float := -2.0
private def fHalf : Float := 0.5
private def fNegHalf : Float := -0.5
private def f6 : Float := 6.0
private def f09 : Float := 0.9
private def eps12 : Float := 1e-12
private def eps15 : Float := 1e-15
private def eps18 : Float := 1e-18
private def eps24 : Float := 1e-24

private def zeroV3 : Values Float 3 := Values.replicate f0
private def zeroV4 : Values Float 4 := Values.replicate f0
private def zeroV6 : Values Float 6 := Values.replicate f0
private def zeroV8 : Values Float 8 := Values.replicate f0
private def zeroMat4 : FloatArray := (Values.replicate (n := 16) f0).data
private def idMat4 : FloatArray :=
  (((zeroMat4.set! 0 f1).set! 5 f1).set! 10 f1).set! 15 f1

/-- Build a `Values Float 3` from 3 unboxed floats (1 copy + 2 in-place stores). -/
@[inline] private def vals3 (a b c : Float) : Values Float 3 :=
  ((zeroV3.set ⟨0, by decide⟩ a).set ⟨1, by decide⟩ b).set ⟨2, by decide⟩ c

/-- Build a `Values Float 4` from 4 unboxed floats (1 copy + 3 in-place stores). -/
@[inline] private def vals4 (a b c d : Float) : Values Float 4 :=
  (((zeroV4.set ⟨0, by decide⟩ a).set ⟨1, by decide⟩ b).set ⟨2, by decide⟩ c).set ⟨3, by decide⟩ d

/-- Build a `Values Float 6` from 6 unboxed floats (1 copy + 5 in-place stores). -/
@[inline] private def vals6 (a b c d e f : Float) : Values Float 6 :=
  (((((zeroV6.set ⟨0, by decide⟩ a).set ⟨1, by decide⟩ b).set ⟨2, by decide⟩ c).set
    ⟨3, by decide⟩ d).set ⟨4, by decide⟩ e).set ⟨5, by decide⟩ f

/-- Build a `Values Float 8` from 8 unboxed floats (1 copy + 7 in-place stores). -/
@[inline] private def vals8 (a b c d e f g h : Float) : Values Float 8 :=
  (((((((zeroV8.set ⟨0, by decide⟩ a).set ⟨1, by decide⟩ b).set ⟨2, by decide⟩ c).set
    ⟨3, by decide⟩ d).set ⟨4, by decide⟩ e).set ⟨5, by decide⟩ f).set ⟨6, by decide⟩ g).set
    ⟨7, by decide⟩ h

/-! ## 2D Projective Geometric Algebra (`PGA2 := D!"0,1,1"`) -/

/-- A 2D PGA line `c·e0 + a·e1 + b·e2` (`a x + b y + c = 0`). -/
abbrev Line2 := Chain PGA2 1 Float

/-- A 2D PGA point `!(e0 + x·e1 + y·e2) = y·e01 - x·e02 + e12`. -/
abbrev Point2 := Chain PGA2 2 Float

/-- A 2D PGA motor `[s, e01, e02, e12]`. -/
abbrev Motor2 := Spinor PGA2 Float

/-- Line `a·x + b·y + c = 0` in `PGA2`. -/
@[inline] def mkLine2 (a b c : Float) : Line2 := ⟨vals3 c a b⟩

/-- Finite point `(x, y)` in `PGA2`: `!(e0 + x·e1 + y·e2) = y·e01 - x·e02 + 1·e12`. -/
@[inline] def mkPoint2 (x y : Float) : Point2 := ⟨vals3 y (-x) 1.0⟩

/-- Ideal direction `(dx, dy)` in `PGA2` (`e12 = 0`). -/
@[inline] def mkDir2 (dx dy : Float) : Point2 := ⟨vals3 dy (-dx) 0.0⟩

/-- Extract Euclidean `(x, y)` of a `PGA2` point (`none` for ideal points). -/
@[inline] def point2Coords? (p : Point2) : Option (Float × Float) :=
  let w := p.v.get! 2
  if w.abs < 1e-12 then none
  else
    let invW := 1.0 / w
    some (-(p.v.get! 1) * invW, (p.v.get! 0) * invW)

/-- Normalize a `PGA2` line so `a² + b² = 1`. -/
@[inline] def normalizeLine2 (l : Line2) : Line2 :=
  let c := l.v.get! 0; let a := l.v.get! 1; let b := l.v.get! 2
  let n := Float.sqrt (a * a + b * b)
  if n < 1e-15 then l else let invN := 1.0 / n; ⟨vals3 (c * invN) (a * invN) (b * invN)⟩

/-- Normalize a `PGA2` point so `e12 = 1` (or Euclidean norm 1 for ideal points). -/
@[inline] def normalizePoint2 (p : Point2) : Point2 :=
  let p01 := p.v.get! 0; let p02 := p.v.get! 1; let w := p.v.get! 2
  if w.abs ≥ 1e-15 then
    let invW := 1.0 / w
    ⟨vals3 (p01 * invW) (p02 * invW) 1.0⟩
  else
    let n := Float.sqrt (p01 * p01 + p02 * p02)
    if n < 1e-15 then p else let invN := 1.0 / n; ⟨vals3 (p01 * invN) (p02 * invN) 0.0⟩

/-- Regressive join of two `PGA2` points (`P & Q`), yielding the line through them. -/
@[inline] def joinPoints2 (p q : Point2) : Line2 := p ∨ q

/-- Exterior meet of two `PGA2` lines (`L1 ^ L2`), yielding their intersection point. -/
@[inline] def meetLines2 (l1 l2 : Line2) : Point2 := l1 ∧ l2

/-- Orthogonal line through point `P` perpendicular to line `L` (`L << P` in `ganja.js`). -/
@[inline] def orthoLineThrough2 (l : Line2) (p : Point2) : Line2 :=
  dorstLDotChain l p

/-- 2D PGA counter-clockwise rotor around `(x, y)` by `angle` radians (`exp(-½ θ P)`). -/
@[inline] def rotor2 (x y angle : Float) : Motor2 :=
  let h := 0.5 * angle
  let s := Float.sin h
  ⟨vals4 (Float.cos h) (-s * y) (s * x) (-s)⟩

/-- 2D PGA translator by `(dx, dy)`. -/
@[inline] def translator2 (dx dy : Float) : Motor2 :=
  ⟨vals4 1.0 (-0.5 * dx) (-0.5 * dy) 0.0⟩

/-- Closed-form exponential of a `PGA2` bivector `[b01, b02, b12]`. -/
@[inline] def motorExp2 (b : Chain PGA2 2 Float) : Motor2 :=
  let b01 := b.v.get! 0; let b02 := b.v.get! 1; let b12 := b.v.get! 2
  let θ := b12.abs
  if θ < 1e-12 then ⟨vals4 1.0 b01 b02 0.0⟩
  else
    let a := Float.sin θ / θ
    ⟨vals4 (Float.cos θ) (a * b01) (a * b02) (a * b12)⟩

/-- Apply a `PGA2` motor to a point (`M >>> P`). -/
@[inline] def applyMotor2Point (m : Motor2) (p : Point2) : Point2 := m >>> p

/-- Apply a `PGA2` motor to a line (`M >>> L`). -/
@[inline] def applyMotor2Line (m : Motor2) (l : Line2) : Line2 := m >>> l

/-! ## 3D Projective Geometric Algebra (`PGA3 := D!"0,1,1,1"`) -/

/-- A 3D PGA plane `d·e0 + nx·e1 + ny·e2 + nz·e3` (`nx·x + ny·y + nz·z + d = 0`). -/
abbrev Plane3 := Chain PGA3 1 Float

/-- A 3D PGA Plücker line `[e01, e02, e03, e12, e13, e23]`. -/
abbrev Line3 := Chain PGA3 2 Float

/-- A 3D PGA point `!(e0 + x·e1 + y·e2 + z·e3) = -z·e012 + y·e013 - x·e023 + e123`. -/
abbrev Point3 := Chain PGA3 3 Float

/-- A 3D PGA even motor `[s, e01, e02, e03, e12, e13, e23, e0123]` (exact `GSIR` v1 wire order). -/
abbrev Motor3 := Spinor PGA3 Float

/-- Plane `nx·x + ny·y + nz·z + d = 0` in `PGA3`. -/
@[inline] def mkPlane3 (nx ny nz d : Float) : Plane3 := ⟨vals4 d nx ny nz⟩

/-- Plane through Euclidean point `(px, py, pz)` with normal `(nx, ny, nz)`. -/
@[inline] def mkPlane3PointNormal (px py pz nx ny nz : Float) : Plane3 :=
  let len := Float.sqrt (nx * nx + ny * ny + nz * nz)
  if len < 1e-15 then ⟨vals4 0.0 0.0 1.0 0.0⟩
  else
    let invL := 1.0 / len
    let ux := nx * invL; let uy := ny * invL; let uz := nz * invL
    ⟨vals4 (-(ux * px + uy * py + uz * pz)) ux uy uz⟩

/-- Finite 3D point `(x, y, z)` in `PGA3`: `!(e0 + x·e1 + y·e2 + z·e3)`. -/
@[inline] def mkPoint3 (x y z : Float) : Point3 := ⟨vals4 (-z) y (-x) 1.0⟩

/-- Ideal 3D direction `(dx, dy, dz)` in `PGA3` (`e123 = 0`). -/
@[inline] def mkDir3 (dx dy dz : Float) : Point3 := ⟨vals4 (-dz) dy (-dx) 0.0⟩

/-- Extract Euclidean `(x, y, z)` of a `PGA3` point (`none` for ideal points). -/
@[inline] def point3Coords? (p : Point3) : Option (Float × Float × Float) :=
  let w := p.v.get! 3
  if w.abs < 1e-12 then none
  else
    let invW := 1.0 / w
    some (-(p.v.get! 2) * invW, (p.v.get! 1) * invW, -(p.v.get! 0) * invW)

/-- Normalize a `PGA3` plane so `nx² + ny² + nz² = 1`. -/
@[inline] def normalizePlane3 (π : Plane3) : Plane3 :=
  let d := π.v.get! 0; let nx := π.v.get! 1; let ny := π.v.get! 2; let nz := π.v.get! 3
  let n := Float.sqrt (nx * nx + ny * ny + nz * nz)
  if n < 1e-15 then π else let invN := 1.0 / n; ⟨vals4 (d * invN) (nx * invN) (ny * invN) (nz * invN)⟩

/-- Normalize a `PGA3` point so `e123 = 1` (or unit direction if ideal). -/
@[inline] def normalizePoint3 (p : Point3) : Point3 :=
  let p0 := p.v.get! 0; let p1 := p.v.get! 1; let p2 := p.v.get! 2; let w := p.v.get! 3
  if w.abs ≥ 1e-15 then
    let invW := 1.0 / w
    ⟨vals4 (p0 * invW) (p1 * invW) (p2 * invW) 1.0⟩
  else
    let n := Float.sqrt (p0 * p0 + p1 * p1 + p2 * p2)
    if n < 1e-15 then p else let invN := 1.0 / n; ⟨vals4 (p0 * invN) (p1 * invN) (p2 * invN) 0.0⟩

/-- Regressive join of two 3D points (`P & Q`), yielding the Plücker line through them. -/
@[inline] def joinPoints3 (p q : Point3) : Line3 := p ∨ q

/-- Regressive join of a 3D point and a 3D line (`P & L`), yielding their plane. -/
@[inline] def joinPointLine3 (p : Point3) (l : Line3) : Plane3 := p ∨ l

/-- Regressive join of three 3D points (`P & Q & R`), yielding their plane. -/
@[inline] def join3Points3 (p q r : Point3) : Plane3 := (p ∨ q) ∨ r

/-- Exterior meet of two 3D planes (`π₁ ^ π₂`), yielding their intersection line. -/
@[inline] def meetPlanes3 (p1 p2 : Plane3) : Line3 := p1 ∧ p2

/-- Exterior meet of a 3D plane and a 3D line (`π ^ L`), yielding their intersection point. -/
@[inline] def meetPlaneLine3 (π : Plane3) (l : Line3) : Point3 := π ∧ l

/-- Exterior meet of three 3D planes (`π₁ ^ π₂ ^ π₃`), yielding their intersection point. -/
@[inline] def meet3Planes3 (p1 p2 p3 : Plane3) : Point3 := (p1 ∧ p2) ∧ p3

/-- Signed distance from a unit `PGA3` point `(x, y, z)` to a normalized plane `π`. -/
@[inline] def signedDistPlanePoint (π : Plane3) (x y z : Float) : Float :=
  π.v.get! 1 * x + π.v.get! 2 * y + π.v.get! 3 * z + π.v.get! 0

/-- Extract Plücker origin (closest point to world origin) and unit direction of a `PGA3` line
(`none` for ideal lines at infinity). -/
def line3OriginDir? (l : Line3) : Option ((Float × Float × Float) × (Float × Float × Float)) :=
  let mx := l.v.get! 0; let my := l.v.get! 1; let mz := l.v.get! 2
  let dx := l.v.get! 5; let dy := -(l.v.get! 4); let dz := l.v.get! 3
  let n2 := dx * dx + dy * dy + dz * dz
  if n2 < 1e-18 then none
  else
    let invN2 := 1.0 / n2
    let invN := Float.sqrt invN2
    -- Closest point to origin: (dir × mom) / ‖dir‖²
    let ox := (dy * mz - dz * my) * invN2
    let oy := (dz * mx - dx * mz) * invN2
    let oz := (dx * my - dy * mx) * invN2
    some ((ox, oy, oz), (dx * invN, dy * invN, dz * invN))

/-- Extract plane origin (closest point to world origin) and orthonormal tangent basis `(u, v)`
such that `u × v = n` (`none` for the ideal plane `e0`). -/
def plane3Frame? (π : Plane3) :
    Option ((Float × Float × Float) × (Float × Float × Float) × (Float × Float × Float)) :=
  let d := π.v.get! 0; let nx := π.v.get! 1; let ny := π.v.get! 2; let nz := π.v.get! 3
  let n2 := nx * nx + ny * ny + nz * nz
  if n2 < 1e-18 then none
  else
    let invN := 1.0 / Float.sqrt n2
    let ux := nx * invN; let uy := ny * invN; let uz := nz * invN
    let dn := d * invN
    let ox := -dn * ux; let oy := -dn * uy; let oz := -dn * uz
    -- Pick a non-collinear reference axis to form orthonormal tangent frame (t1, t2)
    let (rx, ry, rz) := if ux.abs < 0.9 then (1.0, 0.0, 0.0) else (0.0, 1.0, 0.0)
    -- t1 = normalize(r × n) or normalize(n × r); choose t1 × t2 = n:
    let tx := ry * uz - rz * uy
    let ty := rz * ux - rx * uz
    let tz := rx * uy - ry * ux
    let tLen := Float.sqrt (tx * tx + ty * ty + tz * tz)
    let invT := 1.0 / tLen
    let t1x := tx * invT; let t1y := ty * invT; let t1z := tz * invT
    -- t2 = n × t1 so that t1 × t2 = t1 × (n × t1) = n
    let t2x := uy * t1z - uz * t1y
    let t2y := uz * t1x - ux * t1z
    let t2z := ux * t1y - uy * t1x
    some ((ox, oy, oz), (t1x, t1y, t1z), (t2x, t2y, t2z))

/-- Normalize a `PGA3` Plücker line so `‖dir‖ = 1` and `dir · mom = 0` (Study condition). -/
def normalizeLine3 (l : Line3) : Line3 :=
  let b01 := l.v.get! 0; let b02 := l.v.get! 1; let b03 := l.v.get! 2
  let b12 := l.v.get! 3; let b13 := l.v.get! 4; let b23 := l.v.get! 5
  let n2 := b12 * b12 + b13 * b13 + b23 * b23
  if n2 < 1e-18 then
    let m2 := b01 * b01 + b02 * b02 + b03 * b03
    if m2 < 1e-18 then l
    else let invM := 1.0 / Float.sqrt m2; ⟨vals6 (b01 * invM) (b02 * invM) (b03 * invM) 0.0 0.0 0.0⟩
  else
    let invN := 1.0 / Float.sqrt n2
    let p := (b12 * b03 - b13 * b02 + b23 * b01) / n2
    let e01 := (b01 - p * b23) * invN
    let e02 := (b02 + p * b13) * invN
    let e03 := (b03 - p * b12) * invN
    ⟨vals6 e01 e02 e03 (b12 * invN) (b13 * invN) (b23 * invN)⟩

/-! ## PGA3 Motors: Constructors, Study Normalization, Closed-Form `Exp`/`Log`/SLERP -/

/-- Identity `PGA3` motor `1`. -/
@[inline] def identityMotor3 : Motor3 := ⟨vals8 1.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0⟩

/-- Embed a `PGA3` Plücker bivector `Line3` directly as a pure-grade-2 `Motor3`. -/
@[inline] def line3ToMotor3 (b : Line3) : Motor3 :=
  ⟨vals8 0.0 (b.v.get! 0) (b.v.get! 1) (b.v.get! 2) (b.v.get! 3) (b.v.get! 4) (b.v.get! 5) 0.0⟩

/-- Right-handed `PGA3` rotation motor around axis `(ax, ay, az)` by `angle` radians. -/
@[inline] def rotor3 (ax ay az angle : Float) : Motor3 :=
  let len := Float.sqrt (ax * ax + ay * ay + az * az)
  if len < 1e-15 then identityMotor3
  else
    let h := 0.5 * angle
    let s := Float.sin h / len
    ⟨vals8 (Float.cos h) 0.0 0.0 0.0 (-az * s) (ay * s) (-ax * s) 0.0⟩

/-- `PGA3` translation motor by `(dx, dy, dz)`: `1 - ½(dx·e01 + dy·e02 + dz·e03)`. -/
@[inline] def translator3 (dx dy dz : Float) : Motor3 :=
  ⟨vals8 1.0 (-0.5 * dx) (-0.5 * dy) (-0.5 * dz) 0.0 0.0 0.0 0.0⟩

/-- Squared Euclidean norm `s² + e12² + e13² + e23²` of a `PGA3` motor. -/
@[inline] def motorNormSq (m : Motor3) : Float :=
  let s := m.v.get! 0; let e12 := m.v.get! 4; let e13 := m.v.get! 5; let e23 := m.v.get! 6
  s * s + e12 * e12 + e13 * e13 + e23 * e23

/-- Study invariant `s·e0123 - e01·e23 + e02·e13 - e03·e12` (`M * ~M = normSq + 2·study·e0123`). -/
@[inline] def motorStudy (m : Motor3) : Float :=
  m.v.get! 0 * m.v.get! 7 - m.v.get! 1 * m.v.get! 6 +
    m.v.get! 2 * m.v.get! 5 - m.v.get! 3 * m.v.get! 4

/-- Check whether `m` is a valid rigid motor within tolerance `tol` (positive norm and Study
condition `|2·study| ≤ tol · normSq`, salvaging the v1 CABI check). -/
@[inline] def motorIsValid (m : Motor3) (tol : Float := 1e-9) : Bool :=
  let q := motorNormSq m
  let st := motorStudy m
  q.isFinite && st.isFinite && q > tol && (2.0 * st).abs ≤ tol * q

/-- Project and normalize a `PGA3` motor onto the Study quadric so `M * ~M = 1` exactly. -/
@[inline] def normalizeMotor3 (m : Motor3) : Motor3 :=
  let s := m.v.get! 0; let e01 := m.v.get! 1; let e02 := m.v.get! 2; let e03 := m.v.get! 3
  let e12 := m.v.get! 4; let e13 := m.v.get! 5; let e23 := m.v.get! 6; let e0123 := m.v.get! 7
  let q := s * s + e12 * e12 + e13 * e13 + e23 * e23
  if q < eps18 then identityMotor3
  else
    let invN := f1 / Float.sqrt q
    let d := -(s * e0123 - e01 * e23 + e02 * e13 - e03 * e12) / q
    ⟨vals8
      (s * invN)
      ((e01 - e23 * d) * invN)
      ((e02 + e13 * d) * invN)
      ((e03 - e12 * d) * invN)
      (e12 * invN)
      (e13 * invN)
      (e23 * invN)
      ((e0123 + s * d) * invN)⟩

/-- Closed-form `O(1)` exponential `exp(B)` of any `PGA3` bivector `B = [e01, e02, e03, e12, e13, e23]`
(handles pure rotations, pure translations, and general Chasles screws without series loops). -/
@[inline] def motorExp (b : Line3) : Motor3 :=
  let b01 := b.v.get! 0; let b02 := b.v.get! 1; let b03 := b.v.get! 2
  let b12 := b.v.get! 3; let b13 := b.v.get! 4; let b23 := b.v.get! 5
  let θ2 := b12 * b12 + b13 * b13 + b23 * b23
  if θ2 < eps24 then
    -- Pure translation (B² = 0)
    ⟨vals8 f1 b01 b02 b03 f0 f0 f0 f0⟩
  else
    let θ := Float.sqrt θ2
    let c := Float.cos θ
    let a := Float.sin θ / θ
    let p := b12 * b03 - b13 * b02 + b23 * b01
    let k := p * (a - c) / θ2
    -- ε · B_e = -b23·e01 + b13·e02 - b12·e03
    ⟨vals8
      c
      (a * b01 - k * b23)
      (a * b02 + k * b13)
      (a * b03 - k * b12)
      (a * b12)
      (a * b13)
      (a * b23)
      (p * a)⟩

/-- Closed-form `O(1)` principal logarithm `log(M)` of a unit `PGA3` motor `M`, satisfying
`motorExp (motorLog M) = ±M` (choosing the shortest-path branch with `s ≥ 0`). -/
@[inline] def motorLog (m : Motor3) : Line3 :=
  let m := normalizeMotor3 m
  let flip := if m.v.get! 0 < f0 then -f1 else f1
  let s := flip * m.v.get! 0
  let e01 := flip * m.v.get! 1; let e02 := flip * m.v.get! 2; let e03 := flip * m.v.get! 3
  let e12 := flip * m.v.get! 4; let e13 := flip * m.v.get! 5; let e23 := flip * m.v.get! 6
  let e0123 := flip * m.v.get! 7
  let u2 := e12 * e12 + e13 * e13 + e23 * e23
  if u2 < eps24 then
    -- Pure translation
    let invS := if s.abs < eps15 then f1 else f1 / s
    ⟨vals6 (e01 * invS) (e02 * invS) (e03 * invS) f0 f0 f0⟩
  else
    let u := Float.sqrt u2
    let θ := Float.atan2 u s
    let invA := θ / u
    let b12 := e12 * invA; let b13 := e13 * invA; let b23 := e23 * invA
    let p := e0123 * invA
    let a := u / θ
    let k := p * (a - s) / (θ * θ)
    ⟨vals6
      ((e01 + k * b23) * invA)
      ((e02 - k * b13) * invA)
      ((e03 + k * b12) * invA)
      b12 b13 b23⟩

/-- Screw Linear Interpolation (ScLERP) between two `PGA3` motors: `m1 * exp(t · log(~m1 * m2))`. -/
@[inline] def motorSlerp (m1 m2 : Motor3) (t : Float) : Motor3 :=
  let rel : Motor3 := (~m1) * m2
  let logRel := motorLog rel
  normalizeMotor3 (m1 * motorExp (t • logRel))

/-- Split a general `PGA3` bivector `B` into commuting pure-rotation and pure-translation
bivectors `(B_rot, B_trans)` such that `B = B_rot + B_trans` and `B_rot * B_trans = B_trans * B_rot`
(Chasles invariant split). -/
def bivectorSplit (b : Line3) : Line3 × Line3 :=
  let b01 := b.v.get! 0; let b02 := b.v.get! 1; let b03 := b.v.get! 2
  let b12 := b.v.get! 3; let b13 := b.v.get! 4; let b23 := b.v.get! 5
  let n2 := b12 * b12 + b13 * b13 + b23 * b23
  if n2 < eps24 then
    (⟨zeroV6⟩, b)
  else
    let p := (b12 * b03 - b13 * b02 + b23 * b01) / n2
    -- Pure translation along the screw axis: -(p) · (ε · B_e) = p·b23·e01 - p·b13·e02 + p·b12·e03
    let t01 := p * b23; let t02 := -p * b13; let t03 := p * b12
    (⟨vals6 (b01 - t01) (b02 - t02) (b03 - t03) b12 b13 b23⟩,
     ⟨vals6 t01 t02 t03 f0 f0 f0⟩)

/-- Apply a `PGA3` motor to a 3D point (`M >>> P`). -/
@[inline] def applyMotor3Point (m : Motor3) (p : Point3) : Point3 := m >>> p

/-- Apply a `PGA3` motor to a 3D line (`M >>> L`). -/
@[inline] def applyMotor3Line (m : Motor3) (l : Line3) : Line3 := m >>> l

/-- Apply a `PGA3` motor to a 3D plane (`M >>> π`). -/
@[inline] def applyMotor3Plane (m : Motor3) (π : Plane3) : Plane3 := m >>> π

/-! ## Motor → Column-Major 4×4 Matrix & Flat XYZ Batch Transform -/

/-- Extract the column-major 4×4 affine matrix (16 floats, matching `GSIR` v1 / WebGL / Metal /
RealityKit) representing `p ↦ M >>> p` for a `PGA3` motor `M` in wire order
`[s, e01, e02, e03, e12, e13, e23, e0123]`. -/
def motorToMat4 (m : Motor3) : FloatArray :=
  let s := m.v.get! 0; let e01 := m.v.get! 1; let e02 := m.v.get! 2; let e03 := m.v.get! 3
  let e12 := m.v.get! 4; let e13 := m.v.get! 5; let e23 := m.v.get! 6; let e0123 := m.v.get! 7
  let q := s * s + e12 * e12 + e13 * e13 + e23 * e23
  if q < eps18 then
    idMat4
  else
    let invQ := f1 / q
    let qw := s; let qx := -e23; let qy := e13; let qz := -e12
    -- Rotation columns (normalized by 1/q)
    let r00 := (qw * qw + qx * qx - qy * qy - qz * qz) * invQ
    let r10 := f2 * (qx * qy + qw * qz) * invQ
    let r20 := f2 * (qx * qz - qw * qy) * invQ
    let r01 := f2 * (qx * qy - qw * qz) * invQ
    let r11 := (qw * qw - qx * qx + qy * qy - qz * qz) * invQ
    let r21 := f2 * (qy * qz + qw * qx) * invQ
    let r02 := f2 * (qx * qz + qw * qy) * invQ
    let r12 := f2 * (qy * qz - qw * qx) * invQ
    let r22 := (qw * qw - qx * qx - qy * qy + qz * qz) * invQ
    -- Translation column (image of origin under M >>> e123)
    let tx := fNeg2 * (s * e01 + e12 * e02 + e13 * e03 + e23 * e0123) * invQ
    let ty := f2 * (-s * e02 + e12 * e01 - e23 * e03 + e13 * e0123) * invQ
    let tz := fNeg2 * (s * e03 - e13 * e01 - e23 * e02 + e12 * e0123) * invQ
    let a := (((zeroMat4.set! 0 r00).set! 1 r10).set! 2 r20).set! 3 f0
    let a := (((a.set! 4 r01).set! 5 r11).set! 6 r21).set! 7 f0
    let a := (((a.set! 8 r02).set! 9 r12).set! 10 r22).set! 11 f0
    (((a.set! 12 tx).set! 13 ty).set! 14 tz).set! 15 f1

/-- Tail-recursive flat XYZ batch transform loop (`3*k` floats). -/
private def transformXYZLoop (r00 r01 r02 tx r10 r11 r12 ty r20 r21 r22 tz : Float)
    (xyz : FloatArray) (i n : Nat) (out : FloatArray) : FloatArray :=
  if i + 2 < n then
    let x := xyz.get! i
    let y := xyz.get! (i + 1)
    let z := xyz.get! (i + 2)
    let ox := r00 * x + r01 * y + r02 * z + tx
    let oy := r10 * x + r11 * y + r12 * z + ty
    let oz := r20 * x + r21 * y + r22 * z + tz
    transformXYZLoop r00 r01 r02 tx r10 r11 r12 ty r20 r21 r22 tz xyz (i + 3) n
      (((out.push ox).push oy).push oz)
  else out
termination_by n - i

/-- Transform a flat packed `FloatArray` `[x₀, y₀, z₀, x₁, y₁, z₁, …]` by a `PGA3` motor in one
unboxed pass (extracting the 3×4 affine rows once). -/
def transformXYZBatch (m : Motor3) (xyz : FloatArray) : FloatArray :=
  let mat := motorToMat4 m
  let n := xyz.size
  transformXYZLoop
    (mat.get! 0) (mat.get! 4) (mat.get! 8)  (mat.get! 12)
    (mat.get! 1) (mat.get! 5) (mat.get! 9)  (mat.get! 13)
    (mat.get! 2) (mat.get! 6) (mat.get! 10) (mat.get! 14)
    xyz 0 n (FloatArray.emptyWithCapacity n)

/-! ## PGA3 Rigid-Body Dynamics (`Adapode` RK4 Compatible) -/

/-- Rigid-body state in `PGA3` (Gunn / De Keninck formulation):
pose `motor : Motor3`, body-frame velocity bivector `vel : Line3`, mass, and principal
moments of inertia `(ix, iy, iz)`. -/
structure RigidBody3 where
  /-- Current pose motor `M` (body → world). -/
  motor : Motor3
  /-- Body-frame velocity bivector `B = [vx, vy, vz, ωz, -ωy, ωx]`. -/
  vel : Line3
  /-- Rigid body mass (`> 0`). -/
  mass : Float := 1.0
  /-- Principal moments of inertia `(Ix, Iy, Iz)`. -/
  ix : Float := 1.0
  iy : Float := 1.0
  iz : Float := 1.0

/-- Body-frame inertia map `B ↦ P` (dualized momentum bivector in body coordinates). -/
@[inline] def inertiaMap (mass ix iy iz : Float) (b : Line3) : Line3 :=
  -- Rotational part (e12↔z, e13↔-y, e23↔x) scaled by (Iz, Iy, Ix); linear (e01,e02,e03) by mass
  ⟨vals6
    (mass * b.v.get! 0) (mass * b.v.get! 1) (mass * b.v.get! 2)
    (iz * b.v.get! 3)   (iy * b.v.get! 4)   (ix * b.v.get! 5)⟩

/-- Inverse body-frame inertia map `P ↦ B`. -/
@[inline] def inertiaInv (mass ix iy iz : Float) (p : Line3) : Line3 :=
  ⟨vals6
    (p.v.get! 0 / mass) (p.v.get! 1 / mass) (p.v.get! 2 / mass)
    (p.v.get! 3 / iz)   (p.v.get! 4 / iy)   (p.v.get! 5 / ix)⟩

/-- Commutator product `½(A * B - B * A)` of two `PGA3` bivectors (Lie bracket of `se(3)`). -/
@[inline] def bivectorCommutator (a b : Line3) : Line3 :=
  let a01 := a.v.get! 0; let a02 := a.v.get! 1; let a03 := a.v.get! 2
  let a12 := a.v.get! 3; let a13 := a.v.get! 4; let a23 := a.v.get! 5
  let b01 := b.v.get! 0; let b02 := b.v.get! 1; let b03 := b.v.get! 2
  let b12 := b.v.get! 3; let b13 := b.v.get! 4; let b23 := b.v.get! 5
  -- [a, b] in se(3): exact grade-2 part of ½(a*b - b*a)
  let c01 := (a02 * b12 - a12 * b02) + (a03 * b13 - a13 * b03)
  let c02 := -(a01 * b12 - a12 * b01) + (a03 * b23 - a23 * b03)
  let c03 := -(a01 * b13 - a13 * b01) - (a02 * b23 - a23 * b02)
  let c12 := (a13 * b23 - a23 * b13)
  let c13 := -(a12 * b23 - a23 * b12)
  let c23 := (a12 * b13 - a13 * b12)
  ⟨vals6 c01 c02 c03 c12 c13 c23⟩

/-- Euler-Poincaré derivative `(dM/dt, dB/dt)` for a rigid body with external world-frame
forque `forqueWorld : Motor3 → Line3 → Line3` (e.g. gravity/springs; pass zero for a free top). -/
def rigidBodyDeriv (mass ix iy iz : Float) (forqueWorld : Motor3 → Line3 → Line3)
    (m : Motor3) (b : Line3) : Motor3 × Line3 :=
  let dM : Motor3 := (-0.5 : Float) • (m * b.toHalf)
  let fBody : Line3 := (~m) >>> (forqueWorld m b)
  -- Euler's equation in body frame: dP/dt = P × B + F_body = [P, B] + F_body (using angular/linear cross)
  let wx := -b.v.get! 5; let wy := b.v.get! 4; let wz := -b.v.get! 3
  let lx := -b.v.get! 0; let ly := -b.v.get! 1; let lz := -b.v.get! 2
  -- Torque cross ω × (I ω) and linear coriolis ω × (m v)
  let tx := (iy - iz) * wy * wz
  let ty := (iz - ix) * wz * wx
  let tz := (ix - iy) * wx * wy
  let fx := mass * (wy * lz - wz * ly)
  let fy := mass * (wz * lx - wx * lz)
  let fz := mass * (wx * ly - wy * lx)
  let dP : Line3 := ⟨vals6
    (-fx + fBody.v.get! 0) (-fy + fBody.v.get! 1) (-fz + fBody.v.get! 2)
    (-tz + fBody.v.get! 3) ( ty + fBody.v.get! 4) (-tx + fBody.v.get! 5)⟩
  (dM, inertiaInv mass ix iy iz dP)

/-- Pack a `RigidBody3` state into a 14-float flat `FloatArray` (for `Adapode` ODE solvers). -/
def rigidBodyPack (rb : RigidBody3) : FloatArray :=
  let a := FloatArray.emptyWithCapacity 14
  let a := (((a.push (rb.motor.v.get! 0)).push (rb.motor.v.get! 1)).push (rb.motor.v.get! 2)).push (rb.motor.v.get! 3)
  let a := (((a.push (rb.motor.v.get! 4)).push (rb.motor.v.get! 5)).push (rb.motor.v.get! 6)).push (rb.motor.v.get! 7)
  let a := ((a.push (rb.vel.v.get! 0)).push (rb.vel.v.get! 1)).push (rb.vel.v.get! 2)
  ((a.push (rb.vel.v.get! 3)).push (rb.vel.v.get! 4)).push (rb.vel.v.get! 5)

/-- Unpack a 14-float flat `FloatArray` back into `(Motor3, Line3)`. -/
def rigidBodyUnpack (x : FloatArray) : Motor3 × Line3 :=
  (⟨vals8 (x.get! 0) (x.get! 1) (x.get! 2) (x.get! 3) (x.get! 4) (x.get! 5) (x.get! 6) (x.get! 7)⟩,
   ⟨vals6 (x.get! 8) (x.get! 9) (x.get! 10) (x.get! 11) (x.get! 12) (x.get! 13)⟩)

/-- Advance a `RigidBody3` by one classical 4th-order Runge-Kutta step of size `dt`, re-projecting
the motor onto the Study quadric (`M * ~M = 1`). -/
def rigidBodyStepRK4 (rb : RigidBody3) (forqueWorld : Motor3 → Line3 → Line3) (dt : Float) :
    RigidBody3 :=
  let stepM := fun (m dm : Motor3) (h : Float) => m + h • dm
  let stepB := fun (b db : Line3) (h : Float) => b + h • db
  let (dm1, db1) := rigidBodyDeriv rb.mass rb.ix rb.iy rb.iz forqueWorld rb.motor rb.vel
  let (dm2, db2) := rigidBodyDeriv rb.mass rb.ix rb.iy rb.iz forqueWorld
    (stepM rb.motor dm1 (0.5 * dt)) (stepB rb.vel db1 (0.5 * dt))
  let (dm3, db3) := rigidBodyDeriv rb.mass rb.ix rb.iy rb.iz forqueWorld
    (stepM rb.motor dm2 (0.5 * dt)) (stepB rb.vel db2 (0.5 * dt))
  let (dm4, db4) := rigidBodyDeriv rb.mass rb.ix rb.iy rb.iz forqueWorld
    (stepM rb.motor dm3 dt) (stepB rb.vel db3 dt)
  let c := dt / 6.0
  let mNext := normalizeMotor3 (rb.motor + c • (dm1 + (2.0 : Float) • dm2 + (2.0 : Float) • dm3 + dm4))
  let bNext := rb.vel + c • (db1 + (2.0 : Float) • db2 + (2.0 : Float) • db3 + db4)
  { rb with motor := mNext, vel := bNext }

/-- Total rotational + translational kinetic energy `½(m‖v‖² + Ix ωx² + Iy ωy² + Iz ωz²)` (an
exact invariant for a torque-free rigid body). -/
def rigidBodyKineticEnergy (rb : RigidBody3) : Float :=
  let lx := rb.vel.v.get! 0; let ly := rb.vel.v.get! 1; let lz := rb.vel.v.get! 2
  let wz := rb.vel.v.get! 3; let wy := rb.vel.v.get! 4; let wx := rb.vel.v.get! 5
  0.5 * (rb.mass * (lx * lx + ly * ly + lz * lz) +
         rb.ix * wx * wx + rb.iy * wy * wy + rb.iz * wz * wz)

/-! ## Exact PGA3 Triangle-Mesh Plane Slicing (`#pga3d_slicing`)

Slices any indexed triangle mesh `(positions, indices)` by a `PGA3` plane `π`, producing:
1. Two cleanly clipped, CCW-wound 3D triangle half-meshes (`posHalf` with `d ≥ 0` and
   `negHalf` with `d ≤ 0`), with flat/face normals computed in Lean.
2. Exact 3D cut segments `π ∧ (P_i ∨ P_j)` packed as `FloatArray`.
3. Stitched 2D slice contour polylines projected into the plane's orthonormal frame `(origin, u, v)`,
   ready for `GSIR` `0x0F CONTOUR_OVERLAY`! -/

/-- A packed 3D triangle mesh (CCW front-face winding, matching `GSIR` `0x0B MESH_ASSETS`). -/
structure ClippedMesh where
  /-- Packed vertex positions `[x₀, y₀, z₀, …]`. -/
  positions : FloatArray
  /-- Packed vertex normals `[nx₀, ny₀, nz₀, …]`. -/
  normals : FloatArray
  /-- CCW triangle vertex indices. -/
  indices : Array UInt32
  deriving Inhabited

/-- Complete result of slicing a 3D triangle mesh by a `PGA3` plane `π`. -/
structure MeshSliceResult where
  /-- Clipped half-mesh on the positive side (`signedDist ≥ 0`). -/
  posHalf : ClippedMesh
  /-- Clipped half-mesh on the negative side (`signedDist ≤ 0`). -/
  negHalf : ClippedMesh
  /-- Raw 3D intersection segments packed as `[ax, ay, az, bx, by, bz, …]`. -/
  contourSegments3D : FloatArray
  /-- Stitched 2D contour polylines in plane `(u, v)` coordinates (each packed `[x₀, y₀, …]`). -/
  contourPolylines2D : Array FloatArray
  /-- Plane origin (closest point on plane to world origin). -/
  planeOrigin : Float × Float × Float
  /-- Orthonormal tangent vector `u` in the slicing plane. -/
  planeU : Float × Float × Float
  /-- Orthonormal tangent vector `v` in the slicing plane (`u × v = n`). -/
  planeV : Float × Float × Float
  deriving Inhabited

/-- Append one CCW triangle `(a, b, c)` with its normalized face normal to a `ClippedMesh`. -/
private def pushTri (m : ClippedMesh)
    (ax ay az bx by_ bz cx cy cz : Float) : ClippedMesh :=
  let e1x := bx - ax; let e1y := by_ - ay; let e1z := bz - az
  let e2x := cx - ax; let e2y := cy - ay; let e2z := cz - az
  let nx := e1y * e2z - e1z * e2y
  let ny := e1z * e2x - e1x * e2z
  let nz := e1x * e2y - e1y * e2x
  let len := Float.sqrt (nx * nx + ny * ny + nz * nz)
  let (ux, uy, uz) :=
    if len < 1e-15 then (0.0, 1.0, 0.0)
    else let invL := 1.0 / len; (nx * invL, ny * invL, nz * invL)
  let base := (m.positions.size / 3).toUInt32
  let pos := ((((((((m.positions.push ax).push ay).push az).push bx).push by_).push bz).push cx).push cy).push cz
  let nrm := ((((((((m.normals.push ux).push uy).push uz).push ux).push uy).push uz).push ux).push uy).push uz
  let idx := ((m.indices.push base).push (base + 1)).push (base + 2)
  ⟨pos, nrm, idx⟩

/-- Exact edge-plane intersection point `π ∧ (P_i ∨ P_j)` for a straddling edge with signed
distances `di, dj` (`di` and `dj` of opposite sign). -/
@[inline] private def edgeCutPoint (ax ay az da bx by_ bz db : Float) : Float × Float × Float :=
  let denom := da - db
  let t := if denom.abs < 1e-15 then 0.5 else da / denom
  (ax + t * (bx - ax), ay + t * (by_ - ay), az + t * (bz - az))

/-- Clip a triangle where vertex `0` is alone on its side (`da ≥ 0` iff `alonePos`), preserving CCW
winding `(0, 1, 2)` on both halves, and emit the exact cut segment. -/
private def splitStraddlingTri (pos neg : ClippedMesh) (segs : FloatArray)
    (alonePos : Bool)
    (x0 y0 z0 d0 x1 y1 z1 d1 x2 y2 z2 d2 : Float) :
    ClippedMesh × ClippedMesh × FloatArray :=
  let (p1x, p1y, p1z) := edgeCutPoint x0 y0 z0 d0 x1 y1 z1 d1
  let (p2x, p2y, p2z) := edgeCutPoint x0 y0 z0 d0 x2 y2 z2 d2
  let segs := (((((segs.push p1x).push p1y).push p1z).push p2x).push p2y).push p2z
  if alonePos then
    let pos := pushTri pos x0 y0 z0 p1x p1y p1z p2x p2y p2z
    let neg := pushTri neg p1x p1y p1z x1 y1 z1 x2 y2 z2
    let neg := pushTri neg p1x p1y p1z x2 y2 z2 p2x p2y p2z
    (pos, neg, segs)
  else
    let neg := pushTri neg x0 y0 z0 p1x p1y p1z p2x p2y p2z
    let pos := pushTri pos p1x p1y p1z x1 y1 z1 x2 y2 z2
    let pos := pushTri pos p1x p1y p1z x2 y2 z2 p2x p2y p2z
    (pos, neg, segs)

/-- Tail-recursive triangle-slicing pass across `indices`. -/
private def sliceLoop (π : Plane3) (positions : FloatArray) (indices : Array UInt32)
    (t triCount : Nat) (pos neg : ClippedMesh) (segs : FloatArray) :
    ClippedMesh × ClippedMesh × FloatArray :=
  if t < triCount then
    let i0 := (indices[3 * t]!).toNat * 3
    let i1 := (indices[3 * t + 1]!).toNat * 3
    let i2 := (indices[3 * t + 2]!).toNat * 3
    let x0 := positions.get! i0;     let y0 := positions.get! (i0 + 1); let z0 := positions.get! (i0 + 2)
    let x1 := positions.get! i1;     let y1 := positions.get! (i1 + 1); let z1 := positions.get! (i1 + 2)
    let x2 := positions.get! i2;     let y2 := positions.get! (i2 + 1); let z2 := positions.get! (i2 + 2)
    let d0 := signedDistPlanePoint π x0 y0 z0
    let d1 := signedDistPlanePoint π x1 y1 z1
    let d2 := signedDistPlanePoint π x2 y2 z2
    let p0 := d0 ≥ 0.0; let p1 := d1 ≥ 0.0; let p2 := d2 ≥ 0.0
    if p0 && p1 && p2 then
      sliceLoop π positions indices (t + 1) triCount (pushTri pos x0 y0 z0 x1 y1 z1 x2 y2 z2) neg segs
    else if !p0 && !p1 && !p2 then
      sliceLoop π positions indices (t + 1) triCount pos (pushTri neg x0 y0 z0 x1 y1 z1 x2 y2 z2) segs
    else if p0 != p1 && p0 != p2 then
      let (pos, neg, segs) := splitStraddlingTri pos neg segs p0 x0 y0 z0 d0 x1 y1 z1 d1 x2 y2 z2 d2
      sliceLoop π positions indices (t + 1) triCount pos neg segs
    else if p1 != p0 && p1 != p2 then
      let (pos, neg, segs) := splitStraddlingTri pos neg segs p1 x1 y1 z1 d1 x2 y2 z2 d2 x0 y0 z0 d0
      sliceLoop π positions indices (t + 1) triCount pos neg segs
    else
      let (pos, neg, segs) := splitStraddlingTri pos neg segs p2 x2 y2 z2 d2 x0 y0 z0 d0 x1 y1 z1 d1
      sliceLoop π positions indices (t + 1) triCount pos neg segs
  else (pos, neg, segs)
termination_by triCount - t

/-- Stitch 2D unordered segments `[ax, ay, bx, by, …]` into ordered contiguous polylines
(stored in packed `FloatArray`s `[x₀, y₀, x₁, y₁, …]`). -/
private def stitch2DPolylines (segs2D : FloatArray) (eps : Float := 1e-4) : Array FloatArray := Id.run do
  let segCount := segs2D.size / 4
  if segCount == 0 then return #[]
  let eps2 := eps * eps
  let mut used := Array.replicate segCount false
  let mut polylines : Array FloatArray := #[]
  for startIdx in [0:segCount] do
    if !used[startIdx]! then
      used := used.set! startIdx true
      let ax := segs2D.get! (4 * startIdx)
      let ay := segs2D.get! (4 * startIdx + 1)
      let bx := segs2D.get! (4 * startIdx + 2)
      let by_ := segs2D.get! (4 * startIdx + 3)
      -- Grow forward from (bx, by_) into packed FloatArray
      let mut fwd := ((((FloatArray.emptyWithCapacity 16).push ax).push ay).push bx).push by_
      let mut ex := bx; let mut ey := by_
      let mut progress := true
      while progress do
        progress := false
        for j in [0:segCount] do
          if !used[j]! then
            let jx0 := segs2D.get! (4 * j);     let jy0 := segs2D.get! (4 * j + 1)
            let jx1 := segs2D.get! (4 * j + 2); let jy1 := segs2D.get! (4 * j + 3)
            let d0 := (jx0 - ex) * (jx0 - ex) + (jy0 - ey) * (jy0 - ey)
            let d1 := (jx1 - ex) * (jx1 - ex) + (jy1 - ey) * (jy1 - ey)
            if d0 ≤ eps2 then
              used := used.set! j true
              fwd := (fwd.push jx1).push jy1
              ex := jx1; ey := jy1; progress := true
            else if d1 ≤ eps2 then
              used := used.set! j true
              fwd := (fwd.push jx0).push jy0
              ex := jx0; ey := jy0; progress := true
      -- Grow backward from (ax, ay) into packed FloatArray
      let mut bwd := FloatArray.emptyWithCapacity 8
      let mut sx := ax; let mut sy := ay
      progress := true
      while progress do
        progress := false
        for j in [0:segCount] do
          if !used[j]! then
            let jx0 := segs2D.get! (4 * j);     let jy0 := segs2D.get! (4 * j + 1)
            let jx1 := segs2D.get! (4 * j + 2); let jy1 := segs2D.get! (4 * j + 3)
            let d0 := (jx0 - sx) * (jx0 - sx) + (jy0 - sy) * (jy0 - sy)
            let d1 := (jx1 - sx) * (jx1 - sx) + (jy1 - sy) * (jy1 - sy)
            if d0 ≤ eps2 then
              used := used.set! j true
              bwd := (bwd.push jx1).push jy1
              sx := jx1; sy := jy1; progress := true
            else if d1 ≤ eps2 then
              used := used.set! j true
              bwd := (bwd.push jx0).push jy0
              sx := jx0; sy := jy0; progress := true
      -- Pack bwd.reverse ++ fwd into flat FloatArray
      let bwdPts := bwd.size / 2
      let fwdPts := fwd.size / 2
      let mut packed := FloatArray.emptyWithCapacity ((bwdPts + fwdPts) * 2)
      for k in [0:bwdPts] do
        let idx := (bwdPts - 1 - k) * 2
        packed := (packed.push (bwd.get! idx)).push (bwd.get! (idx + 1))
      for k in [0:fwdPts] do
        let idx := k * 2
        packed := (packed.push (fwd.get! idx)).push (fwd.get! (idx + 1))
      polylines := polylines.push packed
  return polylines

/-- Project 3D slice segments `[ax, ay, az, bx, by, bz, …]` into plane 2D coordinates `(u, v)`. -/
private def projectSegs2DLoop (ox oy oz ux uy uz vx vy vz : Float)
    (segs3D : FloatArray) (i n : Nat) (out : FloatArray) : FloatArray :=
  if i + 5 < n then
    let ax := segs3D.get! i - ox;     let ay := segs3D.get! (i + 1) - oy; let az := segs3D.get! (i + 2) - oz
    let bx := segs3D.get! (i + 3) - ox; let by_ := segs3D.get! (i + 4) - oy; let bz := segs3D.get! (i + 5) - oz
    let au := ax * ux + ay * uy + az * uz
    let av := ax * vx + ay * vy + az * vz
    let bu := bx * ux + by_ * uy + bz * uz
    let bv := bx * vx + by_ * vy + bz * vz
    projectSegs2DLoop ox oy oz ux uy uz vx vy vz segs3D (i + 6) n
      ((((out.push au).push av).push bu).push bv)
  else out
termination_by n - i

/-- Slice an indexed 3D triangle mesh `(positions, indices)` by a `PGA3` plane `π`, returning both
clipped 3D half-meshes (`posHalf`, `negHalf`), the exact 3D cut segments, and stitched 2D slice
contour polylines in the plane's orthonormal frame. -/
def sliceMeshByPlane (positions : FloatArray) (indices : Array UInt32) (π : Plane3) :
    MeshSliceResult :=
  let π := normalizePlane3 π
  let triCount := indices.size / 3
  let emptyMesh : ClippedMesh := ⟨FloatArray.empty, FloatArray.empty, #[]⟩
  let (pos, neg, segs3D) := sliceLoop π positions indices 0 triCount emptyMesh emptyMesh FloatArray.empty
  let (origin, u, v) := (plane3Frame? π).getD ((0.0, 0.0, 0.0), (1.0, 0.0, 0.0), (0.0, 1.0, 0.0))
  let (ox, oy, oz) := origin
  let (ux, uy, uz) := u
  let (vx, vy, vz) := v
  let segs2D := projectSegs2DLoop ox oy oz ux uy uz vx vy vz segs3D 0 segs3D.size
    (FloatArray.emptyWithCapacity ((segs3D.size / 6) * 4))
  let polylines2D := stitch2DPolylines segs2D
  { posHalf := pos, negHalf := neg, contourSegments3D := segs3D,
    contourPolylines2D := polylines2D, planeOrigin := origin, planeU := u, planeV := v }

end Projective

end Grassmann

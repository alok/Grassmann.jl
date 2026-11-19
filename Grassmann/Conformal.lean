/-
Conformal-model utilities for any conformal space `S"∞∅+⋯+"` (CGA of `ℝᵈ`,
`V.n = d + 2`): fast unboxed `FloatArray` embedding and extraction of points,
dual (IPNS) spheres and planes, spheres and planes through points, point-pair
extraction from a meet, the metric dual and undual, translators, versor
outermorphisms, and a complete OPNS/IPNS geometric classifier (`interpreteCGA3`
/ `interpreteCGA2`) for points, real/imaginary point-pairs, lines, real/imaginary
circles, planes, real/imaginary spheres, dipoles, and tangent blades.

Credits:
- Michael Reed (`chakravala` / `Grassmann.jl`): conformal `S"∞∅+…+"` algebra & `↑`/`↓`.
- Steven De Keninck (`enkimute` / `ganja.js`): CGA `interprete` round/flat classification.

Conventions are Grassmann's: generator order `∞, ∅, e₁ … e_d`, `∞⋅∅ = -1`,
`⋅` is the right contraction, `Chain.up` is Julia's `↑` (`∅ + x + ½x²∞`).

| object | IPNS (grade 1) | OPNS (grade `V.n - 1`) |
|---|---|---|
| point `x` | `up x` | — |
| sphere `(c, r)` | `up c - ½r²∞` | `P₁ ∧ ⋯ ∧ P_{d+1}` |
| plane `n⋅x = δ` | `n + δ∞` | `P₁ ∧ ⋯ ∧ P_d ∧ ∞` |

`X⋅s = -½(|x - c|² - r²)`, so incidence is linear, and `dual` (right
multiplication by `I⁻¹`) turns an OPNS blade through points into its IPNS
vector.
-/
import Grassmann.Composite.Project
import Grassmann.Forms.Outermorphism
import Grassmann.Kernel.Generated.CGA2
import Grassmann.Kernel.Generated.CGA3

namespace Grassmann

open DirectSum StaticVectors AbstractTensors Grassmann.Forms Composite

namespace Conformal

variable {V : TensorBundle} [Kernels V]

/-- A conformal vector: point, dual sphere or dual plane. -/
abbrev CVec (V : TensorBundle) := Chain V 1 Float

private def f0 : Float := 0.0
private def f1 : Float := 1.0
private def f2 : Float := 2.0
private def fNeg2 : Float := -2.0
private def fHalf : Float := 0.5
private def fNegHalf : Float := -0.5
private def eps12 : Float := 1e-12
private def eps300 : Float := 1e-300

private def zeroV4 : Values Float 4 := Values.replicate f0
private def zeroV5 : Values Float 5 := Values.replicate f0

/-- Build a `Values Float n` from a `FloatArray` of matching length (fallback zero if mismatched). -/
@[inline] private def mkVals (n : Nat) (arr : FloatArray) : Values Float n :=
  if h : arr.size = n then ⟨arr, h⟩ else zeroValues n

/-- Build a length-4 `Values Float 4` for `CGA2` (1 copy + 3 in-place stores). -/
@[inline] private def vals4 (a b c d : Float) : Values Float 4 :=
  (((zeroV4.set ⟨0, by decide⟩ a).set ⟨1, by decide⟩ b).set ⟨2, by decide⟩ c).set ⟨3, by decide⟩ d

/-- Build a length-5 `Values Float 5` for `CGA3` (1 copy + 4 in-place stores). -/
@[inline] private def vals5 (a b c d e : Float) : Values Float 5 :=
  ((((zeroV5.set ⟨0, by decide⟩ a).set ⟨1, by decide⟩ b).set ⟨2, by decide⟩ c).set
    ⟨3, by decide⟩ d).set ⟨4, by decide⟩ e

/-- The point at infinity `∞`. -/
@[inline] def inf (V : TensorBundle) : CVec V := unitVec V Float (infBits V)

/-- The origin `∅`. -/
@[inline] def origin (V : TensorBundle) : CVec V := unitVec V Float (originBits V)

/-- The unit pseudoscalar `I` (all generators, in order). -/
@[inline] def pseudoscalar (V : TensorBundle) : Multivector V Float :=
  Multivector.ofBlade (⟨Bits.lowMask V.n⟩ : Submanifold V V.n) 1.0

/-- Scalar part of a multivector. -/
@[inline] def scalarOf (m : Multivector V Float) : Float := m.v.get! 0

/-- Tail-recursive Euclidean inner product `Σ_{i≥2} a[i] * b[i]` over unboxed `FloatArray`s. -/
private def euclidDotLoop (a b : FloatArray) (i n : Nat) (acc : Float) : Float :=
  if i < n then euclidDotLoop a b (i + 1) n (acc + a.get! i * b.get! i) else acc
termination_by n - i

/-- `a ⋅ b` of two conformal vectors in `S"∞∅+…+"`, computed directly on unboxed `FloatArray`s
without allocating an intermediate scalar `Chain`: `-(a∞·b∅ + a∅·b∞) + Σ_{i≥2} aᵢ·bᵢ`. -/
@[inline] def dot (a b : CVec V) : Float :=
  let ad := a.v.data
  let bd := b.v.data
  let n := ad.size
  if V.hasinf && V.hasorigin && n ≥ 2 then
    euclidDotLoop ad bd 2 n (-(ad.get! 0 * bd.get! 1 + ad.get! 1 * bd.get! 0))
  else
    Chain.dot1 a b

/-- The Euclidean part: the `∞` and `∅` coefficients set to zero (in-place on unboxed `FloatArray`). -/
@[inline] def euclidean (X : CVec V) : CVec V :=
  let d := X.v.data
  let d := if d.size > 0 then d.set! 0 0.0 else d
  let d := if d.size > 1 then d.set! 1 0.0 else d
  ⟨mkVals _ d⟩

/-- Tail-recursive copy of `xs : FloatArray` into slots `2 .. n-1` of a conformal vector. -/
private def vecArrLoop (xs : FloatArray) (i n : Nat) (out : FloatArray) : FloatArray :=
  if i < n then
    let v := if i < xs.size then xs.get! i else 0.0
    vecArrLoop xs (i + 1) n (out.push v)
  else out
termination_by n - i

/-- A Euclidean vector `x = Σ xᵢ eᵢ` from a packed `FloatArray` of `d` coordinates (zero `List`
allocation). -/
@[inline] def vecArr (xs : FloatArray) : CVec V :=
  let n := Leibniz.binomial V.n 1
  let d := if n ≥ 2 then n - 2 else 0
  let init := if n ≥ 2 then ((FloatArray.emptyWithCapacity n).push 0.0).push 0.0
              else FloatArray.emptyWithCapacity n
  ⟨mkVals n (vecArrLoop xs 0 d init)⟩

/-- A Euclidean vector `x = Σ xᵢ eᵢ` from its `d` coordinates (`List Float` convenience API). -/
@[inline] def vec (xs : List Float) : CVec V :=
  let n := Leibniz.binomial V.n 1
  let rec go : List Float → Nat → FloatArray → FloatArray
    | _, 0, acc => acc
    | [], k + 1, acc => go [] k (acc.push 0.0)
    | y :: ys, k + 1, acc => go ys k (acc.push y)
  let init := if n ≥ 2 then ((FloatArray.emptyWithCapacity n).push 0.0).push 0.0
              else FloatArray.emptyWithCapacity n
  let rem := if n ≥ 2 then n - 2 else n
  ⟨mkVals n (go xs rem init)⟩

/-- Tail-recursive extraction of Euclidean coordinates into a packed `FloatArray`. -/
private def coordsArrLoop (d : FloatArray) (i n : Nat) (out : FloatArray) : FloatArray :=
  if i < n then coordsArrLoop d (i + 1) n (out.push (d.get! i)) else out
termination_by n - i

/-- Euclidean coordinates of a conformal vector as an unboxed `FloatArray` (`e₁ … e_d`). -/
@[inline] def coordsArr (X : CVec V) : FloatArray :=
  let d := X.v.data
  let n := d.size
  if n ≤ 2 then FloatArray.empty
  else coordsArrLoop d 2 n (FloatArray.emptyWithCapacity (n - 2))

/-- Euclidean coordinates of a conformal vector (its `e₁ … e_d` coefficients). -/
@[inline] def coords (X : CVec V) : List Float := (List.range (V.n - 2)).map fun i => X.v.get! (i + 2)

/-- Fast Euclidean vector `(x, y)` in `CGA2`. -/
@[inline] def vec2 (x y : Float) : CVec CGA2 := ⟨vals4 f0 f0 x y⟩

/-- Fast conformal point `↑(x, y) = ½(x²+y²)∞ + ∅ + x e₁ + y e₂` in `CGA2`. -/
@[inline] def point2 (x y : Float) : CVec CGA2 :=
  ⟨vals4 (fHalf * (x * x + y * y)) f1 x y⟩

/-- Fast Euclidean vector `(x, y, z)` in `CGA3`. -/
@[inline] def vec3 (x y z : Float) : CVec CGA3 := ⟨vals5 f0 f0 x y z⟩

/-- Fast conformal point `↑(x, y, z) = ½(x²+y²+z²)∞ + ∅ + x e₁ + y e₂ + z e₃` in `CGA3`. -/
@[inline] def point3 (x y z : Float) : CVec CGA3 :=
  ⟨vals5 (fHalf * (x * x + y * y + z * z)) f1 x y z⟩

/-- Fast dual sphere `(cx, cy, cz, r)` in `CGA3`: `½(c² - r²)∞ + ∅ + cx e₁ + cy e₂ + cz e₃`. -/
@[inline] def dualSphere3 (cx cy cz r : Float) : CVec CGA3 :=
  ⟨vals5 (fHalf * (cx * cx + cy * cy + cz * cz - r * r)) f1 cx cy cz⟩

/-- Fast dual plane `n⋅x = δ` in `CGA3`: `δ∞ + nx e₁ + ny e₂ + nz e₃`. -/
@[inline] def dualPlane3 (nx ny nz δ : Float) : CVec CGA3 :=
  ⟨vals5 δ f0 nx ny nz⟩

/-- The conformal embedding `x ↦ ∅ + x + ½x²∞` (Julia `↑`), computed directly on unboxed
`FloatArray`s when `V` has `∞` and `∅`. -/
@[inline] def point (x : CVec V) : CVec V :=
  let d := x.v.data
  let n := d.size
  if V.hasinf && V.hasorigin && n ≥ 2 then
    let x2 := euclidDotLoop d d 2 n 0.0
    let d := d.set! 0 (0.5 * x2 + d.get! 0)
    let d := d.set! 1 (1.0 + d.get! 1)
    ⟨mkVals _ d⟩
  else Chain.up x

/-- The weight `-X⋅∞` (`1` for a normalised point or dual sphere; slot 1 = `∅` coeff in Witt CGA). -/
@[inline] def weight (X : CVec V) : Float :=
  if V.hasinf && V.hasorigin && X.v.data.size ≥ 2 then X.v.data.get! 1
  else -dot X (inf V)

/-- Scale a `FloatArray` by `k` into a fresh `FloatArray` (tail-recursive, unboxed). -/
private def scaleArrLoop (d : FloatArray) (k : Float) (i n : Nat) (out : FloatArray) : FloatArray :=
  if i < n then scaleArrLoop d k (i + 1) n (out.push (k * d.get! i)) else out
termination_by n - i

/-- Rescale to unit weight; `none` for flat objects (zero weight). -/
@[inline] def normalize? (X : CVec V) : Option (CVec V) :=
  let w := weight X
  if w.abs < eps300 then none
  else
    let d := X.v.data
    let n := d.size
    some ⟨mkVals _ (scaleArrLoop d (f1 / w) 0 n (FloatArray.emptyWithCapacity n))⟩

/-- The Euclidean point of a (possibly scaled) conformal point. -/
@[inline] def down? (X : CVec V) : Option (CVec V) :=
  let w := weight X
  if w.abs < eps300 then none
  else
    let invW := f1 / w
    let d := X.v.data
    let n := d.size
    let rec go (i : Nat) (out : FloatArray) : FloatArray :=
      if i < n then go (i + 1) (out.push (if i < 2 then f0 else invW * d.get! i)) else out
    some ⟨mkVals _ (go 0 (FloatArray.emptyWithCapacity n))⟩

/-- Extract Euclidean `(x, y, z)` of a `CGA3` conformal point (`none` if weight vanishes). -/
@[inline] def down3? (X : CVec CGA3) : Option (Float × Float × Float) :=
  let w := X.v.get! 1
  if w.abs < eps12 then none
  else
    let invW := f1 / w
    some (X.v.get! 2 * invW, X.v.get! 3 * invW, X.v.get! 4 * invW)

/-- Extract Euclidean `(x, y)` of a `CGA2` conformal point (`none` if weight vanishes). -/
@[inline] def down2? (X : CVec CGA2) : Option (Float × Float) :=
  let w := X.v.get! 1
  if w.abs < eps12 then none
  else
    let invW := f1 / w
    some (X.v.get! 2 * invW, X.v.get! 3 * invW)

/-- Squared Euclidean distance of two (possibly scaled) points:
`|x - y|² = -2 X⋅Y / ((X⋅∞)(Y⋅∞))`. -/
@[inline] def distance2 (X Y : CVec V) : Float :=
  fNeg2 * dot X Y / (weight X * weight Y)

/-- The dual hypersphere with centre `c` and radius `r`: `up c - ½r²∞`. -/
@[inline] def dualSphere (c : CVec V) (r : Float) : CVec V :=
  let d := c.v.data
  let n := d.size
  if V.hasinf && V.hasorigin && n ≥ 2 then
    let c2 := euclidDotLoop d d 2 n f0
    let d := d.set! 0 (fHalf * (c2 - r * r) + d.get! 0)
    let d := d.set! 1 (f1 + d.get! 1)
    ⟨mkVals _ d⟩
  else point c - (fHalf * r * r) • inf V

/-- The dual hyperplane `{x | n⋅x = δ}`: `n + δ∞`. -/
@[inline] def dualPlane (n : CVec V) (δ : Float) : CVec V :=
  let d := n.v.data
  if V.hasinf && V.hasorigin && d.size ≥ 1 then
    ⟨mkVals _ (d.set! 0 (d.get! 0 + δ))⟩
  else n + δ • inf V

/-- Centre and squared radius of a dual sphere (`r² < 0` for an imaginary
sphere); `none` for a flat (a plane). Uses `s⋅s = w² r²` and centre
`= euclidean(s)/w`. -/
@[inline] def sphereCenterRadius2? (s : CVec V) : Option (CVec V × Float) := do
  let w := weight s
  if w.abs < eps300 then none
  let c ← down? s
  some (c, dot s s / (w * w))

/-- Unit normal and distance `(n, δ)` of a dual plane `π = n + δ∞` (any scale);
`none` if the Euclidean part vanishes. -/
@[inline] def planeNormalDistance? (π : CVec V) : Option (CVec V × Float) := do
  let n := euclidean π
  let len := Float.sqrt (dot n n)
  if len < eps300 then none
  let invL := f1 / len
  let d := n.v.data
  let nUnit : CVec V := ⟨mkVals _ (scaleArrLoop d invL 0 d.size (FloatArray.emptyWithCapacity d.size))⟩
  let δ := if V.hasinf && V.hasorigin && π.v.data.size ≥ 1 then π.v.data.get! 0 * invL
           else -dot π (origin V) * invL
  some (nUnit, δ)

/-- The metric dual `X ↦ X I⁻¹`, with `I⁻¹ = I / I²`. -/
@[inline] def dual (X : Multivector V Float) : Multivector V Float :=
  let I := pseudoscalar V
  (1.0 / scalarOf (I * I)) • (X * I)

/-- Inverse of `dual`: `X ↦ X I`. -/
@[inline] def undual (X : Multivector V Float) : Multivector V Float := X * pseudoscalar V

/-- The outer product of a list of conformal vectors, as a multivector
(the scalar `1` for the empty list). -/
def wedgeAll (xs : List (CVec V)) : Multivector V Float :=
  xs.foldl (fun acc x => acc ∧ x.toMultivector) (Multivector.scalar 1.0)

/-- The dual sphere through `d + 1` points (Euclidean coordinates), scaled to
unit weight; `none` if they are degenerate (on a common plane or coincident),
in which case `planeThrough` applies. -/
def sphereThrough? (pts : List (CVec V)) : Option (CVec V) :=
  normalize? ((dual (wedgeAll (pts.map point))).grade 1)

/-- The dual plane through `d` points (Euclidean coordinates), as `n + δ∞`
with unit `n`; `none` if the points are degenerate. -/
def planeThrough? (pts : List (CVec V)) : Option (CVec V) := do
  let π : CVec V := (dual (wedgeAll (pts.map point ++ [inf V]))).grade 1
  let (n, δ) ← planeNormalDistance? π
  some (dualPlane n δ)

/-- The two points of a point pair `T` (a bivector, e.g. the meet of a line and
a sphere), in Euclidean coordinates; `none` when the pair is imaginary
(`T⋅T > 0` in Grassmann's contraction convention) or flat. With
`F = T⋅∞`, the points are `T⋅F ± √disc · F`, `disc = -(T⋅T)`. -/
def pointPair? (T : Chain V 2 Float) : Option (CVec V × CVec V) := do
  let disc := -((T ⋅ T : Chain V (2 - 2) Float).v.get! 0)
  if disc < 0 then none
  let F : CVec V := T ⋅ inf V
  let TF : CVec V := T ⋅ F
  let k := Float.sqrt disc
  let a ← down? (TF + k • F)
  let b ← down? (TF - k • F)
  some (a, b)

/-- The translator `T = 1 - ½ t∞` as a compact even `Spinor V Float`. -/
@[inline] def translatorSpinor (t : CVec V) : Spinor V Float :=
  let biv : Chain V 2 Float := (-0.5 : Float) • (t ∧ inf V)
  Half.ofChain biv + Half.ofBlade (⟨0⟩ : Submanifold V 0) 1.0

/-- The translator `T = 1 - ½ t∞` (as a multivector); `translate` applies it. -/
@[inline] def translator (t : CVec V) : Multivector V Float :=
  (translatorSpinor t).toMultivector

/-- Translate a conformal object by the Euclidean vector `t`: the sandwich
`T X T̃`, written out with geometric products so it applies to any grade. -/
@[inline] def translate (t : CVec V) (X : Multivector V Float) : Multivector V Float :=
  let T := translatorSpinor t
  (T * X) * ~T

/-- Translate a homogeneous conformal `Chain V G Float` using the fused spinor sandwich `T >>> X`. -/
@[inline] def translateChain {G : Nat} (t : CVec V) (X : Chain V G Float) : Chain V G Float :=
  translatorSpinor t >>> X

/-- The matrix of the grade-1 map `x ↦ R x R⁻¹` of a versor `R` (in the
generator basis), as a `Simplex`: column `j` is the image of generator `j`.
Its `Outermorphism` is the action of `R` on every grade, which is how versors
and outermorphisms meet: `ofSimplex (versorMap R)` applied to a blade equals
the sandwich of that blade. -/
def versorMap (R : Multivector V Float) : Simplex V V Float :=
  let Rinv := (1.0 / scalarOf (R * ~R)) • ~R
  let cols : Array (CVec V) := (Array.range V.n).map fun j =>
    (R * (unitVec V Float ((1 : UInt64) <<< j.toUInt64)).toMultivector * Rinv).grade 1
  TensorOperator.ofFn fun i j => cols[j.val]!.v.get! i.val

/-! ## Complete CGA3 Geometric Classifier (`interprete`, matching `ganja.js`)

Classifies any OPNS (or IPNS when `isIPNS := true`) `Multivector CGA3 Float` into its exact
Euclidean geometric primitive for direct 3D rendering in `SceneIR` (`GSIR` v1). -/

/-- Decoded geometric primitive of a conformal blade in `CGA3` (`S!"∞∅+++"`) or `CGA2` (`S!"∞∅++"`). -/
inductive ConformalObject where
  /-- Zero, scalar, pseudoscalar, or degenerate blade. -/
  | empty
  /-- A 3D point `(x, y, z)` (with `z = 0` for `CGA2`). -/
  | point (pos : Float × Float × Float)
  /-- A real (`imaginary = false`) or imaginary (`imaginary = true`) point pair `(p1, p2)`. -/
  | pointPair (p1 p2 : Float × Float × Float) (imaginary : Bool)
  /-- A 3D line given by closest point to origin `origin` and unit direction `dir`. -/
  | line (origin dir : Float × Float × Float)
  /-- A real or imaginary circle given by `center`, unit carrier `normal`, and `radius ≥ 0`. -/
  | circle (center normal : Float × Float × Float) (radius : Float) (imaginary : Bool)
  /-- A 3D plane given by closest point to origin `center` and unit `normal`. -/
  | plane (center normal : Float × Float × Float)
  /-- A real or imaginary sphere given by `center` and `radius ≥ 0`. -/
  | sphere (center : Float × Float × Float) (radius : Float) (imaginary : Bool)
  /-- A null grade-2 tangent vector / dipole at `pos` with unit direction `dir`. -/
  | dipole (pos dir : Float × Float × Float)
  /-- A null grade-3 tangent bivector at `pos` with unit normal `normal`. -/
  | tangent (pos normal : Float × Float × Float)
  deriving Repr, Inhabited

/-- Squared Euclidean L2 norm of a `FloatArray` (tail-recursive, unboxed). -/
private def arrNormSq (d : FloatArray) (i n : Nat) (acc : Float) : Float :=
  if i < n then
    let v := d.get! i
    arrNormSq d (i + 1) n (acc + v * v)
  else acc
termination_by n - i

@[inline] private def chainNormSq {V : TensorBundle} {G : Nat} (c : Chain V G Float) : Float :=
  arrNormSq c.v.data 0 c.v.data.size 0.0

/-- Find the dominant grade (`1 .. 4`) of a `CGA3` multivector by L2 energy directly on its
packed grade-major storage (`[0]`, `[1..6)`, `[6..16)`, `[16..26)`, `[26..31)`) with zero
allocations. -/
@[inline] private def dominantGradeCGA3 (m : Multivector CGA3 Float) : Nat × Float :=
  let d := m.v.data
  let e1 := arrNormSq d 1 6 f0
  let e2 := arrNormSq d 6 16 f0
  let e3 := arrNormSq d 16 26 f0
  let e4 := arrNormSq d 26 31 f0
  let (g, e) := if e2 > e1 then (2, e2) else (1, e1)
  let (g, e) := if e3 > e then (3, e3) else (g, e)
  if e4 > e then (4, e4) else (g, e)

/-- Zero-allocation decoder for a grade-1 IPNS dual sphere/plane `s = [s∞, s∅, sx, sy, sz]` in `CGA3`. -/
@[inline] private def decodeIPNSGrade1CGA3 (s0 w sx sy sz tol : Float) : ConformalObject :=
  if w.abs < tol then
    let len2 := sx * sx + sy * sy + sz * sz
    if len2 < tol * tol then .empty
    else
      let invL := f1 / Float.sqrt len2
      let nx := sx * invL; let ny := sy * invL; let nz := sz * invL
      let δ := s0 * invL
      .plane (δ * nx, δ * ny, δ * nz) (nx, ny, nz)
  else
    let invW := f1 / w
    let cx := sx * invW; let cy := sy * invW; let cz := sz * invW
    let sDotS := fNeg2 * s0 * w + sx * sx + sy * sy + sz * sz
    let r2 := sDotS * invW * invW
    if r2 ≥ f0 then .sphere (cx, cy, cz) (Float.sqrt r2) false
    else .sphere (cx, cy, cz) (Float.sqrt (-r2)) true

/-- Classify an OPNS grade-2 blade `T` in `CGA3`: flat point, real/imaginary point-pair, or
tangent dipole. -/
def interpreteCGA3Grade2 (T : Chain CGA3 2 Float) (tol : Float := 1e-9) : ConformalObject :=
  let n2 := chainNormSq T
  if n2 < tol * tol then .empty
  else
    let flat : Chain CGA3 3 Float := T ∧ inf CGA3
    if chainNormSq flat ≤ tol * tol * n2 then
      -- Flat point `P ∧ ∞`: slots [0..3] are (-w, -w*x, -w*y, -w*z)
      let w := T.v.get! 0
      if w.abs < tol then .empty
      else .point (T.v.get! 1 / w, T.v.get! 2 / w, T.v.get! 3 / w)
    else
      let disc := -((T ⋅ T : Chain CGA3 (2 - 2) Float).v.get! 0)
      let F : CVec CGA3 := T ⋅ inf CGA3
      let TF : CVec CGA3 := T ⋅ F
      if disc > tol * tol * n2 then
        let k := Float.sqrt disc
        match down3? (TF + k • F), down3? (TF - k • F) with
        | some a, some b => .pointPair a b false
        | _, _ => .empty
      else if disc < -(tol * tol * n2) then
        -- Imaginary point pair: center = down3? TF, half-axis from F
        match down3? TF with
        | some (cx, cy, cz) =>
          let w := weight TF
          if w.abs < tol then .empty
          else
            let k := Float.sqrt (-disc) / w.abs
            let dx := F.v.get! 2 * k; let dy := F.v.get! 3 * k; let dz := F.v.get! 4 * k
            .pointPair (cx + dx, cy + dy, cz + dz) (cx - dx, cy - dy, cz - dz) true
        | none => .empty
      else
        -- Null tangent vector / dipole (`T² ≈ 0`)
        match down3? TF with
        | some pos =>
          let fx := F.v.get! 2; let fy := F.v.get! 3; let fz := F.v.get! 4
          let fl := Float.sqrt (fx * fx + fy * fy + fz * fz)
          if fl < tol then .point pos
          else let invF := 1.0 / fl; .dipole pos (fx * invF, fy * invF, fz * invF)
        | none => .empty

/-- Classify an OPNS grade-3 blade `C` in `CGA3`: line, real/imaginary circle, or tangent bivector. -/
def interpreteCGA3Grade3 (C : Chain CGA3 3 Float) (tol : Float := 1e-9) : ConformalObject :=
  let n2 := chainNormSq C
  if n2 < tol * tol then .empty
  else
    let flat : Chain CGA3 4 Float := C ∧ inf CGA3
    if chainNormSq flat ≤ tol * tol * n2 then
      -- Line `P1 ∧ P2 ∧ ∞`: slots [0..2] = (dx, dy, dz), [3..5] = (mz, -my, mx)
      let dx := C.v.get! 0; let dy := C.v.get! 1; let dz := C.v.get! 2
      let d2 := dx * dx + dy * dy + dz * dz
      if d2 < tol * tol then .empty
      else
        let mx := C.v.get! 5; let my := -(C.v.get! 4); let mz := C.v.get! 3
        let invD2 := 1.0 / d2
        let invD := Float.sqrt invD2
        let ox := (dy * mz - dz * my) * invD2
        let oy := (dz * mx - dx * mz) * invD2
        let oz := (dx * my - dy * mx) * invD2
        .line (ox, oy, oz) (dx * invD, dy * invD, dz * invD)
    else
      -- Circle or tangent bivector: carrier plane is `dual (C ∧ ∞)`
      let π : CVec CGA3 := (dual flat.toMultivector).grade 1
      let normal := match planeNormalDistance? π with
        | some (nv, _) => (nv.v.get! 2, nv.v.get! 3, nv.v.get! 4)
        | none => (0.0, 0.0, 1.0)
      let cSq := (C * C).v.get! 0
      let fSq := (flat * flat).v.get! 0
      if fSq.abs < tol * tol then .empty
      else
        let r2 := -cSq / fSq
        let centerHalf := (C * inf CGA3) * C
        match down3? (centerHalf.grade 1) with
        | none => .empty
        | some ctr =>
          if r2.abs ≤ tol then .tangent ctr normal
          else if r2 > 0.0 then .circle ctr normal (Float.sqrt r2) false
          else .circle ctr normal (Float.sqrt (-r2)) true

/-- Classify an OPNS grade-4 blade `S` in `CGA3`: plane or real/imaginary sphere. -/
def interpreteCGA3Grade4 (S : Chain CGA3 4 Float) (tol : Float := 1e-9) : ConformalObject :=
  let n2 := chainNormSq S
  if n2 < tol * tol then .empty
  else
    let s : CVec CGA3 := (dual S.toMultivector).grade 1
    let w := weight s
    if w.abs < tol then
      match planeNormalDistance? s with
      | some (nv, δ) =>
        let nx := nv.v.get! 2; let ny := nv.v.get! 3; let nz := nv.v.get! 4
        .plane (δ * nx, δ * ny, δ * nz) (nx, ny, nz)
      | none => .empty
    else
      match sphereCenterRadius2? s with
      | some (cv, r2) =>
        let ctr := (cv.v.get! 2, cv.v.get! 3, cv.v.get! 4)
        if r2 ≥ 0.0 then .sphere ctr (Float.sqrt r2) false
        else .sphere ctr (Float.sqrt (-r2)) true
      | none => .empty

/-- Classify any OPNS (or IPNS when `isIPNS := true`) `Multivector CGA3 Float` into its exact
3D Euclidean primitive (`point`, `pointPair`, `line`, `circle`, `plane`, `sphere`, `dipole`,
`tangent`, or `empty`). -/
def interpreteCGA3 (X : Multivector CGA3 Float) (isIPNS : Bool := false) (tol : Float := 1e-9) :
    ConformalObject :=
  if isIPNS then
    let (g0, e0) := dominantGradeCGA3 X
    if e0 < tol * tol then .empty
    else if g0 == 1 then
      -- Direct zero-allocation fast path for IPNS dual spheres & planes (avoids undual+dual!)
      let d := X.v.data
      decodeIPNSGrade1CGA3 (d.get! 1) (d.get! 2) (d.get! 3) (d.get! 4) (d.get! 5) tol
    else
      let opns := undual X
      let (g, e) := dominantGradeCGA3 opns
      if e < tol * tol then .empty
      else match g with
      | 1 => match down3? (opns.grade 1) with | some p => .point p | none => .empty
      | 2 => interpreteCGA3Grade2 (opns.grade 2) tol
      | 3 => interpreteCGA3Grade3 (opns.grade 3) tol
      | 4 => interpreteCGA3Grade4 (opns.grade 4) tol
      | _ => .empty
  else
    let (g, e) := dominantGradeCGA3 X
    if e < tol * tol then .empty
    else match g with
    | 1 => match down3? (X.grade 1) with | some p => .point p | none => .empty
    | 2 => interpreteCGA3Grade2 (X.grade 2) tol
    | 3 => interpreteCGA3Grade3 (X.grade 3) tol
    | 4 => interpreteCGA3Grade4 (X.grade 4) tol
    | _ => .empty

/-- Classify any OPNS (or IPNS when `isIPNS := true`) `Multivector CGA2 Float` into a 2D
primitive embedded in the `z = 0` plane (`point`, `pointPair`, `line`, `circle`, `dipole`, `empty`). -/
def interpreteCGA2 (X : Multivector CGA2 Float) (isIPNS : Bool := false) (tol : Float := 1e-9) :
    ConformalObject :=
  let opns := if isIPNS then undual X else X
  let e1 := chainNormSq (opns.grade 1)
  let e2 := chainNormSq (opns.grade 2)
  let e3 := chainNormSq (opns.grade 3)
  let (g, e) := if e2 > e1 then (2, e2) else (1, e1)
  let (g, e) := if e3 > e then (3, e3) else (g, e)
  if e < tol * tol then .empty
  else match g with
  | 1 => match down2? (opns.grade 1) with | some (x, y) => .point (x, y, 0.0) | none => .empty
  | 2 =>
    let T := opns.grade 2
    let flat : Chain CGA2 3 Float := T ∧ inf CGA2
    if chainNormSq flat ≤ tol * tol * e2 then
      let w := T.v.get! 0
      if w.abs < tol then .empty
      else .point (T.v.get! 1 / w, T.v.get! 2 / w, 0.0)
    else
      let disc := -((T ⋅ T : Chain CGA2 (2 - 2) Float).v.get! 0)
      let F : CVec CGA2 := T ⋅ inf CGA2
      let TF : CVec CGA2 := T ⋅ F
      if disc > tol * tol * e2 then
        let k := Float.sqrt disc
        match down2? (TF + k • F), down2? (TF - k • F) with
        | some (ax, ay), some (bx, by_) => .pointPair (ax, ay, 0.0) (bx, by_, 0.0) false
        | _, _ => .empty
      else if disc < -(tol * tol * e2) then
        match down2? TF with
        | some (cx, cy) =>
          let w := weight TF
          if w.abs < tol then .empty
          else
            let k := Float.sqrt (-disc) / w.abs
            let dx := F.v.get! 2 * k; let dy := F.v.get! 3 * k
            .pointPair (cx + dx, cy + dy, 0.0) (cx - dx, cy - dy, 0.0) true
        | none => .empty
      else
        match down2? TF with
        | some (px, py) =>
          let fx := F.v.get! 2; let fy := F.v.get! 3
          let fl := Float.sqrt (fx * fx + fy * fy)
          if fl < tol then .point (px, py, 0.0)
          else .dipole (px, py, 0.0) (fx / fl, fy / fl, 0.0)
        | none => .empty
  | 3 =>
    let s : CVec CGA2 := (dual (opns.grade 3).toMultivector).grade 1
    let w := weight s
    if w.abs < tol then
      match planeNormalDistance? s with
      | some (nv, δ) =>
        let nx := nv.v.get! 2; let ny := nv.v.get! 3
        .line (δ * nx, δ * ny, 0.0) (-ny, nx, 0.0)
      | none => .empty
    else
      match sphereCenterRadius2? s with
      | some (cv, r2) =>
        let ctr := (cv.v.get! 2, cv.v.get! 3, 0.0)
        if r2 ≥ 0.0 then .circle ctr (0.0, 0.0, 1.0) (Float.sqrt r2) false
        else .circle ctr (0.0, 0.0, 1.0) (Float.sqrt (-r2)) true
      | none => .empty
  | _ => .empty

end Conformal

end Grassmann

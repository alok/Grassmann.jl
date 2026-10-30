/-
Conformal-model utilities for any conformal space `S"∞∅+⋯+"` (CGA of `ℝᵈ`,
`V.n = d + 2`): embedding and extraction of points, dual (IPNS) spheres and
planes, spheres and planes through points, point-pair extraction from a meet,
the metric dual and undual, translators, and the outermorphism of a versor.

Conventions are Grassmann's: generator order `∞, ∅, e₁ … e_d`, `∞⋅∅ = -1`,
`⋅` is the right contraction, `Chain.up` is Julia's `↑` (`∅ + x + ½x²∞`).

| object | IPNS (grade 1) | OPNS (grade `V.n - 1`) |
|---|---|---|
| point `x` | `up x` | — |
| sphere `(c, r)` | `up c - ½r²∞` | `P₁ ∧ ⋯ ∧ P_{d+1}` |
| plane `n⋅x = δ` | `n + δ∞` | `P₁ ∧ ⋯ ∧ P_d ∧ ∞` |

`X⋅s = -½(|x - c|² - r²)`, so incidence is linear, and `dual` (right
multiplication by `I⁻¹`) turns an OPNS blade through points into its IPNS
vector. Everything here goes through the space's product kernels, so the null
pair needs no special-casing.
-/
import Grassmann.Composite.Project
import Grassmann.Forms.Outermorphism

namespace Grassmann

open DirectSum StaticVectors AbstractTensors Grassmann.Forms Composite

namespace Conformal

variable {V : TensorBundle} [Kernels V]

/-- A conformal vector: point, dual sphere or dual plane. -/
abbrev CVec (V : TensorBundle) := Chain V 1 Float

/-- The point at infinity `∞`. -/
@[inline] def inf (V : TensorBundle) : CVec V := unitVec V Float (infBits V)

/-- The origin `∅`. -/
@[inline] def origin (V : TensorBundle) : CVec V := unitVec V Float (originBits V)

/-- The unit pseudoscalar `I` (all generators, in order). -/
@[inline] def pseudoscalar (V : TensorBundle) : Multivector V Float :=
  Multivector.ofBlade (⟨Bits.lowMask V.n⟩ : Submanifold V V.n) 1.0

/-- Scalar part of a multivector. -/
@[inline] def scalarOf (m : Multivector V Float) : Float := (m.grade 0).v.get! 0

/-- `a ⋅ b` of two conformal vectors. -/
@[inline] def dot (a b : CVec V) : Float := Chain.dot1 a b

/-- The Euclidean part: the `∞` and `∅` coefficients set to zero. -/
@[inline] def euclidean (X : CVec V) : CVec V :=
  ⟨Values.ofFn fun i => if i.val < 2 then 0.0 else X.v.get! i.val⟩

/-- A Euclidean vector `x = Σ xᵢ eᵢ` from its `d` coordinates. -/
@[inline] def vec (xs : List Float) : CVec V :=
  ⟨Values.ofFn fun i => if i.val < 2 then 0.0 else xs.getD (i.val - 2) 0.0⟩

/-- Euclidean coordinates of a conformal vector (its `e₁ … e_d` coefficients). -/
@[inline] def coords (X : CVec V) : List Float := (List.range (V.n - 2)).map fun i => X.v.get! (i + 2)

/-- The conformal embedding `x ↦ ∅ + x + ½x²∞` (Julia `↑`). -/
@[inline] def point (x : CVec V) : CVec V := Chain.up x

/-- The weight `-X⋅∞` (1 for a normalised point or dual sphere). -/
@[inline] def weight (X : CVec V) : Float := -dot X (inf V)

/-- Rescale to unit weight; `none` for flat objects (zero weight). -/
@[inline] def normalize? (X : CVec V) : Option (CVec V) :=
  let w := weight X
  if w.abs < 1e-300 then none else some ((1.0 / w) • X)

/-- The Euclidean point of a (possibly scaled) conformal point. -/
@[inline] def down? (X : CVec V) : Option (CVec V) := (normalize? X).map euclidean

/-- Squared Euclidean distance of two (possibly scaled) points:
`|x - y|² = -2 X⋅Y / ((X⋅∞)(Y⋅∞))`. -/
@[inline] def distance2 (X Y : CVec V) : Float := -2.0 * dot X Y / (dot X (inf V) * dot Y (inf V))

/-- The dual hypersphere with centre `c` and radius `r`: `up c - ½r²∞`. -/
@[inline] def dualSphere (c : CVec V) (r : Float) : CVec V := point c - (0.5 * r * r) • inf V

/-- The dual hyperplane `{x | n⋅x = δ}`: `n + δ∞`. -/
@[inline] def dualPlane (n : CVec V) (δ : Float) : CVec V := n + δ • inf V

/-- Centre and squared radius of a dual sphere (`r² < 0` for an imaginary
sphere); `none` for a flat (a plane). Uses `s⋅s = w² r²` and centre
`= euclidean(s)/w`. -/
@[inline] def sphereCenterRadius2? (s : CVec V) : Option (CVec V × Float) := do
  let w := weight s
  if w.abs < 1e-300 then none
  some ((1.0 / w) • euclidean s, dot s s / (w * w))

/-- Unit normal and distance `(n, δ)` of a dual plane `π = n + δ∞` (any scale);
`none` if the Euclidean part vanishes. -/
@[inline] def planeNormalDistance? (π : CVec V) : Option (CVec V × Float) := do
  let n := euclidean π
  let len := Float.sqrt (dot n n)
  if len < 1e-300 then none
  some ((1.0 / len) • n, -dot π (origin V) / len)

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

/-- The translator `T = 1 - ½ t∞` (as a multivector); `translate` applies it. -/
@[inline] def translator (t : CVec V) : Multivector V Float :=
  Multivector.scalar 1.0 - (0.5 • (t ∧ inf V)).toMultivector

/-- Translate a conformal object by the Euclidean vector `t`: the sandwich
`T X T̃`, written out with geometric products so it applies to any grade. -/
@[inline] def translate (t : CVec V) (X : Multivector V Float) : Multivector V Float :=
  let T := translator t
  T * X * ~T

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

end Conformal

end Grassmann

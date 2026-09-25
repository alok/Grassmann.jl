/-
The canonical up/down maps `↑` (`project`) and `↓` (`reject`) of Grassmann.jl
(`src/Grassmann.jl:164-228`): Euclidean points to and from the Riemann sphere (a space
with a null point `∞` *or* `∅`) or conformal space (`∞` *and* `∅`), and the identity in a
space without them.

| space | `↑ω` | `↓ω` |
|---|---|---|
| `∞` and `∅` (conformal) | `(v∞/2)·((~ω)⋅ω) + v∅ + ω` | `((v∞∅ ∧ ω) ⋅ inv(~v∞∅)) / (-ω⋅v∞)` |
| `∞` or `∅` alone (Riemann sphere, `b` the null point) | `b·(ω²-1)/(ω²+1) + 2ω/(ω²+1)` | `(~(ω∧b) ⋅ b)/(1 - b⋅ω)` |
| neither | `ω` | `ω` |

with `ω² = (~ω)⋅ω`. The choice of `v∞`/`v∅` is automatic, from `V.hasinf`/`V.hasorigin`
(Julia's `@generated` dispatch on `hasinf(V)`, `hasorigin(V)`). The typed functions are
`Chain.up`/`Chain.down` and `Multivector.up`/`Multivector.down` (`Chain.project` is the
subspace projection `W(x)` of `Grassmann.Forms.Eval`); `Grassmann.project`/`reject` dispatch
on the element type. The explicit forms
`project(ω, b)`, `project(ω, p, m)`, `reject(ω, b)` and `reject(ω, ∞, ∅)`
(`src/Grassmann.jl:185-210`) take the null points (or the conformal split) as arguments.
On spaces, `↓V` drops the null generators (`V(2:n)`, conformal `V(3:n)`).

Lean's `↑` is the coercion arrow, so the notation here is `⇡ω` (`project`) and `⇣ω`
(`reject`), scoped in `Grassmann`; the functions keep Julia's names.

Typing: on vectors (`Chain V 1 α`, any field-like coefficient) every result is a vector,
the static type of Julia's values (Julia returns a `Multivector` with a zero scalar for
`↑` in conformal space, the same coefficients); on multivectors (`Float`) the formulas run
in the full algebra, with `inv` undefined giving `NaN` coefficients.
-/
import Grassmann.Composite.Ring
import Grassmann.Forms.Eval

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase

variable {V : TensorBundle} {α : Type} [Coeff α]

namespace Composite

/-- The blade bits of the point at infinity `v∞` (generator 1, when `V.hasinf`). -/
@[inline] def infBits (_ : TensorBundle) : UInt64 := 1

/-- The blade bits of the origin `v∅` (the generator after `v∞`, when `V.hasorigin`). -/
@[inline] def originBits (V : TensorBundle) : UInt64 := if V.hasinf then 2 else 1

/-- The unit vector of the one-generator blade `b`. -/
@[inline] def unitVec (V : TensorBundle) (α : Type) [Coeff α] (b : UInt64) : Chain V 1 α :=
  Chain.ofBlade (⟨b⟩ : Submanifold V 1) Coeff.one

end Composite

open Composite

namespace Chain

variable [Kernels V] [Div α]

/-- `(~ω)⋅ω` of a vector, the scalar `ω²` of the up/down maps. -/
@[inline] def sqr (ω : Chain V 1 α) : α := getD (contraction (~ω) ω : Chain V (1 - 1) α).v 0

/-- `a ⋅ b` of two vectors, a scalar. -/
@[inline] def dot1 (a b : Chain V 1 α) : α := getD (contraction a b : Chain V (1 - 1) α).v 0

/-- Julia `project(ω, b)` (`src/Grassmann.jl:185-189`): `(2/(ω²+1))·ω + ((ω²-1)/(ω²+1))·b`,
the stereographic lift to the sphere with null point `b`. -/
@[inline] def upWith (ω b : Chain V 1 α) : Chain V 1 α :=
  let ω2 := ω.sqr
  let iω2 := Coeff.one / (ω2 + Coeff.one)
  (Coeff.ofInt 2 * iω2) * ω + ((ω2 - Coeff.one) * iω2) * b

/-- Julia `project(ω, p, m)` (`src/Grassmann.jl:190-194`): the conformal split with point-like
part `p` and Minkowski part `m`, `(2ω + (ω²-1)p + (ω²+1)m)/(ω²+1)` (each term scaled
separately, in Julia's order). -/
@[inline] def upPM (ω p m : Chain V 1 α) : Chain V 1 α :=
  let ω2 := ω.sqr
  let iω2 := Coeff.one / (ω2 + Coeff.one)
  (Coeff.ofInt 2 * iω2) * ω + ((ω2 - Coeff.one) * iω2) * p + ((ω2 + Coeff.one) * iω2) * m

/-- Julia `↑ω` = `project(ω)` of a vector (`src/Grassmann.jl:164-183`), choosing `v∞`/`v∅`
from the space: conformal `(v∞/2)ω² + v∅ + ω`, Riemann sphere `project(ω, b)`, else `ω`. -/
@[inline] def up (ω : Chain V 1 α) : Chain V 1 α :=
  if V.hasinf && V.hasorigin then
    let half : α := Coeff.one / Coeff.ofInt 2
    let a : Chain V 1 α := unitVec V α (infBits V) * half
    let b : Chain V 1 α := a * ω.sqr
    b + unitVec V α (originBits V) + ω
  else if V.hasinf then
    let ω2 := ω.sqr
    let iω2 := Coeff.one / (ω2 + Coeff.one)
    unitVec V α (infBits V) * ((ω2 - Coeff.one) * iω2) + (Coeff.ofInt 2 * iω2) * ω
  else if V.hasorigin then
    let ω2 := ω.sqr
    let iω2 := Coeff.one / (ω2 + Coeff.one)
    unitVec V α (originBits V) * ((ω2 - Coeff.one) * iω2) + (Coeff.ofInt 2 * iω2) * ω
  else ω

/-- Julia `reject(ω, b)` (`src/Grassmann.jl:209`): `(~(b∧ω) ⋅ b)/(1 - ω⋅b)`. -/
@[inline] def downWith (ω b : Chain V 1 α) : Chain V 1 α :=
  let num : Chain V (1 + 1 - 1) α := contraction (~(b ∧ ω : Chain V (1 + 1) α)) b
  num.cast (by decide) / (Coeff.one - dot1 ω b)

/-- `(~(ω∧b) ⋅ b)/(1 - b⋅ω)`: the canonical Riemann-sphere `↓` (`src/Grassmann.jl:201-205`). -/
@[inline] def downRiemann (ω b : Chain V 1 α) : Chain V 1 α :=
  let num : Chain V (1 + 1 - 1) α := contraction (~(ω ∧ b : Chain V (1 + 1) α)) b
  num.cast (by decide) / (Coeff.one - dot1 b ω)

/-- Julia `reject(ω, ∞, ∅)` (`src/Grassmann.jl:210`): with `m = ∞∧∅`,
`((m∧ω) ⋅ ~inv(m)) / (-ω⋅∞)`. -/
@[inline] def downPM (ω inf orig : Chain V 1 α) : Chain V 1 α :=
  let m : Chain V (1 + 1) α := inf ∧ orig
  let t : Chain V (1 + 1 + 1) α := m ∧ ω
  let num : Chain V (1 + 1 + 1 - (1 + 1)) α := contraction t (~(Chain.inv m))
  num.cast (by decide) / (-(dot1 ω inf))

/-- The canonical conformal `↓` (`src/Grassmann.jl:196-200`):
`((v∞∅ ∧ ω) ⋅ inv(~v∞∅)) / (-ω⋅v∞)`. -/
@[inline] def downConformal (ω inf orig : Chain V 1 α) : Chain V 1 α :=
  let m : Chain V (1 + 1) α := inf ∧ orig
  let t : Chain V (1 + 1 + 1) α := m ∧ ω
  let num : Chain V (1 + 1 + 1 - (1 + 1)) α := contraction t (Chain.inv (~m))
  num.cast (by decide) / (-(dot1 ω inf))

/-- Julia `↓ω` = `reject(ω)` of a vector (`src/Grassmann.jl:196-205`), choosing `v∞`/`v∅`
from the space. -/
@[inline] def down (ω : Chain V 1 α) : Chain V 1 α :=
  if V.hasinf && V.hasorigin then
    downConformal ω (unitVec V α (infBits V)) (unitVec V α (originBits V))
  else if V.hasinf then downRiemann ω (unitVec V α (infBits V))
  else if V.hasorigin then downRiemann ω (unitVec V α (originBits V))
  else ω

end Chain

namespace Multivector

variable [Kernels V]

/-- The multivector `x·e_b` of a blade. -/
@[inline] def bladeF (b : UInt64) (x : Float) : Multivector V Float :=
  toMultivector (Chain.ofBlade (⟨b⟩ : Submanifold V (popcount b)) x)

/-- `a / b = a ⟑ inv(b)` of multivectors (Julia's right division), `NaN` where `inv` is
undefined. -/
@[inline] def rdiv (a b : Multivector V Float) : Multivector V Float := a * Multivector.invD b

/-- Julia `↑ω` of a general element (`src/Grassmann.jl:164-183`) in the full algebra:
conformal `(v∞/2)⟑((~ω)⋅ω) + v∅ + ω`, Riemann sphere `b⟑((ω²-1)⟑inv(ω²+1)) + (2inv(ω²+1))⟑ω`
with `ω² = (~ω)⋅ω`, else `ω`. -/
@[specialize V] def up (ω : Multivector V Float) : Multivector V Float :=
  let ω2 : Multivector V Float := contraction (~ω) ω
  if V.hasinf && V.hasorigin then
    (bladeF (V := V) (infBits V) 0.5 * ω2 : Multivector V Float) + bladeF (originBits V) 1 + ω
  else if V.hasinf || V.hasorigin then
    let b : Multivector V Float := bladeF (if V.hasinf then infBits V else originBits V) (1 : Float)
    let iω2 := Multivector.invD (Multivector.addScalar 1 ω2)
    b * (Multivector.addScalar (-1) ω2 * iω2) + (iω2 * (2 : Float)) * ω
  else ω

/-- Julia `↓ω` of a general element (`src/Grassmann.jl:196-205`) in the full algebra:
conformal `((v∞∅∧ω)⋅inv(~v∞∅)) / (-ω⋅v∞)`, Riemann sphere `(~(ω∧b)⋅b)/(1-b⋅ω)`, else `ω`. -/
@[specialize V] def down (ω : Multivector V Float) : Multivector V Float :=
  if V.hasinf && V.hasorigin then
    let m : Multivector V Float := bladeF (infBits V ||| originBits V) (1 : Float)
    let num : Multivector V Float := contraction (m ∧ ω : Multivector V Float) (Multivector.invD (~m : Multivector V Float))
    let den : Multivector V Float := -(contraction ω (bladeF (V := V) (infBits V) (1 : Float)) : Multivector V Float)
    rdiv num den
  else if V.hasinf || V.hasorigin then
    let b : Multivector V Float := bladeF (if V.hasinf then infBits V else originBits V) (1 : Float)
    let num : Multivector V Float := contraction (~(ω ∧ b : Multivector V Float)) b
    let bw : Multivector V Float := contraction b ω
    rdiv num (Multivector.addScalar 1 (-bw))
  else ω

end Multivector

/-- The up/down maps of an element type (Julia's `project`/`reject` methods). -/
class UpDown (X : Type) where
  /-- Julia `↑` / `project`. -/
  project : X → X
  /-- Julia `↓` / `reject`. -/
  reject : X → X

instance [Kernels V] [Div α] : UpDown (Chain V 1 α) := ⟨Chain.up, Chain.down⟩
instance [Kernels V] : UpDown (Multivector V Float) := ⟨Multivector.up, Multivector.down⟩

/-- Julia `project(ω)` (`↑ω`). -/
@[inline] def project {X : Type} [UpDown X] (x : X) : X := UpDown.project x

/-- Julia `reject(ω)` (`↓ω`). -/
@[inline] def reject {X : Type} [UpDown X] (x : X) : X := UpDown.reject x

/-- Julia `↑ω` (`project`; Lean's `↑` is the coercion arrow). -/
scoped prefix:max "⇡" => project

/-- Julia `↓ω` (`reject`). -/
scoped prefix:max "⇣" => reject

namespace Composite

/-- Julia `↓V` of a space (`src/Grassmann.jl:196-205` on a `Submanifold` that is not a
basis blade): the subspace without the null generators, `V(2:n)` for a space with `∞` or
`∅`, `V(3:n)` for conformal space, `V` itself otherwise. -/
@[specialize V] def rejectSpace (V : TensorBundle) : TensorBundle :=
  if V.hasinf && V.hasorigin then Forms.restrict V (lowMask V.n &&& ~~~3)
  else if V.hasinf || V.hasorigin then Forms.drop1 V
  else V

end Composite

end Grassmann

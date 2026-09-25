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

/-- The signature mask of a space whose vectors have a diagonal `±1` Gram matrix apart from a
conformal null pair (DirectSum's `gram`: `g(e∞,e∅) = -1`, `g(e∞,e∞) = g(e∅,e∅) = 0`, every
other generator `-1` iff its signature bit is set): `.signature`/`.euclid` metrics of
non-dual, non-tangent spaces; `none` otherwise (the product kernels are used there). -/
@[inline] def vecSig? (V : TensorBundle) : Option UInt64 :=
  if V.diffvars != 0 || V.dyadmode != 0 then none
  else match V.metric with
    | .signature s => some s
    | .euclid => some 0
    | _ => none

/-- `Σ_{k ≥ k₀} g(e_k, e_k)·x_k·y_k` over the generators with signature mask `s`. -/
@[specialize] def vdotLoop {n : Nat} (s : UInt64) (x y : Values α n) (k : Nat) (acc : α) : Nat → α
  | 0 => acc
  | fuel + 1 =>
    if h : k < n then
      let p := x.get ⟨k, h⟩ * y.get ⟨k, h⟩
      vdotLoop s x y (k + 1) (if (s >>> k.toUInt64) &&& 1 == 1 then acc - p else acc + p) fuel
    else acc

/-- `x ⋅ y` of two vectors (coefficients in generator order) in a `vecSig?` space with mask
`s`: the Gram form, the conformal pair contributing `-(x∞y∅ + x∅y∞)`. -/
@[inline] def vdot (V : TensorBundle) (s : UInt64) {n : Nat} (x y : Values α n) : α :=
  if V.hasinf && V.hasorigin then
    vdotLoop s x y 2 Coeff.zero n - (getD x 0 * getD y 1 + getD x 1 * getD y 0)
  else vdotLoop s x y 0 Coeff.zero n

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

/-- `up` in a `vecSig?` space (mask `sg`) without product kernels: conformal
`ω + v∅ + (ω²/2)·v∞`, Riemann sphere `(2/(ω²+1))·ω + ((ω²-1)/(ω²+1))·b`, one pass over the
coefficients (`ω² = ω⋅ω` from the Gram form). -/
@[inline] def upFast (sg : UInt64) (ω : Chain V 1 α) : Chain V 1 α :=
  if V.hasinf || V.hasorigin then
    let x := ω.v
    let ω2 := vdot V sg x x
    if V.hasinf && V.hasorigin then
      let half : α := Coeff.one / Coeff.ofInt 2
      let q := half * ω2
      ⟨Values.ofFn fun i =>
        if i.1 == 0 then q + x.get i else if i.1 == 1 then Coeff.one + x.get i else x.get i⟩
    else
      let iω2 := Coeff.one / (ω2 + Coeff.one)
      let a := Coeff.ofInt 2 * iω2
      let c := (ω2 - Coeff.one) * iω2
      ⟨Values.ofFn fun i => if i.1 == 0 then c + a * x.get i else a * x.get i⟩
  else ω

/-- `up` through the space's product kernels (every metric). -/
@[inline] def upGeneric (ω : Chain V 1 α) : Chain V 1 α :=
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

/-- Julia `↑ω` = `project(ω)` of a vector (`src/Grassmann.jl:164-183`), choosing `v∞`/`v∅`
from the space: conformal `(v∞/2)ω² + v∅ + ω`, Riemann sphere `project(ω, b)`, else `ω`. -/
@[inline] def up (ω : Chain V 1 α) : Chain V 1 α :=
  match vecSig? V with
  | some sg => upFast sg ω
  | none => upGeneric ω

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

/-- `down` in a `vecSig?` space (mask `sg`) without product kernels. Conformal: the
numerator `(v∞∅ ∧ ω) ⋅ inv(~v∞∅)` keeps the non-null part of `ω` (the null pair's
bivector squares to `1`) and `-ω⋅v∞ = ω∅`, so `↓ω = ω_E / ω∅` (zero on the pair). Riemann
sphere with null point `b = e₀`, `σ = g(b, b)`: `~(ω∧b) ⋅ b = σ·ω_E` (zero on `b`) and
`b⋅ω = σ·ω_b`, so `↓ω = σ·ω_E / (1 - σ·ω_b)`. -/
@[inline] def downFast (sg : UInt64) (ω : Chain V 1 α) : Chain V 1 α :=
  let x := ω.v
  if V.hasinf && V.hasorigin then
    let d := getD x 1
    ⟨Values.ofFn fun i => if i.1 < 2 then Coeff.zero / d else x.get i / d⟩
  else if V.hasinf || V.hasorigin then
    let neg := sg &&& 1 == 1
    let xb := getD x 0
    let den := if neg then Coeff.one + xb else Coeff.one - xb
    ⟨Values.ofFn fun i => if i.1 == 0 then Coeff.zero / den else (if neg then -(x.get i) else x.get i) / den⟩
  else ω

/-- `down` through the space's product kernels (every metric). -/
@[inline] def downGeneric (ω : Chain V 1 α) : Chain V 1 α :=
  if V.hasinf && V.hasorigin then
    downConformal ω (unitVec V α (infBits V)) (unitVec V α (originBits V))
  else if V.hasinf then downRiemann ω (unitVec V α (infBits V))
  else if V.hasorigin then downRiemann ω (unitVec V α (originBits V))
  else ω

/-- Julia `↓ω` = `reject(ω)` of a vector (`src/Grassmann.jl:196-205`), choosing `v∞`/`v∅`
from the space. -/
@[inline] def down (ω : Chain V 1 α) : Chain V 1 α :=
  match vecSig? V with
  | some sg => downFast sg ω
  | none => downGeneric ω

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

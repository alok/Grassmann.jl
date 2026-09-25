/-
`abs`, `unit`, `unitize`, `unitnorm` and `geomabs` of every element kind, with Julia's
result kinds (AbstractTensors `AT:435-480`, Grassmann `src/multivectors.jl:669-696`):

| element | `abs` | `unit`, `unitize`, `unitnorm` | `geomabs` |
|---|---|---|---|
| `Chain V G`, `Single V G`, `Couple V` | `Single V 0` (`3.74v`) | the same kind | `Couple V` on the pseudoscalar |
| `Spinor V`, `CoSpinor V` | `Spinor V` (Julia: a scalar `Single` in `ℝ3`) | the same kind | `Multivector V` |
| `PseudoCouple V`, `Multivector V` | `Multivector V` | `Multivector V` | `Multivector V` |

* `abs(t) = sqrt(abs2(t))` (`AT:435`): for chains, terms and couples `abs2` is a scalar, so
  `abs` is the scalar `Single`; for spinors it is the spinor square root (`Half.sqrt`), a
  scalar whenever `abs2` is (every spinor of a space of dimension ≤ 3). `NaN` where the
  square root of a negative scalar is taken (Julia throws `DomainError`).
* `unit(t) = t/abs(t)` (`AT:462`), `unitize(t) = counit(t) = t/value(coabs(t))` (`AT:470-472`),
  `unitnorm(t) = t/norm(geomabs(t))` (`AT:479`), where `norm` is the coefficient 2-norm.
* `geomabs(t) = abs(t) + coabs(t)` (`AT:454`), `coabs(t) = complementleft(abs(complementright(t)))`:
  a couple `|t| + c·I` for chains, terms and couples.

Division by a scalar element is coefficient-wise (Julia's `/` by a `Single{V,0}`).
-/
import Grassmann.Composite.Ring

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase Composite

variable {V : TensorBundle}

namespace Composite

/-- The coefficient 2-norm `√(re² + im²)` of a couple (Julia `norm(::Couple)`). -/
@[inline] def norm2 (re im : Float) : Float := Float.sqrt (re * re + im * im)

/-- The pseudoscalar coefficient of a multivector (storage index `2ⁿ - 1`). -/
@[inline] def pseudoCoef (m : Multivector V Float) : Float := getD m.v (Forms.pow2 V.n - 1)

end Composite

namespace Chain

variable {G : Nat} [Kernels V]

/-- Julia `abs(t)` of a chain (`AT:435`): the scalar `Single` `√abs2(t)` (`abs(v1+2v2+3v3) =
3.74v` in `ℝ3`). -/
@[inline] def abs (c : Chain V G Float) : Single V 0 Float := ⟨0, c.absF⟩

/-- Julia `unit(t) = t/abs(t)` of a chain (`AT:462`). -/
@[inline] def unit (c : Chain V G Float) : Chain V G Float := c / c.absF

/-- The coefficient of `coabs(t)` on the pseudoscalar (Julia `value(coabs(t))`). -/
@[inline] def coabsF (c : Chain V G Float) : Float := getD c.coabs.v 0

/-- Julia `geomabs(t) = abs(t) + coabs(t)` of a chain (`AT:454`): `|t| + c·I`
(`geomabs(v1+2v2+3v3) = 3.74 + 3.74v₁₂₃` in `ℝ3`). -/
@[inline] def geomabs (c : Chain V G Float) : Couple V Float := ⟨pseudoMask V, c.absF, c.coabsF⟩

/-- Julia `unitnorm(t) = t/norm(geomabs(t))` of a chain (`AT:479`). -/
@[inline] def unitnorm (c : Chain V G Float) : Chain V G Float := c / norm2 c.absF c.coabsF

/-- Julia `unitize(t) = counit(t) = t/value(coabs(t))` of a chain (`AT:470-472`). -/
@[inline] def unitize (c : Chain V G Float) : Chain V G Float := c / c.coabsF

end Chain

namespace Single

variable {G : Nat} [Kernels V]

/-- `√abs2(t)` of a term (a `Float`). -/
@[inline] def absF (s : Single V G Float) : Float := Float.sqrt s.abs2

/-- Julia `abs(t)` of a term (`abs(2v12) = 2.0v`): the scalar `Single`. -/
@[inline] def abs (s : Single V G Float) : Single V 0 Float := ⟨0, s.absF⟩

/-- Julia `unit(t) = t/abs(t)` of a term. -/
@[inline] def unit (s : Single V G Float) : Single V G Float := ⟨s.bits, s.val / s.absF⟩

/-- The coefficient of `coabs(t)` on the pseudoscalar (through the chain of the term). -/
@[inline] def coabsF (s : Single V G Float) : Float := (toChain s).coabsF

/-- Julia `geomabs(t)` of a term: `|t| + c·I`. -/
@[inline] def geomabs (s : Single V G Float) : Couple V Float := ⟨pseudoMask V, s.absF, s.coabsF⟩

/-- Julia `unitnorm(t)` of a term. -/
@[inline] def unitnorm (s : Single V G Float) : Single V G Float := ⟨s.bits, s.val / norm2 s.absF s.coabsF⟩

/-- Julia `unitize(t)` of a term. -/
@[inline] def unitize (s : Single V G Float) : Single V G Float := ⟨s.bits, s.val / s.coabsF⟩

end Single

namespace Couple

variable [Kernels V]

/-- `√abs2(z)` of a couple. -/
@[inline] def absF (z : Couple V Float) : Float := Float.sqrt z.abs2

/-- Julia `abs(z)` of a couple (`abs(1+2v12) = 2.236v`): the scalar `Single`. -/
@[inline] def abs (z : Couple V Float) : Single V 0 Float := ⟨0, z.absF⟩

/-- Julia `unit(z) = z/abs(z)` of a couple. -/
@[inline] def unit (z : Couple V Float) : Couple V Float := let a := z.absF; ⟨z.bits, z.re / a, z.im / a⟩

/-- The coefficient of `coabs(z)` on the pseudoscalar. -/
@[inline] def coabsF (z : Couple V Float) : Float := pseudoCoef (Multivector.coabs (toMultivector z))

/-- Julia `geomabs(z)` of a couple: `|z| + c·I`. -/
@[inline] def geomabs (z : Couple V Float) : Couple V Float := ⟨pseudoMask V, z.absF, z.coabsF⟩

/-- Julia `unitnorm(z)` of a couple. -/
@[inline] def unitnorm (z : Couple V Float) : Couple V Float :=
  let a := norm2 z.absF z.coabsF
  ⟨z.bits, z.re / a, z.im / a⟩

/-- Julia `unitize(z)` of a couple. -/
@[inline] def unitize (z : Couple V Float) : Couple V Float :=
  let a := z.coabsF
  ⟨z.bits, z.re / a, z.im / a⟩

end Couple

namespace Half

variable {p : Bool} [Kernels V]

/-- Julia `abs(t) = sqrt(abs2(t))` of a spinor or co-spinor: the spinor square root of
`abs2(t) = (~t)⟑t` (a scalar spinor when `abs2` is a scalar). -/
@[inline] def abs (h : Half V p Float) : Half V false Float :=
  let a := h.abs2
  if a.isScalar then Half.scalarF (Float.sqrt a.scalarValue) else Half.sqrt a

/-- Julia `unit(t) = t/abs(t) = t ⟑ inv(abs(t))` of a spinor or co-spinor. -/
@[inline] def unit (h : Half V p Float) : Half V p Float :=
  let a := h.abs
  if a.isScalar then ⟨vmap (· / a.scalarValue) h.v⟩
  else ((h * Half.invD a : Half V (p ^^ false) Float)).cast (by simp)

/-- Julia `geomabs(t) = abs(t) + coabs(t)` of a spinor or co-spinor (a multivector). -/
@[inline] def geomabs (h : Half V p Float) : Multivector V Float := Multivector.geomabs (toMultivector h)

/-- Julia `unitnorm(t) = t/norm(geomabs(t))` of a spinor or co-spinor. -/
@[inline] def unitnorm (h : Half V p Float) : Half V p Float :=
  let a := h.geomabs.fnorm
  ⟨vmap (· / a) h.v⟩

/-- Julia `unitize(t) = t/value(coabs(t))` of a spinor or co-spinor. -/
@[inline] def unitize (h : Half V p Float) : Half V p Float :=
  let a := pseudoCoef (Multivector.coabs (toMultivector h))
  ⟨vmap (· / a) h.v⟩

end Half

namespace PseudoCouple

variable [Kernels V]

/-- Julia `abs(z)` of a pseudo-couple (`abs2` need not be a scalar: a multivector). -/
@[inline] def abs (z : PseudoCouple V Float) : Multivector V Float := Multivector.abs (toMultivector z)

/-- Julia `unit(z)` of a pseudo-couple. -/
@[inline] def unit (z : PseudoCouple V Float) : Multivector V Float := Multivector.unit (toMultivector z)

/-- Julia `geomabs(z)` of a pseudo-couple. -/
@[inline] def geomabs (z : PseudoCouple V Float) : Multivector V Float := Multivector.geomabs (toMultivector z)

/-- Julia `unitnorm(z)` of a pseudo-couple. -/
@[inline] def unitnorm (z : PseudoCouple V Float) : Multivector V Float := Multivector.unitnorm (toMultivector z)

/-- Julia `unitize(z)` of a pseudo-couple. -/
@[inline] def unitize (z : PseudoCouple V Float) : Multivector V Float := Multivector.unitize (toMultivector z)

end PseudoCouple

end Grassmann

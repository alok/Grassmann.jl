/-
Quaternions and the other even/odd containers: `Spinor` closed forms of `log`,
`log1p`, `sqrt`, `cbrt`, the quaternion helpers, and the `CoSpinor` /
`PseudoCouple` dispatch (Grassmann.jl `src/composite.jl:112-128`, `:360-405`,
`:436-452`, `:629-633`, `src/multivectors.jl:999-1014`, `:1079-1090`;
port-notes/grassmann-composite.md §4.2.6, §4.3.1, §4.3.4, §4.4,
grassmann-types.md §4.8).

A `Quaternion` is Julia's `Spinor{V,T,4}` (`n = 3`); in a space without negative
generators (`iszero(metric(V))`) its `log`, `sqrt`, `cbrt` use the polar form
`q = r·exp(θ·b/|b|)` with `r = radius(q) = √⟨~q q⟩₀` and
`angle(q) = (acos(⟨q⟩₀/r)/|b|)·b`, `b` the bivector part; every other spinor goes
through the `qlog` series. Julia returns `NaN` for a real quaternion (the angle's
`0/0`, port-notes §8.3 item 14); here the angle of a positive real quaternion is
`0` (a negative one keeps the `NaN`: its axis is undetermined).

`CoSpinor` functions convert to `Multivector` (`C:392-405`); a `PseudoCouple`
`a + b·I` (scalar blade) is the couple on the pseudoscalar, any other goes through
its `multispin` (here: the `Multivector`, whose values agree).
-/
import Grassmann.Composite.Chain

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase Composite

variable {V : TensorBundle}

namespace Composite

/-- Julia's `Quaternion` dispatch with `iszero(metric(V))` (`src/composite.jl:367-368`,
`:441-442`): a 3-generator space without negative generators. -/
@[inline] def euclideanQuaternions (V : TensorBundle) : Bool := V.n == 3 && zeroMetric V

end Composite

namespace Half

variable [Kernels V]

/-- The bivector part of a spinor (Julia `bivector(z)`). -/
@[inline] def bivectorPart (s : Half V false Float) : Chain V 2 Float := s.grade 2

/-- Julia `radius(z::Quaternion) = value(scalar(abs(z)))` (`src/composite.jl:629`):
`√⟨~z z⟩₀`. -/
@[inline] def radius (s : Half V false Float) : Float := Float.sqrt (revScalar s s)

/-- The coefficient `acos(⟨z⟩₀/r)/|b|` of Julia's `angle(z::Quaternion, r)`
(`src/composite.jl:630-633`), `b` the bivector part, `|b| = √contraction(b, b)`; `0` for a
positive real quaternion (Julia: `0/0`). -/
def angleCoef (s : Half V false Float) (r : Float) : Float :=
  let θ := Float.acos (s.scalarValue / r)
  let nb := Float.sqrt (getD s.bivectorPart.abs2.v 0)
  if nb == f0 && θ == f0 then f0 else θ / nb

/-- Julia `angle(z::Quaternion) = (acos(⟨z⟩₀/r)/|b|)·b` as a bivector chain. -/
@[inline] def angle (s : Half V false Float) : Chain V 2 Float :=
  s.bivectorPart * s.angleCoef s.radius

/-- The polar `log(z::Quaternion) = log(r) + angle(z, r)` (`src/composite.jl:367`). -/
def logPolar (s : Half V false Float) : Half V false Float :=
  let r := s.radius
  addScalar (F64.log r) (Chain.evenHalf (s.bivectorPart * s.angleCoef r))

/-- Julia `log(t::Spinor)`: the polar form for Euclidean quaternions
(`src/composite.jl:367`), otherwise `qlog((t - 1)/(t + 1))` (`C:369`); `none` where Julia
throws. -/
def log? (s : Half V false Float) : Option (Half V false Float) :=
  if euclideanQuaternions V then some s.logPolar else s.logSeries?

/-- Julia `log(t::Spinor)`; `NaN` coefficients where Julia throws. -/
@[inline] def log (s : Half V false Float) : Half V false Float := s.log?.getD nan

/-- Julia `log1p(t::Spinor)`: `log(1 + t)` for Euclidean quaternions (`C:368`), otherwise
`qlog(t/(t + 2))` (`C:370`); `none` where Julia throws. -/
def log1p? (s : Half V false Float) : Option (Half V false Float) :=
  if euclideanQuaternions V then some (addScalar f1 s).logPolar else s.log1pSeries?

/-- Julia `log1p(t::Spinor)`; `NaN` coefficients where Julia throws. -/
@[inline] def log1p (s : Half V false Float) : Half V false Float := s.log1p?.getD nan

/-- Julia `sqrt`/`cbrt` of a spinor (`src/composite.jl:436-445`): for Euclidean quaternions
`qrt(radius(t))·exp(angle(t)/n)` (no scalar test); otherwise
`isscalar(t) ? qrt(scalar(t)) : exp(log(t)/n)`. -/
def root (qrt : Float → Float) (n : Float) (s : Half V false Float) : Half V false Float :=
  if euclideanQuaternions V then
    let r := s.radius
    let e := Chain.expEven (s.bivectorPart * (s.angleCoef r / n))
    ⟨e.v.map (qrt r * ·)⟩
  else if s.isScalar then scalarF (qrt s.scalarValue)
  else match s.logSeries? with
    | some l => exp (sdiv l n)
    | none => nan

/-- Julia `sqrt(t::Spinor)`. -/
@[inline] def sqrt (s : Half V false Float) : Half V false Float := root Float.sqrt f2 s

/-- Julia `cbrt(t::Spinor)`. -/
@[inline] def cbrt (s : Half V false Float) : Half V false Float := root F64.cbrt f3 s

/-- `tanh t = sinh t / cosh t` (AbstractTensors `AT:419`) on a spinor. -/
def tanh (s : Half V false Float) : Half V false Float := smul' s.sinh (invD s.cosh)

/-- Julia `b ^ t = exp(t ⟑ log(b))` for a real base (AbstractTensors `AT:326`). -/
@[inline] def rpow (b : Float) (s : Half V false Float) : Half V false Float :=
  exp ⟨s.v.map (· * F64.log b)⟩

end Half

/-! ## Quaternion helpers (`src/multivectors.jl:1079-1090`) -/

namespace Spinor

variable {α : Type} [Coeff α]

/-- Julia `quatvalue(q::Quaternion) = (q[1], q[2], -q[3], q[4])`: the components
`(s, i, j, k)` of `quaternion(s, i, j, k)` (`i = v₁₂`, `j = -v₁₃`, `k = v₂₃`). -/
def quatvalue (q : Spinor V α) : Values α 4 :=
  Values.ofFn fun t => match t.1 with
    | 0 => getD q.v 0 | 1 => getD q.v 1 | 2 => -getD q.v 2 | _ => getD q.v 3

/-- Julia `quatvalue(q::TensorAlgebra) = quatvalue(Spinor(even(q)))` for a multivector. -/
@[inline] def quatvalueOf (m : Multivector V α) : Values α 4 := quatvalue (m.half false)

end Spinor

namespace CoSpinor

variable {α : Type} [Coeff α]

/-- Julia `quatvalue(q::AntiQuaternion) = (q[4], q[3], q[2], q[1])`. -/
def quatvalue (q : CoSpinor V α) : Values α 4 :=
  Values.ofFn fun t => getD q.v (3 - t.1)

variable [Kernels V]

/-- Julia `exp(t::CoSpinor) = exp(Multivector(t))` (`src/composite.jl:392`). -/
@[inline] def exp (t : CoSpinor V Float) : Multivector V Float := Multivector.exp (toMultivector t)
/-- Julia `expm1(t::CoSpinor) = expm1(Multivector(t))` (`C:393`). -/
@[inline] def expm1 (t : CoSpinor V Float) : Multivector V Float := Multivector.expm1 (toMultivector t)
/-- Julia `log(t::CoSpinor) = log(Multivector(t))` (`C:394`). -/
@[inline] def log (t : CoSpinor V Float) : Multivector V Float := Multivector.log (toMultivector t)
/-- Julia `log1p(t::CoSpinor) = log1p(Multivector(t))` (`C:395`). -/
@[inline] def log1p (t : CoSpinor V Float) : Multivector V Float := Multivector.log1p (toMultivector t)
/-- Julia `cosh(t::CoSpinor) = cosh(Multivector(t))` (`C:403`). -/
@[inline] def cosh (t : CoSpinor V Float) : Multivector V Float := Multivector.cosh (toMultivector t)
/-- Julia `sinh(t::CoSpinor) = sinh(Multivector(t))` (`C:403`). -/
@[inline] def sinh (t : CoSpinor V Float) : Multivector V Float := Multivector.sinh (toMultivector t)
/-- Julia `sqrt(t::CoSpinor)`: the generic `isscalar(t) ? … : exp(log(t)/2)` on the multivector. -/
@[inline] def sqrt (t : CoSpinor V Float) : Multivector V Float := Multivector.sqrt (toMultivector t)
/-- Julia `cbrt(t::CoSpinor)`. -/
@[inline] def cbrt (t : CoSpinor V Float) : Multivector V Float := Multivector.cbrt (toMultivector t)

end CoSpinor

/-! ## Pseudo-couples (`src/composite.jl:112-128`, `:373-390`, `:400-405`) -/

namespace PseudoCouple

variable [Kernels V]

/-- The couple `re + im·I` on the pseudoscalar of a pseudo-couple on the scalar blade
(Julia `Couple{V,Submanifold(V)}(realvalue(t), imagvalue(t))`). -/
@[inline] def onPseudo (z : PseudoCouple V Float) : Couple V Float := ⟨pseudoMask V, z.re, z.im⟩

/-- A couple on the pseudoscalar as the pseudo-couple `re·1 + im·I` (blade `B = 1`). -/
@[inline] def ofPseudo (w : Couple V Float) : PseudoCouple V Float := ⟨0, w.re, w.im⟩

/-- Julia `exp(t::PseudoCouple{V,B})` (`src/composite.jl:120-128`): through the couple on
`I` when `B` is the scalar blade, else through `multispin(t)`; as a multivector. -/
def exp (z : PseudoCouple V Float) : Multivector V Float :=
  if z.bits == 0 then toMultivector (ofPseudo z.onPseudo.exp)
  else Multivector.exp (toMultivector z)

/-- Julia `expm1(t::PseudoCouple)` (`C:112-119`): `exp(t) - 1` for the scalar blade, else
`expm1(multispin(t))`. -/
def expm1 (z : PseudoCouple V Float) : Multivector V Float :=
  if z.bits == 0 then Multivector.addScalar (-f1) (exp z)
  else Multivector.expm1 (toMultivector z)

/-- Julia `log(t::PseudoCouple)` (`C:373-381`). -/
def log (z : PseudoCouple V Float) : Multivector V Float :=
  if z.bits == 0 then toMultivector (ofPseudo z.onPseudo.log)
  else Multivector.log (toMultivector z)

/-- Julia `log1p(t::PseudoCouple)` (`C:382-390`). -/
def log1p (z : PseudoCouple V Float) : Multivector V Float :=
  if z.bits == 0 then toMultivector (ofPseudo z.onPseudo.log1p)
  else Multivector.log1p (toMultivector z)

/-- Julia `cosh(t::PseudoCouple) = cosh(multispin(t))` (`C:402`). -/
@[inline] def cosh (z : PseudoCouple V Float) : Multivector V Float := Multivector.cosh (toMultivector z)

/-- Julia `sinh(t::PseudoCouple) = sinh(multispin(t))` (`C:402`). -/
@[inline] def sinh (z : PseudoCouple V Float) : Multivector V Float := Multivector.sinh (toMultivector z)

/-- Julia `complexify(t::PseudoCouple) = !t` (`src/multivectors.jl:1049`): the right
complement, a couple on the complement of `B` (`complexify(3v₁ + 4v₁₂₃) = 4 + 3v₂₃`). -/
def complexify {α : Type} [Coeff α] (z : PseudoCouple V α) : Multivector V α :=
  Multivector.complementright (toMultivector z)

end PseudoCouple

/-! ## Couple and vector helpers -/

/-- Julia `complexify(t::Chain{V,1,T,2}) = Couple{V,Submanifold(V)}(t[1], t[2])`
(`src/multivectors.jl:1046`): a plane vector as a couple on the pseudoscalar. -/
def Chain.complexify {α : Type} [Coeff α] (c : Chain V 1 α) : Couple V α :=
  ⟨pseudoMask V, getD c.v 0, getD c.v 1⟩

/-- Julia `polarize(t::Chain{V,1,T,2}) = Phasor{V}(t[1], t[2]·I)`
(`src/multivectors.jl:1054`): the chain is read as (amplitude, angle). -/
def Chain.polarize {α : Type} [Coeff α] (c : Chain V 1 α) : Phasor V α :=
  ⟨getD c.v 0, ⟨pseudoMask V, Coeff.zero, getD c.v 1⟩⟩

end Grassmann

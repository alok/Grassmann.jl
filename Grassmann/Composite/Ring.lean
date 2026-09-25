/-
AbstractTensors' derived transcendental family on Grassmann's containers
(AbstractTensors.jl `AT:318-431`, `AT:435-569`; port-notes/abstracttensors-staticvectors.md
§2.1.9-2.1.10, §4.2, grassmann-composite.md §4.6, §4.16).

`AbstractTensors.Generic` writes the family once over the class `TensorRing`:
`cos t = cosh(I ⟑ t)`, `sin t = sinh(I ⟑ t)/I`, `tan`, `cot`, `sec`, …, `asinh`,
`acos`, …, `sinc`, `cosc`, `exp2`, `log10`, `b ^ t`, `abs`, `unit`, and the
complement-conjugated `co`/`pseudo` family `co f = complementleft ∘ f ∘ complementright`.
This module instantiates it:

* `TensorRing (Multivector V Float)` for every space, with Grassmann's primitives
  (`Grassmann.Composite.Dense`: closed-form `exp`, the generated series, `qlog`);
* `TensorRing (Spinor V Float)` for spaces with an even number of generators
  (`EvenDim V`): only then are the pseudoscalar and the complements even, so that
  `I ⟑ t` and `co f` stay in the even subalgebra.

and exposes the family under the container namespaces (`Multivector.tan`, …). For
spinors of odd-dimensional spaces (quaternions!) `cos`/`sin`/`tan` are computed
directly (`I ⟑ s` is odd, its `cosh` even), and couples, co-spinors and
pseudo-couples go through the multivector. **Quirk B2** is kept as DESIGN.md
prescribes: `cos t` is literally `cosh(I ⟑ t)`, which is `cosh t` for a scalar `t`
in a space with `I² = +1` (oracle defect `scalar-trig-hyperbolic`, policy
`replicate`).
-/
import Grassmann.Composite.Spinor

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase Composite

variable {V : TensorBundle}

/-- `V` has an even number of (non-tangent) generators: the pseudoscalar and the
complements of even elements are even, so the `Spinor` subalgebra carries the whole
AbstractTensors family (`TensorRing (Spinor V Float)`). Declare it per space:
`instance : EvenDim ℝ4 := ⟨by decide⟩`. -/
class EvenDim (V : TensorBundle) : Prop where
  /-- The number of generators is even. -/
  even : V.n % 2 = 0

/-! ## Multivectors -/

section Instances

variable [Kernels V]

/-- The series arithmetic of multivectors (`AbstractTensors.SeriesRing`): geometric product,
real scalars on the scalar coefficient, the coefficient norm, Julia's `inv` (`NaN` where it
throws). -/
instance instSeriesRingMultivector : SeriesRing (Multivector V Float) where
  toAdd := inferInstance
  toSub := inferInstance
  toMul := inferInstance
  toNeg := inferInstance
  addScalar := Multivector.addScalar
  smul k m := k * m
  sdiv m k := m / k
  norm := Multivector.fnorm
  inv := Multivector.invD

/-- Grassmann's multivectors as the carrier of AbstractTensors' derived functions. -/
instance instTensorRingMultivector : TensorRing (Multivector V Float) where
  zero := Multivector.zero
  one := (mvScalar f1)
  pseudoscalar := Multivector.ofBlade (⟨pseudoMask V⟩ : Submanifold V (pseudoGrade V)) f1
  reverse := Multivector.reverse
  isScalar := Multivector.isScalar
  scalar m := mvScalar m.scalarValue
  complementLeft := Multivector.complementleft
  complementRight := Multivector.complementright
  expm1 := Multivector.expm1
  exp := Multivector.exp
  log := Multivector.log
  log1p := Multivector.log1p
  sqrt := Multivector.sqrt
  cbrt := Multivector.cbrt
  cosh := Multivector.cosh
  sinh := Multivector.sinh

/-- The series arithmetic of spinors. -/
instance instSeriesRingSpinor : SeriesRing (Half V false Float) where
  add := (· + ·)
  sub := (· - ·)
  mul := Half.smul'
  neg := (- ·)
  addScalar := Half.addScalar
  smul k s := ⟨vmap (k * ·) s.v⟩
  sdiv := Half.sdiv
  norm := Half.fnorm
  inv := Half.invD

/-- Grassmann's spinors of an even-dimensional space as the carrier of AbstractTensors'
derived functions. -/
instance instTensorRingSpinor [h : EvenDim V] : TensorRing (Half V false Float) where
  zero := Half.zero
  one := (spScalar f1)
  pseudoscalar := Half.ofBlade (⟨pseudoMask V⟩ : Submanifold V (pseudoGrade V)) f1
  reverse := Half.reverse
  isScalar := Half.isScalar
  scalar s := Half.scalarF s.scalarValue
  complementLeft s := (Half.complementleft s).cast (by simp [h.even])
  complementRight s := (Half.complementright s).cast (by simp [h.even])
  expm1 := Half.expm1
  exp := Half.exp
  log := Half.log
  log1p := Half.log1p
  sqrt := Half.sqrt
  cbrt := Half.cbrt
  cosh := Half.cosh
  sinh := Half.sinh

end Instances

namespace Multivector

variable [Kernels V]

/-- AbstractTensors `cos(t) = cosh(I ⟑ t)` (`AT:407`). -/
@[specialize V] def cos (t : Multivector V Float) : Multivector V Float := Generic.cos t
/-- AbstractTensors `sin(t) = sinh(I ⟑ t)/I` (`AT:408`). -/
@[specialize V] def sin (t : Multivector V Float) : Multivector V Float := Generic.sin t
/-- AbstractTensors `tan(t) = sin(t)/cos(t)` (`AT:409`). -/
@[specialize V] def tan (t : Multivector V Float) : Multivector V Float := Generic.tan t
/-- AbstractTensors `cot(t) = cos(t)/sin(t)` (`AT:410`). -/
@[specialize V] def cot (t : Multivector V Float) : Multivector V Float := Generic.cot t
/-- AbstractTensors `sec(t) = inv(cos(t))` (`AT:411`). -/
@[specialize V] def sec (t : Multivector V Float) : Multivector V Float := Generic.sec t
/-- AbstractTensors `csc(t) = inv(sin(t))` (`AT:412`). -/
@[specialize V] def csc (t : Multivector V Float) : Multivector V Float := Generic.csc t
/-- AbstractTensors `tanh(t) = sinh(t)/cosh(t)` (`AT:419`). -/
@[specialize V] def tanh (t : Multivector V Float) : Multivector V Float := Generic.tanh t
/-- AbstractTensors `coth(t) = cosh(t)/sinh(t)` (`AT:420`). -/
@[specialize V] def coth (t : Multivector V Float) : Multivector V Float := Generic.coth t
/-- AbstractTensors `sech(t) = inv(cosh(t))` (`AT:415`). -/
@[specialize V] def sech (t : Multivector V Float) : Multivector V Float := Generic.sech t
/-- AbstractTensors `csch(t) = inv(sinh(t))` (`AT:416`). -/
@[specialize V] def csch (t : Multivector V Float) : Multivector V Float := Generic.csch t
/-- AbstractTensors `asinh(t) = log(t + sqrt(1 + t⟑t))` (`AT:421`). -/
@[specialize V] def asinh (t : Multivector V Float) : Multivector V Float := Generic.asinh t
/-- AbstractTensors `acosh(t) = log(t + sqrt(t⟑t - 1))` (`AT:422`). -/
@[specialize V] def acosh (t : Multivector V Float) : Multivector V Float := Generic.acosh t
/-- AbstractTensors `atanh(t) = (log(1+t) - log(1-t))/2` (`AT:423`). -/
@[specialize V] def atanh (t : Multivector V Float) : Multivector V Float := Generic.atanh t
/-- AbstractTensors `acoth(t) = (log(t+1) - log(t-1))/2` (`AT:424`). -/
@[specialize V] def acoth (t : Multivector V Float) : Multivector V Float := Generic.acoth t
/-- AbstractTensors `asin(t) = (-I) ⟑ log(I⟑t + sqrt(1 - t⟑t))` (`AT:425`). -/
@[specialize V] def asin (t : Multivector V Float) : Multivector V Float := Generic.asin t
/-- AbstractTensors `acos(t) = (-I) ⟑ log(t + I⟑sqrt(1 - t⟑t))` (`AT:426`). -/
@[specialize V] def acos (t : Multivector V Float) : Multivector V Float := Generic.acos t
/-- AbstractTensors `atan(t) = ((-I)/2) ⟑ (log(1 + I⟑t) - log(1 - I⟑t))` (`AT:427`). -/
@[specialize V] def atan (t : Multivector V Float) : Multivector V Float := Generic.atan t
/-- AbstractTensors `acot(t) = ((-I)/2) ⟑ (log(t - I) - log(t + I))` (`AT:428`). -/
@[specialize V] def acot (t : Multivector V Float) : Multivector V Float := Generic.acot t
/-- AbstractTensors `asec(t) = acos(inv(t))` (`AT:413`). -/
@[specialize V] def asec (t : Multivector V Float) : Multivector V Float := Generic.asec t
/-- AbstractTensors `acsc(t) = asin(inv(t))` (`AT:414`). -/
@[specialize V] def acsc (t : Multivector V Float) : Multivector V Float := Generic.acsc t
/-- AbstractTensors `asech(t) = acosh(inv(t))` (`AT:417`). -/
@[specialize V] def asech (t : Multivector V Float) : Multivector V Float := Generic.asech t
/-- AbstractTensors `acsch(t) = asinh(inv(t))` (`AT:418`). -/
@[specialize V] def acsch (t : Multivector V Float) : Multivector V Float := Generic.acsch t
/-- AbstractTensors `sinc(t)` (`AT:429`). -/
@[specialize V] def sinc (t : Multivector V Float) : Multivector V Float := Generic.sinc t
/-- AbstractTensors `cosc(t)` (`AT:430`). -/
@[specialize V] def cosc (t : Multivector V Float) : Multivector V Float := Generic.cosc t
/-- AbstractTensors `exp2(t) = exp(log(2)·t)` (`AT:384`). -/
@[specialize V] def exp2 (t : Multivector V Float) : Multivector V Float := Generic.exp2 t
/-- AbstractTensors `exp10(t) = exp(log(10)·t)` (`AT:384`). -/
@[specialize V] def exp10 (t : Multivector V Float) : Multivector V Float := Generic.exp10 t
/-- AbstractTensors `log2(t) = log2(ℯ)·log(t)` (`AT:383`). -/
@[specialize V] def log2 (t : Multivector V Float) : Multivector V Float := Generic.log2 t
/-- AbstractTensors `log10(t) = log10(ℯ)·log(t)` (`AT:383`). -/
@[specialize V] def log10 (t : Multivector V Float) : Multivector V Float := Generic.log10 t
/-- AbstractTensors `b ^ t = exp(t ⟑ log(b))` (`AT:326`). -/
@[specialize V] def rpow (b : Float) (t : Multivector V Float) : Multivector V Float := Generic.rpow b t
/-- `log(t)/log(b)` (AbstractTensors `AT:330`, bug B1 fixed: Julia returns `log(b)`). -/
@[specialize V] def logBase (b : Float) (t : Multivector V Float) : Multivector V Float := Generic.logBase b t
/-- AbstractTensors `exph(t) = cosh(t) + sinh(t)` (Grassmann `C:572`). -/
@[specialize V] def exph (t : Multivector V Float) : Multivector V Float := t.cosh + t.sinh
/-- AbstractTensors `abs(t) = sqrt(abs2(t))` (`AT:435`, `abs2` collapsed to its scalar). -/
@[specialize V] def abs (t : Multivector V Float) : Multivector V Float := Generic.abs t
/-- AbstractTensors `unit(t) = t/abs(t)` (`AT:462`). -/
@[specialize V] def unit (t : Multivector V Float) : Multivector V Float := Generic.unit t
/-- AbstractTensors `coabs(t) = complementleft(abs(complementright(t)))` (`AT:532`). -/
@[specialize V] def coabs (t : Multivector V Float) : Multivector V Float := Generic.coabs t
/-- AbstractTensors `coabs2` (`AT:532-548`). -/
@[specialize V] def coabs2 (t : Multivector V Float) : Multivector V Float := Generic.coabs2 t
/-- AbstractTensors `geomabs(t) = abs(t) + coabs(t)` (`AT:454`). -/
@[specialize V] def geomabs (t : Multivector V Float) : Multivector V Float := Generic.geomabs t
/-- AbstractTensors `unitnorm(t) = t/norm(geomabs(t))` (`AT:479`). -/
@[specialize V] def unitnorm (t : Multivector V Float) : Multivector V Float := Generic.unitnorm t
/-- AbstractTensors `counit(t) = unitize(t) = t/value(coabs(t))` (`AT:476-478`): the
coefficient of `coabs(t)` on the pseudoscalar, applied as `t ⟑ inv(x)`. -/
@[specialize V] def unitize (t : Multivector V Float) : Multivector V Float :=
  let c := Generic.coabs t
  t * (f1 / getD c.v (2 ^ V.n - 1))
/-- AbstractTensors `metric(a, b) = abs(a - b)` (`AT:368`). -/
@[specialize V] def metricDist (a b : Multivector V Float) : Multivector V Float := Generic.metric a b
/-- AbstractTensors `cometric(a, b) = coabs(a - b)` (`AT:368`). -/
@[specialize V] def cometric (a b : Multivector V Float) : Multivector V Float := Generic.cometric a b
/-- AbstractTensors `coexp` / `pseudoexp` (`AT:532-548`). -/
@[specialize V] def coexp (t : Multivector V Float) : Multivector V Float := Generic.coexp t
/-- AbstractTensors `colog` / `pseudolog`. -/
@[specialize V] def colog (t : Multivector V Float) : Multivector V Float := Generic.colog t
/-- AbstractTensors `cosqrt` / `pseudosqrt`. -/
@[specialize V] def cosqrt (t : Multivector V Float) : Multivector V Float := Generic.cosqrt t
/-- AbstractTensors `cocbrt` / `pseudocbrt`. -/
@[specialize V] def cocbrt (t : Multivector V Float) : Multivector V Float := Generic.cocbrt t
/-- AbstractTensors `coinv` / `pseudoinv`. -/
@[specialize V] def coinv (t : Multivector V Float) : Multivector V Float := Generic.coinv t
/-- AbstractTensors `cosin` / `pseudosin` (complemented `sin`). -/
@[specialize V] def cosin (t : Multivector V Float) : Multivector V Float := Generic.cosin t
/-- AbstractTensors `cocos` / `pseudocos` (complemented `cos`). -/
@[specialize V] def cocos (t : Multivector V Float) : Multivector V Float := Generic.cocos t
/-- AbstractTensors `cotan` / `pseudotan` (complemented `tan`, not the cotangent). -/
@[specialize V] def cotan (t : Multivector V Float) : Multivector V Float := Generic.cotan t
/-- AbstractTensors `cosinh` / `pseudosinh`. -/
@[specialize V] def cosinh (t : Multivector V Float) : Multivector V Float := Generic.cosinh t
/-- AbstractTensors `cocosh` / `pseudocosh`. -/
@[specialize V] def cocosh (t : Multivector V Float) : Multivector V Float := Generic.cocosh t
/-- AbstractTensors `cotanh` / `pseudotanh`. -/
@[specialize V] def cotanh (t : Multivector V Float) : Multivector V Float := Generic.cotanh t

end Multivector

/-! ## Spinors: the trigonometric functions through the odd `I ⟑ s` -/

namespace Composite

variable [Kernels V]

/-- The generated `cosh` of a half of parity `p` (its coefficients) as a spinor: the spinor
`cosh` for `p = false`; for an odd `x` Julia's multivector `cosh` (`C:483-513`), whose
series `1 + τ/2 + …` over `τ = x⟑x` is even. -/
@[specialize V] def coshHalfV : (p : Bool) → Values Float ((halfLayout p).size V.n) → Half V false Float
  | false, x => Half.cosh ⟨x⟩
  | true, x =>
    if approx f0 x.norm then Half.scalarF f1
    else
      let τ : Half V false Float := ⟨Kernels.bin .mul .odd .odd (halfLayout false) x x⟩
      Half.addScalar f1 (coshGeneratedTail (· + ·) Half.smul' Half.sdiv Half.fnorm τ)

/-- The generated `sinh` of a half of parity `p` (its coefficients), in the same half. -/
@[specialize V] def sinhHalfV : (p : Bool) → Values Float ((halfLayout p).size V.n) → Values Float ((halfLayout p).size V.n)
  | false, x => (Half.sinh ⟨x⟩).v
  | true, x =>
    if approx f0 x.norm then x
    else
      let τ : Values Float ((halfLayout false).size V.n) := Kernels.bin .mul .odd .odd .even x x
      sinhGeneratedWith (X := Values Float ((halfLayout true).size V.n)) (vzip (· + ·)) (fun y k => vmap (· / k) y)
        (·.norm) (fun y => Kernels.bin .mul .odd .even .odd y τ) x

/-- `I ⟑ s` for a spinor: the half of the parity of the pseudoscalar. -/
@[inline] def mulPseudoSpinor (s : Half V false Float) :
    Values Float ((halfLayout (pseudoGrade V % 2 == 1)).size V.n) :=
  Kernels.binProj .mul (.chain (pseudoGrade V)) (halfLayout false) (halfLayout (pseudoGrade V % 2 == 1))
    (pseudoValues V f1) s.v

end Composite

namespace Half

variable [Kernels V]

/-- AbstractTensors `cos(s) = cosh(I ⟑ s)` (`AT:407`) of a spinor (any dimension; the
cosine of a spinor is even). -/
@[specialize V] def cos (s : Half V false Float) : Half V false Float :=
  coshHalfV (pseudoGrade V % 2 == 1) (mulPseudoSpinor s)

/-- AbstractTensors `sin(s) = sinh(I ⟑ s)/I` (`AT:408`) of a spinor. -/
@[specialize V] def sin (s : Half V false Float) : Half V false Float :=
  let p := pseudoGrade V % 2 == 1
  ⟨divPseudo (halfLayout p) (halfLayout false) (sinhHalfV p (mulPseudoSpinor s))⟩

/-- AbstractTensors `tan(s) = sin(s)/cos(s)` (`AT:409`) of a spinor; `NaN` coefficients where
the inverse of `cos s` is undefined. -/
@[specialize V] def tan (s : Half V false Float) : Half V false Float := smul' s.sin (invD s.cos)

/-- AbstractTensors `exph(s) = cosh(s) + sinh(s)` (Grassmann `C:572`). -/
@[specialize V] def exph (s : Half V false Float) : Half V false Float := s.cosh + s.sinh

end Half

/-! ## Couples, co-spinors and pseudo-couples: trigonometric functions -/

namespace Couple

variable [Kernels V]

/-- AbstractTensors `cos(z) = cosh(I ⟑ z)` (`AT:407`) of a couple: for a couple on the
pseudoscalar `I ⟑ z = im·I² + re·I` is again a couple on `I` (the complex cosine when
`I² = -1`); otherwise `I ⟑ z` is a pseudo-couple, whose `cosh` Julia routes to the
generated multivector series (`UndefVarError` in 0.8.46), computed here on the multivector. -/
@[specialize V] def cos (z : Couple V Float) : Multivector V Float :=
  let i := pseudoMask V
  if z.bits == i && i != 0 then
    toMultivector (Couple.cosh (⟨i, z.im * bladeSq V i, z.re⟩ : Couple V Float))
  else Multivector.cos (toMultivector z)

/-- AbstractTensors `sin(z) = sinh(I ⟑ z)/I` (`AT:408`) of a couple (see `cos`). -/
@[specialize V] def sin (z : Couple V Float) : Multivector V Float :=
  let i := pseudoMask V
  if z.bits == i && i != 0 then
    let w := Couple.sinh (⟨i, z.im * bladeSq V i, z.re⟩ : Couple V Float)
    let c := invPseudoCoef V
    toMultivector (⟨i, w.im * c * bladeSq V i, w.re * c⟩ : Couple V Float)
  else Multivector.sin (toMultivector z)

/-- AbstractTensors `tan(z) = sin(z)/cos(z)` (`AT:409`) of a couple (see `cos`). -/
@[specialize V] def tan (z : Couple V Float) : Multivector V Float :=
  let i := pseudoMask V
  if z.bits == i && i != 0 then
    let w : Couple V Float := ⟨i, z.im * bladeSq V i, z.re⟩
    let s := Couple.sinh w
    let c := invPseudoCoef V
    let sn : Couple V Float := ⟨i, s.im * c * bladeSq V i, s.re * c⟩
    toMultivector (Couple.divSame sn (Couple.cosh w))
  else Multivector.tan (toMultivector z)

end Couple

namespace CoSpinor

variable [Kernels V]

/-- AbstractTensors `cos` of a co-spinor (through the multivector, as Julia). -/
@[inline] def cos (t : CoSpinor V Float) : Multivector V Float := Multivector.cos (toMultivector t)
/-- AbstractTensors `sin` of a co-spinor. -/
@[inline] def sin (t : CoSpinor V Float) : Multivector V Float := Multivector.sin (toMultivector t)
/-- AbstractTensors `tan` of a co-spinor. -/
@[inline] def tan (t : CoSpinor V Float) : Multivector V Float := Multivector.tan (toMultivector t)

end CoSpinor

namespace PseudoCouple

variable [Kernels V]

/-- AbstractTensors `cos` of a pseudo-couple (through the multivector). -/
@[inline] def cos (z : PseudoCouple V Float) : Multivector V Float := Multivector.cos (toMultivector z)
/-- AbstractTensors `sin` of a pseudo-couple. -/
@[inline] def sin (z : PseudoCouple V Float) : Multivector V Float := Multivector.sin (toMultivector z)
/-- AbstractTensors `tan` of a pseudo-couple. -/
@[inline] def tan (z : PseudoCouple V Float) : Multivector V Float := Multivector.tan (toMultivector z)

end PseudoCouple

/-! ## The `co`/`pseudo` family on chains (`AT:500-569`) -/

namespace Chain

variable {G : Nat} [Kernels V]

/-- The value of Julia `abs(t) = sqrt(abs2(t))` of a chain with `abs2(t) = contraction(t, t)`
(`AT:435-439`), the square root of a (metric) scalar, as a `Float` (`Chain.abs` in
`Grassmann.Composite.Norm` is the scalar element Julia returns). -/
@[inline] def absF (c : Chain V G Float) : Float := Float.sqrt (getD c.abs2.v 0)

/-- AbstractTensors `co f(t) = complementleft(f(complementright(t)))` for a function of chains
with multivector values (`AT:500-505`). -/
@[inline] def coMV (f : Chain V (V.n - G) Float → Multivector V Float) (c : Chain V G Float) :
    Multivector V Float :=
  Multivector.complementleft (f c.complementright)

/-- `coexp(t) = pseudoexp(t)` of a chain (`pseudoexp(0.5v₃) = 0.4794v₃ + 0.8776v₁₂₃` in `ℝ3`). -/
@[specialize V] def coexp (c : Chain V G Float) : Multivector V Float := coMV Chain.exp c
/-- `colog(t) = pseudolog(t)` of a chain. -/
@[specialize V] def colog (c : Chain V G Float) : Multivector V Float := coMV Chain.log c
/-- `cosqrt(t) = pseudosqrt(t)` of a chain. -/
@[specialize V] def cosqrt (c : Chain V G Float) : Multivector V Float := coMV Chain.sqrt c
/-- `cocbrt(t) = pseudocbrt(t)` of a chain. -/
@[specialize V] def cocbrt (c : Chain V G Float) : Multivector V Float := coMV Chain.cbrt c
/-- `cocosh(t) = pseudocosh(t)` of a chain. -/
@[specialize V] def cocosh (c : Chain V G Float) : Multivector V Float := coMV (fun x => Half.toMultivector x.cosh) c
/-- `cosinh(t) = pseudosinh(t)` of a chain. -/
@[specialize V] def cosinh (c : Chain V G Float) : Multivector V Float := coMV (fun x => Half.toMultivector x.sinh) c
/-- `cocos(t) = pseudocos(t)` of a chain. -/
@[specialize V] def cocos (c : Chain V G Float) : Multivector V Float := coMV (fun x => Half.toMultivector x.cos) c
/-- `cosin(t) = pseudosin(t)` of a chain (`pseudosin(0.5v₃) = 0.5211v₃` in `ℝ3`). -/
@[specialize V] def cosin (c : Chain V G Float) : Multivector V Float := coMV (fun x => Half.toMultivector x.sin) c
/-- `cotan(t) = pseudotan(t)` of a chain (complemented `tan`). -/
@[specialize V] def cotan (c : Chain V G Float) : Multivector V Float := coMV (fun x => Half.toMultivector x.tan) c
/-- `cotanh(t) = pseudotanh(t)` of a chain. -/
@[specialize V] def cotanh (c : Chain V G Float) : Multivector V Float := coMV (fun x => Half.toMultivector x.tanh) c
/-- `coinv(t) = pseudoinv(t)` of a chain (`pseudoinv(2v₁₂) = 0.5v₁₂` in `ℝ3`). -/
@[specialize V] def coinv (c : Chain V G Float) : Chain V (V.n - (V.n - G)) Float := c.complementright.inv.complementleft
/-- `coabs(t) = pseudoabs(t)` of a chain: `abs` of the complement on the pseudoscalar
(`pseudoabs(3v₁ + 4v₂) = 5.0v₁₂₃` in `ℝ3`). -/
@[specialize V] def coabs (c : Chain V G Float) : Chain V (V.n - 0) Float :=
  (Chain.scalar c.complementright.absF : Chain V 0 Float).complementleft
/-- `coabs2(t) = pseudoabs2(t)` of a chain. -/
@[specialize V] def coabs2 (c : Chain V G Float) : Chain V (V.n - 0) Float :=
  c.complementright.abs2.complementleft

end Chain

/-! ## Inverse hyperbolic functions of spinors, real powers -/

namespace Half

variable [Kernels V]

/-- AbstractTensors `asinh(s) = log(s + sqrt(1 + s⟑s))` (`AT:421`) of a spinor (any
dimension: the formula never leaves the even subalgebra). -/
@[specialize V] def asinh (s : Half V false Float) : Half V false Float :=
  log (s + sqrt (addScalar f1 (smul' s s)))

/-- AbstractTensors `acosh(s) = log(s + sqrt(s⟑s - 1))` (`AT:422`) of a spinor. -/
@[specialize V] def acosh (s : Half V false Float) : Half V false Float :=
  log (s + sqrt (addScalar (-f1) (smul' s s)))

/-- AbstractTensors `atanh(s) = (log(1 + s) - log(1 - s))/2` (`AT:423`) of a spinor. -/
@[specialize V] def atanh (s : Half V false Float) : Half V false Float :=
  sdiv (log (addScalar f1 s) - log (addScalar f1 (-s))) f2

/-- AbstractTensors `acoth(s) = (log(s + 1) - log(s - 1))/2` (`AT:424`) of a spinor. -/
@[specialize V] def acoth (s : Half V false Float) : Half V false Float :=
  sdiv (log (addScalar f1 s) - log (addScalar (-f1) s)) f2

/-- A real power `s ^ x = exp(x·log(s))` (the principal branch; Julia defines no
`TensorAlgebra ^ Real`, only `Real ^ TensorAlgebra`, `rpow`). -/
@[specialize V] def powf (s : Half V false Float) (x : Float) : Half V false Float := exp ⟨vmap (x * ·) s.log.v⟩

end Half

namespace Multivector

variable [Kernels V]

/-- A real power `t ^ x = exp(x·log(t))` (the principal branch; Julia defines no
`TensorAlgebra ^ Real`). -/
@[specialize V] def powf (t : Multivector V Float) (x : Float) : Multivector V Float := exp (x * t.log)

end Multivector

namespace Couple

/-- AbstractTensors `exph(z) = cosh(z) + sinh(z)` (Grassmann `C:572`). -/
@[specialize V] def exph (z : Couple V Float) : Couple V Float :=
  let c := z.cosh
  let s := z.sinh
  ⟨z.bits, c.re + s.re, c.im + s.im⟩

/-- AbstractTensors `log2(z) = log2(ℯ)·log(z)` (`AT:383`). -/
@[specialize V] def log2 (z : Couple V Float) : Couple V Float := let l := z.log; ⟨l.bits, F64.log2e * l.re, F64.log2e * l.im⟩
/-- AbstractTensors `log10(z) = log10(ℯ)·log(z)` (`AT:383`). -/
@[specialize V] def log10 (z : Couple V Float) : Couple V Float := let l := z.log; ⟨l.bits, F64.log10e * l.re, F64.log10e * l.im⟩
/-- AbstractTensors `exp2(z) = exp(log(2)·z)` (`AT:384`). -/
@[specialize V] def exp2 (z : Couple V Float) : Couple V Float := exp ⟨z.bits, F64.ln2 * z.re, F64.ln2 * z.im⟩
/-- AbstractTensors `exp10(z) = exp(log(10)·z)` (`AT:384`). -/
@[specialize V] def exp10 (z : Couple V Float) : Couple V Float := exp ⟨z.bits, F64.ln10 * z.re, F64.ln10 * z.im⟩

end Couple

/-! ## `log_fast`, `logh_fast` (`src/composite.jl:574-587`) -/

namespace Composite

/-- The iteration cap of `log_fast`/`logh_fast` (Julia loops forever where the iteration
does not converge, port-notes/grassmann-composite.md §8.3 item 9). -/
def logFastCap : Nat := 200

/-- Julia's `log_fast` iteration from `term = 0` (`src/composite.jl:574-587`):
`term -= 2(e - t)/(e + t)` with `e = expf(term)` (right division `div`), stopping when two
consecutive iterates have `≈` norms; `none` when a division is undefined or after
`logFastCap` steps. -/
@[specialize] def logFastLoop {X : Type} (sub : X → X → X) (add : X → X → X) (smul2 : X → X)
    (div? : X → X → Option X) (norm : X → Float) (expf : X → X) (t term : X) (n2 : Float) :
    Nat → Option X
  | 0 => none
  | fuel + 1 =>
    let e := expf term
    match div? (smul2 (sub e t)) (add e t) with
    | none => none
    | some d =>
      let term := sub term d
      let n := norm term
      if approx n2 n then some term
      else logFastLoop sub add smul2 div? norm expf t term n fuel

end Composite

namespace Multivector

variable [Kernels V]

/-- The shared iteration of `log_fast`/`logh_fast` on multivectors. -/
@[inline] def logFastWith (expf : Multivector V Float → Multivector V Float) (t : Multivector V Float) :
    Option (Multivector V Float) :=
  logFastLoop (· - ·) (· + ·) (fun m => f2 * m) (fun a b => b.inv?.map (a * ·)) fnorm expf t
    Multivector.zero f0 logFastCap

/-- Julia `log_fast(t)` (`src/composite.jl:574-587`): Halley's iteration for `exp(y) = t`;
`none` where it breaks down or does not converge (Julia hangs). -/
@[specialize V] def logFast (t : Multivector V Float) : Option (Multivector V Float) := logFastWith exp t

/-- Julia `logh_fast(t)`: the same iteration on `exph = cosh + sinh` (whose generated
series Julia cannot run, port-notes §4.3.3). -/
@[specialize V] def loghFast (t : Multivector V Float) : Option (Multivector V Float) := logFastWith exph t

end Multivector

namespace Half

variable [Kernels V]

/-- The shared iteration of `log_fast`/`logh_fast` on spinors. -/
@[inline] def logFastWith (expf : Half V false Float → Half V false Float) (t : Half V false Float) :
    Option (Half V false Float) :=
  logFastLoop (· - ·) (· + ·) (fun m => ⟨vmap (f2 * ·) m.v⟩) (fun a b => b.inv?.map (smul' a ·))
    fnorm expf t Half.zero f0 logFastCap

/-- Julia `log_fast(t)` of a spinor (`src/composite.jl:574-587`), `none` where it fails. -/
@[specialize V] def logFast (t : Half V false Float) : Option (Half V false Float) := logFastWith exp t

/-- Julia `logh_fast(t)` of a spinor. -/
@[specialize V] def loghFast (t : Half V false Float) : Option (Half V false Float) := logFastWith exph t

end Half

namespace Couple

/-- The shared iteration of `log_fast`/`logh_fast` on a couple (its blade algebra). -/
@[inline] def logFastWith (expf : Couple V Float → Couple V Float) (z : Couple V Float) : Option (Couple V Float) :=
  logFastLoop (fun a b => ⟨a.bits, a.re - b.re, a.im - b.im⟩) (fun a b => ⟨a.bits, a.re + b.re, a.im + b.im⟩)
    (fun a => ⟨a.bits, (2 : Float) * a.re, (2 : Float) * a.im⟩)
    (fun a b => let q := divSame a b; if q.re.isNaN || q.im.isNaN then none else some q)
    (fun a => Float.sqrt (a.re * a.re + a.im * a.im)) expf z ⟨z.bits, f0, f0⟩ f0 logFastCap

/-- Julia `log_fast(z)` of a couple (`src/composite.jl:574-587`): Halley's iteration on the
closed-form `exp`; `none` where Julia hangs (hyperbolic couples outside the light cone). -/
@[specialize V] def logFast (z : Couple V Float) : Option (Couple V Float) := logFastWith exp z

/-- Julia `logh_fast(z)` of a couple, on `exph = cosh + sinh`. -/
@[specialize V] def loghFast (z : Couple V Float) : Option (Couple V Float) := logFastWith exph z

end Couple

end Grassmann

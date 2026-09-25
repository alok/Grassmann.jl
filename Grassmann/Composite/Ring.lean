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
  one := Multivector.one
  pseudoscalar := Multivector.ofBlade (⟨pseudoMask V⟩ : Submanifold V (pseudoGrade V)) f1
  reverse := Multivector.reverse
  isScalar := Multivector.isScalar
  scalar m := Multivector.scalar m.scalarValue
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
  smul k s := ⟨s.v.map (k * ·)⟩
  sdiv := Half.sdiv
  norm := Half.fnorm
  inv := Half.invD

/-- Grassmann's spinors of an even-dimensional space as the carrier of AbstractTensors'
derived functions. -/
instance instTensorRingSpinor [h : EvenDim V] : TensorRing (Half V false Float) where
  zero := Half.zero
  one := Spinor.one
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
def cos (t : Multivector V Float) : Multivector V Float := Generic.cos t
/-- AbstractTensors `sin(t) = sinh(I ⟑ t)/I` (`AT:408`). -/
def sin (t : Multivector V Float) : Multivector V Float := Generic.sin t
/-- AbstractTensors `tan(t) = sin(t)/cos(t)` (`AT:409`). -/
def tan (t : Multivector V Float) : Multivector V Float := Generic.tan t
/-- AbstractTensors `cot(t) = cos(t)/sin(t)` (`AT:410`). -/
def cot (t : Multivector V Float) : Multivector V Float := Generic.cot t
/-- AbstractTensors `sec(t) = inv(cos(t))` (`AT:411`). -/
def sec (t : Multivector V Float) : Multivector V Float := Generic.sec t
/-- AbstractTensors `csc(t) = inv(sin(t))` (`AT:412`). -/
def csc (t : Multivector V Float) : Multivector V Float := Generic.csc t
/-- AbstractTensors `tanh(t) = sinh(t)/cosh(t)` (`AT:419`). -/
def tanh (t : Multivector V Float) : Multivector V Float := Generic.tanh t
/-- AbstractTensors `coth(t) = cosh(t)/sinh(t)` (`AT:420`). -/
def coth (t : Multivector V Float) : Multivector V Float := Generic.coth t
/-- AbstractTensors `sech(t) = inv(cosh(t))` (`AT:415`). -/
def sech (t : Multivector V Float) : Multivector V Float := Generic.sech t
/-- AbstractTensors `csch(t) = inv(sinh(t))` (`AT:416`). -/
def csch (t : Multivector V Float) : Multivector V Float := Generic.csch t
/-- AbstractTensors `asinh(t) = log(t + sqrt(1 + t⟑t))` (`AT:421`). -/
def asinh (t : Multivector V Float) : Multivector V Float := Generic.asinh t
/-- AbstractTensors `acosh(t) = log(t + sqrt(t⟑t - 1))` (`AT:422`). -/
def acosh (t : Multivector V Float) : Multivector V Float := Generic.acosh t
/-- AbstractTensors `atanh(t) = (log(1+t) - log(1-t))/2` (`AT:423`). -/
def atanh (t : Multivector V Float) : Multivector V Float := Generic.atanh t
/-- AbstractTensors `acoth(t) = (log(t+1) - log(t-1))/2` (`AT:424`). -/
def acoth (t : Multivector V Float) : Multivector V Float := Generic.acoth t
/-- AbstractTensors `asin(t) = (-I) ⟑ log(I⟑t + sqrt(1 - t⟑t))` (`AT:425`). -/
def asin (t : Multivector V Float) : Multivector V Float := Generic.asin t
/-- AbstractTensors `acos(t) = (-I) ⟑ log(t + I⟑sqrt(1 - t⟑t))` (`AT:426`). -/
def acos (t : Multivector V Float) : Multivector V Float := Generic.acos t
/-- AbstractTensors `atan(t) = ((-I)/2) ⟑ (log(1 + I⟑t) - log(1 - I⟑t))` (`AT:427`). -/
def atan (t : Multivector V Float) : Multivector V Float := Generic.atan t
/-- AbstractTensors `acot(t) = ((-I)/2) ⟑ (log(t - I) - log(t + I))` (`AT:428`). -/
def acot (t : Multivector V Float) : Multivector V Float := Generic.acot t
/-- AbstractTensors `asec(t) = acos(inv(t))` (`AT:413`). -/
def asec (t : Multivector V Float) : Multivector V Float := Generic.asec t
/-- AbstractTensors `acsc(t) = asin(inv(t))` (`AT:414`). -/
def acsc (t : Multivector V Float) : Multivector V Float := Generic.acsc t
/-- AbstractTensors `asech(t) = acosh(inv(t))` (`AT:417`). -/
def asech (t : Multivector V Float) : Multivector V Float := Generic.asech t
/-- AbstractTensors `acsch(t) = asinh(inv(t))` (`AT:418`). -/
def acsch (t : Multivector V Float) : Multivector V Float := Generic.acsch t
/-- AbstractTensors `sinc(t)` (`AT:429`). -/
def sinc (t : Multivector V Float) : Multivector V Float := Generic.sinc t
/-- AbstractTensors `cosc(t)` (`AT:430`). -/
def cosc (t : Multivector V Float) : Multivector V Float := Generic.cosc t
/-- AbstractTensors `exp2(t) = exp(log(2)·t)` (`AT:384`). -/
def exp2 (t : Multivector V Float) : Multivector V Float := Generic.exp2 t
/-- AbstractTensors `exp10(t) = exp(log(10)·t)` (`AT:384`). -/
def exp10 (t : Multivector V Float) : Multivector V Float := Generic.exp10 t
/-- AbstractTensors `log2(t) = log2(ℯ)·log(t)` (`AT:383`). -/
def log2 (t : Multivector V Float) : Multivector V Float := Generic.log2 t
/-- AbstractTensors `log10(t) = log10(ℯ)·log(t)` (`AT:383`). -/
def log10 (t : Multivector V Float) : Multivector V Float := Generic.log10 t
/-- AbstractTensors `b ^ t = exp(t ⟑ log(b))` (`AT:326`). -/
def rpow (b : Float) (t : Multivector V Float) : Multivector V Float := Generic.rpow b t
/-- `log(t)/log(b)` (AbstractTensors `AT:330`, bug B1 fixed: Julia returns `log(b)`). -/
def logBase (b : Float) (t : Multivector V Float) : Multivector V Float := Generic.logBase b t
/-- AbstractTensors `exph(t) = cosh(t) + sinh(t)` (Grassmann `C:572`). -/
def exph (t : Multivector V Float) : Multivector V Float := t.cosh + t.sinh
/-- AbstractTensors `abs(t) = sqrt(abs2(t))` (`AT:435`, `abs2` collapsed to its scalar). -/
def abs (t : Multivector V Float) : Multivector V Float := Generic.abs t
/-- AbstractTensors `unit(t) = t/abs(t)` (`AT:462`). -/
def unit (t : Multivector V Float) : Multivector V Float := Generic.unit t
/-- AbstractTensors `coabs(t) = complementleft(abs(complementright(t)))` (`AT:532`). -/
def coabs (t : Multivector V Float) : Multivector V Float := Generic.coabs t
/-- AbstractTensors `coabs2` (`AT:532-548`). -/
def coabs2 (t : Multivector V Float) : Multivector V Float := Generic.coabs2 t
/-- AbstractTensors `geomabs(t) = abs(t) + coabs(t)` (`AT:454`). -/
def geomabs (t : Multivector V Float) : Multivector V Float := Generic.geomabs t
/-- AbstractTensors `unitnorm(t) = t/norm(geomabs(t))` (`AT:479`). -/
def unitnorm (t : Multivector V Float) : Multivector V Float := Generic.unitnorm t
/-- AbstractTensors `counit(t) = unitize(t) = t/value(coabs(t))` (`AT:476-478`): the
coefficient of `coabs(t)` on the pseudoscalar, applied as `t ⟑ inv(x)`. -/
def unitize (t : Multivector V Float) : Multivector V Float :=
  let c := Generic.coabs t
  t * (f1 / getD c.v (2 ^ V.n - 1))
/-- AbstractTensors `metric(a, b) = abs(a - b)` (`AT:368`). -/
def metricDist (a b : Multivector V Float) : Multivector V Float := Generic.metric a b
/-- AbstractTensors `cometric(a, b) = coabs(a - b)` (`AT:368`). -/
def cometric (a b : Multivector V Float) : Multivector V Float := Generic.cometric a b
/-- AbstractTensors `coexp` / `pseudoexp` (`AT:532-548`). -/
def coexp (t : Multivector V Float) : Multivector V Float := Generic.coexp t
/-- AbstractTensors `colog` / `pseudolog`. -/
def colog (t : Multivector V Float) : Multivector V Float := Generic.colog t
/-- AbstractTensors `cosqrt` / `pseudosqrt`. -/
def cosqrt (t : Multivector V Float) : Multivector V Float := Generic.cosqrt t
/-- AbstractTensors `cocbrt` / `pseudocbrt`. -/
def cocbrt (t : Multivector V Float) : Multivector V Float := Generic.cocbrt t
/-- AbstractTensors `coinv` / `pseudoinv`. -/
def coinv (t : Multivector V Float) : Multivector V Float := Generic.coinv t
/-- AbstractTensors `cosin` / `pseudosin` (complemented `sin`). -/
def cosin (t : Multivector V Float) : Multivector V Float := Generic.cosin t
/-- AbstractTensors `cocos` / `pseudocos` (complemented `cos`). -/
def cocos (t : Multivector V Float) : Multivector V Float := Generic.cocos t
/-- AbstractTensors `cotan` / `pseudotan` (complemented `tan`, not the cotangent). -/
def cotan (t : Multivector V Float) : Multivector V Float := Generic.cotan t
/-- AbstractTensors `cosinh` / `pseudosinh`. -/
def cosinh (t : Multivector V Float) : Multivector V Float := Generic.cosinh t
/-- AbstractTensors `cocosh` / `pseudocosh`. -/
def cocosh (t : Multivector V Float) : Multivector V Float := Generic.cocosh t
/-- AbstractTensors `cotanh` / `pseudotanh`. -/
def cotanh (t : Multivector V Float) : Multivector V Float := Generic.cotanh t

end Multivector

/-! ## Spinors: the trigonometric functions through the odd `I ⟑ s` -/

namespace Composite

variable [Kernels V]

/-- The generated `cosh` of a half of parity `p` (its coefficients) as a spinor: the spinor
`cosh` for `p = false`; for an odd `x` Julia's multivector `cosh` (`C:483-513`), whose
series `1 + τ/2 + …` over `τ = x⟑x` is even. -/
def coshHalfV : (p : Bool) → Values Float ((halfLayout p).size V.n) → Half V false Float
  | false, x => Half.cosh ⟨x⟩
  | true, x =>
    if approx f0 x.norm then Half.scalarF f1
    else
      let τ : Half V false Float := ⟨Kernels.bin .mul .odd .odd (halfLayout false) x x⟩
      Half.addScalar f1 (coshGeneratedTail (· + ·) Half.smul' Half.sdiv Half.fnorm τ)

/-- The generated `sinh` of a half of parity `p` (its coefficients), in the same half. -/
def sinhHalfV : (p : Bool) → Values Float ((halfLayout p).size V.n) → Values Float ((halfLayout p).size V.n)
  | false, x => (Half.sinh ⟨x⟩).v
  | true, x =>
    if approx f0 x.norm then x
    else
      let τ : Values Float ((halfLayout false).size V.n) := Kernels.bin .mul .odd .odd .even x x
      sinhGeneratedWith (X := Values Float ((halfLayout true).size V.n)) (· + ·) (fun y k => y.map (· / k))
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
def cos (s : Half V false Float) : Half V false Float :=
  coshHalfV (pseudoGrade V % 2 == 1) (mulPseudoSpinor s)

/-- AbstractTensors `sin(s) = sinh(I ⟑ s)/I` (`AT:408`) of a spinor. -/
def sin (s : Half V false Float) : Half V false Float :=
  let p := pseudoGrade V % 2 == 1
  ⟨divPseudo (halfLayout p) (halfLayout false) (sinhHalfV p (mulPseudoSpinor s))⟩

/-- AbstractTensors `tan(s) = sin(s)/cos(s)` (`AT:409`) of a spinor; `NaN` coefficients where
the inverse of `cos s` is undefined. -/
def tan (s : Half V false Float) : Half V false Float := smul' s.sin (invD s.cos)

/-- AbstractTensors `exph(s) = cosh(s) + sinh(s)` (Grassmann `C:572`). -/
def exph (s : Half V false Float) : Half V false Float := s.cosh + s.sinh

end Half

/-! ## Couples, co-spinors and pseudo-couples: trigonometric functions -/

namespace Couple

variable [Kernels V]

/-- AbstractTensors `cos(z) = cosh(I ⟑ z)` (`AT:407`) of a couple: for a couple on the
pseudoscalar `I ⟑ z = im·I² + re·I` is again a couple on `I` (the complex cosine when
`I² = -1`); otherwise `I ⟑ z` is a pseudo-couple, whose `cosh` Julia routes to the
generated multivector series (`UndefVarError` in 0.8.46), computed here on the multivector. -/
def cos (z : Couple V Float) : Multivector V Float :=
  let i := pseudoMask V
  if z.bits == i && i != 0 then
    toMultivector (Couple.cosh (⟨i, z.im * bladeSq V i, z.re⟩ : Couple V Float))
  else Multivector.cos (toMultivector z)

/-- AbstractTensors `sin(z) = sinh(I ⟑ z)/I` (`AT:408`) of a couple (see `cos`). -/
def sin (z : Couple V Float) : Multivector V Float :=
  let i := pseudoMask V
  if z.bits == i && i != 0 then
    let w := Couple.sinh (⟨i, z.im * bladeSq V i, z.re⟩ : Couple V Float)
    let c := invPseudoCoef V
    toMultivector (⟨i, w.im * c * bladeSq V i, w.re * c⟩ : Couple V Float)
  else Multivector.sin (toMultivector z)

/-- AbstractTensors `tan(z) = sin(z)/cos(z)` (`AT:409`) of a couple (see `cos`). -/
def tan (z : Couple V Float) : Multivector V Float :=
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

/-- Julia `abs(t) = sqrt(abs2(t))` of a chain with `abs2(t) = contraction(t, t)` (`AT:435-439`),
the square root of a (metric) scalar. -/
@[inline] def abs (c : Chain V G Float) : Float := Float.sqrt (getD c.abs2.v 0)

/-- AbstractTensors `co f(t) = complementleft(f(complementright(t)))` for a function of chains
with multivector values (`AT:500-505`). -/
@[inline] def coMV (f : Chain V (V.n - G) Float → Multivector V Float) (c : Chain V G Float) :
    Multivector V Float :=
  Multivector.complementleft (f c.complementright)

/-- `coexp(t) = pseudoexp(t)` of a chain (`pseudoexp(0.5v₃) = 0.4794v₃ + 0.8776v₁₂₃` in `ℝ3`). -/
def coexp (c : Chain V G Float) : Multivector V Float := coMV Chain.exp c
/-- `colog(t) = pseudolog(t)` of a chain. -/
def colog (c : Chain V G Float) : Multivector V Float := coMV Chain.log c
/-- `cosqrt(t) = pseudosqrt(t)` of a chain. -/
def cosqrt (c : Chain V G Float) : Multivector V Float := coMV Chain.sqrt c
/-- `cocbrt(t) = pseudocbrt(t)` of a chain. -/
def cocbrt (c : Chain V G Float) : Multivector V Float := coMV Chain.cbrt c
/-- `cocosh(t) = pseudocosh(t)` of a chain. -/
def cocosh (c : Chain V G Float) : Multivector V Float := coMV (fun x => Half.toMultivector x.cosh) c
/-- `cosinh(t) = pseudosinh(t)` of a chain. -/
def cosinh (c : Chain V G Float) : Multivector V Float := coMV (fun x => Half.toMultivector x.sinh) c
/-- `cocos(t) = pseudocos(t)` of a chain. -/
def cocos (c : Chain V G Float) : Multivector V Float := coMV (fun x => Half.toMultivector x.cos) c
/-- `cosin(t) = pseudosin(t)` of a chain (`pseudosin(0.5v₃) = 0.5211v₃` in `ℝ3`). -/
def cosin (c : Chain V G Float) : Multivector V Float := coMV (fun x => Half.toMultivector x.sin) c
/-- `cotan(t) = pseudotan(t)` of a chain (complemented `tan`). -/
def cotan (c : Chain V G Float) : Multivector V Float := coMV (fun x => Half.toMultivector x.tan) c
/-- `cotanh(t) = pseudotanh(t)` of a chain. -/
def cotanh (c : Chain V G Float) : Multivector V Float := coMV (fun x => Half.toMultivector x.tanh) c
/-- `coinv(t) = pseudoinv(t)` of a chain (`pseudoinv(2v₁₂) = 0.5v₁₂` in `ℝ3`). -/
def coinv (c : Chain V G Float) : Chain V (V.n - (V.n - G)) Float := c.complementright.inv.complementleft
/-- `coabs(t) = pseudoabs(t)` of a chain: `abs` of the complement on the pseudoscalar
(`pseudoabs(3v₁ + 4v₂) = 5.0v₁₂₃` in `ℝ3`). -/
def coabs (c : Chain V G Float) : Chain V (V.n - 0) Float :=
  (Chain.scalar c.complementright.abs : Chain V 0 Float).complementleft
/-- `coabs2(t) = pseudoabs2(t)` of a chain. -/
def coabs2 (c : Chain V G Float) : Chain V (V.n - 0) Float :=
  c.complementright.abs2.complementleft

end Chain

end Grassmann

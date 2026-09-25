/-
Generic transcendental algorithms (port-notes §2.1.9-2.1.10, §4.2, §8.2 item 3).

Julia's AbstractTensors derives `cos`, `sin`, `tan`, …, `asinh`, …, `exp2`,
`log10`, `b^t`, `/`, `abs`, `unit` and the `co`/`pseudo` family from a few
primitives (`⟑`, `inv`, `~`, `cosh`, `sinh`, `expm1`, `log`, `sqrt`, `V(I)`,
the complements), and Grassmann implements those primitives by power series
with a norm-based stopping rule (`Grassmann.jl src/composite.jl`). Both layers
are written once here, generically:

* `SeriesRing X` is the arithmetic the series kernels need; `expm1Series`,
  `coshSeries`, `sinhSeries` and `qlog` are Grassmann's generic loops
  (`composite.jl:31-53, 304-321, 458-479, 517-536`) with Julia's exact
  termination rule and evaluation order;
* `TensorRing X` adds the unit pseudoscalar, complements, reverse and the
  *primitive* transcendentals as fields, so a carrier can override them with
  closed forms (Grassmann does, per element kind) while `TensorRing.ofSeries`
  fills them with the generic series; the derived family in `Generic` is
  AbstractTensors' formula table (AT:405-431, 435-480, 532-569).

Julia's second, "metric" family (every function threading a metric `g`)
needs no second copy: it is the same functions at a different `TensorRing`
instance (`letI := metricRing g; Generic.cos t`).

Semantics kept on purpose (port-notes §8.4):
* **B2**: `cos t = cosh(I ⟑ t)` literally, so for a scalar in a space with
  `I² = +1` (Euclidean `n ≡ 0, 1 mod 4`) `cos` returns `cosh`;
* `exp t = 1 + expm1 t` (AT:329);
* `a / b = a ⟑ inv(b)` is **right** division;
* **B1 fixed**: `logBase b t = log t / log b` (Julia returns `log b`).

Deviation: Julia's generic loops have no iteration cap and never terminate on
some non-finite inputs (`expm1(-Inf)` alternates `±Inf` forever); here every
loop has fuel (10000 terms, the cap of Grassmann's `@generated` variants).
-/
import AbstractTensors.Ops

namespace AbstractTensors

open StaticVectors JuliaBase

/-- The arithmetic the power-series kernels need (Julia `TensorAlgebra` values
with `+ - ⟑`, scalar scaling, `norm` and `inv`). `*` is the geometric product
`⟑`; real scalars act through `smul`/`sdiv`/`addScalar`, which leave every
other coefficient untouched (so signed zeros survive, as in Julia). -/
class SeriesRing (X : Type) extends Add X, Sub X, Mul X, Neg X where
  /-- Julia `k + t` for a real constant `k`: adds `k` to the scalar part only. -/
  addScalar : Float → X → X
  /-- Julia `k * t` for a real scalar `k`. -/
  smul : Float → X → X
  /-- Julia `t / k` for a real scalar `k`: true division of every coefficient. -/
  sdiv : X → Float → X
  /-- Julia `norm(t) = norm(value(t))`: the Euclidean norm of the coefficients. -/
  norm : X → Float
  /-- Julia `inv(t)`. -/
  inv : X → X

namespace Generic

open SeriesRing

variable {X : Type} [SeriesRing X]

/-- The iteration cap of the series loops. -/
def seriesFuel : Nat := 10000

/-- Julia `≈` on two running norms (`Base.isapprox`, default `rtol = √eps`). -/
@[inline] def approx (a b : Float) : Bool := F64.isapprox a b

/-- The shared loop of `expm1Series` (`composite.jl:39-50`): `n1 n2 n3` are
Julia's `norms`, `k` the next divisor. -/
@[specialize] def expm1Loop (t : X) (S term : X) (n1 n2 n3 : Float) (k : Nat) : Nat → X
  | 0 => S
  | fuel + 1 =>
    if n2 < n1 || n2 > 1 then
      let S := S + term
      let ns := norm S
      if approx ns n3 then S
      else
        let term := term * sdiv t (Float.ofNat k)
        expm1Loop t S term n2 (norm term) ns (k + 1) fuel
    else S

/-- Grassmann's generic `expm1(t)` (`composite.jl:31-53`):
`t + t²/2 + t³/3! + …`, summing while the term norms decrease or exceed 1 and
stopping when `norm(S)` stops changing (`≈`). Term `k` is `term ⟑ (t/k)`. -/
@[specialize] def expm1Series (t : X) : X :=
  let term := sdiv (t * t) 2
  let f := norm t
  expm1Loop t t term f (norm term) f 3 seriesFuel

/-- The shared loop of `coshSeries`/`sinhSeries` (`composite.jl:466-475`):
the next term is `term ⟑ (τ/(k(k-1)))`, `k` steps by 2. -/
@[specialize] def hypLoop (τ : X) (S term : X) (n1 n2 n3 : Float) (k : Nat) : Nat → X
  | 0 => S
  | fuel + 1 =>
    if n2 < n1 || n2 > 1 then
      let S := S + term
      let ns := norm S
      if approx ns n3 then S
      else
        let term := term * sdiv τ (Float.ofNat (k * (k - 1)))
        hypLoop τ S term n2 (norm term) ns (k + 2) fuel
    else S

/-- Grassmann's generic `cosh(t)` (`composite.jl:458-479`):
`1 + τ/2 + τ²/4! + …` with `τ = t ⟑ t`. -/
@[specialize] def coshSeries (t : X) : X :=
  let τ := t * t
  let S := sdiv τ 2
  let term := sdiv (τ * τ) 24
  let f := norm S
  addScalar 1 (hypLoop τ S term f (norm term) f 6 seriesFuel)

/-- Grassmann's generic `sinh(t)` (`composite.jl:517-536`):
`t + t⟑τ/3! + …` with `τ = t ⟑ t`. -/
@[specialize] def sinhSeries (t : X) : X :=
  let τ := t * t
  let f := norm t
  let term := sdiv (t * τ) 6
  hypLoop τ t term f (norm term) f 5 seriesFuel

/-- The loop of `qlog` (`composite.jl:311-319`). -/
@[specialize] def qlogLoop (w2 : X) (x : Nat) (S prod term : X) (n1 n2 n3 : Float) (k : Nat) :
    Nat → X
  | 0 => S
  | fuel + 1 =>
    if (n2 < n1 || n2 > 1) && k ≤ x then
      let S := S + term
      let ns := norm S
      if approx ns n3 then S
      else
        let prod := prod * w2
        let term := sdiv prod (Float.ofNat k)
        qlogLoop w2 x S prod term n2 (norm term) ns (k + 2) fuel
    else S

/-- Grassmann's `qlog(w, x = 10000)` (`composite.jl:304-321`, after Cephes
`qlog`): `2(w + w³/3 + w⁵/5 + …)`, the series of `log((1+w)/(1-w))`, with the
same stopping rule and the term cap `k ≤ x`. -/
@[specialize] def qlog (w : X) (x : Nat := 10000) : X :=
  let w2 := w * w
  let f := norm w
  let prod := w * w2
  let term := sdiv prod 3
  smul 2 (qlogLoop w2 x w prod term f (norm term) f 5 (x / 2 + 1))

/-- Grassmann's generic `log(t) = qlog((t - 1)/(t + 1))` (`composite.jl:369`),
with right division `a ⟑ inv(b)`. -/
@[specialize] def logSeries (t : X) : X :=
  qlog (addScalar (-1) t * inv (addScalar 1 t))

/-- Grassmann's generic `log1p(t) = qlog(t/(t + 2))` (`composite.jl:370`). -/
@[specialize] def log1pSeries (t : X) : X :=
  qlog (t * inv (addScalar 2 t))

/-- Julia `isapprox(a::TensorAlgebra, b::TensorAlgebra; atol, rtol, nans)`
(AT:229-232): with `x, y = norm(a), norm(b)`,
`(isfinite(x) && isfinite(y) && norm(a - b) ≤ max(atol, rtol·max(x, y))) || (nans && isnan(x) && isnan(y))`.
The default `rtol` is `rtoldefault(Float64) = √eps`, and `0` when `atol > 0`.
(Julia's `TensorGraded` method additionally compares manifolds and grades,
which are type indices here.) -/
def isapprox (a b : X) (atol : Float := 0) (rtol : Float := if atol > 0 then 0 else F64.rtoldefault)
    (nans : Bool := false) : Bool :=
  let x := norm a
  let y := norm b
  (x.isFinite && y.isFinite && norm (a - b) ≤ F64.max atol (rtol * F64.max x y)) ||
    (nans && x.isNaN && y.isNaN)

end Generic

/-- The homogeneous carrier of AbstractTensors' derived transcendental
functions (port-notes §8.2 item 3). The transcendental *primitives* are
fields, so a carrier can override them (Grassmann's closed forms per element
kind); `TensorRing.ofSeries` fills them with the generic series. -/
class TensorRing (X : Type) extends SeriesRing X where
  /-- Julia `zero(V)`. -/
  zero : X
  /-- Julia `one(V)`. -/
  one : X
  /-- Julia `V(I)`: the unit pseudoscalar of the manifold. -/
  pseudoscalar : X
  /-- Julia `~t` (reverse). -/
  reverse : X → X
  /-- Julia `isscalar(t)`. -/
  isScalar : X → Bool
  /-- Julia `scalar(t)`, as an element. -/
  scalar : X → X
  /-- Julia `complementleft(t)`. -/
  complementLeft : X → X
  /-- Julia `complementright(t)`. -/
  complementRight : X → X
  /-- Julia `expm1(t)`. -/
  expm1 : X → X
  /-- Julia `exp(t)`. -/
  exp : X → X
  /-- Julia `log(t)` (the metric family's `log_metric`). -/
  log : X → X
  /-- Julia `log1p(t)`. -/
  log1p : X → X
  /-- Julia `sqrt(t)`. -/
  sqrt : X → X
  /-- Julia `cbrt(t)`. -/
  cbrt : X → X
  /-- Julia `cosh(t)`. -/
  cosh : X → X
  /-- Julia `sinh(t)`. -/
  sinh : X → X

namespace TensorRing

/-- A `TensorRing` whose transcendental primitives are the generic ones:
`expm1`, `cosh`, `sinh` by series, `exp t = 1 + expm1 t` (AT:329),
`log`/`log1p` through `qlog`, and Grassmann's generic roots
`sqrt t = isscalar(t) ? √(scalar t) : exp(log(t)/2)` (`composite.jl:422-433`),
where the scalar root is supplied by the carrier. -/
@[reducible] def ofSeries {X : Type} [SeriesRing X] (zero one pseudoscalar : X)
    (reverse : X → X) (isScalar : X → Bool) (scalar : X → X)
    (complementLeft complementRight : X → X) (sqrtScalar cbrtScalar : X → X) : TensorRing X :=
  let exp : X → X := fun t => SeriesRing.addScalar 1 (Generic.expm1Series t)
  { zero, one, pseudoscalar, reverse, isScalar, scalar, complementLeft, complementRight
    expm1 := Generic.expm1Series
    exp := exp
    log := Generic.logSeries
    log1p := Generic.log1pSeries
    sqrt := fun t => if isScalar t then sqrtScalar t
      else exp (SeriesRing.sdiv (Generic.logSeries t) 2)
    cbrt := fun t => if isScalar t then cbrtScalar t
      else exp (SeriesRing.sdiv (Generic.logSeries t) 3)
    cosh := Generic.coshSeries
    sinh := Generic.sinhSeries }

end TensorRing

namespace Generic

open SeriesRing TensorRing

variable {X : Type} [TensorRing X]

/-! ## Division and powers (AT:318-330, 383-384) -/

/-- Julia `a / b = a ⟑ inv(b)` (AT:320): **right** division. -/
@[inline] def div (a b : X) : X := a * SeriesRing.inv b

/-- Julia `a \ b = inv(a) ⟑ b` (AT:323). -/
@[inline] def ldiv (a b : X) : X := SeriesRing.inv a * b

/-- Julia `b ^ t = exp(t ⟑ log(b))` for a real base `b > 0` (AT:326). -/
@[inline] def rpow (b : Float) (t : X) : X := TensorRing.exp (smul (F64.log b) t)

/-- Julia `log(b, t) = log(t)/log(b)` (AT:330), with bug B1 **fixed** (Julia's
metric pass-through at AT:401 shadows it and returns `log(b)`). -/
@[inline] def logBase (b : Float) (t : X) : X := sdiv (TensorRing.log t) (F64.log b)

/-- Julia `log2(t) = log2(ℯ)·log(t)` (AT:383). -/
@[inline] def log2 (t : X) : X := smul F64.log2e (TensorRing.log t)

/-- Julia `log10(t) = log10(ℯ)·log(t)` (AT:383). -/
@[inline] def log10 (t : X) : X := smul F64.log10e (TensorRing.log t)

/-- Julia `exp2(t) = exp(log(2)·t)` (AT:384). -/
@[inline] def exp2 (t : X) : X := TensorRing.exp (smul F64.ln2 t)

/-- Julia `exp10(t) = exp(log(10)·t)` (AT:384). -/
@[inline] def exp10 (t : X) : X := TensorRing.exp (smul F64.ln10 t)

/-- Julia `iszero(t) = norm(t) ≈ 0` (AT:445): exactly `norm(t) == 0` (NaN is not zero). -/
@[inline] def isZero (t : X) : Bool := approx (norm t) 0

/-! ## Trigonometric and hyperbolic (AT:405-431) -/

/-- Julia `cos(t) = cosh(I ⟑ t)` (AT:407). **B2 replicated**: for a scalar `t`
in a space with `I² = +1` this is `cosh t`. -/
@[inline] def cos (t : X) : X := TensorRing.cosh (pseudoscalar * t)

/-- Julia `sin(t) = sinh(I ⟑ t)/I` (AT:408), right division by `I`. -/
@[inline] def sin (t : X) : X := let i : X := pseudoscalar; div (TensorRing.sinh (i * t)) i

/-- Julia `tan(t) = sin(t)/cos(t)` (AT:409). -/
@[inline] def tan (t : X) : X := div (sin t) (cos t)

/-- Julia `cot(t) = cos(t)/sin(t)` (AT:410). -/
@[inline] def cot (t : X) : X := div (cos t) (sin t)

/-- Julia `sec(t) = inv(cos(t))` (AT:411). -/
@[inline] def sec (t : X) : X := SeriesRing.inv (cos t)

/-- Julia `csc(t) = inv(sin(t))` (AT:412). -/
@[inline] def csc (t : X) : X := SeriesRing.inv (sin t)

/-- Julia `sech(t) = inv(cosh(t))` (AT:415). -/
@[inline] def sech (t : X) : X := SeriesRing.inv (TensorRing.cosh t)

/-- Julia `csch(t) = inv(sinh(t))` (AT:416). -/
@[inline] def csch (t : X) : X := SeriesRing.inv (TensorRing.sinh t)

/-- Julia `tanh(t) = sinh(t)/cosh(t)` (AT:419). -/
@[inline] def tanh (t : X) : X := div (TensorRing.sinh t) (TensorRing.cosh t)

/-- Julia `coth(t) = cosh(t)/sinh(t)` (AT:420). -/
@[inline] def coth (t : X) : X := div (TensorRing.cosh t) (TensorRing.sinh t)

/-- Julia `asinh(t) = log(t + sqrt(1 + t⟑t))` (AT:421). -/
@[inline] def asinh (t : X) : X :=
  TensorRing.log (t + TensorRing.sqrt (addScalar 1 (t * t)))

/-- Julia `acosh(t) = log(t + sqrt(t⟑t - 1))` (AT:422). -/
@[inline] def acosh (t : X) : X :=
  TensorRing.log (t + TensorRing.sqrt (addScalar (-1) (t * t)))

/-- Julia `atanh(t) = (log(1+t) - log(1-t))/2` (AT:423). -/
@[inline] def atanh (t : X) : X :=
  sdiv (TensorRing.log (addScalar 1 t) - TensorRing.log (addScalar 1 (-t))) 2

/-- Julia `acoth(t) = (log(t+1) - log(t-1))/2` (AT:424). -/
@[inline] def acoth (t : X) : X :=
  sdiv (TensorRing.log (addScalar 1 t) - TensorRing.log (addScalar (-1) t)) 2

/-- Julia `asin(t) = (-I) ⟑ log(I⟑t + sqrt(1 - t⟑t))` (AT:425). -/
@[inline] def asin (t : X) : X :=
  let i : X := pseudoscalar
  (-i) * TensorRing.log (i * t + TensorRing.sqrt (addScalar 1 (-(t * t))))

/-- Julia `acos(t) = (-I) ⟑ log(t + I⟑sqrt(1 - t⟑t))` (AT:426). -/
@[inline] def acos (t : X) : X :=
  let i : X := pseudoscalar
  (-i) * TensorRing.log (t + i * TensorRing.sqrt (addScalar 1 (-(t * t))))

/-- Julia `atan(t) = ((-I)/2) ⟑ (log(1 + I⟑t) - log(1 - I⟑t))` (AT:427). -/
@[inline] def atan (t : X) : X :=
  let i : X := pseudoscalar
  let it := i * t
  sdiv (-i) 2 * (TensorRing.log (addScalar 1 it) - TensorRing.log (addScalar 1 (-it)))

/-- Julia `acot(t) = ((-I)/2) ⟑ (log(t - I) - log(t + I))` (AT:428). -/
@[inline] def acot (t : X) : X :=
  let i : X := pseudoscalar
  sdiv (-i) 2 * (TensorRing.log (t - i) - TensorRing.log (t + i))

/-- Julia `asec(t) = acos(inv(t))` (AT:413). -/
@[inline] def asec (t : X) : X := acos (SeriesRing.inv t)

/-- Julia `acsc(t) = asin(inv(t))` (AT:414). -/
@[inline] def acsc (t : X) : X := asin (SeriesRing.inv t)

/-- Julia `asech(t) = acosh(inv(t))` (AT:417). -/
@[inline] def asech (t : X) : X := acosh (SeriesRing.inv t)

/-- Julia `acsch(t) = asinh(inv(t))` (AT:418). -/
@[inline] def acsch (t : X) : X := asinh (SeriesRing.inv t)

/-- Julia `sinc(t) = iszero(t) ? 1 : sin(πt)/(πt)` (AT:429). -/
@[inline] def sinc (t : X) : X :=
  if isZero t then TensorRing.one else let x := smul F64.pi t; div (sin x) x

/-- Julia `cosc(t) = iszero(t) ? 0 : cos(πt)/t - sin(πt)/(πt ⟑ t)` (AT:430). -/
@[inline] def cosc (t : X) : X :=
  if isZero t then TensorRing.zero
  else let x := smul F64.pi t; div (cos x) t - div (sin x) (x * t)

/-! ## Norms (AT:435-480) -/

/-- Julia `abs2(t) = (a = (~t)⟑t; isscalar(a) ? scalar(a) : a)` for mixed
elements (AT:437); graded carriers override this with `contraction(t,t)`. -/
@[inline] def abs2 (t : X) : X :=
  let a := TensorRing.reverse t * t
  if TensorRing.isScalar a then TensorRing.scalar a else a

/-- Julia `abs(t) = sqrt(abs2(t))` (AT:435). -/
@[inline] def abs (t : X) : X := TensorRing.sqrt (abs2 t)

/-- Julia `unit(t) = t/abs(t)` (AT:462). -/
@[inline] def unit (t : X) : X := div t (abs t)

/-- Julia `coabs(t) = complementleft(abs(complementright(t)))` (AT:532). -/
@[inline] def coabs (t : X) : X := TensorRing.complementLeft (abs (TensorRing.complementRight t))

/-- Julia `geomabs(t) = abs(t) + coabs(t)` (AT:454). -/
@[inline] def geomabs (t : X) : X := abs t + coabs t

/-- Julia `unitnorm(t) = t/norm(geomabs(t))` (AT:479). -/
@[inline] def unitnorm (t : X) : X := sdiv t (norm (geomabs t))

/-- Julia `metric(a, b) = abs(a - b)` (AT:368). -/
@[inline] def metric (a b : X) : X := abs (a - b)

/-! ## The `co`/`pseudo` family (AT:532-569)

`co f = complementleft ∘ f ∘ complementright`; AT generates both a `co` and a
`pseudo` name for 13 functions. `cotan` is the *complemented* `tan`, not the
cotangent. -/

/-- Julia `@co f`: `complementleft(f(complementright(t)))`. -/
@[inline] def coOf (f : X → X) (t : X) : X := TensorRing.complementLeft (f (TensorRing.complementRight t))

/-- Julia `coabs2`/`pseudoabs2`/`antiabs2`. -/
@[inline] def coabs2 (t : X) : X := coOf abs2 t
/-- Julia `cosqrt`/`pseudosqrt`. -/
@[inline] def cosqrt (t : X) : X := coOf TensorRing.sqrt t
/-- Julia `cocbrt`/`pseudocbrt`. -/
@[inline] def cocbrt (t : X) : X := coOf TensorRing.cbrt t
/-- Julia `coexp`/`pseudoexp`. -/
@[inline] def coexp (t : X) : X := coOf TensorRing.exp t
/-- Julia `colog`/`pseudolog`. -/
@[inline] def colog (t : X) : X := coOf TensorRing.log t
/-- Julia `coinv`/`pseudoinv`. -/
@[inline] def coinv (t : X) : X := coOf SeriesRing.inv t
/-- Julia `cosin`/`pseudosin` (complemented `sin`). -/
@[inline] def cosin (t : X) : X := coOf sin t
/-- Julia `cocos`/`pseudocos` (complemented `cos`). -/
@[inline] def cocos (t : X) : X := coOf cos t
/-- Julia `cotan`/`pseudotan` (complemented `tan`, **not** the cotangent). -/
@[inline] def cotan (t : X) : X := coOf tan t
/-- Julia `cosinh`/`pseudosinh`. -/
@[inline] def cosinh (t : X) : X := coOf TensorRing.sinh t
/-- Julia `cocosh`/`pseudocosh`. -/
@[inline] def cocosh (t : X) : X := coOf TensorRing.cosh t
/-- Julia `cotanh`/`pseudotanh`. -/
@[inline] def cotanh (t : X) : X := coOf tanh t

/-- Julia `cometric(a, b) = pseudoabs(a - b)` (AT:368; its `Single`-pair
method ambiguity B4 does not arise here). -/
@[inline] def cometric (a b : X) : X := coabs (a - b)

/-- Julia `antiabs = coabs` (AT:551). -/
abbrev antiabs (t : X) : X := coabs t
/-- Julia `antiabs2 = coabs2` (AT:551). -/
abbrev antiabs2 (t : X) : X := coabs2 t
/-- Julia's binary `antimetric = cometric` (AT:551). -/
abbrev antimetric (a b : X) : X := cometric a b
/-- Julia `pseudometric = cometric` (AT:551). -/
abbrev pseudometric (a b : X) : X := cometric a b

/-- Julia `pseudo<f>` is the same function as `co<f>` (AT:532-548). -/
abbrev pseudoabs (t : X) : X := coabs t
/-- Julia `pseudoabs2`. -/
abbrev pseudoabs2 (t : X) : X := coabs2 t
/-- Julia `pseudosqrt`. -/
abbrev pseudosqrt (t : X) : X := cosqrt t
/-- Julia `pseudocbrt`. -/
abbrev pseudocbrt (t : X) : X := cocbrt t
/-- Julia `pseudoexp`. -/
abbrev pseudoexp (t : X) : X := coexp t
/-- Julia `pseudolog`. -/
abbrev pseudolog (t : X) : X := colog t
/-- Julia `pseudoinv`. -/
abbrev pseudoinv (t : X) : X := coinv t
/-- Julia `pseudosin`. -/
abbrev pseudosin (t : X) : X := cosin t
/-- Julia `pseudocos`. -/
abbrev pseudocos (t : X) : X := cocos t
/-- Julia `pseudotan`. -/
abbrev pseudotan (t : X) : X := cotan t
/-- Julia `pseudosinh`. -/
abbrev pseudosinh (t : X) : X := cosinh t
/-- Julia `pseudocosh`. -/
abbrev pseudocosh (t : X) : X := cocosh t
/-- Julia `pseudotanh`. -/
abbrev pseudotanh (t : X) : X := cotanh t

end Generic

end AbstractTensors

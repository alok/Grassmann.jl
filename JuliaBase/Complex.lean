import JuliaBase.Math
import JuliaBase.Trig
import JuliaBase.Hyperbolic

/-!
Julia's `Complex{T}` (Julia `base/complex.jl`): the port's one computable complex number
type (DESIGN.md §4.1). Lean core has no complex numbers and Mathlib's `Complex` sits on
the noncomputable `ℝ`.

* **Generic algebra** (namespace `Complex`), for any component type: `+ - *` in Julia's
  operation order, `conj`, `abs2`, and the mixed real/complex operations. Julia does
  **not** promote the real operand: `x + z = Complex(x + re, im)` and
  `x * z = Complex(x·re, x·im)`, so signed zeros in the untouched part survive. Numeric
  literals do embed as complex numbers (`(2 : Complex Float) = ⟨2, 0⟩`), so write
  `(2.0 : Float) * z` to get Julia's `2.0 * z` exactly. `/` and `inv` on an exact field
  (`Rat`) use the textbook formulas, which are exact there.
* **`ComplexF64`** (namespace `ComplexF64`, Julia's `Complex{Float64}`): the robust
  Baudin–Smith division and inverse (complex.jl:390-510), `abs = hypot`, `isapprox`, and
  Julia's `sqrt`, `exp`, `expm1`, `log`, `log1p`, `cis`, the trigonometric and hyperbolic
  functions and their inverses, and `^` (`_cpow`), ported line by line from Julia 1.13.
  Every real function they call is Julia's own kernel (`exp`, `log`, `expm1`, `log1p`, `^`
  from `JuliaBase.Math`; `sincos`, `sin`, `tan`, `atan`, `atan(y, x)`, `sinpi`, `cospi` from
  `JuliaBase.Trig`; `sinh`, `cosh`, `asinh` from `JuliaBase.Hyperbolic`), never the platform
  `libm`, so all of them agree with the oracle bit for bit (`Tests/JuliaBase/trig.json`).
  `div` and `inv` are `@[inline]` with their constants decoded at elaboration time or hoisted
  (the rare over/underflow paths stay out of line), so they specialize into hot loops.
* **`ComplexF32`**: Julia's `/` and `inv`, which widen to `Float64`.
-/

universe u

namespace JuliaBase

/-- Julia `Complex{T}`: `re + im·i`. -/
structure Complex (α : Type u) where
  /-- Real part (Julia `real(z)`). -/
  re : α
  /-- Imaginary part (Julia `imag(z)`). -/
  im : α
  deriving BEq, Repr, Inhabited, Hashable, DecidableEq

namespace Complex

variable {α : Type u}

/-- Julia `complex(x)` for a real `x`: `x + 0im`. -/
@[inline] def ofReal [OfNat α 0] (x : α) : Complex α := ⟨x, 0⟩

/-- Julia `im`. -/
@[inline] def I [OfNat α 0] [OfNat α 1] : Complex α := ⟨0, 1⟩

/-- Numeric literals embed as real complex numbers (`zero(Complex{T})` = `0 + 0im`,
`one(Complex{T})` = `1 + 0im`). -/
instance {n : Nat} [OfNat α n] [OfNat α 0] : OfNat (Complex α) n := ⟨⟨OfNat.ofNat n, 0⟩⟩

/-- Scientific literals embed as real complex numbers. -/
instance [OfScientific α] [OfNat α 0] : OfScientific (Complex α) :=
  ⟨fun m s e => ⟨OfScientific.ofScientific m s e, 0⟩⟩

/-! ## Ring operations (complex.jl:276-336) -/

/-- Julia `+(z::Complex, w::Complex)` (complex.jl:288). -/
instance [Add α] : Add (Complex α) := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

/-- Julia `-(z::Complex, w::Complex)` (complex.jl:289). -/
instance [Sub α] : Sub (Complex α) := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

/-- Julia `-(z::Complex)` (complex.jl:287). -/
instance [Neg α] : Neg (Complex α) := ⟨fun z => ⟨-z.re, -z.im⟩⟩

/-- Julia `*(z::Complex, w::Complex)` (complex.jl:290):
`(re z·re w - im z·im w) + (re z·im w + im z·re w)i`, in that order. -/
instance [Add α] [Sub α] [Mul α] : Mul (Complex α) :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

/-- Julia `*(x::Real, z::Complex)` (complex.jl:335): `Complex(x·re, x·im)`. -/
@[inline] def smul [Mul α] (x : α) (z : Complex α) : Complex α := ⟨x * z.re, x * z.im⟩

/-- Julia `x * z = Complex(x·re, x·im)` for real `x` (complex.jl:335). -/
instance [Mul α] : HMul α (Complex α) (Complex α) := ⟨smul⟩

/-- Julia `z * x = Complex(x·re, x·im)` for real `x` (complex.jl:336). -/
instance [Mul α] : HMul (Complex α) α (Complex α) := ⟨fun z x => smul x z⟩

/-- Julia `z / x = Complex(re/x, im/x)` for real `x` (complex.jl:348). -/
instance [Div α] : HDiv (Complex α) α (Complex α) := ⟨fun z x => ⟨z.re / x, z.im / x⟩⟩

/-- Julia `x + z = Complex(x + re, im)` (complex.jl:327). -/
instance [Add α] : HAdd α (Complex α) (Complex α) := ⟨fun x z => ⟨x + z.re, z.im⟩⟩

/-- Julia `z + x = Complex(x + re, im)` (complex.jl:328). -/
instance [Add α] : HAdd (Complex α) α (Complex α) := ⟨fun z x => ⟨x + z.re, z.im⟩⟩

/-- Julia `x - z = Complex(x - re, -im)` (complex.jl:329). -/
instance [Sub α] [Neg α] : HSub α (Complex α) (Complex α) := ⟨fun x z => ⟨x - z.re, -z.im⟩⟩

/-- Julia `z - x = Complex(re - x, im)` (complex.jl:334). -/
instance [Sub α] : HSub (Complex α) α (Complex α) := ⟨fun z x => ⟨z.re - x, z.im⟩⟩

/-- Julia `conj(z)` (complex.jl:276). -/
@[inline] def conj [Neg α] (z : Complex α) : Complex α := ⟨z.re, -z.im⟩

/-- Julia `abs2(z)` = `re·re + im·im` (complex.jl:278). -/
@[inline] def abs2 [Add α] [Mul α] (z : Complex α) : α := z.re * z.re + z.im * z.im

/-- `/` on complex numbers over an exact field (`Rat`): the textbook formula
`z·conj(w)/abs2(w)`, exact there (Julia's generic `/`, complex.jl:350, computes the same
exact value by Smith's algorithm). `Complex Float` and `Complex Float32` use Julia's
`ComplexF64.div`/`ComplexF32.div`. Over `Int` this is truncating division, whereas Julia's
`/` on `Complex{Int}` returns a `ComplexF64`. -/
instance (priority := low) instDivGeneric [Add α] [Sub α] [Mul α] [Div α] : Div (Complex α) :=
  ⟨fun z w =>
    let d := w.re * w.re + w.im * w.im
    ⟨(z.re * w.re + z.im * w.im) / d, (z.im * w.re - z.re * w.im) / d⟩⟩

/-- Julia `inv(z) = conj(z)/abs2(z)` (complex.jl:279) over an exact field. `Complex Float`
and `Complex Float32` use `ComplexF64.inv`/`ComplexF32.inv`. -/
instance (priority := low) instInvGeneric [Add α] [Mul α] [Neg α] [Div α] : Inv (Complex α) :=
  ⟨fun z => let d := z.re * z.re + z.im * z.im; ⟨z.re / d, -z.im / d⟩⟩

end Complex

/-! ## `ComplexF64` -/

/-- Julia `ComplexF64 = Complex{Float64}` (complex.jl:38). The namespace `ComplexF64` holds
Julia's `Float64`-specific complex algorithms. -/
abbrev ComplexF64 : Type := Complex Float

namespace ComplexF64

/-- Julia `abs(z::Complex)` = `hypot(re, im)` (complex.jl:277). -/
@[inline] def abs (z : Complex Float) : Float := F64.hypot z.re z.im

/-- Julia `angle(z) = atan(im, re)` (complex.jl:641), with Julia's own two-argument arctangent
(`F64.atan2`). -/
@[inline] def angle (z : Complex Float) : Float := F64.atan2 z.im z.re

/-- Julia `isfinite(z::Complex)`. -/
@[inline] def isFinite (z : Complex Float) : Bool := F64.isfinite z.re && F64.isfinite z.im

/-- Julia `isnan(z::Complex)`. -/
@[inline] def isNaN (z : Complex Float) : Bool := F64.isnan z.re || F64.isnan z.im

/-- Julia `cis(ϕ) = cos ϕ + i sin ϕ` (complex.jl:577), from one `sincos`. -/
@[inline] def cis (ϕ : Float) : Complex Float := F64.sincosK ϕ fun s c => ⟨c, s⟩

/-! ### Division and inverse -/

/-- Julia's over/underflow threshold `0.5*floatmax(Float64)` (complex.jl:398). -/
def halfov : Float := f64! 0.5 * F64.floatmax

/-- Julia's underflow threshold `floatmin(Float64)*2.0/eps(Float64)` (complex.jl:399). -/
def twounϵ : Float := F64.floatmin * f64! 2.0 / F64.eps

/-- Julia's scale factor `2.0/(ϵ*ϵ)` (complex.jl:439). -/
def bs : Float := f64! 2.0 / (F64.eps * F64.eps)

/-- `1/bs`, the unscaling factor of a scaled-up numerator (`s /= bs`, complex.jl:442). -/
def invBs : Float := f64! 1.0 / bs

/-- `sqrt(floatmin(Float64)/2)`, the lower end of `inv`'s unscaled range (complex.jl:477). -/
def invLo : Float := (F64.floatmin / f64! 2.0).sqrt

/-- `sqrt(floatmax(Float64)/2)`, the upper end of `inv`'s unscaled range (complex.jl:477). -/
def invHi : Float := (F64.floatmax / f64! 2.0).sqrt

/-- `floatmax(Float64)/2`, `inv`'s scale-down threshold (complex.jl:487). -/
def halfFloatmax : Float := F64.floatmax / f64! 2.0

/-- Julia `robust_cdiv2` (complex.jl:457). -/
@[inline] def robustCdiv2 (a b c d r t : Float) : Float :=
  if r != f64! 0.0 then
    let br := b * r
    if br != f64! 0.0 then (a + br) * t else a * t + (b * t) * r
  else (a + d * (b / c)) * t

/-- Julia `robust_cdiv1` (complex.jl:450), times the unscaling factor `s`. -/
@[inline] def robustCdiv1 (a b c d s : Float) : Complex Float :=
  let r := d / c
  let t := f64! 1.0 / (c + d * r)
  ⟨robustCdiv2 a b c d r t * s, robustCdiv2 b (-a) c d r t * s⟩

/-- Julia `cdiv` (complex.jl:425), times the unscaling factor `s` (`scaling_cdiv`,
complex.jl:432). -/
@[inline] def cdiv (a b c d s : Float) : Complex Float :=
  if d.abs ≤ c.abs then robustCdiv1 a b c d s
  else
    let r := c / d
    let t := f64! 1.0 / (d + c * r)
    ⟨robustCdiv2 b a d c r t * s, -(robustCdiv2 a (-b) d c r t) * s⟩

/-- The `c, d` half of `scaleargs_cdiv` (complex.jl:444-448), then `cdiv` and unscaling. -/
@[inline] def scaleCD (a b c d cd s : Float) : Complex Float :=
  if cd ≥ halfov then cdiv a b (c * f64! 0.5) (d * f64! 0.5) (s * f64! 0.5)
  else if cd ≤ twounϵ then cdiv a b (c * bs) (d * bs) (s * bs)
  else cdiv a b c d s

/-- Julia `scaling_cdiv` (complex.jl:430-435, `@noinline` there too): the over/underflow path
of `/`, kept out of line so that the common path stays small. -/
def scalingCdiv (a b c d ab cd : Float) : Complex Float :=
  -- scaleargs_cdiv (complex.jl:436-449): `s` starts at 1.0
  if ab ≥ halfov then scaleCD (a * f64! 0.5) (b * f64! 0.5) c d cd (f64! 2.0)
  else if ab ≤ twounϵ then scaleCD (a * bs) (b * bs) c d cd invBs
  else scaleCD a b c d cd (f64! 1.0)

/-- Julia `/(z::ComplexF64, w::ComplexF64)` (complex.jl:390-423): robust division with
over/underflow scaling (Baudin–Smith, arXiv:1210.4539). Inlined, with every constant decoded at
elaboration time or hoisted, so that a division inside a specialized loop stays unboxed and
free of `Float.ofScientific` calls (`docs/PERF.md`). -/
@[inline] def div (z w : Complex Float) : Complex Float :=
  let a := z.re
  let b := z.im
  let c := w.re
  let d := w.im
  let absa := a.abs
  let absb := b.abs
  let ab := if absa ≥ absb then absa else absb
  let absc := c.abs
  let absd := d.abs
  let cd := if absc ≥ absd then absc else absd
  if F64.isinf c || F64.isinf d then
    if isFinite z then ⟨f64! 0.0 * F64.sign a * F64.sign c, (f64! -0.0) * F64.sign b * F64.sign d⟩
    else ⟨F64.nan, F64.nan⟩
  else if ab ≥ halfov || ab ≤ twounϵ || cd ≥ halfov || cd ≤ twounϵ then scalingCdiv a b c d ab cd
  else cdiv a b c d (f64! 1.0)  -- the unscaled path; multiplying by 1.0 is exact

/-- `z / w` on `ComplexF64` is Julia's robust division. -/
instance : Div (Complex Float) := ⟨div⟩

/-- Julia `robust_cinv(c, d)` (complex.jl:503) as `(p, q)` scaled by `s`, written into the
real (`swap = false`) or swapped (`swap = true`, the `q, p = robust_cinv(-d, -c)` call)
slots. -/
@[inline] def robustCinv (c d s : Float) (swap : Bool) : Complex Float :=
  let r := d / c
  let z := Float.fma d r c
  let p := f64! 1.0 / z
  let q := -r / z
  if swap then ⟨q * s, p * s⟩ else ⟨p * s, q * s⟩

/-- The scaled path of Julia `inv(w::ComplexF64)` (complex.jl:480-500), out of line. -/
def scaledInv (c d absc absd cd : Float) : Complex Float :=
  let finish (c d s : Float) : Complex Float :=
    if absd ≤ absc then robustCinv c d s false else robustCinv (-d) (-c) s true
  if cd ≥ halfFloatmax then finish (c * f64! 0.5) (d * f64! 0.5) (f64! 0.5)
  else if cd ≤ twounϵ then finish (c * bs) (d * bs) bs
  else finish c d (f64! 1.0)

/-- Julia `inv(w::ComplexF64)` (complex.jl:472-501): `conj(w)/muladd(cd, cd, dc²)` in the
safe range (the `muladd` is a hardware FMA on the oracle machine), and a scaled robust
inversion outside it. Inlined, with hoisted constants. -/
@[inline] def inv (w : Complex Float) : Complex Float :=
  let c := w.re
  let d := w.im
  let absc := c.abs
  let absd := d.abs
  let cd := if absc > absd then absc else absd
  let dc := if absc > absd then absd else absc
  if invLo ≤ cd && cd ≤ invHi then
    let m := Float.fma cd cd (dc * dc)
    ⟨c / m, -d / m⟩
  else if F64.isinf c || F64.isinf d then ⟨F64.copysign (f64! 0.0) c, F64.flipsign (f64! -0.0) d⟩
  else scaledInv c d absc absd cd

/-- `z⁻¹` on `ComplexF64` is Julia's robust inverse. -/
instance : Inv (Complex Float) := ⟨inv⟩

/-- Julia `isapprox(x::ComplexF64, y::ComplexF64; atol=0, rtol=√eps, nans=false)`
(floatfuncs.jl:222) with `norm = abs`:
`x == y || (isfinite(x) && isfinite(y) && |x-y| ≤ max(atol, rtol·max(|x|,|y|))) || (nans && isnan(x) && isnan(y))`. -/
def isapprox (x y : Complex Float) (atol : Float := 0)
    (rtol : Float := if atol > 0 then 0 else F64.rtoldefault) (nans : Bool := false) : Bool :=
  x == y ||
    (isFinite x && isFinite y && abs (x - y) ≤ F64.max atol (rtol * F64.max (abs x) (abs y))) ||
    (nans && isNaN x && isNaN y)

/-! ### Roots, exponentials and logarithms -/

/-- `nextfloat(0.0)/(2*eps(Float64)^2)`, the underflow threshold of `ssqs` (complex.jl:513). -/
def ssqsTiny : Float := Float.ofBits 1 / (f64! 2.0 * (F64.eps * F64.eps))

/-- Julia `ssqs(x, y)` (complex.jl:509): `x² + y²` and a scaling exponent `k`, rescaled
when the sum over/underflows. -/
@[inline] def ssqs (x y : Float) : Float × Int :=
  let ρ := x * x + y * y
  if !F64.isfinite ρ && (F64.isinf x || F64.isinf y) then (F64.inf, 0)
  else if F64.isinf ρ || (ρ == f64! 0.0 && (x != f64! 0.0 || y != f64! 0.0)) || ρ < ssqsTiny then
    let m := F64.max x.abs y.abs
    let k := if m == f64! 0.0 then 0 else F64.exponent m
    let xk := F64.ldexp x (-k)
    let yk := F64.ldexp y (-k)
    (xk * xk + yk * yk, k)
  else (ρ, 0)

/-- Julia `sqrt(z::Complex)` (complex.jl:523), Kahan's algorithm without intermediate
over/underflow. -/
@[inline] def sqrt (z : Complex Float) : Complex Float :=
  let x := z.re
  let y := z.im
  if x == f64! 0.0 && y == f64! 0.0 then ⟨f64! 0.0, y⟩
  else
    let (ρ, k) := ssqs x y
    let ρ := if F64.isfinite x then F64.ldexp x.abs (-k) + ρ.sqrt else ρ
    let (ρ, k) := if JInt.isodd k then (ρ, (k - 1) / 2) else (ρ + ρ, k / 2 - 1)
    let ρ := F64.ldexp ρ.sqrt k
    if ρ != f64! 0.0 then
      let η := if F64.isfinite y then (y / ρ) / f64! 2.0 else y
      if x < f64! 0.0 then ⟨η.abs, F64.copysign ρ y⟩ else ⟨ρ, η⟩
    else ⟨ρ, y⟩

/-- Julia `log(z::Complex)` (complex.jl:643). -/
@[inline] def log (z : Complex Float) : Complex Float :=
  let x := z.re
  let y := z.im
  let (ρ, k) := ssqs x y
  let ax := x.abs
  let ay := y.abs
  let (θ, β) := if ax < ay then (ax, ay) else (ay, ax)
  let ρρ :=
    if k == 0 && f64! 0.5 < β * β && (β ≤ f64! 1.25 || ρ < f64! 3.0) then
      F64.log1p ((β - f64! 1.0) * (β + f64! 1.0) + θ * θ) / f64! 2.0
    else F64.log ρ / f64! 2.0 + F64.ofInt k * F64.ln2
  ⟨ρρ, angle z⟩

/-- Julia `exp(z::Complex)` (complex.jl:694). -/
@[inline] def exp (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if F64.isnan zr then ⟨zr, if zi == f64! 0.0 then zi else zr⟩
  else if !F64.isfinite zi then
    if zr == F64.inf then ⟨-zr, F64.nan⟩
    else if zr == -F64.inf then ⟨f64! -0.0, F64.copysign (f64! 0.0) zi⟩
    else ⟨F64.nan, F64.nan⟩
  else
    let er := F64.exp zr
    if zi == f64! 0.0 then ⟨er, zi⟩
    else F64.sincosK zi fun s c => ⟨er * c, er * s⟩

/-- Julia `expm1(z::Complex)` (complex.jl:717). -/
def expm1 (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if F64.isnan zr then ⟨zr, if zi == f64! 0.0 then zi else zr⟩
  else if !F64.isfinite zi then
    if zr == F64.inf then ⟨-zr, F64.nan⟩
    else if zr == -F64.inf then ⟨f64! -1.0, F64.copysign (f64! 0.0) zi⟩
    else ⟨F64.nan, F64.nan⟩
  else
    let erm1 := F64.expm1 zr
    if zi == f64! 0.0 then ⟨erm1, zi⟩
    else
      let er := erm1 + f64! 1.0
      if F64.isfinite er then
        let s := F64.sin (f64! 0.5 * zi)
        ⟨erm1 - f64! 2.0 * er * (s * s), er * F64.sin zi⟩
      else F64.sincosK zi fun s c => ⟨er * c, er * s⟩

/-- Julia `log1p(z::Complex)` (complex.jl:747). -/
def log1p (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if F64.isfinite zr then
    if F64.isinf zi then log z
    else
      let u : Complex Float := f64! 1.0 + z
      if u.re == f64! 1.0 && u.im == f64! 0.0 then z
      else if u.re ≤ f64! 0.0 then log u
      else log u * div z (u - f64! 1.0)
  else if F64.isnan zr then ⟨zr, zr⟩
  else if F64.isfinite zi then ⟨F64.inf, F64.copysign (if zr > f64! 0.0 then f64! 0.0 else F64.pi) zi⟩
  else ⟨F64.inf, F64.nan⟩

/-! ### Trigonometric and hyperbolic functions -/

/-- `Float64(π)/2` (Julia's `oftype(x, pi)/2`, an exact halving). -/
def halfPi : Float := f64! 1.5707963267948966

/-- `Float64(π)/4`. -/
def quarterPi : Float := f64! 0.7853981633974483

/-- Julia `sin(z::Complex)` (complex.jl:887), with Julia's own `sincos`, `sinh` and `cosh`. -/
def sin (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if zr == f64! 0.0 then ⟨zr, F64.sinh zi⟩
  else if !F64.isfinite zr then
    if zi == f64! 0.0 || F64.isinf zi then ⟨F64.nan, zi⟩ else ⟨F64.nan, F64.nan⟩
  else
    let ch := F64.cosh zi
    let sh := F64.sinh zi
    F64.sincosK zr fun s c => ⟨s * ch, c * sh⟩

/-- Julia `cos(z::Complex)` (complex.jl:905). -/
def cos (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if zr == f64! 0.0 then ⟨F64.cosh zi, if F64.isnan zi then zr else -(F64.flipsign zr zi)⟩
  else if !F64.isfinite zr then
    if zi == f64! 0.0 then ⟨F64.nan, if F64.isnan zr then f64! 0.0 else -(F64.flipsign zi zr)⟩
    else if F64.isinf zi then ⟨F64.inf, F64.nan⟩
    else ⟨F64.nan, F64.nan⟩
  else
    let ch := F64.cosh zi
    let sh := F64.sinh zi
    F64.sincosK zr fun s c => ⟨c * ch, -s * sh⟩

/-- Julia `sinh(z) = i⁻¹ sin(iz)` computed by swapping parts (complex.jl:973). -/
def sinh (z : Complex Float) : Complex Float :=
  let w := sin ⟨z.im, z.re⟩
  ⟨w.im, w.re⟩

/-- Julia `cosh(z) = cos(iz)` (complex.jl:979). -/
def cosh (z : Complex Float) : Complex Float := cos ⟨z.im, -z.re⟩

/-- `asinh(floatmax(Float64))` (Julia's own `asinh`), the overflow threshold of `tanh`
(complex.jl:990). -/
def asinhFloatmax : Float := F64.asinh F64.floatmax

/-- Julia `tanh(z::Complex)` (complex.jl:984), Kahan's overflow-free form. -/
def tanh (z : Complex Float) : Complex Float :=
  let ξ := z.re
  let η := z.im
  if F64.isnan ξ && η == f64! 0.0 then ⟨ξ, η⟩
  else if f64! 4.0 * ξ.abs > asinhFloatmax then
    ⟨F64.copysign (f64! 1.0) ξ,
      F64.copysign (f64! 0.0) (η * (if F64.isfinite η then F64.sin (f64! 2.0 * η.abs) else f64! 1.0))⟩
  else
    let t := F64.tan η
    let β := f64! 1.0 + t * t
    let s := F64.sinh ξ
    let ρ := (f64! 1.0 + s * s).sqrt
    if F64.isinf t then ⟨ρ / s, f64! 1.0 / t⟩
    else (⟨β * ρ * s, t⟩ : Complex Float) / (f64! 1.0 + β * s * s)

/-- Julia `tan(z) = -i tanh(iz)` (complex.jl:925). -/
def tan (z : Complex Float) : Complex Float :=
  let w := tanh ⟨-z.im, z.re⟩
  ⟨w.im, -w.re⟩

/-- Julia `asin(z::Complex)` (complex.jl:931), Kahan's branch-cut-exact form. -/
def asin (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if F64.isinf zr && F64.isinf zi then ⟨F64.copysign quarterPi zr, zi⟩
  else if F64.isnan zi && F64.isinf zr then ⟨zi, F64.inf⟩
  else
    let ξ :=
      if zr == f64! 0.0 then zr
      else if !F64.isfinite zr then halfPi * F64.sign zr
      else F64.atan2 zr (sqrt (f64! 1.0 - z) * sqrt (f64! 1.0 + z)).re
    let η := F64.asinh
      (F64.copysign (sqrt (Complex.conj (f64! 1.0 - z)) * sqrt (f64! 1.0 + z)).im zi)
    ⟨ξ, η⟩

/-- Julia `acos(z::Complex)` (complex.jl:945). -/
def acos (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if F64.isnan zr then (if F64.isinf zi then ⟨zr, -zi⟩ else ⟨zr, zr⟩)
  else if F64.isnan zi then
    if F64.isinf zr then ⟨zi, zr.abs⟩
    else if zr == f64! 0.0 then ⟨halfPi, zi⟩
    else ⟨zi, zi⟩
  else if zr == f64! 0.0 && zi == f64! 0.0 then ⟨halfPi, -zi⟩
  else if zr == F64.inf && zi.toBits == 0 then ⟨zi, -zr⟩  -- `zi === 0.0`
  else if zr == -F64.inf && zi.toBits == F64.signMask then ⟨F64.pi, -zr⟩  -- `zi === -0.0`
  else
    let ξ := f64! 2.0 * F64.atan2 (sqrt (f64! 1.0 - z)).re (sqrt (f64! 1.0 + z)).re
    let η := F64.asinh (sqrt (Complex.conj (f64! 1.0 + z)) * sqrt (f64! 1.0 - z)).im
    let ξ := if F64.isinf zr && F64.isinf zi then ξ - quarterPi * F64.sign zr else ξ
    ⟨ξ, η⟩

/-- Julia `asinh(z) = -i asin(iz)` by part swapping (complex.jl:1006). -/
def asinh (z : Complex Float) : Complex Float :=
  let w := asin ⟨-z.im, z.re⟩
  ⟨w.im, -w.re⟩

/-- Julia `acosh(z::Complex)` (complex.jl:1011). -/
def acosh (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if F64.isnan zr || F64.isnan zi then
    if F64.isinf zr || F64.isinf zi then ⟨F64.inf, F64.nan⟩ else ⟨F64.nan, F64.nan⟩
  else if zr == -F64.inf && zi.toBits == F64.signMask then ⟨F64.inf, -F64.pi⟩
  else
    let ξ := F64.asinh (sqrt (Complex.conj (z - f64! 1.0)) * sqrt (z + f64! 1.0)).re
    let η := f64! 2.0 * F64.atan2 (sqrt (z - f64! 1.0)).im (sqrt (z + f64! 1.0)).re
    let η := if F64.isinf zr && F64.isinf zi then η - quarterPi * F64.sign zi * F64.sign zr else η
    ⟨ξ, η⟩

/-- `sqrt(floatmax(Float64))/4`, the overflow threshold of `atanh` (complex.jl:1034). -/
def atanhBig : Float := F64.floatmax.sqrt / f64! 4.0

/-- Julia `atanh(z::Complex)` (complex.jl:1030), Kahan's form. -/
def atanh (z : Complex Float) : Complex Float :=
  let x := z.re
  let y := z.im
  let ax := x.abs
  let ay := y.abs
  if ax > atanhBig || ay > atanhBig then
    if F64.isnan y then
      if F64.isinf x then ⟨F64.copysign (f64! 0.0) x, y⟩ else ⟨(inv z).re, y⟩
    else if F64.isinf y then ⟨F64.copysign (f64! 0.0) x, F64.copysign halfPi y⟩
    else ⟨(inv z).re, F64.copysign halfPi y⟩
  else
    let β := F64.copysign (f64! 1.0) x
    let z : Complex Float := β * z
    let x := z.re
    let y := z.im
    let (ξ, η) :=
      if x == f64! 1.0 then
        if y == f64! 0.0 then (F64.inf, y)
        else
          (F64.log ((Float.fma y y (f64! 4.0)).sqrt.sqrt / ay.sqrt),
            F64.copysign (halfPi + F64.atan (ay / f64! 2.0)) y / f64! 2.0)
      else
        let ysq := ay * ay
        let ξ := if x == f64! 0.0 then x
          else F64.log1p (f64! 4.0 * x / Float.fma (f64! 1.0 - x) (f64! 1.0 - x) ysq) / f64! 4.0
        (ξ, angle ⟨(f64! 1.0 - x) * (f64! 1.0 + x) - ysq, f64! 2.0 * y⟩ / f64! 2.0)
    β * (⟨ξ, η⟩ : Complex Float)

/-- Julia `atan(z) = -i atanh(iz)` (complex.jl:968).

Julia negates `imag(z)`, and for a NaN imaginary part that flips the NaN's sign bit, which
`atanh` then reads back through `copysign(zero(x), x)`: `atan(±Inf + NaN·im) = ±π/2 + 0.0im`. A
Lean NaN has no observable sign (`Float.toBits` canonicalizes NaNs, as Float's logical model
identifies them), so every Lean NaN behaves as Julia's positive `NaN` and `-NaN` would read as
positive too; that one case is written out. -/
def atan (z : Complex Float) : Complex Float :=
  if F64.isnan z.im && F64.isinf z.re then ⟨F64.copysign halfPi z.re, f64! 0.0⟩
  else
    let w := atanh ⟨-z.im, z.re⟩
    ⟨w.im, -w.re⟩

/-! ### Powers -/

/-- Julia `_cpow(z, p)` (complex.jl:782): `z^p` for complex `z` and `p`. A negative real base
with a real, non-integer power uses Julia's own `cospi`/`sinpi`. -/
def pow (z p : Complex Float) : Complex Float :=
  if p.im == f64! 0.0 then
    let pr := p.re
    if pr == pr.floor && pr.abs < f64! 2147483647.0 then
      if pr == f64! 0.0 then ⟨f64! 1.0, F64.flipsign (F64.copysign (f64! 0.0) pr) z.im⟩
      else
        let ip : Int := if pr < f64! 0.0 then -((-pr).toUInt64.toNat : Int) else (pr.toUInt64.toNat : Int)
        if z.im == f64! 0.0 then
          let zr := z.re
          if ip < 0 && zr == f64! 0.0 then ⟨F64.nan, F64.nan⟩
          else
            let (re, im) :=
              if ip < 0 then (powBySquaring (· * ·) (f64! 1.0) (f64! 1.0 / zr) ip.natAbs, -z.im)
              else (powBySquaring (· * ·) (f64! 1.0) zr ip.natAbs, z.im)
            ⟨re, if ip % 2 == 0 && F64.signbit zr then -im else im⟩
        else if ip < 0 then powBySquaring (· * ·) ⟨f64! 1.0, f64! 0.0⟩ (inv z) ip.natAbs
        else powBySquaring (· * ·) ⟨f64! 1.0, f64! 0.0⟩ z ip.natAbs
    else if z.im == f64! 0.0 then
      let zr := z.re
      if zr == f64! 0.0 then (if pr > f64! 0.0 then z else ⟨F64.nan, F64.nan⟩)
      else if zr > f64! 0.0 then ⟨F64.pow zr pr, F64.flipsign z.im pr⟩
      else
        let rp := F64.pow (-zr) pr
        if F64.isfinite pr then
          rp * (⟨F64.cospi pr, F64.flipsign (F64.sinpi pr) z.im⟩ : Complex Float)
        else if rp == f64! 0.0 then ⟨f64! 0.0, f64! 0.0⟩ else ⟨F64.nan, F64.nan⟩
    else finish (F64.pow (abs z) pr) (pr * angle z)
  else if z.im == f64! 0.0 then
    if z.re == f64! 0.0 then (if p.re > f64! 0.0 then z else ⟨F64.nan, F64.nan⟩)
    else
      let zr := z.re
      if zr > f64! 0.0 then finish (F64.pow zr p.re) (p.im * F64.log zr)
      else
        let r := -zr
        let θ := F64.copysign F64.pi z.im
        finish (F64.pow r p.re * F64.exp (-p.im * θ)) (p.re * θ + p.im * F64.log r)
  else
    let r := abs z
    let θ := angle z
    finish (F64.pow r p.re * F64.exp (-p.im * θ)) (p.re * θ + p.im * F64.log r)
where
  /-- `rᵖ · cis(ϕ)` with Julia's non-finite-phase handling. -/
  finish (rp ϕ : Float) : Complex Float :=
    if F64.isfinite ϕ then rp * cis ϕ
    else if rp == f64! 0.0 then ⟨f64! 0.0, f64! 0.0⟩ else ⟨F64.nan, F64.nan⟩

end ComplexF64

/-! ## `ComplexF32` -/

/-- Julia `ComplexF32 = Complex{Float32}` (complex.jl:39). -/
abbrev ComplexF32 : Type := Complex Float32

namespace ComplexF32

/-- Julia `/(z::ComplexF32, w::ComplexF32)` (complex.jl:369): widen both to `Float64`,
`mag = inv(muladd(c, c, d^2))`, then `muladd(a, c, b*d)*mag + muladd(b, c, -a*d)*mag·i`
rounded back to `Float32` (the `muladd`s are FMAs on the oracle machine). -/
def div (z w : Complex Float32) : Complex Float32 :=
  let a := z.re.toFloat
  let b := z.im.toFloat
  let c := w.re.toFloat
  let d := w.im.toFloat
  if F64.isinf c || F64.isinf d then
    if F32.isfinite z.re && F32.isfinite z.im then
      ⟨f32! 0.0 * F32.sign z.re * F32.sign w.re, (f32! -0.0) * F32.sign z.im * F32.sign w.im⟩
    else ⟨Float32.ofBits 0x7FC00000, Float32.ofBits 0x7FC00000⟩
  else
    let mag := f64! 1.0 / Float.fma c c (d * d)
    ⟨(Float.fma a c (b * d) * mag).toFloat32, (Float.fma b c (-(a * d)) * mag).toFloat32⟩

/-- `z / w` on `ComplexF32` is Julia's widened division. -/
instance : Div (Complex Float32) := ⟨div⟩

/-- Julia `inv(z::ComplexF32)` (complex.jl:466): widen to `Float64`,
`mag = inv(muladd(c, c, d^2))`, `Complex(c*mag, -d*mag)` rounded back. -/
def inv (w : Complex Float32) : Complex Float32 :=
  let c := w.re.toFloat
  let d := w.im.toFloat
  if F64.isinf c || F64.isinf d then
    ⟨F32.copysign (f32! 0.0) w.re, if F32.signbit w.im then f32! 0.0 else f32! -0.0⟩
  else
    let mag := f64! 1.0 / Float.fma c c (d * d)
    ⟨(c * mag).toFloat32, (-d * mag).toFloat32⟩

/-- `z⁻¹` on `ComplexF32` is Julia's widened inverse. -/
instance : Inv (Complex Float32) := ⟨inv⟩

end ComplexF32

end JuliaBase

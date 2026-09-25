import JuliaBase.Num

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
  Julia's `sqrt`, `exp`, `expm1`, `log`, `log1p`, the trigonometric and hyperbolic
  functions and their inverses, and `^` (`_cpow`), ported line by line from Julia 1.13.
  The arithmetic-only functions (`/`, `inv`, `abs`, `sqrt`) agree with the oracle bit for
  bit; the ones that call `libm` agree to within its tolerance (Julia uses its own
  `libm`).
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

/-- Julia `angle(z) = atan(im, re)` (complex.jl:641). -/
@[inline] def angle (z : Complex Float) : Float := Float.atan2 z.im z.re

/-- Julia `isfinite(z::Complex)`. -/
@[inline] def isFinite (z : Complex Float) : Bool := z.re.isFinite && z.im.isFinite

/-- Julia `isnan(z::Complex)`. -/
@[inline] def isNaN (z : Complex Float) : Bool := z.re.isNaN || z.im.isNaN

/-- Julia `cis(ϕ) = cos ϕ + i sin ϕ` (complex.jl:577). -/
@[inline] def cis (ϕ : Float) : Complex Float := ⟨Float.cos ϕ, Float.sin ϕ⟩

/-! ### Division and inverse -/

/-- Julia `robust_cdiv2` (complex.jl:457). -/
@[inline] def robustCdiv2 (a b c d r t : Float) : Float :=
  if r != 0 then
    let br := b * r
    if br != 0 then (a + br) * t else a * t + (b * t) * r
  else (a + d * (b / c)) * t

/-- Julia `robust_cdiv1` (complex.jl:450), times the unscaling factor `s`. -/
@[inline] def robustCdiv1 (a b c d s : Float) : Complex Float :=
  let r := d / c
  let t := 1.0 / (c + d * r)
  ⟨robustCdiv2 a b c d r t * s, robustCdiv2 b (-a) c d r t * s⟩

/-- Julia `cdiv` (complex.jl:425), times the unscaling factor `s` (`scaling_cdiv`,
complex.jl:432). -/
@[inline] def cdiv (a b c d s : Float) : Complex Float :=
  if d.abs ≤ c.abs then robustCdiv1 a b c d s
  else
    let r := c / d
    let t := 1.0 / (d + c * r)
    ⟨robustCdiv2 b a d c r t * s, -(robustCdiv2 a (-b) d c r t) * s⟩

/-- Julia's over/underflow threshold `0.5*floatmax(Float64)` (complex.jl:398). -/
def halfov : Float := 0.5 * F64.floatmax

/-- Julia's underflow threshold `floatmin(Float64)*2.0/eps(Float64)` (complex.jl:399). -/
def twounϵ : Float := F64.floatmin * 2.0 / F64.eps

/-- Julia's scale factor `2.0/(ϵ*ϵ)` (complex.jl:439). -/
def bs : Float := 2.0 / (F64.eps * F64.eps)

/-- The `c, d` half of `scaleargs_cdiv` (complex.jl:444-448), then `cdiv` and unscaling. -/
@[inline] def scaleCD (a b c d cd s : Float) : Complex Float :=
  if cd ≥ halfov then cdiv a b (c * 0.5) (d * 0.5) (s * 0.5)
  else if cd ≤ twounϵ then cdiv a b (c * bs) (d * bs) (s * bs)
  else cdiv a b c d s

/-- Julia `/(z::ComplexF64, w::ComplexF64)` (complex.jl:390-423): robust division with
over/underflow scaling (Baudin–Smith, arXiv:1210.4539). -/
def div (z w : Complex Float) : Complex Float :=
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
  if c.isInf || d.isInf then
    if isFinite z then ⟨0.0 * F64.sign a * F64.sign c, (-0.0) * F64.sign b * F64.sign d⟩
    else ⟨F64.nan, F64.nan⟩
  else if ab ≥ halfov || ab ≤ twounϵ || cd ≥ halfov || cd ≤ twounϵ then
    -- scaleargs_cdiv (complex.jl:436-449): `s` starts at 1.0
    if ab ≥ halfov then scaleCD (a * 0.5) (b * 0.5) c d cd 2.0
    else if ab ≤ twounϵ then scaleCD (a * bs) (b * bs) c d cd (1.0 / bs)
    else scaleCD a b c d cd 1.0
  else cdiv a b c d 1.0  -- the unscaled path; multiplying by 1.0 is exact

/-- `z / w` on `ComplexF64` is Julia's robust division. -/
instance : Div (Complex Float) := ⟨div⟩

/-- Julia `robust_cinv(c, d)` (complex.jl:503) as `(p, q)` scaled by `s`, written into the
real (`swap = false`) or swapped (`swap = true`, the `q, p = robust_cinv(-d, -c)` call)
slots. -/
@[inline] def robustCinv (c d s : Float) (swap : Bool) : Complex Float :=
  let r := d / c
  let z := Float.fma d r c
  let p := 1.0 / z
  let q := -r / z
  if swap then ⟨q * s, p * s⟩ else ⟨p * s, q * s⟩

/-- Julia `inv(w::ComplexF64)` (complex.jl:472-501): `conj(w)/muladd(cd, cd, dc²)` in the
safe range (the `muladd` is a hardware FMA on the oracle machine), and a scaled robust
inversion outside it. -/
def inv (w : Complex Float) : Complex Float :=
  let c := w.re
  let d := w.im
  let absc := c.abs
  let absd := d.abs
  let cd := if absc > absd then absc else absd
  let dc := if absc > absd then absd else absc
  if (F64.floatmin / 2).sqrt ≤ cd && cd ≤ (F64.floatmax / 2).sqrt then
    Complex.conj w / Float.fma cd cd (dc * dc)
  else if c.isInf || d.isInf then ⟨F64.copysign 0.0 c, F64.flipsign (-0.0) d⟩
  else
    let ϵ := F64.eps
    let bs := 2 / (ϵ * ϵ)
    let finish (c d s : Float) : Complex Float :=
      if absd ≤ absc then robustCinv c d s false else robustCinv (-d) (-c) s true
    if cd ≥ F64.floatmax / 2 then finish (c * 0.5) (d * 0.5) 0.5
    else if cd ≤ 2 * F64.floatmin / ϵ then finish (c * bs) (d * bs) bs
    else finish c d 1.0

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

/-- Julia `ssqs(x, y)` (complex.jl:509): `x² + y²` and a scaling exponent `k`, rescaled
when the sum over/underflows. -/
def ssqs (x y : Float) : Float × Int := Id.run do
  let mut k : Int := 0
  let mut ρ := x * x + y * y
  if !ρ.isFinite && (x.isInf || y.isInf) then
    ρ := F64.inf
  else if ρ.isInf || (ρ == 0 && (x != 0 || y != 0)) || ρ < 5e-324 / (2 * F64.eps * F64.eps) then
    let m := F64.max x.abs y.abs
    k := if m == 0 then 0 else F64.exponent m
    let xk := F64.ldexp x (-k)
    let yk := F64.ldexp y (-k)
    ρ := xk * xk + yk * yk
  return (ρ, k)

/-- Julia `sqrt(z::Complex)` (complex.jl:523), Kahan's algorithm without intermediate
over/underflow. -/
def sqrt (z : Complex Float) : Complex Float := Id.run do
  let x := z.re
  let y := z.im
  if x == 0 && y == 0 then return ⟨0, y⟩
  let (ρ0, k0) := ssqs x y
  let mut ρ := ρ0
  let mut k := k0
  if x.isFinite then ρ := F64.ldexp x.abs (-k) + Float.sqrt ρ
  if JInt.isodd k then
    k := (k - 1) / 2
  else
    k := k / 2 - 1
    ρ := ρ + ρ
  ρ := F64.ldexp (Float.sqrt ρ) k
  let mut ξ := ρ
  let mut η := y
  if ρ != 0 then
    if η.isFinite then η := (η / ρ) / 2
    if x < 0 then
      ξ := η.abs
      η := F64.copysign ρ y
  return ⟨ξ, η⟩

/-- Julia `log(z::Complex)` (complex.jl:643). -/
def log (z : Complex Float) : Complex Float :=
  let x := z.re
  let y := z.im
  let (ρ, k) := ssqs x y
  let ax := x.abs
  let ay := y.abs
  let (θ, β) := if ax < ay then (ax, ay) else (ay, ax)
  let ρρ :=
    if k == 0 && 0.5 < β * β && (β ≤ 1.25 || ρ < 3) then
      F64.log1p ((β - 1) * (β + 1) + θ * θ) / 2
    else Float.log ρ / 2 + Float.ofInt k * F64.ln2
  ⟨ρρ, angle z⟩

/-- Julia `exp(z::Complex)` (complex.jl:694). -/
def exp (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if zr.isNaN then ⟨zr, if zi == 0 then zi else zr⟩
  else if !zi.isFinite then
    if zr == F64.inf then ⟨-zr, F64.nan⟩
    else if zr == -F64.inf then ⟨-0.0, F64.copysign 0 zi⟩
    else ⟨F64.nan, F64.nan⟩
  else
    let er := Float.exp zr
    if zi == 0 then ⟨er, zi⟩
    else ⟨er * Float.cos zi, er * Float.sin zi⟩

/-- Julia `expm1(z::Complex)` (complex.jl:717). -/
def expm1 (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if zr.isNaN then ⟨zr, if zi == 0 then zi else zr⟩
  else if !zi.isFinite then
    if zr == F64.inf then ⟨-zr, F64.nan⟩
    else if zr == -F64.inf then ⟨-1, F64.copysign 0 zi⟩
    else ⟨F64.nan, F64.nan⟩
  else
    let erm1 := F64.expm1 zr
    if zi == 0 then ⟨erm1, zi⟩
    else
      let er := erm1 + 1
      if er.isFinite then
        let s := Float.sin (0.5 * zi)
        ⟨erm1 - 2 * er * (s * s), er * Float.sin zi⟩
      else ⟨er * Float.cos zi, er * Float.sin zi⟩

/-- Julia `log1p(z::Complex)` (complex.jl:747). -/
def log1p (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if zr.isFinite then
    if zi.isInf then log z
    else
      let u : Complex Float := (1.0 : Float) + z
      if u.re == 1 && u.im == 0 then z
      else if u.re ≤ 0 then log u
      else log u * div z (u - (1.0 : Float))
  else if zr.isNaN then ⟨zr, zr⟩
  else if zi.isFinite then ⟨F64.inf, F64.copysign (if zr > 0 then 0 else F64.pi) zi⟩
  else ⟨F64.inf, F64.nan⟩

/-! ### Trigonometric and hyperbolic functions -/

/-- Julia `sin(z::Complex)` (complex.jl:887); `sincos` is two `libm` calls. -/
def sin (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if zr == 0 then ⟨zr, Float.sinh zi⟩
  else if !zr.isFinite then
    if zi == 0 || zi.isInf then ⟨F64.nan, zi⟩ else ⟨F64.nan, F64.nan⟩
  else ⟨Float.sin zr * Float.cosh zi, Float.cos zr * Float.sinh zi⟩

/-- Julia `cos(z::Complex)` (complex.jl:905). -/
def cos (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if zr == 0 then ⟨Float.cosh zi, if zi.isNaN then zr else -(F64.flipsign zr zi)⟩
  else if !zr.isFinite then
    if zi == 0 then ⟨F64.nan, if zr.isNaN then 0 else -(F64.flipsign zi zr)⟩
    else if zi.isInf then ⟨F64.inf, F64.nan⟩
    else ⟨F64.nan, F64.nan⟩
  else ⟨Float.cos zr * Float.cosh zi, -(Float.sin zr) * Float.sinh zi⟩

/-- Julia `sinh(z) = i⁻¹ sin(iz)` computed by swapping parts (complex.jl:973). -/
def sinh (z : Complex Float) : Complex Float :=
  let w := sin ⟨z.im, z.re⟩
  ⟨w.im, w.re⟩

/-- Julia `cosh(z) = cos(iz)` (complex.jl:979). -/
def cosh (z : Complex Float) : Complex Float := cos ⟨z.im, -z.re⟩

/-- Julia `tanh(z::Complex)` (complex.jl:984), Kahan's overflow-free form. -/
def tanh (z : Complex Float) : Complex Float :=
  let ξ := z.re
  let η := z.im
  if ξ.isNaN && η == 0 then ⟨ξ, η⟩
  else if 4 * ξ.abs > Float.asinh F64.floatmax then
    ⟨F64.copysign 1 ξ, F64.copysign 0 (η * (if η.isFinite then Float.sin (2 * η.abs) else 1))⟩
  else
    let t := Float.tan η
    let β := 1 + t * t
    let s := Float.sinh ξ
    let ρ := Float.sqrt (1 + s * s)
    if t.isInf then ⟨ρ / s, 1 / t⟩
    else (⟨β * ρ * s, t⟩ : Complex Float) / (1 + β * s * s)

/-- Julia `tan(z) = -i tanh(iz)` (complex.jl:925). -/
def tan (z : Complex Float) : Complex Float :=
  let w := tanh ⟨-z.im, z.re⟩
  ⟨w.im, -w.re⟩

/-- Julia `asin(z::Complex)` (complex.jl:931), Kahan's branch-cut-exact form. -/
def asin (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if zr.isInf && zi.isInf then ⟨F64.copysign (F64.pi / 4) zr, zi⟩
  else if zi.isNaN && zr.isInf then ⟨zi, F64.inf⟩
  else
    let ξ :=
      if zr == 0 then zr
      else if !zr.isFinite then F64.pi / 2 * F64.sign zr
      else Float.atan2 zr (sqrt ((1.0 : Float) - z) * sqrt ((1.0 : Float) + z)).re
    let η := Float.asinh
      (F64.copysign (sqrt (Complex.conj ((1.0 : Float) - z)) * sqrt ((1.0 : Float) + z)).im zi)
    ⟨ξ, η⟩

/-- Julia `acos(z::Complex)` (complex.jl:945). -/
def acos (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if zr.isNaN then (if zi.isInf then ⟨zr, -zi⟩ else ⟨zr, zr⟩)
  else if zi.isNaN then
    if zr.isInf then ⟨zi, zr.abs⟩
    else if zr == 0 then ⟨F64.pi / 2, zi⟩
    else ⟨zi, zi⟩
  else if zr == 0 && zi == 0 then ⟨F64.pi / 2, -zi⟩
  else if zr == F64.inf && zi.toBits == (0.0 : Float).toBits then ⟨zi, -zr⟩
  else if zr == -F64.inf && zi.toBits == (-0.0 : Float).toBits then ⟨F64.pi, -zr⟩
  else
    let ξ := 2 * Float.atan2 (sqrt ((1.0 : Float) - z)).re (sqrt ((1.0 : Float) + z)).re
    let η := Float.asinh (sqrt (Complex.conj ((1.0 : Float) + z)) * sqrt ((1.0 : Float) - z)).im
    let ξ := if zr.isInf && zi.isInf then ξ - F64.pi / 4 * F64.sign zr else ξ
    ⟨ξ, η⟩

/-- Julia `asinh(z) = -i asin(iz)` by part swapping (complex.jl:1006). -/
def asinh (z : Complex Float) : Complex Float :=
  let w := asin ⟨-z.im, z.re⟩
  ⟨w.im, -w.re⟩

/-- Julia `acosh(z::Complex)` (complex.jl:1011). -/
def acosh (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if zr.isNaN || zi.isNaN then
    if zr.isInf || zi.isInf then ⟨F64.inf, F64.nan⟩ else ⟨F64.nan, F64.nan⟩
  else if zr == -F64.inf && zi.toBits == (-0.0 : Float).toBits then ⟨F64.inf, -F64.pi⟩
  else
    let ξ := Float.asinh (sqrt (Complex.conj (z - (1.0 : Float))) * sqrt (z + (1.0 : Float))).re
    let η := 2 * Float.atan2 (sqrt (z - (1.0 : Float))).im (sqrt (z + (1.0 : Float))).re
    let η := if zr.isInf && zi.isInf then η - F64.pi / 4 * F64.sign zi * F64.sign zr else η
    ⟨ξ, η⟩

/-- Julia `atanh(z::Complex)` (complex.jl:1030), Kahan's form. -/
def atanh (z : Complex Float) : Complex Float :=
  let x := z.re
  let y := z.im
  let ax := x.abs
  let ay := y.abs
  let θ := Float.sqrt F64.floatmax / 4
  if ax > θ || ay > θ then
    if y.isNaN then
      if x.isInf then ⟨F64.copysign 0 x, y⟩ else ⟨(inv z).re, y⟩
    else if y.isInf then ⟨F64.copysign 0 x, F64.copysign (F64.pi / 2) y⟩
    else ⟨(inv z).re, F64.copysign (F64.pi / 2) y⟩
  else
    let β := F64.copysign 1 x
    let z : Complex Float := β * z
    let x := z.re
    let y := z.im
    let (ξ, η) :=
      if x == 1 then
        if y == 0 then (F64.inf, y)
        else
          (Float.log (Float.sqrt (Float.sqrt (Float.fma y y 4)) / Float.sqrt ay),
            F64.copysign (F64.pi / 2 + Float.atan (ay / 2)) y / 2)
      else
        let ysq := ay * ay
        let ξ := if x == 0 then x else F64.log1p (4 * x / Float.fma (1 - x) (1 - x) ysq) / 4
        (ξ, angle ⟨(1 - x) * (1 + x) - ysq, 2 * y⟩ / 2)
    β * (⟨ξ, η⟩ : Complex Float)

/-- Julia `atan(z) = -i atanh(iz)` (complex.jl:968). -/
def atan (z : Complex Float) : Complex Float :=
  let w := atanh ⟨-z.im, z.re⟩
  ⟨w.im, -w.re⟩

/-! ### Powers -/

/-- Julia `_cpow(z, p)` (complex.jl:782): `z^p` for complex `z` and `p`. -/
def pow (z p : Complex Float) : Complex Float :=
  if p.im == 0 then
    let pr := p.re
    if pr == pr.floor && pr.abs < 2147483647 then
      if pr == 0 then ⟨1, F64.flipsign (F64.copysign 0 pr) z.im⟩
      else
        let ip : Int := if pr < 0 then -((-pr).toUInt64.toNat : Int) else (pr.toUInt64.toNat : Int)
        if z.im == 0 then
          let zr := z.re
          if ip < 0 && zr == 0 then ⟨F64.nan, F64.nan⟩
          else
            let (re, im) :=
              if ip < 0 then (powBySquaring (· * ·) 1 (1 / zr) ip.natAbs, -z.im)
              else (powBySquaring (· * ·) 1 zr ip.natAbs, z.im)
            ⟨re, if ip % 2 == 0 && F64.signbit zr then -im else im⟩
        else if ip < 0 then powBySquaring (· * ·) ⟨1, 0⟩ (inv z) ip.natAbs
        else powBySquaring (· * ·) ⟨1, 0⟩ z ip.natAbs
    else if z.im == 0 then
      let zr := z.re
      if zr == 0 then (if pr > 0 then z else ⟨F64.nan, F64.nan⟩)
      else if zr > 0 then ⟨Float.pow zr pr, F64.flipsign z.im pr⟩
      else
        let rp := Float.pow (-zr) pr
        if pr.isFinite then
          -- Julia uses `cospi`/`sinpi`; `cos(π p)`/`sin(π p)` here (≤ 1 ulp apart).
          rp * (⟨Float.cos (F64.pi * pr), F64.flipsign (Float.sin (F64.pi * pr)) z.im⟩ : Complex Float)
        else if rp == 0 then ⟨0, 0⟩ else ⟨F64.nan, F64.nan⟩
    else finish (Float.pow (abs z) pr) (pr * angle z)
  else if z.im == 0 then
    if z.re == 0 then (if p.re > 0 then z else ⟨F64.nan, F64.nan⟩)
    else
      let zr := z.re
      if zr > 0 then finish (Float.pow zr p.re) (p.im * Float.log zr)
      else
        let r := -zr
        let θ := F64.copysign F64.pi z.im
        finish (Float.pow r p.re * Float.exp (-p.im * θ)) (p.re * θ + p.im * Float.log r)
  else
    let r := abs z
    let θ := angle z
    finish (Float.pow r p.re * Float.exp (-p.im * θ)) (p.re * θ + p.im * Float.log r)
where
  /-- `rᵖ · cis(ϕ)` with Julia's non-finite-phase handling. -/
  finish (rp ϕ : Float) : Complex Float :=
    if ϕ.isFinite then rp * cis ϕ
    else if rp == 0 then ⟨0, 0⟩ else ⟨F64.nan, F64.nan⟩

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
  if c.isInf || d.isInf then
    if z.re.isFinite && z.im.isFinite then
      ⟨0 * F32.sign z.re * F32.sign w.re, -0.0 * F32.sign z.im * F32.sign w.im⟩
    else ⟨Float32.ofBits 0x7FC00000, Float32.ofBits 0x7FC00000⟩
  else
    let mag := 1 / Float.fma c c (d * d)
    ⟨(Float.fma a c (b * d) * mag).toFloat32, (Float.fma b c (-(a * d)) * mag).toFloat32⟩

/-- `z / w` on `ComplexF32` is Julia's widened division. -/
instance : Div (Complex Float32) := ⟨div⟩

/-- Julia `inv(z::ComplexF32)` (complex.jl:466): widen to `Float64`,
`mag = inv(muladd(c, c, d^2))`, `Complex(c*mag, -d*mag)` rounded back. -/
def inv (w : Complex Float32) : Complex Float32 :=
  let c := w.re.toFloat
  let d := w.im.toFloat
  if c.isInf || d.isInf then
    ⟨F32.copysign 0 w.re, if F32.signbit w.im then 0 else -0.0⟩
  else
    let mag := 1 / Float.fma c c (d * d)
    ⟨(c * mag).toFloat32, (-d * mag).toFloat32⟩

/-- `z⁻¹` on `ComplexF32` is Julia's widened inverse. -/
instance : Inv (Complex Float32) := ⟨inv⟩

end ComplexF32

end JuliaBase

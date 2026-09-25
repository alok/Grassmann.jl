import JuliaBase.Num

/-!
Julia's `Complex{T}` (Julia `base/complex.jl`): a computable complex number over any
coefficient type, with Julia's operation order for `+ - *`, `conj`, `abs2`, and the
`ComplexF64`-specific robust division and inverse (Baudin–Smith, complex.jl:390-510), so
results agree bit for bit with the oracle.

Lean core has no complex numbers and Mathlib's `Complex` sits on noncomputable `ℝ`; this
is the `Complex α` of DESIGN.md §4.1.
-/

universe u

namespace JuliaBase

/-- Julia `Complex{T}`: `re + im·i`. -/
structure Complex (α : Type u) where
  /-- real part -/
  re : α
  /-- imaginary part -/
  im : α
  deriving BEq, Repr, Inhabited, Hashable

namespace Complex

variable {α : Type u}

/-- Julia `complex(x)` for a real `x`: `x + 0im`. -/
@[inline] def ofReal [OfNat α 0] (x : α) : Complex α := ⟨x, 0⟩

/-- Julia `zero(Complex{T})` = `0 + 0im`. -/
instance [OfNat α 0] : OfNat (Complex α) 0 := ⟨⟨0, 0⟩⟩

/-- Julia `one(Complex{T})` = `1 + 0im`. -/
instance [OfNat α 0] [OfNat α 1] : OfNat (Complex α) 1 := ⟨⟨1, 0⟩⟩

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

/-- Julia `conj(z)` (complex.jl:276). -/
@[inline] def conj [Neg α] (z : Complex α) : Complex α := ⟨z.re, -z.im⟩

/-- Julia `abs2(z)` = `re² + im²` (complex.jl:278). -/
@[inline] def abs2 [Add α] [Mul α] (z : Complex α) : α := z.re * z.re + z.im * z.im

/-- Scalar multiplication `x * z` (Julia `*(x::Real, z::Complex)`). -/
@[inline] def smul [Mul α] (x : α) (z : Complex α) : Complex α := ⟨x * z.re, x * z.im⟩

end Complex

/-! ## `ComplexF64` -/

namespace ComplexF64

/-- Julia `abs(z::Complex)` = `hypot(re, im)` (complex.jl:277). -/
@[inline] def abs (z : Complex Float) : Float := F64.hypot z.re z.im

/-- Julia `isfinite(z::Complex)`. -/
@[inline] def isFinite (z : Complex Float) : Bool := z.re.isFinite && z.im.isFinite

/-- Julia `isnan(z::Complex)`. -/
@[inline] def isNaN (z : Complex Float) : Bool := z.re.isNaN || z.im.isNaN

/-- Julia `/(z::Complex, x::Real)` (complex.jl:348). -/
@[inline] def divReal (z : Complex Float) (x : Float) : Complex Float := ⟨z.re / x, z.im / x⟩

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
over/underflow scaling (arXiv:1210.4539). -/
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

/-- Julia `inv(w::ComplexF64)` (complex.jl:472-501). -/
def inv (w : Complex Float) : Complex Float :=
  let c := w.re
  let d := w.im
  let absc := c.abs
  let absd := d.abs
  let cd := if absc > absd then absc else absd
  let dc := if absc > absd then absd else absc
  if (F64.floatmin / 2).sqrt ≤ cd && cd ≤ (F64.floatmax / 2).sqrt then
    divReal (Complex.conj w) (Float.fma cd cd (dc * dc))
  else if c.isInf || d.isInf then ⟨F64.copysign 0.0 c, F64.flipsign (-0.0) d⟩
  else
    let ϵ := F64.eps
    let bs := 2 / (ϵ * ϵ)
    let finish (c d s : Float) : Complex Float :=
      if absd ≤ absc then robustCinv c d s false else robustCinv (-d) (-c) s true
    if cd ≥ F64.floatmax / 2 then finish (c * 0.5) (d * 0.5) 0.5
    else if cd ≤ 2 * F64.floatmin / ϵ then finish (c * bs) (d * bs) bs
    else finish c d 1.0

/-- Julia `isapprox(x::ComplexF64, y::ComplexF64; atol=0, rtol=√eps, nans=false)`
(floatfuncs.jl:222) with `norm = abs`. -/
def isapprox (x y : Complex Float) (atol : Float := 0)
    (rtol : Float := if atol > 0 then 0 else F64.rtoldefault) (nans : Bool := false) : Bool :=
  x == y ||
    (isFinite x && isFinite y && abs (x - y) ≤ F64.max atol (rtol * F64.max (abs x) (abs y))) ||
    (nans && isNaN x && isNaN y)

end ComplexF64

end JuliaBase

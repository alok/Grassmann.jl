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

instance [OfNat α 0] : OfNat (Complex α) 0 := ⟨⟨0, 0⟩⟩
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

/-- Julia `robust_cdiv1` (complex.jl:450). -/
@[inline] def robustCdiv1 (a b c d : Float) : Float × Float :=
  let r := d / c
  let t := 1.0 / (c + d * r)
  (robustCdiv2 a b c d r t, robustCdiv2 b (-a) c d r t)

/-- Julia `cdiv` (complex.jl:425). -/
@[inline] def cdiv (a b c d : Float) : Float × Float :=
  if d.abs ≤ c.abs then robustCdiv1 a b c d
  else
    let (p, q) := robustCdiv1 b a d c
    (p, -q)

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
  else
    let halfov := 0.5 * F64.floatmax
    let twounϵ := F64.floatmin * 2.0 / F64.eps
    if ab ≥ halfov || ab ≤ twounϵ || cd ≥ halfov || cd ≤ twounϵ then
      -- scaleargs_cdiv (complex.jl:436-449)
      let bs := 2.0 / (F64.eps * F64.eps)
      let (a, b, s) :=
        if ab ≥ halfov then (a * 0.5, b * 0.5, (2.0 : Float))
        else if ab ≤ twounϵ then (a * bs, b * bs, 1.0 / bs)
        else (a, b, (1.0 : Float))
      let (c, d, s) :=
        if cd ≥ halfov then (c * 0.5, d * 0.5, s * 0.5)
        else if cd ≤ twounϵ then (c * bs, d * bs, s * bs)
        else (c, d, s)
      let (p, q) := cdiv a b c d
      ⟨p * s, q * s⟩
    else
      let (p, q) := cdiv a b c d
      ⟨p, q⟩

instance : Div (Complex Float) := ⟨div⟩

/-- Julia `robust_cinv` (complex.jl:503). -/
@[inline] def robustCinv (c d : Float) : Float × Float :=
  let r := d / c
  let z := Float.fma d r c
  (1.0 / z, -r / z)

/-- Julia `inv(w::ComplexF64)` (complex.jl:472-501). -/
def inv (w : Complex Float) : Complex Float :=
  let c := w.re
  let d := w.im
  let absc := c.abs
  let absd := d.abs
  let (cd, dc) := if absc > absd then (absc, absd) else (absd, absc)
  if (F64.floatmin / 2).sqrt ≤ cd && cd ≤ (F64.floatmax / 2).sqrt then
    divReal (Complex.conj w) (Float.fma cd cd (dc * dc))
  else if c.isInf || d.isInf then ⟨F64.copysign 0.0 c, F64.flipsign (-0.0) d⟩
  else
    let ϵ := F64.eps
    let bs := 2 / (ϵ * ϵ)
    let (c, d, s) :=
      if cd ≥ F64.floatmax / 2 then (c * 0.5, d * 0.5, (0.5 : Float))
      else if cd ≤ 2 * F64.floatmin / ϵ then (c * bs, d * bs, bs)
      else (c, d, (1.0 : Float))
    if absd ≤ absc then
      let (p, q) := robustCinv c d
      ⟨p * s, q * s⟩
    else
      let (q, p) := robustCinv (-d) (-c)
      ⟨p * s, q * s⟩

/-- Julia `isapprox(x::ComplexF64, y::ComplexF64; atol=0, rtol=√eps, nans=false)`
(floatfuncs.jl:222) with `norm = abs`. -/
def isapprox (x y : Complex Float) (atol : Float := 0)
    (rtol : Float := if atol > 0 then 0 else F64.rtoldefault) (nans : Bool := false) : Bool :=
  x == y ||
    (isFinite x && isFinite y && abs (x - y) ≤ F64.max atol (rtol * F64.max (abs x) (abs y))) ||
    (nans && isNaN x && isNaN y)

end ComplexF64

end JuliaBase

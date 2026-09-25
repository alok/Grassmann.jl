/-
A computable complex number type (Julia `Complex{T}`, `base/complex.jl`).

Lean core has no complex numbers, and Mathlib's `Complex` is built on the
noncomputable reals, so the port carries its own `Complex α`. The generic
algebra (`+ - *`, conjugation, real scaling) works for any coefficient type;
`Complex Float` additionally gets Julia's floating-point algorithms for
`inv`, `/` (Baudin–Smith robust division), `abs` (`hypot`), `sqrt`, `exp`,
`log`, the trigonometric and hyperbolic functions and `^`, ported line by line
from Julia 1.13 so that results agree bitwise for the arithmetic-only ones
and to within the libm tolerance for the rest.

Mixed real/complex operations follow Julia, which does **not** promote the
real operand: `x + z = Complex(x + re, im)` and `x * z = Complex(x*re, x*im)`.
Numeric literals do embed as complex numbers (`(2 : Complex Float) = ⟨2, 0⟩`),
so write `(2.0 : Float) * z` to get Julia's `2.0 * z` exactly.
-/
import JuliaBase.Num
import StaticVectors.Scalar

universe u

namespace AbstractTensors

open StaticVectors

/-- A complex number `re + im·i` with components in `α` (Julia `Complex{α}`). -/
structure Complex (α : Type u) where
  /-- Real part (Julia `real(z)`). -/
  re : α
  /-- Imaginary part (Julia `imag(z)`). -/
  im : α
  deriving Repr, BEq, Hashable, Inhabited, DecidableEq

namespace Complex

variable {α : Type u}

/-- Embed a real number (Julia `Complex(x)`). -/
@[inline] def ofReal [OfNat α 0] (x : α) : Complex α := ⟨x, 0⟩

/-- Julia `im`. -/
@[inline] def I [OfNat α 0] [OfNat α 1] : Complex α := ⟨0, 1⟩

instance {n : Nat} [OfNat α n] [OfNat α 0] : OfNat (Complex α) n := ⟨⟨OfNat.ofNat n, 0⟩⟩
instance [OfScientific α] [OfNat α 0] : OfScientific (Complex α) :=
  ⟨fun m s e => ⟨OfScientific.ofScientific m s e, 0⟩⟩

/-! ## Ring operations (`base/complex.jl:276-336`) -/

/-- Julia `z + w`. -/
instance [Add α] : Add (Complex α) := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
/-- Julia `z - w`. -/
instance [Sub α] : Sub (Complex α) := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
/-- Julia `-z`. -/
instance [Neg α] : Neg (Complex α) := ⟨fun z => ⟨-z.re, -z.im⟩⟩
/-- Julia `z * w = Complex(re·re' - im·im', re·im' + im·re')` (`complex.jl:290`). -/
instance [Add α] [Sub α] [Mul α] : Mul (Complex α) :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

/-- Julia `x * z = Complex(x·re, x·im)` for real `x` (`complex.jl:335`). -/
instance [Mul α] : HMul α (Complex α) (Complex α) := ⟨fun x z => ⟨x * z.re, x * z.im⟩⟩
/-- Julia `z * x = Complex(x·re, x·im)` for real `x` (`complex.jl:336`). -/
instance [Mul α] : HMul (Complex α) α (Complex α) := ⟨fun z x => ⟨x * z.re, x * z.im⟩⟩
/-- Julia `z / x = Complex(re/x, im/x)` for real `x` (`complex.jl:348`). -/
instance [Div α] : HDiv (Complex α) α (Complex α) := ⟨fun z x => ⟨z.re / x, z.im / x⟩⟩
/-- Julia `x + z = Complex(x + re, im)` (`complex.jl:327`). -/
instance [Add α] : HAdd α (Complex α) (Complex α) := ⟨fun x z => ⟨x + z.re, z.im⟩⟩
/-- Julia `z + x = Complex(x + re, im)` (`complex.jl:328`). -/
instance [Add α] : HAdd (Complex α) α (Complex α) := ⟨fun z x => ⟨x + z.re, z.im⟩⟩
/-- Julia `x - z = Complex(x - re, -im)` (`complex.jl:329`). -/
instance [Sub α] [Neg α] : HSub α (Complex α) (Complex α) := ⟨fun x z => ⟨x - z.re, -z.im⟩⟩
/-- Julia `z - x = Complex(re - x, im)` (`complex.jl:334`). -/
instance [Sub α] : HSub (Complex α) α (Complex α) := ⟨fun z x => ⟨z.re - x, z.im⟩⟩

/-- Julia `conj(z)`. -/
instance [Neg α] : Conj (Complex α) := ⟨fun z => ⟨z.re, -z.im⟩⟩

/-- Julia `abs2(z) = re·re + im·im` (`complex.jl:278`). -/
@[inline] def abs2 [Add α] [Mul α] (z : Complex α) : α := z.re * z.re + z.im * z.im

/-- Julia `/` on complex numbers of an exact field (`Rat`): the textbook
formula, exact there. `Complex Float` uses the robust algorithm below. -/
instance (priority := low) instDivGeneric [Add α] [Sub α] [Mul α] [Div α] : Div (Complex α) :=
  ⟨fun z w =>
    let d := w.re * w.re + w.im * w.im
    ⟨(z.re * w.re + z.im * w.im) / d, (z.im * w.re - z.re * w.im) / d⟩⟩

/-- Julia `inv(z) = conj(z) / abs2(z)` on an exact field. -/
instance (priority := low) instInvGeneric [Add α] [Mul α] [Neg α] [Div α] : Inv (Complex α) :=
  ⟨fun z => let d := z.re * z.re + z.im * z.im; ⟨z.re / d, -z.im / d⟩⟩

/-! ## `Complex Float`: Julia's floating-point algorithms -/

section FloatAlgorithms

open JuliaBase

/-- Julia `abs(z) = hypot(re, im)` (`complex.jl:277`). -/
@[inline] def abs (z : Complex Float) : Float := F64.hypot z.re z.im

/-- Julia `angle(z) = atan(im, re)` (`complex.jl:641`). -/
@[inline] def angle (z : Complex Float) : Float := Float.atan2 z.im z.re

/-- Julia `robust_cinv` (`complex.jl:501`). -/
@[inline] private def robustCinv (c d : Float) : Float × Float :=
  let r := d / c
  let z := Float.fma d r c
  (1.0 / z, -r / z)

/-- Julia `inv(w::ComplexF64)` (`complex.jl:472`): `conj(w)/muladd(cd,cd,dc²)`
in the safe range (the `muladd` is a hardware FMA on Apple Silicon), and a
scaled robust inversion outside it. -/
def inv (w : Complex Float) : Complex Float := Id.run do
  let mut c := w.re
  let mut d := w.im
  let absc := c.abs
  let absd := d.abs
  let (cd, dc) := if absc > absd then (absc, absd) else (absd, absc)
  if Float.sqrt (F64.floatmin / 2) ≤ cd && cd ≤ Float.sqrt (F64.floatmax / 2) then
    let m := Float.fma cd cd (dc * dc)
    return ⟨c / m, -d / m⟩
  if c.isInf || d.isInf then return ⟨F64.copysign 0 c, F64.flipsign (-0.0) d⟩
  let ϵ := F64.eps
  let bs := 2 / (ϵ * ϵ)
  let mut s := 1.0
  if cd ≥ F64.floatmax / 2 then
    c := c * 0.5; d := d * 0.5; s := 0.5
  else if cd ≤ 2 * F64.floatmin / ϵ then
    c := c * bs; d := d * bs; s := bs
  if absd ≤ absc then
    let (p, q) := robustCinv c d
    return ⟨p * s, q * s⟩
  else
    let (q, p) := robustCinv (-d) (-c)
    return ⟨p * s, q * s⟩

/-- Julia `robust_cdiv2` (`complex.jl:457`). -/
@[inline] private def robustCdiv2 (a b c d r t : Float) : Float :=
  if r != 0 then
    let br := b * r
    if br != 0 then (a + br) * t else a * t + (b * t) * r
  else (a + d * (b / c)) * t

/-- Julia `robust_cdiv1` (`complex.jl:450`). -/
@[inline] private def robustCdiv1 (a b c d : Float) : Float × Float :=
  let r := d / c
  let t := 1.0 / (c + d * r)
  (robustCdiv2 a b c d r t, robustCdiv2 b (-a) c d r t)

/-- Julia `cdiv` (`complex.jl:414`). -/
@[inline] private def cdiv (a b c d : Float) : Float × Float :=
  if d.abs ≤ c.abs then robustCdiv1 a b c d
  else let (p, q) := robustCdiv1 b a d c; (p, -q)

/-- Julia `/(z::ComplexF64, w::ComplexF64)` (`complex.jl:390`, Baudin–Smith,
arXiv:1210.4539), with the over/underflow rescaling of `scaleargs_cdiv`. -/
def div (z w : Complex Float) : Complex Float := Id.run do
  let a := z.re; let b := z.im; let c := w.re; let d := w.im
  let absa := a.abs; let absb := b.abs
  let ab := if absa ≥ absb then absa else absb
  let absc := c.abs; let absd := d.abs
  let cd := if absc ≥ absd then absc else absd
  if c.isInf || d.isInf then
    if a.isFinite && b.isFinite then
      return ⟨0.0 * F64.sign a * F64.sign c, -0.0 * F64.sign b * F64.sign d⟩
    return ⟨Float.nan, Float.nan⟩
  let halfov := 0.5 * F64.floatmax
  let twounϵ := F64.floatmin * 2.0 / F64.eps
  if ab ≥ halfov || ab ≤ twounϵ || cd ≥ halfov || cd ≤ twounϵ then
    -- `scaling_cdiv` / `scaleargs_cdiv` (`complex.jl:423-449`)
    let bs := 2.0 / (F64.eps * F64.eps)
    let mut a := a; let mut b := b; let mut c := c; let mut d := d
    let mut s := 1.0
    if ab ≥ halfov then
      a := a * 0.5; b := b * 0.5; s := s * 2.0
    else if ab ≤ twounϵ then
      a := a * bs; b := b * bs; s := s / bs
    if cd ≥ halfov then
      c := c * 0.5; d := d * 0.5; s := s * 0.5
    else if cd ≤ twounϵ then
      c := c * bs; d := d * bs; s := s * bs
    let (p, q) := cdiv a b c d
    return ⟨p * s, q * s⟩
  let (p, q) := cdiv a b c d
  return ⟨p, q⟩

instance : Inv (Complex Float) := ⟨inv⟩
instance : Div (Complex Float) := ⟨div⟩

/-- Julia `ssqs(x, y)` (`complex.jl:509`): `x² + y²` and a scaling exponent
`k`, rescaled when the sum over/underflows. -/
def ssqs (x y : Float) : Float × Int := Id.run do
  let mut k : Int := 0
  let mut ρ := x * x + y * y
  if !ρ.isFinite && (x.isInf || y.isInf) then
    ρ := Float.inf
  else if ρ.isInf || (ρ == 0 && (x != 0 || y != 0)) || ρ < 5e-324 / (2 * F64.eps * F64.eps) then
    let m := F64.max x.abs y.abs
    k := if m == 0 then 0 else F64.exponent m
    let xk := F64.ldexp x (-k)
    let yk := F64.ldexp y (-k)
    ρ := xk * xk + yk * yk
  return (ρ, k)

/-- Julia `sqrt(z::Complex)` (`complex.jl:523`), Kahan's algorithm without
intermediate over/underflow. -/
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

/-- Julia `log(z::Complex)` (`complex.jl:643`). -/
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

/-- Julia `exp(z::Complex)` (`complex.jl:694`). -/
def exp (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if zr.isNaN then ⟨zr, if zi == 0 then zi else zr⟩
  else if !zi.isFinite then
    if zr == Float.inf then ⟨-zr, Float.nan⟩
    else if zr == -Float.inf then ⟨-0.0, F64.copysign 0 zi⟩
    else ⟨Float.nan, Float.nan⟩
  else
    let er := Float.exp zr
    if zi == 0 then ⟨er, zi⟩
    else ⟨er * Float.cos zi, er * Float.sin zi⟩

/-- Julia `expm1(z::Complex)` (`complex.jl:717`). -/
def expm1 (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if zr.isNaN then ⟨zr, if zi == 0 then zi else zr⟩
  else if !zi.isFinite then
    if zr == Float.inf then ⟨-zr, Float.nan⟩
    else if zr == -Float.inf then ⟨-1, F64.copysign 0 zi⟩
    else ⟨Float.nan, Float.nan⟩
  else
    let erm1 := F64.expm1 zr
    if zi == 0 then ⟨erm1, zi⟩
    else
      let er := erm1 + 1
      if er.isFinite then
        let s := Float.sin (0.5 * zi)
        ⟨erm1 - 2 * er * (s * s), er * Float.sin zi⟩
      else ⟨er * Float.cos zi, er * Float.sin zi⟩

/-- Julia `log1p(z::Complex)` (`complex.jl:747`). -/
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
  else if zi.isFinite then ⟨Float.inf, F64.copysign (if zr > 0 then 0 else F64.pi) zi⟩
  else ⟨Float.inf, Float.nan⟩

/-- Julia `sin(z::Complex)` (`complex.jl:887`); `sincos` is two libm calls. -/
def sin (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if zr == 0 then ⟨zr, Float.sinh zi⟩
  else if !zr.isFinite then
    if zi == 0 || zi.isInf then ⟨Float.nan, zi⟩ else ⟨Float.nan, Float.nan⟩
  else ⟨Float.sin zr * Float.cosh zi, Float.cos zr * Float.sinh zi⟩

/-- Julia `cos(z::Complex)` (`complex.jl:905`). -/
def cos (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if zr == 0 then ⟨Float.cosh zi, if zi.isNaN then zr else -(F64.flipsign zr zi)⟩
  else if !zr.isFinite then
    if zi == 0 then ⟨Float.nan, if zr.isNaN then 0 else -(F64.flipsign zi zr)⟩
    else if zi.isInf then ⟨Float.inf, Float.nan⟩
    else ⟨Float.nan, Float.nan⟩
  else ⟨Float.cos zr * Float.cosh zi, -(Float.sin zr) * Float.sinh zi⟩

/-- Julia `sinh(z) = i⁻¹ sin(iz)` computed by swapping parts (`complex.jl:973`). -/
def sinh (z : Complex Float) : Complex Float :=
  let w := sin ⟨z.im, z.re⟩
  ⟨w.im, w.re⟩

/-- Julia `cosh(z) = cos(iz)` (`complex.jl:979`). -/
def cosh (z : Complex Float) : Complex Float := cos ⟨z.im, -z.re⟩

/-- Julia `tanh(z::Complex)` (`complex.jl:984`), Kahan's overflow-free form. -/
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

/-- Julia `tan(z) = -i tanh(iz)` (`complex.jl:925`). -/
def tan (z : Complex Float) : Complex Float :=
  let w := tanh ⟨-z.im, z.re⟩
  ⟨w.im, -w.re⟩

/-- Julia `asin(z::Complex)` (`complex.jl:931`), Kahan's branch-cut-exact form. -/
def asin (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if zr.isInf && zi.isInf then ⟨F64.copysign (F64.pi / 4) zr, zi⟩
  else if zi.isNaN && zr.isInf then ⟨zi, Float.inf⟩
  else
    let ξ :=
      if zr == 0 then zr
      else if !zr.isFinite then F64.pi / 2 * F64.sign zr
      else Float.atan2 zr (sqrt ((1.0 : Float) - z) * sqrt ((1.0 : Float) + z)).re
    let η := Float.asinh (F64.copysign (sqrt (conj ((1.0 : Float) - z)) * sqrt ((1.0 : Float) + z)).im zi)
    ⟨ξ, η⟩

/-- Julia `acos(z::Complex)` (`complex.jl:945`). -/
def acos (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if zr.isNaN then (if zi.isInf then ⟨zr, -zi⟩ else ⟨zr, zr⟩)
  else if zi.isNaN then
    if zr.isInf then ⟨zi, zr.abs⟩
    else if zr == 0 then ⟨F64.pi / 2, zi⟩
    else ⟨zi, zi⟩
  else if zr == 0 && zi == 0 then ⟨F64.pi / 2, -zi⟩
  else if zr == Float.inf && zi.toBits == (0.0 : Float).toBits then ⟨zi, -zr⟩
  else if zr == -Float.inf && zi.toBits == (-0.0 : Float).toBits then ⟨F64.pi, -zr⟩
  else
    let ξ := 2 * Float.atan2 (sqrt ((1.0 : Float) - z)).re (sqrt ((1.0 : Float) + z)).re
    let η := Float.asinh (sqrt (conj ((1.0 : Float) + z)) * sqrt ((1.0 : Float) - z)).im
    let ξ := if zr.isInf && zi.isInf then ξ - F64.pi / 4 * F64.sign zr else ξ
    ⟨ξ, η⟩

/-- Julia `asinh(z) = -i asin(iz)` by part swapping (`complex.jl:1006`). -/
def asinh (z : Complex Float) : Complex Float :=
  let w := asin ⟨-z.im, z.re⟩
  ⟨w.im, -w.re⟩

/-- Julia `acosh(z::Complex)` (`complex.jl:1011`). -/
def acosh (z : Complex Float) : Complex Float :=
  let zr := z.re
  let zi := z.im
  if zr.isNaN || zi.isNaN then
    if zr.isInf || zi.isInf then ⟨Float.inf, Float.nan⟩ else ⟨Float.nan, Float.nan⟩
  else if zr == -Float.inf && zi.toBits == (-0.0 : Float).toBits then ⟨Float.inf, -F64.pi⟩
  else
    let ξ := Float.asinh (sqrt (conj (z - (1.0 : Float))) * sqrt (z + (1.0 : Float))).re
    let η := 2 * Float.atan2 (sqrt (z - (1.0 : Float))).im (sqrt (z + (1.0 : Float))).re
    let η := if zr.isInf && zi.isInf then η - F64.pi / 4 * F64.sign zi * F64.sign zr else η
    ⟨ξ, η⟩

/-- Julia `atanh(z::Complex)` (`complex.jl:1030`), Kahan's form. -/
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
        if y == 0 then (Float.inf, y)
        else
          (Float.log (Float.sqrt (Float.sqrt (Float.fma y y 4)) / Float.sqrt ay),
            F64.copysign (F64.pi / 2 + Float.atan (ay / 2)) y / 2)
      else
        let ysq := ay * ay
        let ξ := if x == 0 then x else F64.log1p (4 * x / Float.fma (1 - x) (1 - x) ysq) / 4
        (ξ, angle ⟨(1 - x) * (1 + x) - ysq, 2 * y⟩ / 2)
    β * (⟨ξ, η⟩ : Complex Float)

/-- Julia `atan(z) = -i atanh(iz)` (`complex.jl:968`). -/
def atan (z : Complex Float) : Complex Float :=
  let w := atanh ⟨-z.im, z.re⟩
  ⟨w.im, -w.re⟩

/-- Julia `cis(ϕ) = cos ϕ + i sin ϕ`. -/
@[inline] def cis (ϕ : Float) : Complex Float := ⟨Float.cos ϕ, Float.sin ϕ⟩

/-- Julia `Base.power_by_squaring(x, p)` (`base/intfuncs.jl`): the exact
multiplication order Julia uses for `x^p` with an integer `p ≥ 0`, generic in
the multiplication. -/
def powBySquaring {β : Type} (mul : β → β → β) (one x : β) (p : Nat) : β :=
  if p == 0 then one
  else if p == 1 then x
  else if p == 2 then mul x x
  else
    let t := trailingZeros p + 1
    let p := p >>> t
    let x := square x (t - 1)
    loop x x p (p + 1)
where
  /-- Number of trailing zero bits of a positive `n` (`0` for `n = 0`). -/
  trailingZeros (n : Nat) : Nat := tz n 64
  /-- Fuelled trailing-zero count. -/
  tz : Nat → Nat → Nat
    | _, 0 => 0
    | m, fuel + 1 => if m % 2 == 1 || m == 0 then 0 else tz (m / 2) fuel + 1
  /-- `x^(2^k)` by repeated squaring. -/
  square (x : β) : Nat → β
    | 0 => x
    | k + 1 => square (mul x x) k
  /-- The main loop of `power_by_squaring` (the fuel bounds the bit count). -/
  loop (x y : β) (p : Nat) : Nat → β
    | 0 => y
    | fuel + 1 =>
      if p == 0 then y
      else
        let t := trailingZeros p + 1
        let p := p >>> t
        let x := square x t
        loop x (mul y x) p fuel

/-- Julia `_cpow(z, p)` (`complex.jl:782`): `z^p` for complex `z` and `p`. -/
def pow (z p : Complex Float) : Complex Float :=
  if p.im == 0 then
    let pr := p.re
    if pr == pr.floor && pr.abs < 2147483647 then
      if pr == 0 then ⟨1, F64.flipsign (F64.copysign 0 pr) z.im⟩
      else
        let ip : Int := if pr < 0 then -((-pr).toUInt64.toNat : Int) else (pr.toUInt64.toNat : Int)
        if z.im == 0 then
          let zr := z.re
          if ip < 0 && zr == 0 then ⟨Float.nan, Float.nan⟩
          else
            let (re, im) :=
              if ip < 0 then (powBySquaring (· * ·) 1 (1 / zr) ip.natAbs, -z.im)
              else (powBySquaring (· * ·) 1 zr ip.natAbs, z.im)
            ⟨re, if ip % 2 == 0 && F64.signbit zr then -im else im⟩
        else if ip < 0 then powBySquaring (· * ·) ⟨1, 0⟩ (inv z) ip.natAbs
        else powBySquaring (· * ·) ⟨1, 0⟩ z ip.natAbs
    else if z.im == 0 then
      let zr := z.re
      if zr == 0 then (if pr > 0 then z else ⟨Float.nan, Float.nan⟩)
      else if zr > 0 then ⟨Float.pow zr pr, F64.flipsign z.im pr⟩
      else
        let rp := Float.pow (-zr) pr
        if pr.isFinite then
          -- Julia uses `cospi`/`sinpi`; `cos(π p)`/`sin(π p)` here (≤ 1 ulp apart).
          rp * (⟨Float.cos (F64.pi * pr), F64.flipsign (Float.sin (F64.pi * pr)) z.im⟩ : Complex Float)
        else if rp == 0 then ⟨0, 0⟩ else ⟨Float.nan, Float.nan⟩
    else finish (Float.pow (abs z) pr) (pr * angle z)
  else if z.im == 0 then
    if z.re == 0 then (if p.re > 0 then z else ⟨Float.nan, Float.nan⟩)
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
    else if rp == 0 then ⟨0, 0⟩ else ⟨Float.nan, Float.nan⟩

/-- Julia `cbrt` has no complex method; this is the principal cube root
`z^(1/3)` (Julia `z^(1/3)`). -/
@[inline] def cbrt (z : Complex Float) : Complex Float := pow z ⟨1 / 3, 0⟩

/-- Complex two-argument arctangent, `-i log((x + iy)/√(x² + y²))`. Julia has
no complex `atan(y, x)`; for real arguments this is `atan2(y, x)` up to
rounding. -/
def atan2 (y x : Complex Float) : Complex Float :=
  let w := x + (⟨0, 1⟩ : Complex Float) * y
  let l := log (div w (sqrt (x * x + y * y)))
  ⟨l.im, -l.re⟩

end FloatAlgorithms

/-- Julia `norm`/`abs2` for complex entries: `abs2 = re² + im²`, `norm = hypot`. -/
instance : JNorm (Complex Float) := ⟨fun z => z.abs2, abs⟩

/-- Julia `isapprox(z, w)` on complex numbers: `|z - w| ≤ max(atol, rtol·max(|z|, |w|))`
with `|·| = abs = hypot` (`base/floatfuncs.jl:222`). -/
instance : JApprox (Complex Float) where
  rtolDefault := JuliaBase.F64.rtoldefault
  isapprox z w atol rtol nans :=
    (z.re == w.re && z.im == w.im) ||
      (z.re.isFinite && z.im.isFinite && w.re.isFinite && w.im.isFinite &&
        abs (z - w) ≤ JuliaBase.F64.max atol (rtol * JuliaBase.F64.max (abs z) (abs w))) ||
      (nans && (z.re.isNaN || z.im.isNaN) && (w.re.isNaN || w.im.isNaN))

end Complex

end AbstractTensors

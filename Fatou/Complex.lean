import JuliaBase

/-!
# `ComplexF64` arithmetic with Julia's semantics

Fatou.jl compiles its maps (`z^2 + c`, Newton maps from REDUCE, the colouring `C`) into
ordinary Julia functions, so a pixel's iteration count depends on the exact rounding of
Julia's `Complex{Float64}` operations. This module collects those operations, each one a
transliteration of `base/complex.jl` (Julia 1.13), so that maps written with them reproduce
the oracle bit for bit:

* `+ - *` and the robust (Baudin–Smith) `/` and `inv` come from `JuliaBase.Complex`;
* mixed real/complex arithmetic (`x + z`, `x * z`, `z / x`, `x / z`, …) as the `HAdd`,
  `HSub`, `HMul`, `HDiv` instances below (complex.jl:317-331, 347-348). These are **not** the
  same as promoting the real to `x + 0im` first: the signs of zero differ, and the angle
  colouring (`atan(imag, real)`) sees the difference;
* integer powers with the lowering Julia applies to literal exponents (`literal_pow`,
  intfuncs.jl:465-487) and `power_by_squaring` (intfuncs.jl:394-438);
* `abs` (correctly rounded `hypot`), `abs2`, `angle`, `exp`, `sin`, `cos`, `sinh`, `cosh`,
  `log`, `sqrt` (complex.jl:523-714, 887-981). The real kernels they call (`sin`, `cosh`,
  `atan2`, …) are the platform libm's, which may differ from Julia's own implementations in
  the last bit; tests put these in a tolerance tier.

Everything is `@[inline]` so that a map written as a lambda over `C64` specializes into the
escape-time kernel with its `Complex` constructors cancelled (no allocation per iteration).
-/

namespace Fatou

open JuliaBase

/-- Julia `ComplexF64` = `Complex{Float64}`: the number type of every Fatou grid and orbit. -/
abbrev C64 := JuliaBase.Complex Float

/-- `log1p` from the C math library (Julia's `log1p` is an openlibm port; they agree to
within an ulp). Lean core does not bind it. -/
@[extern "log1p"] opaque log1pF (x : Float) : Float

namespace C64

/-- The complex number `re + im·i`. -/
@[inline] def mk' (re im : Float) : C64 := ⟨re, im⟩

/-- Julia `complex(x)`: `x + 0im`. -/
@[inline] def ofReal (x : Float) : C64 := ⟨x, 0⟩

/-- Julia `im` as a `ComplexF64`, `0.0 + 1.0im`. -/
def I : C64 := ⟨0, 1⟩

/-- Julia `x + z` and `z + x` for real `x` (complex.jl:317-318): `Complex(x + real(z), imag(z))`. -/
@[inline] def addReal (z : C64) (x : Float) : C64 := ⟨x + z.re, z.im⟩

/-- Julia `z - x` for real `x` (complex.jl:324): `Complex(real(z) - x, imag(z))`. -/
@[inline] def subReal (z : C64) (x : Float) : C64 := ⟨z.re - x, z.im⟩

/-- Julia `x - z` for real `x` (complex.jl:319-323): `Complex(x - real(z), -imag(z))`. -/
@[inline] def realSub (x : Float) (z : C64) : C64 := ⟨x - z.re, -z.im⟩

/-- Julia `x * z` and `z * x` for real `x` (complex.jl:325-326): `Complex(x*real(z), x*imag(z))`. -/
@[inline] def scale (x : Float) (z : C64) : C64 := ⟨x * z.re, x * z.im⟩

/-- Julia `z / x` for real `x` (complex.jl:348): `Complex(real(z)/x, imag(z)/x)`. -/
@[inline] def divReal (z : C64) (x : Float) : C64 := ⟨z.re / x, z.im / x⟩

/-! ### Division

Decimal constants live in top-level definitions: a decimal literal inlined into a specialized
kernel can survive as a runtime `Float.ofScientific` call (big-number arithmetic on every
iteration), while a top-level `Float` is a plain global. Integer literals (`Float.ofNat`) are
cheap and stay inline. -/

/-- `0.5`. -/
def fHalf : Float := 0.5
/-- `1.0`. -/
def fOne : Float := 1.0
/-- `2.0`. -/
def fTwo : Float := 2.0
/-- `0.0`. -/
def fZero : Float := 0.0
/-- `-0.0`. -/
def fNegZero : Float := -0.0
/-- `1.25`. -/
def f125 : Float := 1.25

/-- Julia `robust_cdiv2` (complex.jl:457). -/
@[inline] def robustCdiv2 (a b c d r t : Float) : Float :=
  if r != 0 then
    let br := b * r
    if br != 0 then (a + br) * t else a * t + (b * t) * r
  else (a + d * (b / c)) * t

/-- Julia `robust_cdiv1` (complex.jl:450), times the unscaling factor `s`. -/
@[inline] def robustCdiv1 (a b c d s : Float) : C64 :=
  let r := d / c
  let t := fOne / (c + d * r)
  ⟨robustCdiv2 a b c d r t * s, robustCdiv2 b (-a) c d r t * s⟩

/-- Julia `cdiv` (complex.jl:425) times the unscaling factor `s`: the swapped case computes
`robust_cdiv1(b, a, d, c)` and negates the imaginary part. -/
@[inline] def cdiv (a b c d s : Float) : C64 :=
  if d.abs ≤ c.abs then robustCdiv1 a b c d s
  else
    let r := c / d
    let t := fOne / (d + c * r)
    ⟨robustCdiv2 b a d c r t * s, -(robustCdiv2 a (-b) d c r t) * s⟩

/-- The `c, d` half of Julia `scaleargs_cdiv` (complex.jl:444-448), then `cdiv`. -/
@[inline] def scaleCD (a b c d cd s : Float) : C64 :=
  if cd ≥ ComplexF64.halfov then cdiv a b (c * fHalf) (d * fHalf) (s * fHalf)
  else if cd ≤ ComplexF64.twounϵ then cdiv a b (c * ComplexF64.bs) (d * ComplexF64.bs) (s * ComplexF64.bs)
  else cdiv a b c d s

/-- Julia `/(z::ComplexF64, w::ComplexF64)` (complex.jl:390-423), the robust Baudin–Smith
division with over/underflow scaling: `JuliaBase.ComplexF64.div`, restated with hoisted
constants and `@[inline]` throughout so a map's division specializes into the kernel without
boxing (the oracle tests check the two agree bit for bit). -/
@[inline] def div (z w : C64) : C64 :=
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
    if a.isFinite && b.isFinite then ⟨fZero * F64.sign a * F64.sign c, fNegZero * F64.sign b * F64.sign d⟩
    else ⟨F64.nan, F64.nan⟩
  else if ab ≥ ComplexF64.halfov || ab ≤ ComplexF64.twounϵ || cd ≥ ComplexF64.halfov ||
      cd ≤ ComplexF64.twounϵ then
    if ab ≥ ComplexF64.halfov then scaleCD (a * fHalf) (b * fHalf) c d cd fTwo
    else if ab ≤ ComplexF64.twounϵ then
      scaleCD (a * ComplexF64.bs) (b * ComplexF64.bs) c d cd (fOne / ComplexF64.bs)
    else scaleCD a b c d cd fOne
  else cdiv a b c d fOne

/-- `z / w` for `ComplexF64` is Julia's robust division, inlined (`C64.div`). -/
instance (priority := high) : Div C64 := ⟨div⟩

/-- Julia `inv(w::ComplexF64)` (complex.jl:472-501), the robust inverse; the algorithm of
`JuliaBase.ComplexF64.inv`, inlined. -/
@[inline] def inv (w : C64) : C64 :=
  let c := w.re
  let d := w.im
  let absc := c.abs
  let absd := d.abs
  let cd := if absc > absd then absc else absd
  let dc := if absc > absd then absd else absc
  if (F64.floatmin / 2).sqrt ≤ cd && cd ≤ (F64.floatmax / 2).sqrt then
    divReal ⟨c, -d⟩ (Float.fma cd cd (dc * dc))
  else if c.isInf || d.isInf then ⟨F64.copysign 0 c, F64.flipsign fNegZero d⟩
  else ComplexF64.inv w

/-- Julia `x / z` for real `x` (complex.jl:347): `x * inv(z)`. -/
@[inline] def realDiv (x : Float) (z : C64) : C64 := scale x (inv z)

/-- `z + x` for a real `x`, as Julia computes it. -/
instance : HAdd C64 Float C64 := ⟨addReal⟩
/-- `x + z` for a real `x`, as Julia computes it. -/
instance : HAdd Float C64 C64 := ⟨fun x z => addReal z x⟩
/-- `z - x` for a real `x`, as Julia computes it. -/
instance : HSub C64 Float C64 := ⟨subReal⟩
/-- `x - z` for a real `x`, as Julia computes it. -/
instance : HSub Float C64 C64 := ⟨realSub⟩
/-- `x * z` for a real `x`, as Julia computes it. -/
instance : HMul Float C64 C64 := ⟨scale⟩
/-- `z * x` for a real `x`, as Julia computes it. -/
instance : HMul C64 Float C64 := ⟨fun z x => scale x z⟩
/-- `z / x` for a real `x`, as Julia computes it. -/
instance : HDiv C64 Float C64 := ⟨divReal⟩
/-- `x / z` for a real `x`, as Julia computes it. -/
instance : HDiv Float C64 C64 := ⟨realDiv⟩

/-- Julia `abs2(z)` = `re² + im²` (complex.jl:278). -/
@[inline] def abs2 (z : C64) : Float := z.re * z.re + z.im * z.im

/-- Julia `abs(z)` = `hypot(re, im)` (complex.jl:277), correctly rounded. -/
@[inline] def abs (z : C64) : Float := F64.hypot z.re z.im

/-- Julia `angle(z)` = `atan(imag(z), real(z))` (complex.jl:641), in `[-π, π]`. -/
@[inline] def angle (z : C64) : Float := F64.atan2 z.im z.re

/-- Julia `conj(z)`. -/
@[inline] def conj (z : C64) : C64 := ⟨z.re, -z.im⟩

/-- Julia `isnan(z)`. -/
@[inline] def isNaN (z : C64) : Bool := z.re.isNaN || z.im.isNaN

/-- Julia `isfinite(z)`. -/
@[inline] def isFinite (z : C64) : Bool := z.re.isFinite && z.im.isFinite

/-! ## Integer powers -/

/-- The trailing-zero count of a positive natural number (`trailing_zeros`). -/
def trailingZeros (p : Nat) : Nat :=
  go 64 p 0
where
  /-- count low zero bits, at most `fuel` of them -/
  go : Nat → Nat → Nat → Nat
    | 0, _, k => k
    | fuel + 1, p, k => if p % 2 == 0 && p != 0 then go fuel (p / 2) (k + 1) else k

/-- `x` squared `t` times (`while (t -= 1) > 0; x = x*x; end` with the counter already
decremented). -/
def squareTimes : Nat → C64 → C64
  | 0, x => x
  | t + 1, x => squareTimes t (x * x)

/-- The main loop of `power_by_squaring` (intfuncs.jl:429-436): consume the bits of `p`,
squaring `x` and multiplying it into `y`. `fuel` bounds the number of rounds. -/
def powLoop : Nat → Nat → C64 → C64 → C64
  | 0, _, _, y => y
  | fuel + 1, p, x, y =>
    if p == 0 then y
    else
      let t := trailingZeros p + 1
      let x := squareTimes t x
      powLoop fuel (p >>> t) x (y * x)

/-- Julia `power_by_squaring(z, p)` for `p ≥ 0` (intfuncs.jl:394-438), with the same order of
multiplications (so the result matches the oracle bit for bit). -/
def powBySquaring (z : C64) (p : Nat) : C64 :=
  if p == 1 then z
  else if p == 0 then ⟨1, 0⟩
  else if p == 2 then z * z
  else
    let t := trailingZeros p + 1
    let p' := p >>> t
    -- `square_is_useful`: the first squaring reuses `z*z`
    let x := if t - 1 > 0 then squareTimes (t - 2) (z * z) else z
    powLoop 64 p' x x

/-- Julia `z^n` for a *literal* natural exponent `n` on a `ComplexF64`: Julia lowers it to
`Base.literal_pow(^, z, Val(n))` (intfuncs.jl:465-487), which is `1`, `z`, `z*z`, `z*z*z`
for `n = 0, 1, 2, 3` and `power_by_squaring(z, n)` beyond. Inlined, so a literal exponent
folds to the multiplication chain. -/
@[inline] def natPow (z : C64) (n : Nat) : C64 :=
  if n == 0 then ⟨1, 0⟩
  else if n == 1 then z
  else if n == 2 then z * z
  else if n == 3 then z * z * z
  else powBySquaring z n

/-- Julia `z^n` for a *literal* integer exponent `n` (intfuncs.jl:465-487): `natPow` for
`n ≥ 0`, `inv(z)` and `inv(z)*inv(z)` for `n = -1, -2`, and `power_by_squaring(inv(z), -n)`
below. -/
@[inline] def literalPow (z : C64) (n : Int) : C64 :=
  match n with
  | .ofNat k => natPow z k
  | .negSucc 0 => inv z
  | .negSucc 1 => let i := inv z; i * i
  | .negSucc k => powBySquaring (inv z) (k + 1)

/-- Julia `z^n` for a runtime (non-literal) integer `n` (complex.jl:873-875):
`n ≥ 0 ? power_by_squaring(z, n) : power_by_squaring(inv(z), -n)`. -/
def powInt (z : C64) (n : Int) : C64 :=
  match n with
  | .ofNat k => powBySquaring z k
  | .negSucc k => powBySquaring (inv z) (k + 1)

/-- `z ^ n` with a natural exponent means Julia's *literal* power `z^n` (the form in every
Fatou map written as an expression, e.g. `z^3 - 1`). Given as `NatPow` so that `z ^ 2` has a
known type early and mixes with real operands (`z ^ 2 - (0.06 : Float)`). -/
instance : NatPow C64 := ⟨natPow⟩

/-- `z ^ n` with an integer exponent means Julia's literal power `z^n`. -/
instance : HPow C64 Int C64 := ⟨literalPow⟩

/-- Julia `z ^ p` for a complex exponent: `_cpow` (complex.jl:782, 864), e.g. the wiki map
`z^(4.0+3.0im) - 1`. -/
instance : HPow C64 C64 C64 := ⟨JuliaBase.ComplexF64.pow⟩

/-- Julia `z ^ p` for a real exponent that is not an integer literal (complex.jl:865, 878:
`_cpow(z, Float64(p))`). Natural-number literals keep the literal power (`NatPow`). -/
instance : HPow C64 Float C64 := ⟨fun z p => JuliaBase.ComplexF64.pow z ⟨p, 0⟩⟩

/-! ## Elementary functions (complex.jl) -/

/-- Julia `exp(z::Complex)` (complex.jl:694-714). -/
@[inline] def exp (z : C64) : C64 :=
  let zr := z.re
  let zi := z.im
  if zr.isNaN then ⟨zr, if zi == 0 then zi else zr⟩
  else if !zi.isFinite then
    if zr == F64.inf then ⟨-zr, F64.nan⟩
    else if zr == -F64.inf then ⟨fNegZero, F64.copysign 0 zi⟩
    else ⟨F64.nan, F64.nan⟩
  else
    let er := zr.exp
    if zi == 0 then ⟨er, zi⟩ else ⟨er * zi.cos, er * zi.sin⟩

/-- Julia `sin(z::Complex)` (complex.jl:887-903). -/
@[inline] def sin (z : C64) : C64 :=
  let zr := z.re
  let zi := z.im
  if zr == 0 then ⟨zr, zi.sinh⟩
  else if !zr.isFinite then
    if zi == 0 || zi.isInf then ⟨F64.nan, zi⟩ else ⟨F64.nan, F64.nan⟩
  else ⟨zr.sin * zi.cosh, zr.cos * zi.sinh⟩

/-- Julia `cos(z::Complex)` (complex.jl:905-923). -/
@[inline] def cos (z : C64) : C64 :=
  let zr := z.re
  let zi := z.im
  if zr == 0 then ⟨zi.cosh, if zi.isNaN then zr else -(F64.flipsign zr zi)⟩
  else if !zr.isFinite then
    if zi == 0 then ⟨F64.nan, if zr.isNaN then 0 else -(F64.flipsign zi zr)⟩
    else if zi.isInf then ⟨F64.inf, F64.nan⟩
    else ⟨F64.nan, F64.nan⟩
  else ⟨zr.cos * zi.cosh, -zr.sin * zi.sinh⟩

/-- Julia `sinh(z::Complex)` (complex.jl:973-977): `sin(zi + zr·i)` with the parts swapped. -/
@[inline] def sinh (z : C64) : C64 :=
  let w := sin ⟨z.im, z.re⟩
  ⟨w.im, w.re⟩

/-- Julia `cosh(z::Complex)` (complex.jl:979-982): `cos(zi - zr·i)`. -/
@[inline] def cosh (z : C64) : C64 := cos ⟨z.im, -z.re⟩

/-- Julia `tan(z::Complex)` via `tanh`, simplified to `sin(z)/cos(z)` (tolerance tier only). -/
@[inline] def tan (z : C64) : C64 := div (sin z) (cos z)

/-- `x · 2^k` (Julia `ldexp`), exact including subnormal results. -/
@[inline] def ldexp (x : Float) (k : Int) : Float := Float.scaleB x k

/-- Julia `exponent(x)` for a finite nonzero `x`: the unbiased binary exponent `⌊log₂|x|⌋`. -/
def exponent (x : Float) : Int := (Float.frExp x).2 - 1

/-- Julia `ssqs(x, y)` (complex.jl:509-521): `x² + y²` rescaled by `2^(-2k)` to avoid over-
and underflow, with the exponent `k`. -/
def ssqs (x y : Float) : Float × Int :=
  let ρ := x * x + y * y
  if !ρ.isFinite && (x.isInf || y.isInf) then (F64.inf, 0)
  else if ρ.isInf || (ρ == 0 && (x != 0 || y != 0)) ||
      ρ < F64.nextfloat 0 / (2 * F64.eps * F64.eps) then
    let m := F64.max x.abs y.abs
    let k : Int := if m == 0 then 0 else exponent m
    let xk := ldexp x (-k)
    let yk := ldexp y (-k)
    (xk * xk + yk * yk, k)
  else (ρ, 0)

/-- Julia `sqrt(z::Complex)` (complex.jl:523-546). -/
def sqrt (z : C64) : C64 :=
  let x := z.re
  let y := z.im
  if x == 0 && y == 0 then ⟨0, y⟩
  else
    let (ρ, k) := ssqs x y
    let ρ := if x.isFinite then ldexp x.abs (-k) + ρ.sqrt else ρ
    let (ρ, k) := if k % 2 == 1 || k % 2 == -1 then (ρ, (k - 1) / 2) else (ρ + ρ, k / 2 - 1)
    let ρ := ldexp ρ.sqrt k
    if ρ != 0 then
      let η := if y.isFinite then (y / ρ) / 2 else y
      if x < 0 then ⟨η.abs, F64.copysign ρ y⟩ else ⟨ρ, η⟩
    else ⟨ρ, y⟩

/-- Julia `log(z::Complex)` (complex.jl:643-662). -/
def log (z : C64) : C64 :=
  let x := z.re
  let y := z.im
  let (ρ, k) := ssqs x y
  let ax := x.abs
  let ay := y.abs
  let (θ, β) := if ax < ay then (ax, ay) else (ay, ax)
  let ln2 : Float := (2 : Float).log
  let ρρ :=
    if k == 0 && fHalf < β * β && (β ≤ f125 || ρ < 3) then log1pF ((β - 1) * (β + 1) + θ * θ) / 2
    else ρ.log / 2 + Float.ofInt k * ln2
  ⟨ρρ, angle z⟩

/-! ## Poincaré maps (Fatou `src/Fatou.jl:337-338`) -/

/-- Julia `false * x` for a float `x` (bool.jl): `copysign(0, x)`. `im * x` is
`Complex(false * x, true * x)`, so this is the real part of `im * x`. -/
@[inline] def falseTimes (x : Float) : Float := F64.copysign 0 x

/-- Fatou `plane(z)` (`src/Fatou.jl:337`), the Möbius map `(z + i)/(1 + iz)` from the unit
disk to the upper half-plane, evaluated exactly as Julia parses
`(2z.re/(z.re^2+(1-z.im)^2)) + im*(1-z.re^2-z.im^2)/(z.re^2+(1-z.im)^2)`. -/
@[inline] def plane (z : C64) : C64 :=
  let x := z.re
  let y := z.im
  let d := x * x + (1 - y) * (1 - y)
  let a := (2 * x) / d
  let num := 1 - x * x - y * y
  -- `im*num` = `Complex(false*num, num)`, then `/ d`, then `a + ·`
  ⟨a + falseTimes num / d, num / d⟩

/-- Fatou `disk(z)` (`src/Fatou.jl:338`), the inverse Möbius map `(z - i)/(1 - iz)` from the
upper half-plane to the unit disk, evaluated as Julia parses
`(2z.re/(z.re^2+(1+z.im)^2)) + im*(z.re^2+z.im^2-1)/(z.re^2+(1+z.im)^2)`. -/
@[inline] def disk (z : C64) : C64 :=
  let x := z.re
  let y := z.im
  let d := x * x + (1 + y) * (1 + y)
  let a := (2 * x) / d
  let num := x * x + y * y - 1
  ⟨a + falseTimes num / d, num / d⟩

end C64

end Fatou

/-
Scalar `Float` functions that Lean core lacks and Julia's `Base` provides.

Lean's `Float` calls the platform C `libm`; Julia uses its own pure-Julia
`libm`. Both are faithful to within an ulp or two, which is the tolerance the
oracle tests use for transcendental functions (arithmetic `+ - * / sqrt fma`
is correctly rounded on both sides and compared bitwise).

`expm1` and `log1p` are missing from Lean core. They are computed here in pure
Lean with Kahan's compensation tricks (a C shim would need lakefile changes,
and `@[extern]` symbols do not run in the interpreter), accurate to a few
ulps.
-/
import StaticVectors.Julia

namespace AbstractTensors.FloatExt

open StaticVectors

/-- `π` rounded to `Float64` (Julia `Float64(π)`). -/
def pi : Float := 3.141592653589793
/-- `log(2)` rounded to `Float64` (Julia `log(2.0)`, `0x3FE62E42FEFA39EF`). -/
def ln2 : Float := 0.6931471805599453
/-- `log(10)` rounded to `Float64`. -/
def ln10 : Float := 2.302585092994046
/-- `log2(ℯ)` rounded to `Float64` (Julia `log2(ℯ)`). -/
def log2e : Float := 1.4426950408889634
/-- `log10(ℯ)` rounded to `Float64` (Julia `log10(ℯ)`). -/
def log10e : Float := 0.4342944819032518

/-- Julia `expm1(x)` = `eˣ - 1`, accurate near `0`.

Kahan's trick: with `u = exp x` (rounded), `(u - 1)·x / log u` cancels the
rounding error of `u`. Exact special cases: `expm1(±0) = ±0`,
`expm1(-Inf) = -1`, `expm1(Inf) = Inf`, NaN propagates. -/
def expm1 (x : Float) : Float :=
  let u := Float.exp x
  if u == 1 then x
  else if u.isInf then u
  else
    let um1 := u - 1
    if um1 == -1 then -1 else um1 * (x / Float.log u)

/-- Julia `log1p(x)` = `log(1 + x)`, accurate near `0`.

Goldberg's trick: with `u = 1 + x` (rounded), `log(u)·x / (u - 1)` cancels the
rounding error of `u`. Exact special cases: `log1p(±0) = ±0`,
`log1p(-1) = -Inf`, `log1p(Inf) = Inf`; NaN and `x < -1` give NaN (Julia
throws a `DomainError` for `x < -1`). -/
def log1p (x : Float) : Float :=
  let u := 1 + x
  if u == 1 then x
  else if u.isInf then (if x > 0 then u else Float.nan)
  else if u == 0 then -Float.inf
  else Float.log u * (x / (u - 1))

/-- Julia `sign(x)` for floats: `±1.0`, `±0.0` for zeros, NaN for NaN. -/
@[inline] def sign (x : Float) : Float :=
  if x > 0 then 1 else if x < 0 then -1 else x

/-- Julia `exponent(x)`: the unbiased binary exponent `⌊log₂|x|⌋` of a finite
nonzero `x` (also for subnormals). -/
@[inline] def exponent (x : Float) : Int := x.frExp.2 - 1

/-- Julia `ldexp(x, k)` = `x · 2ᵏ`. -/
@[inline] def ldexp (x : Float) (k : Int) : Float := x.scaleB k

/-- Julia `atanh(x)` via libm. -/
@[inline] def atanh (x : Float) : Float := Float.atanh x

/-- Julia `isodd(k)`. -/
@[inline] def isOdd (k : Int) : Bool := k % 2 != 0

/-- `Float32` versions via `Float` (then rounded): Julia's `expm1(::Float32)`. -/
@[inline] def expm1F32 (x : Float32) : Float32 := (expm1 x.toFloat).toFloat32

/-- Julia's `log1p(::Float32)` (computed in `Float` then rounded). -/
@[inline] def log1pF32 (x : Float32) : Float32 := (log1p x.toFloat).toFloat32

/-- Kept for callers that want the Julia name. -/
@[inline] def hypot (x y : Float) : Float := Julia.hypot x y

end AbstractTensors.FloatExt

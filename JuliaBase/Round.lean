import JuliaBase.Math

/-!
# Julia `round(x; digits)` / `round(x; sigdigits)` for `Float64`

`base/floatfuncs.jl:40-150` with `RoundNearest` and base 10: scale by a power of ten computed
with Julia's own `^` (`JuliaBase.Math`), round half to even, unscale. `Base.hidigit` uses
Julia's own `log10`.
-/

namespace JuliaBase

namespace F64

/-- Julia `_round_digits(x, RoundNearest, d, 10)` (floatfuncs.jl:112-126) for finite `x`: round
to a multiple of `10^-d` through `invstep = 10.0^d` (`_round_invstep`), `10.0^(d/2)` twice when
`10.0^d` overflows (`_round_invstepsqrt`), or `step = 10.0^-d` for `d < 0` (`_round_step`).
An overflowing result falls back to `x` (`invstep`) or to a signed zero (`step`), as in
Julia. -/
def roundDigitsFinite (x : Float) (d : Int) : Float :=
  if d ≥ 0 then
    let invstep := powInt (f64! 10.0) d
    if invstep.isFinite then
      let y := round (x * invstep) / invstep
      if y.isFinite then y else x
    else
      let invstepsqrt := pow (f64! 10.0) (Float.ofInt d / f64! 2.0)
      let y := round ((x * invstepsqrt) * invstepsqrt) / invstepsqrt / invstepsqrt
      if y.isFinite then y else x
  else
    let step := powInt (f64! 10.0) (-d)
    let y := round (x / step) * step
    if y.isFinite then y
    else if x > 0 then f64! 0.0
    else if x < 0 then f64! -0.0
    else x

/-- Julia `round(x::Float64, digits = d)` (floatfuncs.jl:48): `x` itself if it is not
finite. -/
def roundDigits (x : Float) (d : Int) : Float :=
  if x.isFinite then roundDigitsFinite x d else x

/-- Julia `Base.hidigit(x::AbstractFloat, 10) = 1 + floor(Int, log10(abs(x)))`
(floatfuncs.jl:129), the decimal exponent of the leading digit plus one, with Julia's own
`log10`; `0` for `x = 0` (and, where Julia throws, for `±Inf` and `NaN`). -/
def hidigit (x : Float) : Int :=
  if x == f64! 0.0 || !x.isFinite then 0
  else 1 + toIntTrunc (log10 x.abs).floor

/-- Julia `round(x::Float64, sigdigits = n)` (floatfuncs.jl:141): round to `n - hidigit(x)`
decimal digits. -/
def roundSigdigits (x : Float) (n : Int) : Float :=
  if x.isFinite then roundDigitsFinite x (n - hidigit x) else x

end F64

end JuliaBase

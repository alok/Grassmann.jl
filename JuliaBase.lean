import JuliaBase.Num
import JuliaBase.IEEE
import JuliaBase.Ryu
import JuliaBase.Float
import JuliaBase.Complex
import JuliaBase.Show
import JuliaBase.Range

/-!
# JuliaBase

Exact ports of the Julia `Base` behaviour the rest of the port prints and compares with,
verified bit for bit against the Julia 1.13 oracle (`Tests/JuliaBase/`).

* `JuliaBase.Num`: `F64`/`F32`/`JInt` namespaces with Julia `rem`, `mod`, `div`, `fld`,
  `cld`, NaN-propagating `max`/`min` with `-0.0 < 0.0`, `isapprox` (default
  `rtol = √eps` when `atol = 0`), `round` (half to even), `sign`, `copysign`, `flipsign`,
  `nextfloat`/`prevfloat`, `isless`/`isequal`, `hypot`, Julia's own `cbrt`,
  `Float64(::Rational)`, `exponent`/`ldexp`, `expm1`/`log1p` (to a few ulps), the float
  constants, `isodd`, `power_by_squaring`, and the oracle comparator `F64.ulpDist`. This is
  the one home of Julia's scalar semantics: `StaticVectors` and `AbstractTensors` build on
  it rather than keeping copies.
* `JuliaBase.IEEE`: the exact, format-generic IEEE-754 toolkit (`IEEEFloat` over `Float` and
  `Float32`): exact decoding (`decode`, `toRat?`), correctly rounded conversion from dyadic,
  rational and decimal values (`ofDyadic`, `ofFraction`, `ofRat`, `ofDecimal`), the constants
  and neighbours of either format, Julia `exponent`, `eps(x)` (`F64.epsOf`, `F32.epsOf`) and
  `ulpDistance`.
* `JuliaBase.Ryu`: Ryu shortest round-trip digits (`reduce_shortest`) for `Float64` and
  `Float32`, including the compact 6-significant-digit reduction.
* `JuliaBase.Float`: `writeShortest` (Julia `Ryu.writeshortest` with all its keyword options),
  `F64.showString`/`showCompact`, `F32.showString`/`showCompact`/`printString`.
* `JuliaBase.Complex`: Julia `Complex{T}`, the port's only complex type (the `Coeff`
  and `Analytic` instances are in `AbstractTensors`, the `Conj`/`JNorm`/`JApprox` ones in
  `StaticVectors`), with Julia's operation order and mixed real/complex rules, and
  `ComplexF64`'s robust division and inverse, `abs`, `isapprox`, `sqrt`, `exp`, `log`,
  the trigonometric and hyperbolic functions and `^`.
* `JuliaBase.Show`: the `JuliaShow` class (`show`/`print`, compact or not, plus the
  Leibniz `showvalue` and Grassmann `showterm` coefficient hooks) with instances for `Int`,
  `Nat`, `Bool`, `Float`, `Float32`, `Rat`, unsigned integers and `Complex α`.
* `JuliaBase.Range`: `LinRange`, and `range(start, stop; length)` / `start:step:stop` /
  `range(start; step, length)` as Julia's `TwicePrecision` `StepRangeLen` (plus the
  `Float32` variants and the range scalar/broadcast arithmetic).
-/

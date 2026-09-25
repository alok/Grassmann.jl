import JuliaBase.Num
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
  `nextfloat`/`prevfloat`, `hypot` and Julia's own `cbrt`.
* `JuliaBase.Ryu`: Ryu shortest round-trip digits (`reduce_shortest`) for `Float64` and
  `Float32`, including the compact 6-significant-digit reduction.
* `JuliaBase.Float`: `writeShortest` (Julia `Ryu.writeshortest` with all its keyword options),
  `F64.showString`/`showCompact`, `F32.showString`/`showCompact`/`printString`.
* `JuliaBase.Complex`: Julia `Complex{T}` with Julia's operation order and the robust
  `ComplexF64` division and inverse.
* `JuliaBase.Show`: the `JuliaShow` class (`show`/`print`, compact or not, plus the
  Leibniz `showvalue` and Grassmann `showterm` coefficient hooks) with instances for `Int`,
  `Nat`, `Bool`, `Float`, `Float32`, `Rat`, unsigned integers and `Complex α`.
* `JuliaBase.Range`: `LinRange`, and `range(start, stop; length)` / `start:step:stop` /
  `range(start; step, length)` as Julia's `TwicePrecision` `StepRangeLen` (plus the
  `Float32` variants and the range scalar/broadcast arithmetic).
-/

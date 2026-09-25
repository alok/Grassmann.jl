import FieldConstants.Julia.Float
import FieldConstants.JNum
import FieldConstants.Num

/-!
# FieldConstants

Lean port of `chakravala/FieldConstants.jl` (v0.1.1): numerical field constants
whose Julia payload lives in a type parameter (`Constant{N}`), plus the Julia
numeric semantics every downstream unit-system package relies on:

* `FieldConstants.Julia.parseFloat`: correctly rounded decimal parsing (printing,
  `rem`, `round` and `isapprox` come from `JuliaBase`);
* Julia's own `Base.Math` kernels (`exp`/`log`/`pow`/`powInt`, `round(digits/sigdigits)`)
  come from `JuliaBase.Math` and `JuliaBase.Round` (`JuliaBase.F64.exp`, …);
* `FieldConstants.JNum`: `Int64`/`Float64` payloads with Julia promotion,
  wrapping and `literal_pow` rules, and `logdb`/`expdb`/`dB`.

See `docs/port-notes/unitsystems.md` §2.1 for the Julia API inventory.
-/

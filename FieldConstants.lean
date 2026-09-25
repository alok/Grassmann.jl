import FieldConstants.JNum
import FieldConstants.Num

/-!
# FieldConstants

Lean port of `chakravala/FieldConstants.jl` (v0.1.1): numerical field constants
whose Julia payload lives in a type parameter (`Constant{N}`), plus the Julia
numeric semantics every downstream unit-system package relies on:

* Julia's float printing, parsing (`JuliaBase.F64.parse?`), `rem`, `round`, `isapprox` and
  its own `Base.Math` kernels (`exp`/`log`/`pow`/`powInt`, `round(digits/sigdigits)`) all
  come from `JuliaBase` (`JuliaBase.F64.exp`, …);
* `FieldConstants.JNum`: `Int64`/`Float64` payloads with Julia promotion,
  wrapping and `literal_pow` rules, and `logdb`/`expdb`/`dB`.

See `docs/port-notes/unitsystems.md` §2.1 for the Julia API inventory.
-/

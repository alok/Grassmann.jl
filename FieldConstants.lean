import FieldConstants.Julia.Float
import FieldConstants.Julia.Tables
import FieldConstants.Julia.Math
import FieldConstants.JNum
import FieldConstants.Num

/-!
# FieldConstants

Lean port of `chakravala/FieldConstants.jl` (v0.1.1): numerical field constants
whose Julia payload lives in a type parameter (`Constant{N}`), plus the Julia
numeric semantics every downstream unit-system package relies on:

* `FieldConstants.Julia.showFloat`: Julia's shortest round-trip `Float64` printing;
* `FieldConstants.Julia.parseFloat`: correctly rounded decimal parsing;
* `FieldConstants.Julia.exp`/`log`/`pow`/`powInt`: bit-exact ports of Julia's own
  `Base.Math` kernels (Julia does not use libm for these);
* `FieldConstants.JNum`: `Int64`/`Float64` payloads with Julia promotion,
  wrapping and `literal_pow` rules, and `logdb`/`expdb`/`dB`.

See `docs/port-notes/unitsystems.md` §2.1 for the Julia API inventory.
-/

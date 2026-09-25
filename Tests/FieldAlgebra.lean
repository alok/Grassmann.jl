import Tests.FieldAlgebra.Harness
import Tests.FieldAlgebra.FieldConstants

/-!
# FieldAlgebra (and FieldConstants) test aggregator

`Tests.FieldAlgebra.run` returns `(passed, failed)` over all FieldConstants and
FieldAlgebra golden checks.
-/

namespace Tests.FieldAlgebra

/-- Run the FieldConstants and FieldAlgebra suites; returns `(passed, failed)`. -/
def run : IO (Nat × Nat) := do
  IO.println "FieldAlgebra / FieldConstants"
  let s ← FieldConstantsTests.run
  s.report

end Tests.FieldAlgebra

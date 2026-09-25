import Tests.FieldAlgebra.Harness
import Tests.FieldAlgebra.FieldConstants
import Tests.FieldAlgebra.Groups
import Tests.FieldAlgebra.Rings

/-!
# FieldAlgebra (and FieldConstants) test aggregator

`Tests.FieldAlgebra.run` returns `(passed, failed)` over all FieldConstants and
FieldAlgebra golden checks.
-/

namespace Tests.FieldAlgebra

/-- Run the FieldConstants and FieldAlgebra suites; returns `(passed, failed)`. -/
def run : IO (Nat × Nat) := do
  IO.println "FieldAlgebra / FieldConstants"
  let (p1, f1) ← (← FieldConstantsTests.run).report
  let (p2, f2) ← (← GroupTests.run).report
  let (p3, f3) ← (← RingTests.run).report
  return (p1 + p2 + p3, f1 + f2 + f3)

end Tests.FieldAlgebra

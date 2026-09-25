import Tests.Similitude.Constants
import Tests.Similitude.Homs
import Tests.Similitude.Ratios
import Tests.Similitude.Quantities

/-!
# Similitude test aggregator

`Tests.Similitude.run` returns `(passed, failed)` over all Similitude golden
checks (`oracle/golden/similitude/`).
-/

namespace Tests.Similitude

open Tests.Units Tests.SimilitudeTests

/-- Run all Similitude suites; returns `(passed, failed)`. -/
def run : IO (Nat × Nat) := do
  IO.println "Similitude"
  let mut pass := 0
  let mut fail := 0
  for suite in [constantsSuite, homsSuite, unifiedSuite, ratiosSuite, systemConstantsSuite, quantitySuite] do
    let (p, f) ← (← suite).report
    pass := pass + p
    fail := fail + f
  return (pass, fail)

end Tests.Similitude

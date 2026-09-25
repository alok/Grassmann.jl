import Tests.MeasureSystems.Goldens

/-!
# MeasureSystems test aggregator

`Tests.MeasureSystems.run` returns `(passed, failed)` over the MeasureSystems
golden checks (`oracle/golden/measuresystems/`).
-/

namespace Tests.MeasureSystems

open Tests.Units Tests.MeasureSystemsTests

/-- Run all MeasureSystems suites; returns `(passed, failed)`. -/
def run : IO (Nat × Nat) := do
  IO.println "MeasureSystems"
  let mut pass := 0
  let mut fail := 0
  for suite in [measuresSuite, measurementsSuite, systemConstantsSuite, ratiosSuite] do
    let (p, f) ← (← suite).report
    pass := pass + p
    fail := fail + f
  return (pass, fail)

end Tests.MeasureSystems

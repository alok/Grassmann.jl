import Tests.UnitSystems.Common
import Tests.UnitSystems.Systems
import Tests.UnitSystems.Scalars
import Tests.UnitSystems.Display
import Tests.UnitSystems.Extras
import Tests.UnitSystems.FastPaths

/-!
# UnitSystems test aggregator

`Tests.UnitSystems.run` returns `(passed, failed)`. Float goldens pass within
`rtol = 1e-12` and integers must match exactly; the bit-exact tallies are
reported separately (they also count as checks).
-/

namespace Tests.UnitSystems

open Tests.Units Tests.UnitSystemsTests

/-- Run all UnitSystems suites; returns `(passed, failed)`. -/
def run : IO (Nat × Nat) := do
  IO.println "UnitSystems"
  let mut pass := 0
  let mut fail := 0
  for suite in [systemsSuite, displaySuite, constantsSuite, scalarsSuite, conversionsSuite,
      couplingSuite, constructorsSuite, fastPathSuite] do
    let (s, e) ← suite
    let (p, f) ← s.report
    let (p', f') ← e.report
    pass := pass + p + p'
    fail := fail + f + f'
  return (pass, fail)

end Tests.UnitSystems

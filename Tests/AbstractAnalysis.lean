import Tests.AbstractAnalysis.Harness
import Tests.AbstractAnalysis.Sets
import Tests.AbstractAnalysis.Limits
import Tests.AbstractAnalysis.Metric
import Tests.AbstractAnalysis.Groups
import Tests.AbstractAnalysis.FloatPrint
import Tests.AbstractAnalysis.Props

/-!
Test aggregator for the AbstractAnalysis port: Julia-oracle goldens
(`oracle/golden/abstractanalysis/`), property tests and compile-time checks.
Run from the package root (the goldens are read by relative path).
-/

namespace Tests.AbstractAnalysis

open Tests.Golden

/-- Run every AbstractAnalysis suite; returns `(passed, failed)`. -/
def run : IO (Nat × Nat) := do
  let suites : List (String × TestM Unit) :=
    [("AbstractAnalysis.sets", Sets.suite), ("AbstractAnalysis.limits", Limits.suite),
     ("AbstractAnalysis.metric", Metric.suite), ("AbstractAnalysis.groups", Groups.suite),
     ("AbstractAnalysis.floatprint", FloatPrint.suite), ("AbstractAnalysis.props", Props.suite)]
  let mut total := (0, 0)
  for (label, s) in suites do
    let (p, f) ← runSuite label s
    total := (total.1 + p, total.2 + f)
  return total

end Tests.AbstractAnalysis

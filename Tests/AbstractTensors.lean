import Tests.AbstractTensors.Harness
import Tests.AbstractTensors.Golden
import Tests.AbstractTensors.Notation
import Tests.AbstractTensors.StaticVectorsTests
import Tests.AbstractTensors.ComplexTests
import Tests.AbstractTensors.GenericTests
import Tests.AbstractTensors.Kinds
import Tests.AbstractTensors.ValuesShow

/-!
AbstractTensors and StaticVectors test suites. `Notation` and `Kinds` are compile-time
only; the others check oracle goldens at run time.
-/

/-- Run every AbstractTensors/StaticVectors suite; returns `(passed, failed)`. -/
def Tests.AbstractTensors.run : IO (Nat × Nat) := do
  let suites : List (String × Tests.AbstractTensors.TestM Unit) := [
    ("abstracttensors.staticvectors", Tests.AbstractTensors.StaticVectorsTests.suite),
    ("abstracttensors.complex", Tests.AbstractTensors.ComplexTests.suite),
    ("abstracttensors.generic", Tests.AbstractTensors.GenericTests.suite),
    ("abstracttensors.valuesshow", Tests.AbstractTensors.ValuesShow.suite)]
  let mut passed := 0
  let mut failed := 0
  for (name, s) in suites do
    let (p, f) ← Tests.AbstractTensors.runSuite name s
    passed := passed + p
    failed := failed + f
  return (passed, failed)

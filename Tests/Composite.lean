/-
The composite suite (`Grassmann.Composite`):

* `composite/unit`: the verbatim oracle values of port-notes/grassmann-composite.md §6,
  abstracttensors-staticvectors.md §6.6 and grassmann-types.md §4.8, algebraic
  identities (`exp ∘ log`, `sqrt²`, `sin² + cos²`, `inv`), the Julia-defect fixes, and
  Grassmann's `atanh(y, x)` special cases (`Tests/Composite/Unit.lean`);
* `composite/golden`: the element oracle's composite suite (`oracle/golden/composite`)
  through the registered evaluator `grassmann/composite` (`Tests/Golden/Composite.lean`),
  and the composite statements of the docs suite (`Tests/Golden/CompositeDocs.lean`).
-/
import Tests.Golden
import Tests.Golden.Composite
import Tests.Composite.Unit

/-- Run the composite suites; returns `(passed, failed)`. -/
def Tests.Composite.run : IO (Nat × Nat) := do
  let (p₁, f₁) ← Tests.Composite.Unit.run
  let (p₂, f₂) ← Tests.ElementOracle.runWith #[Tests.ElementOracle.compositeRegistration] ["composite"]
  return (p₁ + p₂, f₁ + f₂)

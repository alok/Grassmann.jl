/-
The dynamic element layer (`Grassmann.Dynamic`, `TA V α`) suites:

* `dynamic/laws`: the dense value commutes with `+`, `-`, negation and scalars
  (`Tests/Dynamic/Props.lean`);
* `dynamic/products`: the dense values of `⟑ ∧ ∨ contraction` against the reference plan
  kernels (`Tests/Dynamic/Props.lean`);
* `dynamic/equal`: Julia's `==` (`Tests/Dynamic/Props.lean`);
* `dynamic/examples`: Julia-checked kinds, strings, signed zeros, `==`, `abs2`, `norm`
  (`Tests/Dynamic/Examples.lean`).

The Julia oracle goldens for the layer (construct, arith, unary, products) run in the
`Golden` suite through the evaluators of `Tests/Golden/GrassmannEval.lean`.
-/
import Tests.Dynamic.Common
import Tests.Dynamic.Props
import Tests.Dynamic.Examples

open GrassmannTests DynamicTests

/-- Run every dynamic-layer suite; returns `(passed, failed)`. -/
def Tests.Dynamic.run : IO (Nat × Nat) := do
  let suites : List (String × IO Tally) :=
    [ ("dynamic/laws", lawsRun), ("dynamic/products", productsRun),
      ("dynamic/equal", equalRun), ("dynamic/examples", examplesRun) ]
  let mut pass := 0
  let mut fail := 0
  for (name, suite) in suites do
    let t ← suite
    t.report name
    pass := pass + t.pass
    fail := fail + t.fail
  return (pass, fail)

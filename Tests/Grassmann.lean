/-
Grassmann core suites (the element layer, the reference kernels and the typed
algebra):

* `props`: algebraic properties over exact coefficients in `E2`-`E4`, `M4`,
  `PGA3`, `CGA3`, `DUAL3` and `TAN2` (`Tests/Grassmann/Props.lean`);
* `kernel`: the plan kernels against DirectSum's blade rules for every operation
  and layout pair, plan strictness and caching (`Tests/Grassmann/Kernel.lean`);
* `golden`: a spot check of dense results against the Julia oracle goldens
  (`oracle/golden/{products,unary,arith}`, read relative to the repository root;
  `Tests/Grassmann/Golden.lean`);
* `types`, `extension`: static result types, storage orders, conversions, Julia
  display, inverses, and the `Kernels` extension point (`Tests/Grassmann/Types.lean`).
-/
import Tests.Grassmann.Common
import Tests.Grassmann.Props
import Tests.Grassmann.Kernel
import Tests.Grassmann.Golden
import Tests.Grassmann.Types

open GrassmannTests

/-- Run every Grassmann core suite; returns `(passed, failed)`. -/
def Tests.Grassmann.run : IO (Nat × Nat) := do
  let suites : List (String × IO Tally) :=
    [ ("grassmann/props", Props.run), ("grassmann/kernel", Kernel.run),
      ("grassmann/golden", Golden.run),
      ("grassmann/types", Types.run), ("grassmann/basis", Basis.run),
      ("grassmann/extension", Extension.run) ]
  let mut pass := 0
  let mut fail := 0
  for (name, suite) in suites do
    let t ← suite
    t.report name
    pass := pass + t.pass
    fail := fail + t.fail
  return (pass, fail)

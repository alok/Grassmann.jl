/-
DirectSum / Leibniz test suites:

* `blades`: every record of `oracle/golden/blades/dump_{all,small}.jsonl`
  (blade-level products, involutions, complements, container complements);
* `spaces`: space construction, parsing, display, index tables, blade lookup
  by name (`Tests/DirectSum/golden/spaces.json`);
* `index`: exhaustive index-table consistency (`n ≤ 16`) and large-`n` ranks;
* `literals`: `S!`/`D!`/`V!`/`ℝ^` literals and README goldens;
* `props`: algebraic properties (associativity, Chevalley agreement, …);
* `derived`: derived operators, tangent overlaps, large `n`, `signbit`
  (`Tests/DirectSum/golden/derived.jsonl`);
* `plans`: the `DirectSum.Ops` kernel interface (plans, result containers).

Goldens are read relative to the repository root. Julia defects documented in
the port notes are skipped with a reason and counted.
-/
import Tests.DirectSum.Common
import Tests.DirectSum.Blades
import Tests.DirectSum.Spaces
import Tests.DirectSum.Index
import Tests.DirectSum.Literals
import Tests.DirectSum.Props
import Tests.DirectSum.Derived
import Tests.DirectSum.Plans

open DirectSumTests

/-- Run every DirectSum suite; returns `(passed, failed)` and prints failures and
the documented-defect skip counts. -/
def Tests.DirectSum.run : IO (Nat × Nat) := do
  let suites : List (String × IO Tally) :=
    [ ("directsum/blades", Blades.run), ("directsum/spaces", Spaces.run),
      ("directsum/index", Index.run),
      ("directsum/literals", Literals.run),
      ("directsum/props", Props.run),
      ("directsum/derived", Derived.run),
      ("directsum/plans", Plans.run) ]
  let mut pass := 0
  let mut fail := 0
  for (name, suite) in suites do
    let t ← suite
    t.report name
    pass := pass + t.pass
    fail := fail + t.fail
  return (pass, fail)

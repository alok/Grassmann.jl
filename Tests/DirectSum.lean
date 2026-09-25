/-
DirectSum / Leibniz test suites (oracle goldens, index tables, space display).
-/
import Tests.DirectSum.Common
import Tests.DirectSum.Blades
import Tests.DirectSum.Spaces
import Tests.DirectSum.Index
import Tests.DirectSum.Literals
import Tests.DirectSum.Props

open DirectSumTests

/-- Run every DirectSum suite; returns `(passed, failed)` and prints failures and
the documented-defect skip counts. -/
def Tests.DirectSum.run : IO (Nat × Nat) := do
  let suites : List (String × IO Tally) :=
    [ ("directsum/blades", Blades.run), ("directsum/spaces", Spaces.run),
      ("directsum/index", Index.run),
      ("directsum/literals", Literals.run),
      ("directsum/props", Props.run) ]
  let mut pass := 0
  let mut fail := 0
  for (name, suite) in suites do
    let t ← suite
    t.report name
    pass := pass + t.pass
    fail := fail + t.fail
  return (pass, fail)

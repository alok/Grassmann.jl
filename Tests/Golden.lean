import Tests.Golden.Scalar
import Tests.Golden.Elem
import Tests.Golden.Space
import Tests.Golden.Defects
import Tests.Golden.Shard
import Tests.Golden.Registry
import Tests.Golden.Compare
import Tests.Golden.Runner
import Tests.Golden.Builtin

/-!
# The element-oracle harness (`Tests.Golden`)

The Lean consumer of the element-level Julia oracle `oracle/golden/**`
(docs/port-notes/oracle-schema.md, the normative schema; DESIGN.md §7).

| module | role |
|---|---|
| `Tests.Golden.Scalar` | coefficient grammars (§6): exact `Int64`/`Rational`/`Bool`, bit-exact `Float64` from Julia `repr`, `Complex`; `Coeffs` vectors (`FloatArray` for floats); value comparison |
| `Tests.Golden.Elem` | `GoldenElem`: the neutral decoded element (§7), `encode ∘ decode = id`, storage support and field-presence invariants (§7.1) |
| `Tests.Golden.Space` | space descriptors (§5) → `DirectSum.TensorBundle`, twice (fields, and the Julia source evaluated with DirectSum), checked against DirectSum's printing and tables |
| `Tests.Golden.Defects` | `defects.json` (§10): policies and the full match language |
| `Tests.Golden.Shard` | manifests, shards and case records (§3, §4, §8); streaming loaders |
| `Tests.Golden.Registry` | the pluggable evaluator registry |
| `Tests.Golden.Compare` | comparators (§11 rules 2–4) |
| `Tests.Golden.Runner` | the consumer algorithm (§11) and reporting |
| `Tests.Golden.Builtin` | built-in evaluators (JuliaBase scalar display, Leibniz storage orders, identities) |

`Tests.Golden.run` loads every suite end to end (about 129k cases), validates every schema
invariant, re-derives every defect tag, and runs every registered evaluator. Set
`GOLDEN_SUITES=products,unary` to restrict the suites.
-/

namespace Tests.Golden

/-- Run the given suites with the built-in evaluators plus `extra` (highest precedence
last). Returns `(passed, failed)` over schema checks and evaluated cases, and prints a
report per suite. -/
def runWith (extra : Array Registration) (suites : List String := elementSuites) : IO (Nat × Nat) := do
  IO.println "Golden (element oracle):"
  let root := goldenRoot
  let defects ← try loadDefects root catch e => do
    IO.eprintln s!"  [golden] cannot load defects.json: {e}"
    return (0, 1)
  let regs := builtinRegistrations ++ extra
  let mut passed := 1  -- defects.json decoded (ids unique, policies and match tables valid)
  let mut failed := 0
  for suite in suites do
    let r ← runSuite root defects regs suite
    r.print
    passed := passed + r.passed
    failed := failed + r.failed
  return (passed, failed)

end Tests.Golden

/-- Run the element-oracle harness over every suite (or those named in `GOLDEN_SUITES`,
comma-separated) with the built-in and every registered evaluator. -/
def Tests.Golden.run : IO (Nat × Nat) := do
  let suites := match (← IO.getEnv "GOLDEN_SUITES") with
    | some s => (s.splitOn ",").filter (· != "")
    | none => Tests.Golden.elementSuites
  Tests.Golden.runWith (← Tests.Golden.registered) suites

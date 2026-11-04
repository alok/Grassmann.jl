/-
List the docs-corpus statements (`oracle/golden/docs/*.json`) that the docs evaluator
(`Tests.Golden.DocsInterp`) does not model, with the evaluator's reason, one per line:

    UNIMPL <shard> <statement> <reason>
    NOVAL  <shard> <statement>            (evaluated, but the value is not encodable)

`lake test` reports only the count (`[golden/docs] … unimplemented=N`); this is the list
behind it. Run from the repository root after `lake build Tests`:

    lake env lean --run scripts/docs_unimplemented.lean > docs-unimplemented.tsv
    cut -f4 docs-unimplemented.tsv | sort | uniq -c | sort -rn     # by reason
-/
import Tests.Golden.Docs
open Tests.ElementOracle Tests.ElementOracle.Docs
/-- Replay every docs shard and print the statements the evaluator does not model. -/
def main : IO Unit := do
  let dir := goldenRoot / "docs"
  let files ← dir.readDir
  let names := (files.map (·.fileName)).qsort (· < ·)
  for f in names do
    let shard := String.ofList (f.toList.take (f.length - 5))
    let inputs ← loadShardInputs shard
    let mut env : Env := { sandbox := sandboxOf shard }
    for inp in inputs do
      match (evalStatement inp).run { env with approx := false } with
      | .ok (v, env') =>
        env := env'
        if (encodeVal (sandboxOf shard) v).isNone then IO.println s!"NOVAL\t{shard}\t{inp}"
      | .error e => IO.println s!"UNIMPL\t{shard}\t{inp.replace "\n" "⏎"}\t{e}"

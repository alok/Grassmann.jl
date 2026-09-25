import Tests.JuliaBase.FloatShow
import Tests.JuliaBase.Num
import Tests.JuliaBase.Range
import Tests.JuliaBase.Show

/-!
JuliaBase test aggregator.

`Tests.JuliaBase.run` runs the committed oracle goldens (`Tests/JuliaBase/*.json`). Setting
the environment variable `JULIABASE_FUZZ=PREFIX` additionally runs the large TSV fuzz files
written by

    julia --startup-file=no --project=oracle Tests/JuliaBase/gen_golden.jl fuzz PREFIX 200000 1

(`PREFIX_f64.tsv`, `PREFIX_f32.tsv`, `PREFIX_num.tsv`, `PREFIX_range.tsv`).
-/

namespace Tests.JuliaBase

/-- Run the large oracle fuzz files `PREFIX_{f64,f32,num,range}.tsv`. -/
def fuzzAll (pre : String) : IO (Nat × Nat) := do
  let (p1, f1) ← FloatShow.fuzz s!"{pre}_f64.tsv" s!"{pre}_f32.tsv"
  let (p2, f2) ← Num.fuzz s!"{pre}_num.tsv"
  let (p3, f3) ← Range.fuzz s!"{pre}_range.tsv"
  return (p1 + p2 + p3, f1 + f2 + f3)

/-- Run every JuliaBase suite; returns `(passed, failed)` and prints failures. -/
def run : IO (Nat × Nat) := do
  IO.println "JuliaBase:"
  let mut passed := 0
  let mut failed := 0
  for suite in [FloatShow.golden, Num.golden, Range.golden, Show.golden] do
    let (p, f) ← try suite catch e => do
      IO.eprintln s!"  suite error: {e}"
      pure (0, 1)
    passed := passed + p
    failed := failed + f
  if let some pre ← IO.getEnv "JULIABASE_FUZZ" then
    let (p, f) ← fuzzAll pre
    passed := passed + p
    failed := failed + f
  return (passed, failed)

end Tests.JuliaBase

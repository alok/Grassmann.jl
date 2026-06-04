/-
  RunPropertyTests.lean - Execute Plausible property tests
-/
import Grassmann.PropertyTests

def runCGA3PointCloudOnly : IO Unit := do
  let results ← Grassmann.PropertyTests.runCGA3PointCloudTransformTests
  unless results.all (fun r => r.passed) do
    throw <| IO.userError "CGA3 point-cloud property tests failed"

def main (args : List String) : IO Unit := do
  match args with
  | [] => Grassmann.PropertyTests.runFullPropertyTests
  | ["cga-point-cloud"] => runCGA3PointCloudOnly
  | _ =>
      throw <| IO.userError
        "Usage: propertytests [cga-point-cloud]"

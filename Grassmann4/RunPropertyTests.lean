/-
  RunPropertyTests.lean - Execute Plausible property tests
-/
import Grassmann.PropertyTests

def runCGA3PointCloudOnly : IO Unit := do
  let results ← Grassmann.PropertyTests.runCGA3PointCloudTransformTests
  unless results.all (fun r => r.passed) do
    throw <| IO.userError "CGA3 point-cloud property tests failed"

def runMVDispatchOnly : IO Unit := do
  let results ← Grassmann.PropertyTests.runMVDispatchReferenceTests
  unless results.all (fun r => r.passed) do
    throw <| IO.userError "MV dispatch property tests failed"

def runRotorExpOnly : IO Unit := do
  let results ← Grassmann.PropertyTests.runRotorExpReferenceTests
  unless results.all (fun r => r.passed) do
    throw <| IO.userError "rotor exponential property tests failed"

def main (args : List String) : IO Unit := do
  match args with
  | [] => Grassmann.PropertyTests.runFullPropertyTests
  | ["cga-point-cloud"] => runCGA3PointCloudOnly
  | ["mv-dispatch"] => runMVDispatchOnly
  | ["rotor-exp"] => runRotorExpOnly
  | _ =>
      throw <| IO.userError
        "Usage: propertytests [cga-point-cloud|mv-dispatch|rotor-exp]"

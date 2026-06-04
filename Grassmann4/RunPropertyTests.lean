/-
  RunPropertyTests.lean - Execute Plausible property tests
-/
import Grassmann.PropertyTests

def requireAllPassed
    (label : String) (results : List Grassmann.PropertyTests.PropTestResult) : IO Unit := do
  unless results.all (fun r => r.passed) do
    throw <| IO.userError s!"{label} property tests failed"

def runCGA3PointCloudOnly : IO Unit := do
  let results ← Grassmann.PropertyTests.runCGA3PointCloudTransformTests
  requireAllPassed "CGA3 point-cloud" results

def runPGA3PointCloudOnly : IO Unit := do
  let results ← Grassmann.PropertyTests.runPGA3PointCloudTransformTests
  requireAllPassed "PGA3 point-cloud" results

def runMVDispatchOnly : IO Unit := do
  let results ← Grassmann.PropertyTests.runMVDispatchReferenceTests
  requireAllPassed "MV dispatch" results

def runRotorExpOnly : IO Unit := do
  let results ← Grassmann.PropertyTests.runRotorExpReferenceTests
  requireAllPassed "rotor exponential" results

def runNativeReferenceOnly : IO Unit := do
  let results ← Grassmann.PropertyTests.runNativeReferenceTests
  requireAllPassed "native-vector reference" results

def runBladeReferenceOnly : IO Unit := do
  let results ← Grassmann.PropertyTests.runBladeReferenceTests
  requireAllPassed "blade reference" results

def runSignTableReferenceOnly : IO Unit := do
  let results ← Grassmann.PropertyTests.runSignTableReferenceTests
  requireAllPassed "sign-table reference" results

def runPackedReferenceOnly : IO Unit := do
  let r3Results ← Grassmann.PropertyTests.runPackedReferenceTests
  let pga3Results ← Grassmann.PropertyTests.runPGA3PackedReferenceTests
  let cga3Results ← Grassmann.PropertyTests.runCGA3PackedReferenceTests
  requireAllPassed "packed MV reference" (r3Results ++ pga3Results ++ cga3Results)

def runSparseReferenceOnly : IO Unit := do
  let r3Results ← Grassmann.PropertyTests.runSparseReferenceTests
  let pga3Results ← Grassmann.PropertyTests.runPGA3SparseReferenceTests
  let cga3Results ← Grassmann.PropertyTests.runCGA3SparseReferenceTests
  requireAllPassed "sparse MV reference" (r3Results ++ pga3Results ++ cga3Results)

def runTruncatedReferenceOnly : IO Unit := do
  let results ← Grassmann.PropertyTests.runTruncatedReferenceTests
  requireAllPassed "truncated MV reference" results

def runReprConversionOnly : IO Unit := do
  let results ← Grassmann.PropertyTests.runReprConversionTests
  requireAllPassed "representation conversion" results

def runHighDimStressOnly : IO Unit := do
  let results ← Grassmann.PropertyTests.runHighDimStressTests
  requireAllPassed "high-dimensional stress" results

def usage : String :=
  "Usage: propertytests [cga-point-cloud|pga-point-cloud|mv-dispatch|" ++
    "rotor-exp|native-reference|blade-reference|sign-table|packed-reference|" ++
    "sparse-reference|truncated-reference|repr|stress]"

def main (args : List String) : IO Unit := do
  match args with
  | [] => Grassmann.PropertyTests.runFullPropertyTests
  | ["cga-point-cloud"] => runCGA3PointCloudOnly
  | ["pga-point-cloud"] => runPGA3PointCloudOnly
  | ["mv-dispatch"] => runMVDispatchOnly
  | ["rotor-exp"] => runRotorExpOnly
  | ["native-reference"] => runNativeReferenceOnly
  | ["blade-reference"] => runBladeReferenceOnly
  | ["sign-table"] => runSignTableReferenceOnly
  | ["packed-reference"] => runPackedReferenceOnly
  | ["sparse-reference"] => runSparseReferenceOnly
  | ["truncated-reference"] => runTruncatedReferenceOnly
  | ["repr"] => runReprConversionOnly
  | ["stress"] => runHighDimStressOnly
  | _ =>
      throw <| IO.userError usage

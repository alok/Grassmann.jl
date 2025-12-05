/-
  Grassmann/JuliaOracle.lean - Tight integration with Grassmann.jl oracle

  This module provides automated verification of Lean computations against
  the reference Grassmann.jl implementation via IO.Process.

  Usage:
    #eval JuliaOracle.runAllTests
    #eval JuliaOracle.quickCheck
-/
import Lean.Data.Json
import Grassmann.SparseMultivector
import Grassmann.Products
import Grassmann.RotorExp
import Grassmann.Manifold

namespace Grassmann.JuliaOracle

open Grassmann
open Lean (Json)

/-! ## Configuration -/

/-- Path to Julia oracle script (relative to project root) -/
def oraclePath : String := "oracle/grassmann_oracle.jl"

/-- Tolerance for floating point comparison -/
def defaultTolerance : Float := 1e-9

/-! ## JSON Value Extraction using Lean.Json -/

/-- Extract a Float from JSON object by key -/
def getJsonFloat (json : Json) (key : String) : Option Float :=
  match json.getObjVal? key with
  | .ok (.num n) => some n.toFloat
  | _ => none

/-- Extract a Bool from JSON object by key -/
def getJsonBool (json : Json) (key : String) : Option Bool :=
  match json.getObjVal? key with
  | .ok (.bool b) => some b
  | _ => none

/-- Extract an Array of Floats from JSON object by key -/
def getJsonFloatArray (json : Json) (key : String) : Option (Array Float) :=
  match json.getObjVal? key with
  | .ok (.arr arr) =>
    let floats := arr.filterMap fun j =>
      match j with
      | .num n => some n.toFloat
      | _ => none
    if floats.size == arr.size then some floats else none
  | _ => none

/-- Parse JSON string -/
def parseJson (s : String) : Option Json :=
  match Json.parse s with
  | .ok j => some j
  | .error _ => none

/-! ## Oracle Invocation -/

/-- Result of an oracle call -/
structure OracleResult where
  success : Bool
  stdout : String
  stderr : String
  deriving Repr

/-- Call the Julia oracle with arguments.
    Uses `env -i` to spawn Julia in a clean environment, avoiding LLVM library
    conflicts between Lean's bundled LLVM and Julia's codegen. -/
def callOracle (args : List String) : IO OracleResult := do
  -- Use env to spawn Julia with minimal environment to avoid LLVM conflicts
  -- The conflict occurs because Lean loads its own libLLVM which then interferes
  -- with Julia's libjulia-codegen when it tries to load
  let home := (← IO.getEnv "HOME").getD "/Users/alokbeniwal"
  -- Include juliaup bin path and standard paths
  let path := s!"{home}/.juliaup/bin:/usr/local/bin:/usr/bin:/bin"
  let juliaDepot := home ++ "/.julia"
  -- Use --project to activate the Grassmann.jl environment
  let grassmannProject := s!"{home}/Grassmann"
  let child ← IO.Process.spawn {
    cmd := "env"
    args := #["-i",
              s!"HOME={home}",
              s!"PATH={path}",
              s!"JULIA_DEPOT_PATH={juliaDepot}",
              "julia", "--startup-file=no", s!"--project={grassmannProject}",
              oraclePath] ++ args.toArray
    stdout := .piped
    stderr := .piped
    cwd := some "/Users/alokbeniwal/Grassmann/Grassmann4"
  }
  let stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  return {
    success := exitCode == 0
    stdout := stdout.trim
    stderr := stderr.trim
  }

/-! ## Test Results -/

/-- Result of a verification test -/
structure TestResult where
  name : String
  passed : Bool
  leanValue : Float
  juliaValue : Float
  difference : Float
  message : String := ""
  deriving Repr

instance : ToString TestResult where
  toString r :=
    let status := if r.passed then "PASS" else "FAIL"
    let diff := if r.difference < 1e-10 then "~0" else s!"{r.difference}"
    s!"[{status}] {r.name}: lean={r.leanValue}, julia={r.juliaValue}, diff={diff}"

/-- Compare Float values within tolerance -/
def floatsMatch (a b : Float) (tol : Float := defaultTolerance) : Bool :=
  (a - b).abs < tol

/-! ## Verification Functions -/

/-- Verify geometric product scalar part against Julia -/
def verifyGeometricProduct (sig : String) (bladeA bladeB : String)
    (leanResult : Float) : IO TestResult := do
  let result ← callOracle ["geometric_product", sig, bladeA, bladeB]
  if !result.success then
    return {
      name := s!"gp({sig},{bladeA},{bladeB})"
      passed := false
      leanValue := leanResult
      juliaValue := 0.0
      difference := 0.0
      message := s!"Oracle error: {result.stderr}"
    }
  match parseJson result.stdout >>= fun j => getJsonFloat j "scalar_part" with
  | some juliaScalar =>
    let diff := (leanResult - juliaScalar).abs
    return {
      name := s!"gp({sig},{bladeA},{bladeB})"
      passed := floatsMatch leanResult juliaScalar
      leanValue := leanResult
      juliaValue := juliaScalar
      difference := diff
    }
  | none =>
    return {
      name := s!"gp({sig},{bladeA},{bladeB})"
      passed := false
      leanValue := leanResult
      juliaValue := 0.0
      difference := 0.0
      message := s!"Parse failed: {result.stdout}"
    }

/-- Verify signature basis squares -/
def verifySignature (sigName : String) (leanSquares : Array Float) : IO TestResult := do
  let result ← callOracle ["signature_check", sigName]
  if !result.success then
    return {
      name := s!"sig({sigName})"
      passed := false
      leanValue := 0.0
      juliaValue := 0.0
      difference := 0.0
      message := s!"Oracle error: {result.stderr}"
    }
  match parseJson result.stdout >>= fun j => getJsonFloatArray j "basis_squares" with
  | some juliaSquares =>
    if leanSquares.size != juliaSquares.size then
      return {
        name := s!"sig({sigName})"
        passed := false
        leanValue := leanSquares.size.toFloat
        juliaValue := juliaSquares.size.toFloat
        difference := 0.0
        message := "Dimension mismatch"
      }
    let allMatch := (leanSquares.zip juliaSquares).all fun (l, j) => floatsMatch l j
    let maxDiff := (leanSquares.zip juliaSquares).map (fun (l, j) => (l - j).abs)
      |>.foldl max 0.0
    return {
      name := s!"sig({sigName})"
      passed := allMatch
      leanValue := 0.0
      juliaValue := 0.0
      difference := maxDiff
      message := if allMatch then "All match" else "Mismatch"
    }
  | none =>
    return {
      name := s!"sig({sigName})"
      passed := false
      leanValue := 0.0
      juliaValue := 0.0
      difference := 0.0
      message := s!"Parse failed: {result.stdout}"
    }

/-- Verify CGA point nullity -/
def verifyCGAPoint (x y z : Float) (leanSq : Float) : IO TestResult := do
  let result ← callOracle ["point_embedding", toString x, toString y, toString z]
  if !result.success then
    return {
      name := s!"cga_pt({x},{y},{z})"
      passed := false
      leanValue := leanSq
      juliaValue := 0.0
      difference := 0.0
      message := s!"Oracle error: {result.stderr}"
    }
  match parseJson result.stdout >>= fun j => getJsonFloat j "point_squared" with
  | some juliaSq =>
    let passed := floatsMatch leanSq 0.0 (tol := 1e-6) &&
                  floatsMatch juliaSq 0.0 (tol := 1e-6)
    return {
      name := s!"cga_pt({x},{y},{z})"
      passed := passed
      leanValue := leanSq
      juliaValue := juliaSq
      difference := (leanSq - juliaSq).abs
      message := if passed then "Both null" else "Not null"
    }
  | none =>
    return {
      name := s!"cga_pt({x},{y},{z})"
      passed := false
      leanValue := leanSq
      juliaValue := 0.0
      difference := 0.0
      message := "Parse failed"
    }

/-- Verify rotor scalar part -/
def verifyRotor (sigName : String) (angle : Float) (leanScalar : Float) : IO TestResult := do
  let result ← callOracle ["verify_rotor", sigName, toString angle]
  if !result.success then
    return {
      name := s!"rotor({sigName},{angle})"
      passed := false
      leanValue := leanScalar
      juliaValue := 0.0
      difference := 0.0
      message := s!"Oracle error: {result.stderr}"
    }
  match parseJson result.stdout >>= fun j => getJsonFloat j "rotor_scalar" with
  | some juliaScalar =>
    let diff := (leanScalar - juliaScalar).abs
    return {
      name := s!"rotor({sigName},{angle})"
      passed := floatsMatch leanScalar juliaScalar (tol := 1e-6)
      leanValue := leanScalar
      juliaValue := juliaScalar
      difference := diff
    }
  | none =>
    return {
      name := s!"rotor({sigName},{angle})"
      passed := false
      leanValue := leanScalar
      juliaValue := 0.0
      difference := 0.0
      message := "Parse failed"
    }

/-! ## Lean Computation Helpers -/

/-- R3 basis vector -/
def r3e (i : Nat) (h : i < 3 := by omega) : MultivectorS R3 Float :=
  MultivectorS.basis ⟨i, h⟩

/-- CGA3 basis vector -/
def cga3e (i : Nat) (h : i < 5 := by omega) : MultivectorS CGA3 Float :=
  MultivectorS.basis ⟨i, h⟩

/-! ## Test Suites -/

/-- Test R3 geometric products -/
def testR3Products : IO (Array TestResult) := do
  let e1 := r3e 0
  let e2 := r3e 1
  let e3 := r3e 2
  let e12 := e1 * e2
  let e123 := e1 * e2 * e3

  let r1 ← verifyGeometricProduct "R3" "e1" "e1" (e1 * e1).scalarPart
  let r2 ← verifyGeometricProduct "R3" "e2" "e2" (e2 * e2).scalarPart
  let r3 ← verifyGeometricProduct "R3" "e3" "e3" (e3 * e3).scalarPart
  let r4 ← verifyGeometricProduct "R3" "e1" "e2" (e1 * e2).scalarPart
  let r5 ← verifyGeometricProduct "R3" "e12" "e12" (e12 * e12).scalarPart
  let r6 ← verifyGeometricProduct "R3" "e123" "e123" (e123 * e123).scalarPart
  return #[r1, r2, r3, r4, r5, r6]

/-- Test signature verification -/
def testSignatures : IO (Array TestResult) := do
  let r1 ← verifySignature "R3" #[1.0, 1.0, 1.0]
  let r2 ← verifySignature "CGA3" #[1.0, 1.0, 1.0, 1.0, -1.0]
  let r3 ← verifySignature "STA" #[1.0, -1.0, -1.0, -1.0]
  return #[r1, r2, r3]

/-- Test CGA null vectors -/
def testCGANullVectors : IO (Array TestResult) := do
  let w1 := cga3e 0
  let w2 := cga3e 1
  let w3 := cga3e 2
  let w4 := cga3e 3  -- e+ (squares to +1)
  let w5 := cga3e 4  -- e- (squares to -1)

  let einf := w4 + w5
  let e0 := (w5 + w4.smul (-1.0)).smul 0.5

  -- CGA null basis tests
  let einfSq := (einf * einf).scalarPart
  let e0Sq := (e0 * e0).scalarPart
  let inner := ((einf * e0 + e0 * einf).scalarPart) / 2.0

  let r1 : TestResult := {
    name := "CGA e∞²=0"
    passed := floatsMatch einfSq 0.0
    leanValue := einfSq
    juliaValue := 0.0
    difference := einfSq.abs
  }
  let r2 : TestResult := {
    name := "CGA e0²=0"
    passed := floatsMatch e0Sq 0.0
    leanValue := e0Sq
    juliaValue := 0.0
    difference := e0Sq.abs
  }
  let r3 : TestResult := {
    name := "CGA e∞·e0=-1"
    passed := floatsMatch inner (-1.0)
    leanValue := inner
    juliaValue := -1.0
    difference := (inner + 1.0).abs
  }

  -- Point embeddings
  let mkPoint (x y z : Float) : Float :=
    let p := w1.smul x + w2.smul y + w3.smul z
    let pSq := x*x + y*y + z*z
    let P := p + einf.smul (pSq / 2.0) + e0
    (P * P).scalarPart

  let r4 ← verifyCGAPoint 0.0 0.0 0.0 (mkPoint 0.0 0.0 0.0)
  let r5 ← verifyCGAPoint 1.0 0.0 0.0 (mkPoint 1.0 0.0 0.0)
  let r6 ← verifyCGAPoint 1.0 2.0 3.0 (mkPoint 1.0 2.0 3.0)
  return #[r1, r2, r3, r4, r5, r6]

/-- Test rotors -/
def testRotors : IO (Array TestResult) := do
  let e1 := r3e 0
  let e2 := r3e 1
  let B := e1 * e2

  let piOver4 : Float := 0.7853981633974483
  let piOver2 : Float := 1.5707963267948966

  let r1 ← verifyRotor "R3" 0.0 (expBivector (MultivectorS.zero : MultivectorS R3 Float)).scalarPart
  let r2 ← verifyRotor "R3" (piOver4 * 2.0) (expBivector (B.smul piOver4)).scalarPart
  let r3 ← verifyRotor "R3" (piOver2 * 2.0) (expBivector (B.smul piOver2)).scalarPart
  return #[r1, r2, r3]

/-! ## Main Test Runner -/

/-- Run all tests -/
def runAllTests : IO Unit := do
  IO.println "╔══════════════════════════════════════════╗"
  IO.println "║  Grassmann.jl Oracle Verification Suite  ║"
  IO.println "╚══════════════════════════════════════════╝"
  IO.println ""

  -- R3 products
  IO.println "┌─ R3 Geometric Products ─────────────────┐"
  let r3Results ← testR3Products
  for r in r3Results do IO.println s!"│ {r}"
  IO.println "└──────────────────────────────────────────┘"

  -- Signatures
  IO.println "\n┌─ Signature Verification ─────────────────┐"
  let sigResults ← testSignatures
  for r in sigResults do IO.println s!"│ {r}"
  IO.println "└──────────────────────────────────────────┘"

  -- CGA
  IO.println "\n┌─ CGA Null Vectors ───────────────────────┐"
  let cgaResults ← testCGANullVectors
  for r in cgaResults do IO.println s!"│ {r}"
  IO.println "└──────────────────────────────────────────┘"

  -- Rotors
  IO.println "\n┌─ Rotor Exponentials ─────────────────────┐"
  let rotorResults ← testRotors
  for r in rotorResults do IO.println s!"│ {r}"
  IO.println "└──────────────────────────────────────────┘"

  -- Summary
  let all := r3Results ++ sigResults ++ cgaResults ++ rotorResults
  let passed := all.filter (·.passed)
  let failed := all.filter (!·.passed)

  IO.println "\n╔══════════════════════════════════════════╗"
  IO.println s!"║  Summary: {passed.size}/{all.size} tests passed                  ║"
  if failed.size > 0 then
    IO.println "╠══════════════════════════════════════════╣"
    IO.println "║  FAILED:                                 ║"
    for r in failed do
      IO.println s!"║    {r.name}: {r.message}"
  IO.println "╚══════════════════════════════════════════╝"

/-- Quick connection check -/
def quickCheck : IO Bool := do
  IO.println "Testing Julia oracle connection..."
  let result ← callOracle ["signature_check", "R3"]
  if result.success then
    IO.println s!"OK: {result.stdout}"
    return true
  else
    IO.println s!"FAILED: {result.stderr}"
    return false

-- Uncomment to run:
-- #eval quickCheck
-- #eval runAllTests

end Grassmann.JuliaOracle

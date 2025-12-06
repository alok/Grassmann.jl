/-
  Grassmann/Bench.lean - Benchmarks for optimization comparison

  Compare naive vs optimized implementations:
  1. Geometric product: naive vs table-based
  2. Sandwich: naive vs sparse
  3. Rotor composition: naive vs even-only
  4. Vector squared: full product vs O(n)
-/
import Grassmann.StaticOpt
import Grassmann.BladeIndex
import Grassmann.SignTables

namespace Grassmann.Bench

/-! ## Test Data Setup -/

/-- Create a test R3 vector -/
def testVector (seed : Float) : Multivector R3 Float :=
  ⟨fun i =>
    if i.val = 1 then seed * 1.5
    else if i.val = 2 then seed * 0.7
    else if i.val = 4 then seed * 1.2
    else 0.0⟩

/-- Create a test R3 rotor (scalar + bivector) -/
def testRotor (angle : Float) : Multivector R3 Float :=
  let c := Float.cos (angle / 2)
  let s := Float.sin (angle / 2)
  ⟨fun i =>
    if i.val = 0 then c           -- scalar
    else if i.val = 3 then s * 0.577  -- e12 component
    else if i.val = 5 then s * 0.577  -- e13 component
    else if i.val = 6 then s * 0.577  -- e23 component
    else 0.0⟩

/-! ## Benchmark Helpers -/

/-- Run function n times, accumulate into result (prevents dead code elimination) -/
@[noinline]
def runN (n : Nat) (f : Unit → Float) : Float :=
  let rec go (i : Nat) (acc : Float) : Float :=
    if i = 0 then acc
    else go (i - 1) (acc + f ())
  go n 0.0

/-- Simple timing: run and report -/
def timeit (name : String) (iters : Nat) (f : Unit → Float) : IO Float := do
  let start ← IO.monoNanosNow
  let result := runN iters f
  let stop ← IO.monoNanosNow
  let elapsed : Nat := stop - start
  let perIter : Float := elapsed.toFloat / iters.toFloat
  IO.println s!"{name}: {perIter}ns/iter"
  return result

/-! ## Correctness Verification -/

def verifyCorrectness : IO Unit := do
  IO.println "=== Correctness Verification ==="

  let rotor := testRotor 0.5
  let v := testVector 1.0
  let r1 := testRotor 0.3
  let r2 := testRotor 0.7

  -- Sandwich
  let naive_sandwich := rotor.sandwich v
  let sparse_sandwich := R3Fast.sandwichFast rotor v
  let diff_sandwich := (List.finRange 8).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_sandwich.coeffs idx - sparse_sandwich.coeffs idx)
  IO.println s!"Sandwich diff: {diff_sandwich}"

  -- Rotor mul
  let naive_rotor := r1 * r2
  let sparse_rotor := R3Fast.rotorMul r1 r2
  let diff_rotor := (List.finRange 8).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_rotor.coeffs idx - sparse_rotor.coeffs idx)
  IO.println s!"Rotor mul diff: {diff_rotor}"

  -- Vector squared
  let naive_vsq := (v * v).scalarPart
  let opt_vsq := vectorSquaredScalar v
  IO.println s!"Vector squared diff: {Float.abs (naive_vsq - opt_vsq)}"

  IO.println ""

/-! ## Benchmarks -/

def iters : Nat := 100000

def benchGeometricProduct : IO Unit := do
  IO.println "=== Geometric Product ==="
  let v1 := testVector 1.0
  let v2 := testVector 2.0

  let _ ← timeit "Naive geometric" iters fun _ =>
    (v1 * v2).scalarPart

  let _ ← timeit "Table geometric" iters fun _ =>
    (Multivector.geometricProductWithTable R3SignTable v1 v2).scalarPart

  IO.println ""

def benchSandwich : IO Unit := do
  IO.println "=== Sandwich Product ==="
  let rotor := testRotor 0.5
  let v := testVector 1.0

  let _ ← timeit "Naive sandwich" iters fun _ =>
    (rotor.sandwich v).scalarPart

  let _ ← timeit "Table sandwich" iters fun _ =>
    (sandwichWithTable R3SignTable rotor v).scalarPart

  let _ ← timeit "Sparse sandwich" iters fun _ =>
    (R3Fast.sandwichFast rotor v).scalarPart

  IO.println ""

def benchRotorComposition : IO Unit := do
  IO.println "=== Rotor Composition ==="
  let r1 := testRotor 0.3
  let r2 := testRotor 0.7

  let _ ← timeit "Naive rotor mul" iters fun _ =>
    (r1 * r2).scalarPart

  let _ ← timeit "Even-only rotor" iters fun _ =>
    (composeRotorsOpt r1 r2).scalarPart

  let _ ← timeit "Sparse rotor" iters fun _ =>
    (R3Fast.rotorMul r1 r2).scalarPart

  IO.println ""

def benchVectorSquared : IO Unit := do
  IO.println "=== Vector Squared ==="
  let v := testVector 3.0

  let _ ← timeit "Naive v*v" iters fun _ =>
    (v * v).scalarPart

  let _ ← timeit "Optimized v²" iters fun _ =>
    vectorSquaredScalar v

  IO.println ""

def benchWedge : IO Unit := do
  IO.println "=== Wedge Product ==="
  let v1 := testVector 1.0
  let v2 := testVector 2.0

  let _ ← timeit "Naive wedge" iters fun _ =>
    (v1 ⋀ᵐ v2).scalarPart

  let _ ← timeit "Sparse wedge" iters fun _ =>
    (R3Fast.vectorWedge v1 v2).scalarPart

  IO.println ""

/-- Run all benchmarks -/
def runAll : IO Unit := do
  IO.println "╔════════════════════════════════════════════════════════════╗"
  IO.println "║         Grassmann Algebra Optimization Benchmarks          ║"
  IO.println "╚════════════════════════════════════════════════════════════╝"
  IO.println ""

  verifyCorrectness
  benchGeometricProduct
  benchSandwich
  benchRotorComposition
  benchVectorSquared
  benchWedge

  IO.println "Done!"

end Grassmann.Bench

-- Run benchmarks via #eval (interpreter, not accurate for timing)
-- #eval Grassmann.Bench.runAll

-- For accurate benchmarks, compile and run:
-- lake build bench && .lake/build/bin/bench
def main : IO Unit := Grassmann.Bench.runAll

/-
  Grassmann/Bench.lean - Benchmarks for MV (DataArray-backed) vs Multivector (proof-friendly)

  Compare the unified MV type against the proof-friendly Multivector:
  1. Rotor composition: MV sig .even vs Multivector
  2. Sandwich product: MV-based rotation vs dense Multivector
  3. Full geometric product: MV sig .full vs Multivector

  ## Running Benchmarks

  ### Compiled benchmarks (for accurate timing)
  ```bash
  lake build bench && .lake/build/bin/bench
  ```

  ### Hyperfine comparison (recommended)
  ```bash
  lake build bench
  hyperfine '.lake/build/bin/bench mv-rotor' '.lake/build/bin/bench naive-rotor' --warmup 3
  ```
-/
import Grassmann.MV
import Grassmann.Spinor
import Grassmann.SignTables
import Grassmann.StaticOpt

namespace Grassmann.Bench

/-! ## Test Data Setup -/

/-- Create a test R3 vector as Multivector -/
@[noinline]
def testVector (seed : Float) : Multivector R3 Float :=
  ⟨fun i =>
    if i.val = 1 then seed * 1.5
    else if i.val = 2 then seed * 0.7
    else if i.val = 4 then seed * 1.2
    else 0.0⟩

/-- Create a test R3 rotor as Multivector -/
@[noinline]
def testRotor (angle : Float) : Multivector R3 Float :=
  let c := Float.cos (angle / 2)
  let s := Float.sin (angle / 2)
  ⟨fun i =>
    if i.val = 0 then c           -- scalar
    else if i.val = 3 then s * 0.577  -- e12 component
    else if i.val = 5 then s * 0.577  -- e13 component
    else if i.val = 6 then s * 0.577  -- e23 component
    else 0.0⟩

/-- Create a test R3 rotor as MV sig .even -/
@[noinline]
def testRotorMV (angle : Float) : MV R3 .even :=
  let c := Float.cos (angle / 2)
  let s := Float.sin (angle / 2)
  MV.zero R3 .even
    |>.setCoeff 0 c           -- scalar (mask 0)
    |>.setCoeff 3 (s * 0.577) -- e12 (mask 3)
    |>.setCoeff 5 (s * 0.577) -- e13 (mask 5)
    |>.setCoeff 6 (s * 0.577) -- e23 (mask 6)

/-- Create a test R3 vector as MV sig .odd -/
@[noinline]
def testVectorMV (seed : Float) : MV R3 .odd :=
  MV.zero R3 .odd
    |>.setCoeff 1 (seed * 1.5)  -- e1
    |>.setCoeff 2 (seed * 0.7)  -- e2
    |>.setCoeff 4 (seed * 1.2)  -- e3

/-- Create a test PGA3 motor as MV sig .even -/
@[noinline]
def testMotorMV (angle : Float) : MV PGA3 .even :=
  let c := Float.cos (angle / 2)
  let s := Float.sin (angle / 2)
  MV.zero PGA3 .even
    |>.setCoeff 0 c           -- scalar
    |>.setCoeff 3 (s * 0.577) -- bivector components
    |>.setCoeff 5 (s * 0.577)
    |>.setCoeff 6 (s * 0.577)

/-! ## Benchmark Helpers -/

/-- Run function n times with varying index. -/
@[noinline]
def runN (n : Nat) (f : Nat → Float) : Float :=
  let rec go (i : Nat) (acc : Float) : Float :=
    if i = 0 then acc
    else
      let i' := i - 1
      go i' (acc + f i')
  go n 0.0

/-- Black hole to prevent optimizer from eliminating computation -/
@[noinline]
def blackhole (x : Float) : IO Unit := do
  if x.isNaN then IO.println "nan"
  pure ()

/-- Simple timing with warmup -/
def timeit (name : String) (warmupIters : Nat) (iters : Nat) (f : Nat → Float) : IO Float := do
  -- Warmup
  let _ := runN warmupIters f
  -- Timed phase
  let start ← IO.monoNanosNow
  let salt : Float := Float.ofNat (start % 1024)
  let result := runN iters fun i => f i + salt
  blackhole result
  let stop ← IO.monoNanosNow
  let elapsed := stop - start
  let perIterNs := elapsed.toFloat / iters.toFloat
  IO.println s!"{name}: {perIterNs} ns/iter ({iters} iters)"
  return result

/-! ## Correctness Verification -/

def verifyCorrectness : IO Unit := do
  IO.println "=== Correctness Verification ==="

  let r1 := testRotor 0.3
  let r2 := testRotor 0.7
  let r1MV := testRotorMV 0.3
  let r2MV := testRotorMV 0.7

  -- Naive rotor mul
  let naive_rotor := r1 * r2

  -- MV rotor mul
  let mv_rotor := r1MV * r2MV
  let mv_rotor_full := mv_rotor.toMultivector

  let diff_mv_rotor := (List.finRange 8).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_rotor.coeffs idx - mv_rotor_full.coeffs idx)
  IO.println s!"MV rotor diff: {diff_mv_rotor}"

  -- Vector sandwich
  let v := testVector 1.0
  let vMV := testVectorMV 1.0
  let rotor := testRotor 0.5
  let rotorMV := testRotorMV 0.5

  let naive_sandwich := rotor.sandwich v
  let mv_sandwich := mvSandwich rotorMV vMV
  let mv_sandwich_full := mv_sandwich.toMultivector

  let diff_sandwich := (List.finRange 8).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_sandwich.coeffs idx - mv_sandwich_full.coeffs idx)
  IO.println s!"MV sandwich diff: {diff_sandwich}"

  IO.println ""

/-! ## Benchmarks -/

def warmupIters : Nat := 10000
def iters : Nat := 100000

def benchRotorComposition : IO Unit := do
  IO.println "=== Rotor Composition ==="
  let samples : Nat := 16

  -- Multivector rotors (proof-friendly)
  let rotors : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testRotor (0.05 * Float.ofNat (k.val + 1))

  -- MV rotors (DataArray-backed)
  let rotorsMV : Array (MV R3 .even) :=
    Array.ofFn (n := samples) fun k =>
      testRotorMV (0.05 * Float.ofNat (k.val + 1))

  let defaultRotor := testRotor 0.3
  let defaultRotorMV := testRotorMV 0.3

  let _ ← timeit "Naive rotor (Multivector)" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let r1 := rotors.getD idx defaultRotor
    let r2 := rotors.getD idx2 defaultRotor
    (r1 * r2).scalarPart

  let _ ← timeit "MV rotor (DataArray)" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let r1 := rotorsMV.getD idx defaultRotorMV
    let r2 := rotorsMV.getD idx2 defaultRotorMV
    MV.scalarPart (r1 * r2)

  IO.println ""

def benchSandwich : IO Unit := do
  IO.println "=== Sandwich Product ==="
  let samples : Nat := 16

  let rotors : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testRotor (0.05 * Float.ofNat (k.val + 1))
  let rotorsMV : Array (MV R3 .even) :=
    Array.ofFn (n := samples) fun k =>
      testRotorMV (0.05 * Float.ofNat (k.val + 1))
  let vecs : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testVector (Float.ofNat (k.val + 1))
  let vecsMV : Array (MV R3 .odd) :=
    Array.ofFn (n := samples) fun k =>
      testVectorMV (Float.ofNat (k.val + 1))

  let defaultRotor := testRotor 0.5
  let defaultRotorMV := testRotorMV 0.5
  let defaultVec := testVector 1.0
  let defaultVecMV := testVectorMV 1.0

  let _ ← timeit "Naive sandwich (Multivector)" warmupIters iters fun i =>
    let idx := i % samples
    let R := rotors.getD idx defaultRotor
    let v := vecs.getD idx defaultVec
    (R.sandwich v).scalarPart

  let _ ← timeit "MV sandwich (DataArray)" warmupIters iters fun i =>
    let idx := i % samples
    let R := rotorsMV.getD idx defaultRotorMV
    let v := vecsMV.getD idx defaultVecMV
    MV.scalarPart (mvSandwich R v)

  IO.println ""

def benchPGA3Motor : IO Unit := do
  IO.println "=== PGA3 Motor Composition ==="
  let samples : Nat := 16

  let motorsMV : Array (MV PGA3 .even) :=
    Array.ofFn (n := samples) fun k =>
      testMotorMV (0.05 * Float.ofNat (k.val + 1))

  let defaultMotorMV := testMotorMV 0.3

  let _ ← timeit "MV motor mul (PGA3)" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m1 := motorsMV.getD idx defaultMotorMV
    let m2 := motorsMV.getD idx2 defaultMotorMV
    MV.scalarPart (m1 * m2)

  IO.println ""

/-- Run all benchmarks -/
def runAll : IO Unit := do
  IO.println "╔════════════════════════════════════════════════════════════╗"
  IO.println "║      Grassmann MV (DataArray) Benchmarks                   ║"
  IO.println "╚════════════════════════════════════════════════════════════╝"
  IO.println ""

  verifyCorrectness
  benchRotorComposition
  benchSandwich
  benchPGA3Motor

  IO.println "Done!"

/-! ## Hyperfine-friendly single operation runners -/

def singleBenchIters : Nat := 1000000

/-- Run naive (Multivector) rotor mul -/
def runNaiveRotor (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let rotors : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testRotor (0.05 * Float.ofNat (k.val + 1))
  let defaultRotor := testRotor 0.3
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let r1 := rotors.getD idx defaultRotor
    let r2 := rotors.getD idx2 defaultRotor
    (r1 * r2).scalarPart
  blackhole result

/-- Run MV rotor mul -/
def runMVRotor (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let rotorsMV : Array (MV R3 .even) :=
    Array.ofFn (n := samples) fun k =>
      testRotorMV (0.05 * Float.ofNat (k.val + 1))
  let defaultRotorMV := testRotorMV 0.3
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let r1 := rotorsMV.getD idx defaultRotorMV
    let r2 := rotorsMV.getD idx2 defaultRotorMV
    MV.scalarPart (r1 * r2)
  blackhole result

/-- Run naive sandwich -/
def runNaiveSandwich (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let rotors : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testRotor (0.05 * Float.ofNat (k.val + 1))
  let vecs : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testVector (Float.ofNat (k.val + 1))
  let defaultRotor := testRotor 0.5
  let defaultVec := testVector 1.0
  let result := runN iters fun i =>
    let idx := i % samples
    let R := rotors.getD idx defaultRotor
    let v := vecs.getD idx defaultVec
    (R.sandwich v).scalarPart
  blackhole result

/-- Run MV sandwich -/
def runMVSandwich (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let rotorsMV : Array (MV R3 .even) :=
    Array.ofFn (n := samples) fun k =>
      testRotorMV (0.05 * Float.ofNat (k.val + 1))
  let vecsMV : Array (MV R3 .odd) :=
    Array.ofFn (n := samples) fun k =>
      testVectorMV (Float.ofNat (k.val + 1))
  let defaultRotorMV := testRotorMV 0.5
  let defaultVecMV := testVectorMV 1.0
  let result := runN iters fun i =>
    let idx := i % samples
    let R := rotorsMV.getD idx defaultRotorMV
    let v := vecsMV.getD idx defaultVecMV
    MV.scalarPart (mvSandwich R v)
  blackhole result

/-- Run MV PGA3 motor mul -/
def runMVMotor (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let motorsMV : Array (MV PGA3 .even) :=
    Array.ofFn (n := samples) fun k =>
      testMotorMV (0.05 * Float.ofNat (k.val + 1))
  let defaultMotorMV := testMotorMV 0.3
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m1 := motorsMV.getD idx defaultMotorMV
    let m2 := motorsMV.getD idx2 defaultMotorMV
    MV.scalarPart (m1 * m2)
  blackhole result

end Grassmann.Bench

/-- Main entry point -/
def main (args : List String) : IO Unit := do
  let parseNatArg (s : String) : IO Nat := do
    match s.toNat? with
    | some n => pure n
    | none =>
      IO.println s!"Invalid iteration count: {s}"
      throw (IO.userError "invalid iters")
  match args with
  | [] => Grassmann.Bench.runAll
  | ["all"] => Grassmann.Bench.runAll
  | ["verify"] => Grassmann.Bench.verifyCorrectness
  | ["naive-rotor"] => Grassmann.Bench.runNaiveRotor
  | ["naive-rotor", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runNaiveRotor iters
  | ["mv-rotor"] => Grassmann.Bench.runMVRotor
  | ["mv-rotor", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runMVRotor iters
  | ["naive-sandwich"] => Grassmann.Bench.runNaiveSandwich
  | ["naive-sandwich", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runNaiveSandwich iters
  | ["mv-sandwich"] => Grassmann.Bench.runMVSandwich
  | ["mv-sandwich", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runMVSandwich iters
  | ["mv-motor"] => Grassmann.Bench.runMVMotor
  | ["mv-motor", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runMVMotor iters
  | _ => do
    IO.println "Usage: bench [command]"
    IO.println ""
    IO.println "Commands:"
    IO.println "  all               Run all benchmarks (default)"
    IO.println "  verify            Run correctness verification only"
    IO.println "  naive-rotor [n]   Multivector rotor mul (proof-friendly)"
    IO.println "  mv-rotor [n]      MV rotor mul (DataArray-backed)"
    IO.println "  naive-sandwich [n] Multivector sandwich"
    IO.println "  mv-sandwich [n]   MV sandwich"
    IO.println "  mv-motor [n]      MV PGA3 motor mul"
    IO.println ""
    IO.println "Example:"
    IO.println "  hyperfine '.lake/build/bin/bench naive-rotor' '.lake/build/bin/bench mv-rotor'"

/-
  Grassmann/Bench.lean - Benchmarks for optimization comparison

  Compare naive vs optimized implementations:
  1. Geometric product: naive vs table-based
  2. Sandwich: naive vs sparse
  3. Rotor composition: naive vs even-only
  4. Vector squared: full product vs O(n)

  ## Running Benchmarks

  ### Via `#eval` (interpreter - NOT for timing, only correctness)
  ```
  #eval Grassmann.Bench.verifyCorrectness
  ```

  ### Compiled benchmarks (for accurate timing)
  ```bash
  lake build bench && .lake/build/bin/bench
  ```

  ### Hyperfine comparison (recommended for accurate timing)
  ```bash
  lake build bench
  hyperfine \
    '.lake/build/bin/bench naive-geo' \
    '.lake/build/bin/bench table-geo' \
    '.lake/build/bin/bench sparse-sandwich' \
    --warmup 3
  ```
-/
import Grassmann.StaticOpt
import Grassmann.BladeIndex
import Grassmann.SignTables
import Grassmann.EvenMV

namespace Grassmann.Bench

/-! ## Test Data Setup -/

/-- Create a test R3 vector -/
@[noinline]
def testVector (seed : Float) : Multivector R3 Float :=
  ⟨fun i =>
    if i.val = 1 then seed * 1.5
    else if i.val = 2 then seed * 0.7
    else if i.val = 4 then seed * 1.2
    else 0.0⟩

/-- Create a test R3 rotor (scalar + bivector) -/
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

/-- Create a test PGA3 motor -/
@[noinline]
def testMotor (angle : Float) : Multivector PGA3 Float :=
  let c := Float.cos (angle / 2)
  let s := Float.sin (angle / 2)
  ⟨fun i =>
    if i.val = 0 then c           -- scalar
    else if i.val = 3 then s * 0.577  -- bivector components
    else if i.val = 5 then s * 0.577
    else if i.val = 6 then s * 0.577
    else 0.0⟩

/-- Create a test PGA3 point (grade 3): e123 + x·e023 + y·e031 + z·e012. -/
@[noinline]
def testPoint (seed : Float) : Multivector PGA3 Float :=
  ⟨fun i =>
    if i.val = 7 then 1.0                -- e123
    else if i.val = 14 then seed * 1.1   -- e023
    else if i.val = 13 then seed * 0.9   -- e031
    else if i.val = 11 then seed * 0.7   -- e012
    else 0.0⟩

/-- Create a test PGA3 plane (grade 1): a·e1 + b·e2 + c·e3 + d·e0. -/
@[noinline]
def testPlane (seed : Float) : Multivector PGA3 Float :=
  ⟨fun i =>
    if i.val = 1 then seed * 1.0    -- e1
    else if i.val = 2 then seed * 0.7  -- e2
    else if i.val = 4 then seed * 0.4  -- e3
    else if i.val = 8 then seed * 0.9  -- e0
    else 0.0⟩

/-- Create a test PGA3 line (grade 2): direction (e23,e31,e12) + moment (e01,e02,e03). -/
@[noinline]
def testLine (seed : Float) : Multivector PGA3 Float :=
  ⟨fun i =>
    if i.val = 6 then seed * 0.3     -- e23
    else if i.val = 5 then seed * 0.25  -- e31
    else if i.val = 3 then seed * 0.2   -- e12
    else if i.val = 9 then seed * 0.6   -- e01
    else if i.val = 10 then seed * 0.5  -- e02
    else if i.val = 12 then seed * 0.4  -- e03
    else 0.0⟩

/-! ## Benchmark Helpers -/

/-- Run function n times with varying index.
    Passing the index prevents the compiler from hoisting the work. -/
@[noinline]
def runN (n : Nat) (f : Nat → Float) : Float :=
  let rec go (i : Nat) (acc : Float) : Float :=
    if i = 0 then acc
    else
      let i' := i - 1
      go i' (acc + f i')
  go n 0.0

/-- Warmup: run a few iterations to warm caches -/
@[noinline]
def warmup (n : Nat) (f : Nat → Float) : IO Unit := do
  let _ := runN n f
  pure ()

/-- Black hole to prevent optimizer from eliminating computation -/
@[noinline]
def blackhole (x : Float) : IO Unit := do
  if x.isNaN then
    IO.println "nan" -- Never happens but prevents elimination
  pure ()

/-- Simple timing with warmup: run and report -/
def timeit (name : String) (warmupIters : Nat) (iters : Nat) (f : Nat → Float) : IO Float := do
  -- Warmup phase
  warmup warmupIters f

  -- Timed phase
  let start ← IO.monoNanosNow
  -- Salt derived from start prevents the compiler from hoisting `runN`
  -- outside the timed region.
  let salt : Float := Float.ofNat (start % 1024)
  let result := runN iters fun i => f i + salt
  -- Force evaluation of `result` before stopping the timer.
  blackhole result
  let stop ← IO.monoNanosNow
  let elapsed : Nat := stop - start
  let perIterNs : Float := elapsed.toFloat / iters.toFloat
  let perIterStr := toString perIterNs
  let itersStr := Nat.repr iters
  let warmupStr := Nat.repr warmupIters
  IO.println (name ++ ": " ++ perIterStr ++ " ns/iter (" ++ itersStr ++ " iters, warmup " ++ warmupStr ++ ")")
  return result

/-! ## Correctness Verification -/

def verifyCorrectness : IO Unit := do
  IO.println "=== Correctness Verification ==="

  let rotor := testRotor 0.5
  let v := testVector 1.0
  let r1 := testRotor 0.3
  let r2 := testRotor 0.7
  let rotorPacked : EvenMV R3 Float := EvenMV.ofMultivectorEven rotor
  let r1Packed : EvenMV R3 Float := EvenMV.ofMultivectorEven r1
  let r2Packed : EvenMV R3 Float := EvenMV.ofMultivectorEven r2
  let m1 := testMotor 0.3
  let m2 := testMotor 0.7
  let m1Packed : EvenMV PGA3 Float := EvenMV.ofMultivectorEven m1
  let m2Packed : EvenMV PGA3 Float := EvenMV.ofMultivectorEven m2
  let motor := testMotor 0.5
  let motorPacked : EvenMV PGA3 Float := EvenMV.ofMultivectorEven motor
  let p := testPoint 1.0
  let plane := testPlane 1.0
  let line := testLine 1.0

  -- Sandwich
  let naive_sandwich := rotor.sandwich v
  let sparse_sandwich := R3Fast.sandwichFast rotor v
  let packed_sandwich := EvenMV.sandwichVectorFast rotorPacked v
  let diff_sandwich := (List.finRange 8).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_sandwich.coeffs idx - sparse_sandwich.coeffs idx)
  IO.println s!"Sandwich diff: {diff_sandwich}"
  let diff_packed_sandwich := (List.finRange 8).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_sandwich.coeffs idx - packed_sandwich.coeffs idx)
  IO.println s!"Packed sandwich diff: {diff_packed_sandwich}"

  -- Rotor mul
  let naive_rotor := r1 * r2
  let sparse_rotor := R3Fast.rotorMul r1 r2
  let packed_rotor := (r1Packed * r2Packed).toMultivector
  let diff_rotor := (List.finRange 8).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_rotor.coeffs idx - sparse_rotor.coeffs idx)
  IO.println s!"Rotor mul diff: {diff_rotor}"
  let diff_packed_rotor := (List.finRange 8).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_rotor.coeffs idx - packed_rotor.coeffs idx)
  IO.println s!"Packed rotor diff: {diff_packed_rotor}"

  -- PGA3 motor mul
  let naive_motor := m1 * m2
  let sparse_motor := PGA3Fast.motorMul m1 m2
  let packed_motor := (m1Packed * m2Packed).toMultivector
  let diff_motor := (List.finRange 16).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_motor.coeffs idx - sparse_motor.coeffs idx)
  IO.println s!"Motor mul diff: {diff_motor}"
  let diff_packed_motor := (List.finRange 16).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_motor.coeffs idx - packed_motor.coeffs idx)
  IO.println s!"Packed motor diff: {diff_packed_motor}"

  -- PGA3 point transform
  let naive_point := motor.sandwich p
  let sparse_point := PGA3Fast.transformPoint motor p
  let packed_point :=
    EvenMV.sandwichGradeSetFast (sig := PGA3) (n := 4) (F := Float)
      motorPacked p (GradeSet.singleton 3) (GradeSet.odd 4)
  let packed_point_g3 :=
    EvenMV.sandwichGradeSetFastOut (sig := PGA3) (n := 4) (F := Float)
      motorPacked p (GradeSet.singleton 3) (GradeSet.odd 4) (GradeSet.singleton 3)
  let diff_point := (List.finRange 16).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_point.coeffs idx - sparse_point.coeffs idx)
  IO.println s!"Point transform diff: {diff_point}"
  let diff_packed_point := (List.finRange 16).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_point.coeffs idx - packed_point.coeffs idx)
  IO.println s!"Packed point transform diff: {diff_packed_point}"
  let diff_packed_point_g3 := (List.finRange 16).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_point.coeffs idx - packed_point_g3.coeffs idx)
  IO.println s!"Packed point transform (grade3) diff: {diff_packed_point_g3}"

  -- PGA3 plane transform (grade 1)
  let naive_plane := motor.sandwich plane
  let sparse_plane := PGA3Fast.transformPlane motor plane
  let packed_plane :=
    EvenMV.sandwichGradeSetFast (sig := PGA3) (n := 4) (F := Float)
      motorPacked plane GradeSet.vector (GradeSet.odd 4)
  let packed_plane_g1 :=
    EvenMV.sandwichGradeSetFastOut (sig := PGA3) (n := 4) (F := Float)
      motorPacked plane GradeSet.vector (GradeSet.odd 4) GradeSet.vector
  let diff_plane := (List.finRange 16).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_plane.coeffs idx - sparse_plane.coeffs idx)
  IO.println s!"Plane transform diff: {diff_plane}"
  let diff_packed_plane := (List.finRange 16).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_plane.coeffs idx - packed_plane.coeffs idx)
  IO.println s!"Packed plane transform diff: {diff_packed_plane}"
  let diff_packed_plane_g1 := (List.finRange 16).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_plane.coeffs idx - packed_plane_g1.coeffs idx)
  IO.println s!"Packed plane transform (grade1) diff: {diff_packed_plane_g1}"

  -- PGA3 line transform (grade 2)
  let naive_line := motor.sandwich line
  let sparse_line := PGA3Fast.transformLine motor line
  let packed_line :=
    EvenMV.sandwichGradeSetFast (sig := PGA3) (n := 4) (F := Float)
      motorPacked line GradeSet.bivector (GradeSet.even 4)
  let packed_line_g2 :=
    EvenMV.sandwichGradeSetFastOut (sig := PGA3) (n := 4) (F := Float)
      motorPacked line GradeSet.bivector (GradeSet.even 4) GradeSet.bivector
  let diff_line := (List.finRange 16).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_line.coeffs idx - sparse_line.coeffs idx)
  IO.println s!"Line transform diff: {diff_line}"
  let diff_packed_line := (List.finRange 16).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_line.coeffs idx - packed_line.coeffs idx)
  IO.println s!"Packed line transform diff: {diff_packed_line}"
  let diff_packed_line_g2 := (List.finRange 16).foldl (init := 0.0) fun acc idx =>
    acc + Float.abs (naive_line.coeffs idx - packed_line_g2.coeffs idx)
  IO.println s!"Packed line transform (grade2) diff: {diff_packed_line_g2}"

  -- Vector squared
  let naive_vsq := (v * v).scalarPart
  let opt_vsq := vectorSquaredScalar v
  IO.println s!"Vector squared diff: {Float.abs (naive_vsq - opt_vsq)}"

  IO.println ""

/-! ## Benchmarks -/

def warmupIters : Nat := 10000
def iters : Nat := 100000

def benchGeometricProduct : IO Unit := do
  IO.println "=== Geometric Product ==="
  let samples : Nat := 16
  let vecs : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testVector (Float.ofNat (k.val + 1))

  let _ ← timeit "Naive geometric" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let v1 := vecs.getD idx (testVector 1.0)
    let v2 := vecs.getD idx2 (testVector 2.0)
    (v1 * v2).scalarPart

  let _ ← timeit "Table geometric" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let v1 := vecs.getD idx (testVector 1.0)
    let v2 := vecs.getD idx2 (testVector 2.0)
    (Multivector.geometricProductWithTable R3SignTable v1 v2).scalarPart

  IO.println ""

def benchSandwich : IO Unit := do
  IO.println "=== Sandwich Product ==="
  let samples : Nat := 16
  let rotors : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testRotor (0.05 * Float.ofNat (k.val + 1))
  let rotorsPacked : Array (EvenMV R3 Float) :=
    rotors.map (fun r => EvenMV.ofMultivectorEven r)
  let vecs : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testVector (Float.ofNat (k.val + 1))

  let _ ← timeit "Naive sandwich" warmupIters iters fun i =>
    let idx := i % samples
    let R := rotors.getD idx (testRotor 0.5)
    let v := vecs.getD idx (testVector 1.0)
    (R.sandwich v).scalarPart

  let _ ← timeit "Table sandwich" warmupIters iters fun i =>
    let idx := i % samples
    let R := rotors.getD idx (testRotor 0.5)
    let v := vecs.getD idx (testVector 1.0)
    (sandwichWithTable R3SignTable R v).scalarPart

  let _ ← timeit "Packed sandwich" warmupIters iters fun i =>
    let idx := i % samples
    let R := rotorsPacked.getD idx (EvenMV.ofMultivectorEven (testRotor 0.5))
    let v := vecs.getD idx (testVector 1.0)
    (EvenMV.sandwichVectorFast R v).scalarPart

  let _ ← timeit "Sparse sandwich" warmupIters iters fun i =>
    let idx := i % samples
    let R := rotors.getD idx (testRotor 0.5)
    let v := vecs.getD idx (testVector 1.0)
    (R3Fast.sandwichFast R v).scalarPart

  IO.println ""

def benchRotorComposition : IO Unit := do
  IO.println "=== Rotor Composition ==="
  let samples : Nat := 16
  let rotors : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testRotor (0.05 * Float.ofNat (k.val + 1))
  let rotorsPacked : Array (EvenMV R3 Float) :=
    rotors.map (fun r => EvenMV.ofMultivectorEven r)

  let _ ← timeit "Naive rotor mul" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let r1 := rotors.getD idx (testRotor 0.3)
    let r2 := rotors.getD idx2 (testRotor 0.7)
    (r1 * r2).scalarPart

  let _ ← timeit "Even-only rotor" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let r1 := rotors.getD idx (testRotor 0.3)
    let r2 := rotors.getD idx2 (testRotor 0.7)
    (composeRotorsOpt r1 r2).scalarPart

  let _ ← timeit "Packed rotor mul" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let r1 := rotorsPacked.getD idx (EvenMV.ofMultivectorEven (testRotor 0.3))
    let r2 := rotorsPacked.getD idx2 (EvenMV.ofMultivectorEven (testRotor 0.7))
    (r1 * r2).scalarPart

  let _ ← timeit "Sparse rotor" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let r1 := rotors.getD idx (testRotor 0.3)
    let r2 := rotors.getD idx2 (testRotor 0.7)
    (R3Fast.rotorMul r1 r2).scalarPart

  IO.println ""

def benchVectorSquared : IO Unit := do
  IO.println "=== Vector Squared ==="
  let samples : Nat := 16
  let vecs : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testVector (Float.ofNat (k.val + 1))

  let _ ← timeit "Naive v*v" warmupIters iters fun i =>
    let idx := i % samples
    let v := vecs.getD idx (testVector 3.0)
    (v * v).scalarPart

  let _ ← timeit "Optimized v²" warmupIters iters fun i =>
    let idx := i % samples
    let v := vecs.getD idx (testVector 3.0)
    vectorSquaredScalar v

  IO.println ""

def benchWedge : IO Unit := do
  IO.println "=== Wedge Product ==="
  let samples : Nat := 16
  let vecs : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testVector (Float.ofNat (k.val + 1))

  let _ ← timeit "Naive wedge" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let v1 := vecs.getD idx (testVector 1.0)
    let v2 := vecs.getD idx2 (testVector 2.0)
    (v1 ⋀ᵐ v2).scalarPart

  let _ ← timeit "Sparse wedge" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let v1 := vecs.getD idx (testVector 1.0)
    let v2 := vecs.getD idx2 (testVector 2.0)
    (R3Fast.vectorWedge v1 v2).scalarPart

  IO.println ""

def benchPGA3Operations : IO Unit := do
  IO.println "=== PGA3 Operations ==="
  let samples : Nat := 16
  let motors : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testMotor (0.05 * Float.ofNat (k.val + 1))
  let motorsPacked : Array (EvenMV PGA3 Float) :=
    motors.map (fun m => EvenMV.ofMultivectorEven m)
  let points : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testPoint (Float.ofNat (k.val + 1))
  let planes : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testPlane (Float.ofNat (k.val + 1))
  let lines : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testLine (Float.ofNat (k.val + 1))

  let _ ← timeit "Naive motor mul" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m1 := motors.getD idx (testMotor 0.3)
    let m2 := motors.getD idx2 (testMotor 0.7)
    (m1 * m2).scalarPart

  let _ ← timeit "Sparse motor mul" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m1 := motors.getD idx (testMotor 0.3)
    let m2 := motors.getD idx2 (testMotor 0.7)
    (PGA3Fast.motorMul m1 m2).scalarPart

  let _ ← timeit "Packed motor mul" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m1 := motorsPacked.getD idx (EvenMV.ofMultivectorEven (testMotor 0.3))
    let m2 := motorsPacked.getD idx2 (EvenMV.ofMultivectorEven (testMotor 0.7))
    (m1 * m2).scalarPart

  let _ ← timeit "Naive point xform" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m := motors.getD idx (testMotor 0.5)
    let p := points.getD idx2 (testPoint 1.0)
    (m.sandwich p).coeffs ⟨14, by decide⟩

  let _ ← timeit "Sparse point xform" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m := motors.getD idx (testMotor 0.5)
    let p := points.getD idx2 (testPoint 1.0)
    (PGA3Fast.transformPoint m p).coeffs ⟨14, by decide⟩

  let _ ← timeit "Packed point xform" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m := motorsPacked.getD idx (EvenMV.ofMultivectorEven (testMotor 0.5))
    let p := points.getD idx2 (testPoint 1.0)
    let p' :=
      EvenMV.sandwichGradeSetFast (sig := PGA3) (n := 4) (F := Float)
        m p (GradeSet.singleton 3) (GradeSet.odd 4)
    p'.coeffs ⟨14, by decide⟩

  let _ ← timeit "Packed point xform (g3)" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m := motorsPacked.getD idx (EvenMV.ofMultivectorEven (testMotor 0.5))
    let p := points.getD idx2 (testPoint 1.0)
    let p' :=
      EvenMV.sandwichGradeSetFastOut (sig := PGA3) (n := 4) (F := Float)
        m p (GradeSet.singleton 3) (GradeSet.odd 4) (GradeSet.singleton 3)
    p'.coeffs ⟨14, by decide⟩

  let _ ← timeit "Naive plane xform" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m := motors.getD idx (testMotor 0.5)
    let π := planes.getD idx2 (testPlane 1.0)
    (m.sandwich π).coeffs ⟨8, by decide⟩

  let _ ← timeit "Sparse plane xform" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m := motors.getD idx (testMotor 0.5)
    let π := planes.getD idx2 (testPlane 1.0)
    (PGA3Fast.transformPlane m π).coeffs ⟨8, by decide⟩

  let _ ← timeit "Packed plane xform (g1)" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m := motorsPacked.getD idx (EvenMV.ofMultivectorEven (testMotor 0.5))
    let π := planes.getD idx2 (testPlane 1.0)
    let π' :=
      EvenMV.sandwichGradeSetFastOut (sig := PGA3) (n := 4) (F := Float)
        m π GradeSet.vector (GradeSet.odd 4) GradeSet.vector
    π'.coeffs ⟨8, by decide⟩

  let _ ← timeit "Naive line xform" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m := motors.getD idx (testMotor 0.5)
    let l := lines.getD idx2 (testLine 1.0)
    (m.sandwich l).coeffs ⟨9, by decide⟩

  let _ ← timeit "Sparse line xform" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m := motors.getD idx (testMotor 0.5)
    let l := lines.getD idx2 (testLine 1.0)
    (PGA3Fast.transformLine m l).coeffs ⟨9, by decide⟩

  let _ ← timeit "Packed line xform (g2)" warmupIters iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m := motorsPacked.getD idx (EvenMV.ofMultivectorEven (testMotor 0.5))
    let l := lines.getD idx2 (testLine 1.0)
    let l' :=
      EvenMV.sandwichGradeSetFastOut (sig := PGA3) (n := 4) (F := Float)
        m l GradeSet.bivector (GradeSet.even 4) GradeSet.bivector
    l'.coeffs ⟨9, by decide⟩

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
  benchPGA3Operations

  IO.println "Done!"

/-! ## Hyperfine-friendly single operation runners

For accurate external timing with hyperfine, use these entry points:
```bash
hyperfine '.lake/build/bin/bench naive-geo' '.lake/build/bin/bench table-geo'
```
-/

def singleBenchIters : Nat := 1000000

/-- Run naive geometric product many times -/
def runNaiveGeo (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let vecs : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testVector (Float.ofNat (k.val + 1))
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let v1 := vecs.getD idx (testVector 1.0)
    let v2 := vecs.getD idx2 (testVector 2.0)
    (v1 * v2).scalarPart
  blackhole result

/-- Run table-based geometric product many times -/
def runTableGeo (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let vecs : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testVector (Float.ofNat (k.val + 1))
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let v1 := vecs.getD idx (testVector 1.0)
    let v2 := vecs.getD idx2 (testVector 2.0)
    (Multivector.geometricProductWithTable R3SignTable v1 v2).scalarPart
  blackhole result

/-- Run sparse sandwich many times -/
def runSparseSandwich (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let rotors : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testRotor (0.05 * Float.ofNat (k.val + 1))
  let vecs : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testVector (Float.ofNat (k.val + 1))
  let result := runN iters fun i =>
    let idx := i % samples
    let R := rotors.getD idx (testRotor 0.5)
    let v := vecs.getD idx (testVector 1.0)
    (R3Fast.sandwichFast R v).scalarPart
  blackhole result

/-- Run packed (EvenMV) sandwich many times. -/
def runPackedSandwich (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let rotors : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testRotor (0.05 * Float.ofNat (k.val + 1))
  let rotorsPacked : Array (EvenMV R3 Float) :=
    rotors.map (fun r => EvenMV.ofMultivectorEven r)
  let vecs : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testVector (Float.ofNat (k.val + 1))
  let result := runN iters fun i =>
    let idx := i % samples
    let R := rotorsPacked.getD idx (EvenMV.ofMultivectorEven (testRotor 0.5))
    let v := vecs.getD idx (testVector 1.0)
    (EvenMV.sandwichVectorFast R v).scalarPart
  blackhole result

/-- Run naive sandwich many times -/
def runNaiveSandwich (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let rotors : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testRotor (0.05 * Float.ofNat (k.val + 1))
  let vecs : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testVector (Float.ofNat (k.val + 1))
  let result := runN iters fun i =>
    let idx := i % samples
    let R := rotors.getD idx (testRotor 0.5)
    let v := vecs.getD idx (testVector 1.0)
    (R.sandwich v).scalarPart
  blackhole result

/-- Run sparse rotor mul many times -/
def runSparseRotor (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let rotors : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testRotor (0.05 * Float.ofNat (k.val + 1))
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let r1 := rotors.getD idx (testRotor 0.3)
    let r2 := rotors.getD idx2 (testRotor 0.7)
    (R3Fast.rotorMul r1 r2).scalarPart
  blackhole result

/-- Run packed (EvenMV) rotor mul many times. -/
def runPackedRotor (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let rotors : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testRotor (0.05 * Float.ofNat (k.val + 1))
  let rotorsPacked : Array (EvenMV R3 Float) :=
    rotors.map (fun r => EvenMV.ofMultivectorEven r)
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let r1 := rotorsPacked.getD idx (EvenMV.ofMultivectorEven (testRotor 0.3))
    let r2 := rotorsPacked.getD idx2 (EvenMV.ofMultivectorEven (testRotor 0.7))
    (r1 * r2).scalarPart
  blackhole result

/-- Run graded rotor mul many times (type-driven sparse kernel). -/
def runGradedRotor (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let rotors : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testRotor (0.05 * Float.ofNat (k.val + 1))
  let rotorsGraded : Array (GradedMV R3 Float (GradeSet.even 3)) :=
    rotors.map (fun r => GradedMV.ofEven r)
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let r1 := rotorsGraded.getD idx (GradedMV.ofEven (testRotor 0.3))
    let r2 := rotorsGraded.getD idx2 (GradedMV.ofEven (testRotor 0.7))
    ((r1 * r2).toMultivector).scalarPart
  blackhole result

/-- Run graded rotor mul many times (call `mulSparse` directly, bypassing `HMul`). -/
def runGradedRotorDirect (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let rotors : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testRotor (0.05 * Float.ofNat (k.val + 1))
  let rotorsGraded : Array (GradedMV R3 Float (GradeSet.even 3)) :=
    rotors.map (fun r => GradedMV.ofEven r)
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let r1 := rotorsGraded.getD idx (GradedMV.ofEven (testRotor 0.3))
    let r2 := rotorsGraded.getD idx2 (GradedMV.ofEven (testRotor 0.7))
    ((GradedMV.mulSparse r1 r2).toMultivector).scalarPart
  blackhole result

/-- Run optimized vector squared many times -/
def runOptVSq (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let vecs : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testVector (Float.ofNat (k.val + 1))
  let result := runN iters fun i =>
    let idx := i % samples
    let v := vecs.getD idx (testVector 3.0)
    vectorSquaredScalar v
  blackhole result

/-- Run sparse PGA3 motor mul many times. -/
def runSparseMotor (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let motors : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testMotor (0.05 * Float.ofNat (k.val + 1))
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m1 := motors.getD idx (testMotor 0.3)
    let m2 := motors.getD idx2 (testMotor 0.7)
    (PGA3Fast.motorMul m1 m2).scalarPart
  blackhole result

/-- Run packed (EvenMV) PGA3 motor mul many times. -/
def runPackedMotor (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let motors : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testMotor (0.05 * Float.ofNat (k.val + 1))
  let motorsPacked : Array (EvenMV PGA3 Float) :=
    motors.map (fun m => EvenMV.ofMultivectorEven m)
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m1 := motorsPacked.getD idx (EvenMV.ofMultivectorEven (testMotor 0.3))
    let m2 := motorsPacked.getD idx2 (EvenMV.ofMultivectorEven (testMotor 0.7))
    (m1 * m2).scalarPart
  blackhole result

/-- Run sparse PGA3 point transform many times. -/
def runSparsePointXform (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let motors : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testMotor (0.05 * Float.ofNat (k.val + 1))
  let points : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testPoint (Float.ofNat (k.val + 1))
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m := motors.getD idx (testMotor 0.5)
    let p := points.getD idx2 (testPoint 1.0)
    (PGA3Fast.transformPoint m p).coeffs ⟨14, by decide⟩
  blackhole result

/-- Run packed PGA3 point transform many times. -/
def runPackedPointXform (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let motors : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testMotor (0.05 * Float.ofNat (k.val + 1))
  let motorsPacked : Array (EvenMV PGA3 Float) :=
    motors.map (fun m => EvenMV.ofMultivectorEven m)
  let points : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testPoint (Float.ofNat (k.val + 1))
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m := motorsPacked.getD idx (EvenMV.ofMultivectorEven (testMotor 0.5))
    let p := points.getD idx2 (testPoint 1.0)
    let p' :=
      EvenMV.sandwichGradeSetFast (sig := PGA3) (n := 4) (F := Float)
        m p (GradeSet.singleton 3) (GradeSet.odd 4)
    p'.coeffs ⟨14, by decide⟩
  blackhole result

/-- Run packed PGA3 point transform many times (grade-3 output only). -/
def runPackedPointXformG3 (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let motors : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testMotor (0.05 * Float.ofNat (k.val + 1))
  let motorsPacked : Array (EvenMV PGA3 Float) :=
    motors.map (fun m => EvenMV.ofMultivectorEven m)
  let points : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testPoint (Float.ofNat (k.val + 1))
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m := motorsPacked.getD idx (EvenMV.ofMultivectorEven (testMotor 0.5))
    let p := points.getD idx2 (testPoint 1.0)
    let p' :=
      EvenMV.sandwichGradeSetFastOut (sig := PGA3) (n := 4) (F := Float)
        m p (GradeSet.singleton 3) (GradeSet.odd 4) (GradeSet.singleton 3)
    p'.coeffs ⟨14, by decide⟩
  blackhole result

/-- Run sparse PGA3 plane transform many times. -/
def runSparsePlaneXform (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let motors : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testMotor (0.05 * Float.ofNat (k.val + 1))
  let planes : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testPlane (Float.ofNat (k.val + 1))
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m := motors.getD idx (testMotor 0.5)
    let π := planes.getD idx2 (testPlane 1.0)
    (PGA3Fast.transformPlane m π).coeffs ⟨8, by decide⟩
  blackhole result

/-- Run packed PGA3 plane transform many times (grade-1 output only). -/
def runPackedPlaneXformG1 (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let motors : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testMotor (0.05 * Float.ofNat (k.val + 1))
  let motorsPacked : Array (EvenMV PGA3 Float) :=
    motors.map (fun m => EvenMV.ofMultivectorEven m)
  let planes : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testPlane (Float.ofNat (k.val + 1))
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m := motorsPacked.getD idx (EvenMV.ofMultivectorEven (testMotor 0.5))
    let π := planes.getD idx2 (testPlane 1.0)
    let π' :=
      EvenMV.sandwichGradeSetFastOut (sig := PGA3) (n := 4) (F := Float)
        m π GradeSet.vector (GradeSet.odd 4) GradeSet.vector
    π'.coeffs ⟨8, by decide⟩
  blackhole result

/-- Run sparse PGA3 line transform many times. -/
def runSparseLineXform (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let motors : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testMotor (0.05 * Float.ofNat (k.val + 1))
  let lines : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testLine (Float.ofNat (k.val + 1))
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m := motors.getD idx (testMotor 0.5)
    let l := lines.getD idx2 (testLine 1.0)
    (PGA3Fast.transformLine m l).coeffs ⟨9, by decide⟩
  blackhole result

/-- Run packed PGA3 line transform many times (grade-2 output only). -/
def runPackedLineXformG2 (iters : Nat := singleBenchIters) : IO Unit := do
  let samples : Nat := 16
  let motors : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testMotor (0.05 * Float.ofNat (k.val + 1))
  let motorsPacked : Array (EvenMV PGA3 Float) :=
    motors.map (fun m => EvenMV.ofMultivectorEven m)
  let lines : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k =>
      testLine (Float.ofNat (k.val + 1))
  let result := runN iters fun i =>
    let idx := i % samples
    let idx2 := (idx + 1) % samples
    let m := motorsPacked.getD idx (EvenMV.ofMultivectorEven (testMotor 0.5))
    let l := lines.getD idx2 (testLine 1.0)
    let l' :=
      EvenMV.sandwichGradeSetFastOut (sig := PGA3) (n := 4) (F := Float)
        m l GradeSet.bivector (GradeSet.even 4) GradeSet.bivector
    l'.coeffs ⟨9, by decide⟩
  blackhole result

end Grassmann.Bench

/-- Main entry point with subcommands for hyperfine benchmarking -/
def main (args : List String) : IO Unit := do
  let parseNatArg (s : String) : IO Nat := do
    match s.toNat? with
    | some n => pure n
    | none =>
      IO.println s!"Invalid iteration count: {s}"
      IO.println "Expected a natural number."
      throw (IO.userError "invalid iters")
  match args with
  | [] => Grassmann.Bench.runAll
  | ["all"] => Grassmann.Bench.runAll
  | ["verify"] => Grassmann.Bench.verifyCorrectness
  | ["naive-geo"] => Grassmann.Bench.runNaiveGeo
  | ["naive-geo", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runNaiveGeo iters
  | ["table-geo"] => Grassmann.Bench.runTableGeo
  | ["table-geo", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runTableGeo iters
  | ["sparse-sandwich"] => Grassmann.Bench.runSparseSandwich
  | ["sparse-sandwich", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runSparseSandwich iters
  | ["packed-sandwich"] => Grassmann.Bench.runPackedSandwich
  | ["packed-sandwich", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runPackedSandwich iters
  | ["naive-sandwich"] => Grassmann.Bench.runNaiveSandwich
  | ["naive-sandwich", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runNaiveSandwich iters
  | ["sparse-rotor"] => Grassmann.Bench.runSparseRotor
  | ["sparse-rotor", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runSparseRotor iters
  | ["packed-rotor"] => Grassmann.Bench.runPackedRotor
  | ["packed-rotor", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runPackedRotor iters
  | ["graded-rotor"] => Grassmann.Bench.runGradedRotor
  | ["graded-rotor", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runGradedRotor iters
  | ["graded-rotor-direct"] => Grassmann.Bench.runGradedRotorDirect
  | ["graded-rotor-direct", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runGradedRotorDirect iters
  | ["opt-vsq"] => Grassmann.Bench.runOptVSq
  | ["opt-vsq", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runOptVSq iters
  | ["sparse-motor"] => Grassmann.Bench.runSparseMotor
  | ["sparse-motor", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runSparseMotor iters
  | ["packed-motor"] => Grassmann.Bench.runPackedMotor
  | ["packed-motor", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runPackedMotor iters
  | ["sparse-point"] => Grassmann.Bench.runSparsePointXform
  | ["sparse-point", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runSparsePointXform iters
  | ["packed-point"] => Grassmann.Bench.runPackedPointXform
  | ["packed-point", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runPackedPointXform iters
  | ["packed-point-g3"] => Grassmann.Bench.runPackedPointXformG3
  | ["packed-point-g3", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runPackedPointXformG3 iters
  | ["sparse-plane"] => Grassmann.Bench.runSparsePlaneXform
  | ["sparse-plane", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runSparsePlaneXform iters
  | ["packed-plane-g1"] => Grassmann.Bench.runPackedPlaneXformG1
  | ["packed-plane-g1", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runPackedPlaneXformG1 iters
  | ["sparse-line"] => Grassmann.Bench.runSparseLineXform
  | ["sparse-line", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runSparseLineXform iters
  | ["packed-line-g2"] => Grassmann.Bench.runPackedLineXformG2
  | ["packed-line-g2", itersStr] =>
    let iters ← parseNatArg itersStr
    Grassmann.Bench.runPackedLineXformG2 iters
  | _ => do
    IO.println "Usage: bench [command]"
    IO.println ""
    IO.println "Commands:"
    IO.println "  all            Run all benchmarks (default)"
    IO.println "  verify         Run correctness verification only"
    IO.println "  naive-geo [iters]       Run naive geometric product (for hyperfine)"
    IO.println "  table-geo [iters]       Run table geometric product (for hyperfine)"
    IO.println "  sparse-sandwich [iters] Run sparse sandwich (for hyperfine)"
    IO.println "  packed-sandwich [iters] Run packed (EvenMV) sandwich (for hyperfine)"
    IO.println "  naive-sandwich [iters]  Run naive sandwich (for hyperfine)"
    IO.println "  sparse-rotor [iters]    Run sparse rotor mul (for hyperfine)"
    IO.println "  packed-rotor [iters]    Run packed (EvenMV) rotor mul (for hyperfine)"
    IO.println "  graded-rotor [iters]    Run graded rotor mul (for hyperfine)"
    IO.println "  graded-rotor-direct [iters] Run graded rotor mul (direct, for debugging)"
    IO.println "  opt-vsq [iters]         Run optimized v² (for hyperfine)"
    IO.println "  sparse-motor [iters]    Run sparse PGA3 motor mul (for hyperfine)"
    IO.println "  packed-motor [iters]    Run packed (EvenMV) PGA3 motor mul (for hyperfine)"
    IO.println "  sparse-point [iters]    Run sparse PGA3 point transform"
    IO.println "  packed-point [iters]    Run packed PGA3 point transform"
    IO.println "  packed-point-g3 [iters] Run packed PGA3 point transform (grade-3 only)"
    IO.println "  sparse-plane [iters]    Run sparse PGA3 plane transform"
    IO.println "  packed-plane-g1 [iters] Run packed PGA3 plane transform (grade-1 only)"
    IO.println "  sparse-line [iters]     Run sparse PGA3 line transform"
    IO.println "  packed-line-g2 [iters]  Run packed PGA3 line transform (grade-2 only)"
    IO.println ""
    IO.println "Example with hyperfine:"
    IO.println "  hyperfine '.lake/build/bin/bench naive-geo 200000' '.lake/build/bin/bench table-geo 200000'"

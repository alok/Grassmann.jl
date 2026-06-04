/-
  RunPackedMVBench.lean - Focused benchmarks for packed MV exterior/interior products.

  Run from Grassmann4 with:
    lake exe packedmvbench [base-iters]
-/
import Grassmann.MV

namespace Grassmann.PackedMVBench

def tolerance : Float := 1e-6
def defaultBaseIters : Nat := 20000

@[inline]
def coeffPattern (seed : Float) (mask : Nat) : Float :=
  let k := Float.ofNat (mask + 1)
  Float.sin (seed * (0.17 * k)) + Float.cos ((seed + 0.5) * (0.11 * k))

@[noinline]
def denseR3 (seed : Float) : Multivector R3 Float :=
  ⟨fun i => coeffPattern seed i.val⟩

@[noinline]
def densePGA3 (seed : Float) : Multivector PGA3 Float :=
  ⟨fun i => coeffPattern seed i.val⟩

@[noinline]
def denseCGA3 (seed : Float) : Multivector CGA3 Float :=
  ⟨fun i => coeffPattern seed i.val⟩

@[inline]
def denseCoeff {n : Nat} {sig : Signature n} (m : Multivector sig Float)
    (mask : Nat) : Float :=
  if h : mask < 2 ^ n then
    m.coeffs ⟨mask, h⟩
  else
    0.0

@[inline]
def denseProbe {n : Nat} {sig : Signature n} (m : Multivector sig Float) : Float :=
  m.scalarPart + denseCoeff m 1 + denseCoeff m 2 + denseCoeff m 3 +
    denseCoeff m 5 + denseCoeff m 7 + denseCoeff m 15 + denseCoeff m 31

@[inline]
def packedProbe {n : Nat} {sig : Signature n} {p : Parity} (m : MV sig p) : Float :=
  MV.scalarPart m + m.coeff 1 + m.coeff 2 + m.coeff 3 +
    m.coeff 5 + m.coeff 7 + m.coeff 15 + m.coeff 31

def denseL1Diff {n : Nat} {sig : Signature n}
    (a b : Multivector sig Float) : Float :=
  (List.finRange (2 ^ n)).foldl (init := 0.0) fun acc i =>
    acc + Float.abs (a.coeffs i - b.coeffs i)

def requireApproxDense {n : Nat} {sig : Signature n}
    (name : String) (actual expected : Multivector sig Float) : IO Unit := do
  let diff := denseL1Diff actual expected
  IO.println s!"{name}: l1 diff {diff}"
  if diff.isNaN || diff > tolerance then
    throw <| IO.userError s!"{name} exceeded tolerance {tolerance}: {diff}"

def verifyR3 : IO Unit := do
  let a := denseR3 1.0
  let b := denseR3 2.0
  let pa : MV R3 .full := MV.ofMultivector a .full
  let pb : MV R3 .full := MV.ofMultivector b .full
  requireApproxDense "R3 full wedge"
    (MV.toMultivector (MV.wedge pa pb))
    (Multivector.wedgeProduct a b)
  requireApproxDense "R3 full left contraction"
    (MV.toMultivector (MV.leftContract pa pb))
    (Multivector.leftContract a b)
  requireApproxDense "R3 full right contraction"
    (MV.toMultivector (MV.rightContract pa pb))
    (Multivector.rightContract a b)

def verifyPGA3 : IO Unit := do
  let a := densePGA3 1.25
  let b := densePGA3 2.25
  let pa : MV PGA3 .full := MV.ofMultivector a .full
  let pb : MV PGA3 .full := MV.ofMultivector b .full
  requireApproxDense "PGA3 full wedge"
    (MV.toMultivector (MV.wedge pa pb))
    (Multivector.wedgeProduct a b)
  requireApproxDense "PGA3 full left contraction"
    (MV.toMultivector (MV.leftContract pa pb))
    (Multivector.leftContract a b)
  requireApproxDense "PGA3 full right contraction"
    (MV.toMultivector (MV.rightContract pa pb))
    (Multivector.rightContract a b)

def verifyCGA3 : IO Unit := do
  let a := denseCGA3 1.5
  let b := denseCGA3 2.5
  let pa : MV CGA3 .full := MV.ofMultivector a .full
  let pb : MV CGA3 .full := MV.ofMultivector b .full
  requireApproxDense "CGA3 full wedge"
    (MV.toMultivector (MV.wedge pa pb))
    (Multivector.wedgeProduct a b)
  requireApproxDense "CGA3 full left contraction"
    (MV.toMultivector (MV.leftContract pa pb))
    (Multivector.leftContract a b)
  requireApproxDense "CGA3 full right contraction"
    (MV.toMultivector (MV.rightContract pa pb))
    (Multivector.rightContract a b)

def verifyCorrectness : IO Unit := do
  IO.println "=== Correctness guard ==="
  verifyR3
  verifyPGA3
  verifyCGA3
  IO.println ""

@[noinline]
def runN (n : Nat) (f : Nat → Float) : Float :=
  let rec go (i : Nat) (acc : Float) : Float :=
    if i = 0 then acc
    else
      let i' := i - 1
      go i' (acc + f i')
  go n 0.0

@[noinline]
def blackhole (x : Float) : IO Unit := do
  if x.isNaN then
    IO.println "nan"
  pure ()

def timeit (name : String) (warmupIters iters : Nat) (f : Nat → Float) : IO Float := do
  let _ := runN warmupIters f
  let start ← IO.monoNanosNow
  let salt := Float.ofNat (start % 1024)
  let result := runN iters fun i => f i + salt
  blackhole result
  let stop ← IO.monoNanosNow
  let elapsed := stop - start
  let perIterNs := elapsed.toFloat / iters.toFloat
  IO.println s!"  {name}: {perIterNs} ns/iter ({iters} iters)"
  return perIterNs

def compare (denseName packedName : String) (warmupIters iters : Nat)
    (denseF packedF : Nat → Float) : IO Unit := do
  let denseNs ← timeit denseName warmupIters iters denseF
  let packedNs ← timeit packedName warmupIters iters packedF
  IO.println s!"  speedup: {denseNs / packedNs}x"
  IO.println ""

def positiveIters (n : Nat) : Nat :=
  if n = 0 then 1 else n

def runR3 (iters : Nat) : IO Unit := do
  IO.println "=== R3 full packed products ==="
  let samples : Nat := 16
  let denseA : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k => denseR3 (Float.ofNat (k.val + 1))
  let denseB : Array (Multivector R3 Float) :=
    Array.ofFn (n := samples) fun k => denseR3 (Float.ofNat (k.val + 17))
  let packedA : Array (MV R3 .full) := denseA.map fun m => MV.ofMultivector m .full
  let packedB : Array (MV R3 .full) := denseB.map fun m => MV.ofMultivector m .full
  let defaultA := denseR3 1.0
  let defaultB := denseR3 2.0
  let defaultPA : MV R3 .full := MV.ofMultivector defaultA .full
  let defaultPB : MV R3 .full := MV.ofMultivector defaultB .full
  let warmup := positiveIters (iters / 10)
  compare "dense wedge" "packed MV wedge" warmup iters
    (fun i =>
      let idx := i % samples
      denseProbe (Multivector.wedgeProduct (denseA.getD idx defaultA) (denseB.getD idx defaultB)))
    (fun i =>
      let idx := i % samples
      packedProbe (MV.wedge (packedA.getD idx defaultPA) (packedB.getD idx defaultPB)))
  compare "dense left contraction" "packed MV left contraction" warmup iters
    (fun i =>
      let idx := i % samples
      denseProbe (Multivector.leftContract (denseA.getD idx defaultA) (denseB.getD idx defaultB)))
    (fun i =>
      let idx := i % samples
      packedProbe (MV.leftContract (packedA.getD idx defaultPA) (packedB.getD idx defaultPB)))
  compare "dense right contraction" "packed MV right contraction" warmup iters
    (fun i =>
      let idx := i % samples
      denseProbe (Multivector.rightContract (denseA.getD idx defaultA) (denseB.getD idx defaultB)))
    (fun i =>
      let idx := i % samples
      packedProbe (MV.rightContract (packedA.getD idx defaultPA) (packedB.getD idx defaultPB)))

def runPGA3 (iters : Nat) : IO Unit := do
  IO.println "=== PGA3 full packed products ==="
  let samples : Nat := 16
  let denseA : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k => densePGA3 (Float.ofNat (k.val + 1))
  let denseB : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k => densePGA3 (Float.ofNat (k.val + 17))
  let packedA : Array (MV PGA3 .full) := denseA.map fun m => MV.ofMultivector m .full
  let packedB : Array (MV PGA3 .full) := denseB.map fun m => MV.ofMultivector m .full
  let defaultA := densePGA3 1.0
  let defaultB := densePGA3 2.0
  let defaultPA : MV PGA3 .full := MV.ofMultivector defaultA .full
  let defaultPB : MV PGA3 .full := MV.ofMultivector defaultB .full
  let warmup := positiveIters (iters / 10)
  compare "dense wedge" "packed MV wedge" warmup iters
    (fun i =>
      let idx := i % samples
      denseProbe (Multivector.wedgeProduct (denseA.getD idx defaultA) (denseB.getD idx defaultB)))
    (fun i =>
      let idx := i % samples
      packedProbe (MV.wedge (packedA.getD idx defaultPA) (packedB.getD idx defaultPB)))
  compare "dense left contraction" "packed MV left contraction" warmup iters
    (fun i =>
      let idx := i % samples
      denseProbe (Multivector.leftContract (denseA.getD idx defaultA) (denseB.getD idx defaultB)))
    (fun i =>
      let idx := i % samples
      packedProbe (MV.leftContract (packedA.getD idx defaultPA) (packedB.getD idx defaultPB)))
  compare "dense right contraction" "packed MV right contraction" warmup iters
    (fun i =>
      let idx := i % samples
      denseProbe (Multivector.rightContract (denseA.getD idx defaultA) (denseB.getD idx defaultB)))
    (fun i =>
      let idx := i % samples
      packedProbe (MV.rightContract (packedA.getD idx defaultPA) (packedB.getD idx defaultPB)))

def runCGA3 (iters : Nat) : IO Unit := do
  IO.println "=== CGA3 full packed products ==="
  let samples : Nat := 16
  let denseA : Array (Multivector CGA3 Float) :=
    Array.ofFn (n := samples) fun k => denseCGA3 (Float.ofNat (k.val + 1))
  let denseB : Array (Multivector CGA3 Float) :=
    Array.ofFn (n := samples) fun k => denseCGA3 (Float.ofNat (k.val + 17))
  let packedA : Array (MV CGA3 .full) := denseA.map fun m => MV.ofMultivector m .full
  let packedB : Array (MV CGA3 .full) := denseB.map fun m => MV.ofMultivector m .full
  let defaultA := denseCGA3 1.0
  let defaultB := denseCGA3 2.0
  let defaultPA : MV CGA3 .full := MV.ofMultivector defaultA .full
  let defaultPB : MV CGA3 .full := MV.ofMultivector defaultB .full
  let warmup := positiveIters (iters / 10)
  compare "dense wedge" "packed MV wedge" warmup iters
    (fun i =>
      let idx := i % samples
      denseProbe (Multivector.wedgeProduct (denseA.getD idx defaultA) (denseB.getD idx defaultB)))
    (fun i =>
      let idx := i % samples
      packedProbe (MV.wedge (packedA.getD idx defaultPA) (packedB.getD idx defaultPB)))
  compare "dense left contraction" "packed MV left contraction" warmup iters
    (fun i =>
      let idx := i % samples
      denseProbe (Multivector.leftContract (denseA.getD idx defaultA) (denseB.getD idx defaultB)))
    (fun i =>
      let idx := i % samples
      packedProbe (MV.leftContract (packedA.getD idx defaultPA) (packedB.getD idx defaultPB)))
  compare "dense right contraction" "packed MV right contraction" warmup iters
    (fun i =>
      let idx := i % samples
      denseProbe (Multivector.rightContract (denseA.getD idx defaultA) (denseB.getD idx defaultB)))
    (fun i =>
      let idx := i % samples
      packedProbe (MV.rightContract (packedA.getD idx defaultPA) (packedB.getD idx defaultPB)))

def runAll (baseIters : Nat := defaultBaseIters) : IO Unit := do
  IO.println "===================================================="
  IO.println "      Packed MV Exterior/Interior Benchmarks"
  IO.println "===================================================="
  IO.println ""
  verifyCorrectness
  runR3 (positiveIters baseIters)
  runPGA3 (positiveIters (baseIters / 2))
  runCGA3 (positiveIters (baseIters / 5))
  IO.println "Done!"

end Grassmann.PackedMVBench

def main (args : List String) : IO Unit := do
  match args with
  | [] => Grassmann.PackedMVBench.runAll
  | [itersStr] =>
      match itersStr.toNat? with
      | some iters => Grassmann.PackedMVBench.runAll iters
      | none => throw <| IO.userError s!"Invalid iteration count: {itersStr}"
  | _ =>
      throw <| IO.userError "Usage: packedmvbench [base-iters]"

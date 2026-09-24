/-
  RunPackedMVBench.lean - Focused benchmarks for packed MV exterior/interior products.

  Run from Grassmann4 with:
    lake exe packedmvbench [base-iters]
-/
import Grassmann.MVDense
import Grassmann.PGA

namespace Grassmann.PackedMVBench

def tolerance : Float := 1e-6
def defaultBaseIters : Nat := 20000
def defaultMotorPointIters : Nat := 100000
def defaultSubtractionIters : Nat := 250000
def defaultLinearArithmeticIters : Nat := 500000
def defaultUnaryInvolutionIters : Nat := 100000
def defaultHodgeDualIters : Nat := 100000
def defaultProjectionWideningIters : Nat := 100000
def defaultDenseIngressIters : Nat := 100000
def defaultGenericProductIters : Nat := 2000
def defaultXYZBatchPoints : Nat := 4096
def defaultXYZBatchIters : Nat := 100

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

@[noinline]
def densePGA3Motor (seed : Float) : Multivector PGA3 Float :=
  PGA.Proof.rotor 0.25 0.5 1.0 (0.05 * seed)

@[noinline]
def packedPGA3Motor (seed : Float) : PGA.Motor PGA3 :=
  PGA.motor3 0.25 0.5 1.0 (0.05 * seed)

@[noinline]
def densePGA3Point (seed : Float) : Multivector PGA3 Float :=
  PGA.Proof.point (0.7 * seed) (Float.sin seed) (Float.cos (seed * 0.5))

@[noinline]
def packedPGA3Point (seed : Float) : PGA.Point PGA3 :=
  PGA.point3 (0.7 * seed) (Float.sin seed) (Float.cos (seed * 0.5))

def packedXYZInput (pointCount : Nat) (offset : Float := 0.0) : FloatArray := Id.run do
  let mut xyz := FloatArray.emptyWithCapacity (pointCount * 3)
  for i in [0:pointCount] do
    let seed := Float.ofNat (i + 1) + offset
    xyz := xyz
      |>.push (0.7 * seed)
      |>.push (Float.sin seed)
      |>.push (Float.cos (seed * 0.5))
  return xyz

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

@[inline]
def packedDataProbe (a : @& DataArray) : Float :=
  a.get! 0 + a.get! 1 + a.get! 2 + a.get! 3 +
    a.get! 7 + a.get! 15 + a.get! 23 + a.get! 31

@[inline]
def packedHalfDataProbe (a : @& DataArray) : Float :=
  a.get! 0 + a.get! 1 + a.get! 2 + a.get! 3 +
    a.get! 7 + a.get! 11 + a.get! 13 + a.get! 15

def dataL1Diff (a b : @& DataArray) : Float :=
  if a.size != b.size then
    1e300
  else
    (List.range a.size).foldl (init := 0.0) fun acc i =>
      acc + Float.abs (a.get! i - b.get! i)

def denseL1Diff {n : Nat} {sig : Signature n}
    (a b : Multivector sig Float) : Float :=
  (List.finRange (2 ^ n)).foldl (init := 0.0) fun acc i =>
    acc + Float.abs (a.coeffs i - b.coeffs i)

@[inline]
def coordProbe (c : Float × Float × Float) : Float :=
  c.1 + c.2.1 + c.2.2

def coordL1Diff (a b : Float × Float × Float) : Float :=
  Float.abs (a.1 - b.1) +
    Float.abs (a.2.1 - b.2.1) +
    Float.abs (a.2.2 - b.2.2)

def requireApproxDense {n : Nat} {sig : Signature n}
    (name : String) (actual expected : Multivector sig Float) : IO Unit := do
  let diff := denseL1Diff actual expected
  IO.println s!"{name}: l1 diff {diff}"
  if diff.isNaN || diff > tolerance then
    throw <| IO.userError s!"{name} exceeded tolerance {tolerance}: {diff}"

def requireApproxCoords (name : String) (actual expected : Float × Float × Float) : IO Unit := do
  let diff := coordL1Diff actual expected
  IO.println s!"{name}: coord l1 diff {diff}"
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

def verifyPGA3MotorPointTransform : IO Unit := do
  let denseMotor := densePGA3Motor 3.0
  let packedMotor := packedPGA3Motor 3.0
  let densePoint := densePGA3Point 2.0
  let packedPoint := packedPGA3Point 2.0
  requireApproxCoords "PGA3 motor point transform"
    (PGA.extractPoint3 (PGA.Motor.transformPoint packedMotor packedPoint))
    (PGA.Proof.extractPoint (PGA.Proof.applyMotor denseMotor densePoint))

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
  requireApproxDense "CGA3 packed subtraction"
    (MV.toMultivector (pa - pb))
    (a - b)

def verifyCorrectness : IO Unit := do
  IO.println "=== Correctness guard ==="
  verifyR3
  verifyPGA3
  verifyPGA3MotorPointTransform
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

/-! ### Generic full-product baseline -/

/-- Keep the generic geometric kernel behind a stable call boundary. -/
@[noinline]
def genericMulFullData {n : Nat} (sig : Signature n)
    (a b : @& MV sig .full) : DataArray :=
  MV.mulKernelGeneric sig .full .full a.coeffs b.coeffs

/-- Keep the generic exterior kernel behind a stable call boundary. -/
@[noinline]
def genericWedgeFullData {n : Nat} (sig : Signature n)
    (a b : @& MV sig .full) : DataArray :=
  MV.wedgeKernelGeneric sig .full .full a.coeffs b.coeffs

/-- Keep the generic left-contraction kernel behind a stable call boundary. -/
@[noinline]
def genericLeftContractFullData {n : Nat} (sig : Signature n)
    (a b : @& MV sig .full) : DataArray :=
  MV.leftContractKernelGeneric sig .full .full a.coeffs b.coeffs

/-- Keep the generic right-contraction kernel behind a stable call boundary. -/
@[noinline]
def genericRightContractFullData {n : Nat} (sig : Signature n)
    (a b : @& MV sig .full) : DataArray :=
  MV.rightContractKernelGeneric sig .full .full a.coeffs b.coeffs

/-- Weighted checksum that observes every physical result coefficient. -/
@[noinline]
def productDataChecksum (data : @& DataArray) : Float :=
  (List.range data.size).foldl (init := 0.0) fun acc i =>
    acc + Float.ofNat (i + 1) * data.get! i

/-- The same weighted checksum over a dense full-layout reference. -/
def denseProductChecksum {n : Nat} {sig : Signature n}
    (m : Multivector sig Float) : Float :=
  (List.finRange (2 ^ n)).foldl (init := 0.0) fun acc i =>
    acc + Float.ofNat (i.val + 1) * m.coeffs i

/-- Compare a raw full packed result against every dense reference coefficient. -/
def productDataDenseL1Diff {n : Nat} {sig : Signature n}
    (actual : @& DataArray) (expected : Multivector sig Float) : Float :=
  if actual.size != 2 ^ n then
    1e300
  else
    (List.finRange (2 ^ n)).foldl (init := 0.0) fun acc i =>
      acc + Float.abs (actual.get! i.val - expected.coeffs i)

/--
Validate and time all four full-layout generic product kernels for one signature.

Sixteen varied inputs prevent one fixed expression from being constant-folded.
The preflight compares every coefficient with the independent dense API, while
the timed checksum consumes every physical output slot.
-/
def runGenericProductSignature {n : Nat} (label : String) (sig : Signature n)
    (makeDense : Float → Multivector sig Float) (iters : Nat) : IO Unit := do
  IO.println s!"=== {label} full generic packed products ==="
  let samples : Nat := 16
  let denseA : Array (Multivector sig Float) :=
    Array.ofFn (n := samples) fun k => makeDense (Float.ofNat (k.val + 1))
  let denseB : Array (Multivector sig Float) :=
    Array.ofFn (n := samples) fun k => makeDense (Float.ofNat (k.val + 17))
  let packedA : Array (MV sig .full) :=
    denseA.map fun m => MV.ofMultivector m .full
  let packedB : Array (MV sig .full) :=
    denseB.map fun m => MV.ofMultivector m .full
  let defaultDenseA := makeDense 1.0
  let defaultDenseB := makeDense 17.0
  let defaultPackedA : MV sig .full := MV.ofMultivector defaultDenseA .full
  let defaultPackedB : MV sig .full := MV.ofMultivector defaultDenseB .full
  let mut mulDiff := 0.0
  let mut wedgeDiff := 0.0
  let mut leftDiff := 0.0
  let mut rightDiff := 0.0
  let mut mulChecksum := 0.0
  let mut wedgeChecksum := 0.0
  let mut leftChecksum := 0.0
  let mut rightChecksum := 0.0
  let mut denseMulChecksum := 0.0
  let mut denseWedgeChecksum := 0.0
  let mut denseLeftChecksum := 0.0
  let mut denseRightChecksum := 0.0
  for i in [0:samples] do
    let denseLeft := denseA.getD i defaultDenseA
    let denseRight := denseB.getD i defaultDenseB
    let packedLeft := packedA.getD i defaultPackedA
    let packedRight := packedB.getD i defaultPackedB
    let actualMul := genericMulFullData sig packedLeft packedRight
    let actualWedge := genericWedgeFullData sig packedLeft packedRight
    let actualLeft := genericLeftContractFullData sig packedLeft packedRight
    let actualRight := genericRightContractFullData sig packedLeft packedRight
    let expectedMul := Multivector.geometricProduct denseLeft denseRight
    let expectedWedge := Multivector.wedgeProduct denseLeft denseRight
    let expectedLeft := Multivector.leftContract denseLeft denseRight
    let expectedRight := Multivector.rightContract denseLeft denseRight
    mulDiff := mulDiff + productDataDenseL1Diff actualMul expectedMul
    wedgeDiff := wedgeDiff + productDataDenseL1Diff actualWedge expectedWedge
    leftDiff := leftDiff + productDataDenseL1Diff actualLeft expectedLeft
    rightDiff := rightDiff + productDataDenseL1Diff actualRight expectedRight
    mulChecksum := mulChecksum + productDataChecksum actualMul
    wedgeChecksum := wedgeChecksum + productDataChecksum actualWedge
    leftChecksum := leftChecksum + productDataChecksum actualLeft
    rightChecksum := rightChecksum + productDataChecksum actualRight
    denseMulChecksum := denseMulChecksum + denseProductChecksum expectedMul
    denseWedgeChecksum := denseWedgeChecksum + denseProductChecksum expectedWedge
    denseLeftChecksum := denseLeftChecksum + denseProductChecksum expectedLeft
    denseRightChecksum := denseRightChecksum + denseProductChecksum expectedRight
  IO.println s!"  {label} generic mul l1 diff: {mulDiff}"
  IO.println s!"  {label} generic wedge l1 diff: {wedgeDiff}"
  IO.println s!"  {label} generic left contraction l1 diff: {leftDiff}"
  IO.println s!"  {label} generic right contraction l1 diff: {rightDiff}"
  IO.println s!"  {label} generic mul checksum: {mulChecksum} (dense {denseMulChecksum})"
  IO.println s!"  {label} generic wedge checksum: {wedgeChecksum} (dense {denseWedgeChecksum})"
  IO.println s!"  {label} generic left checksum: {leftChecksum} (dense {denseLeftChecksum})"
  IO.println s!"  {label} generic right checksum: {rightChecksum} (dense {denseRightChecksum})"
  let diffs := #[mulDiff, wedgeDiff, leftDiff, rightDiff]
  let checksumDiffs := #[
    Float.abs (mulChecksum - denseMulChecksum),
    Float.abs (wedgeChecksum - denseWedgeChecksum),
    Float.abs (leftChecksum - denseLeftChecksum),
    Float.abs (rightChecksum - denseRightChecksum)]
  let checksumTolerance := tolerance * Float.ofNat (samples * (2 ^ n) + 1)
  if diffs.any fun diff => diff.isNaN || diff > tolerance then
    throw <| IO.userError s!"{label} generic product dense-reference mismatch"
  if checksumDiffs.any fun diff => diff.isNaN || diff > checksumTolerance then
    throw <| IO.userError s!"{label} generic product checksum mismatch"
  let positive := positiveIters iters
  let warmup := positiveIters (positive / 10)
  let _ ← timeit s!"generic {label} full mul" warmup positive fun i =>
    let idx := i % samples
    productDataChecksum <| genericMulFullData sig
      (packedA.getD idx defaultPackedA) (packedB.getD idx defaultPackedB)
  let _ ← timeit s!"generic {label} full wedge" warmup positive fun i =>
    let idx := i % samples
    productDataChecksum <| genericWedgeFullData sig
      (packedA.getD idx defaultPackedA) (packedB.getD idx defaultPackedB)
  let _ ← timeit s!"generic {label} full left contraction" warmup positive fun i =>
    let idx := i % samples
    productDataChecksum <| genericLeftContractFullData sig
      (packedA.getD idx defaultPackedA) (packedB.getD idx defaultPackedB)
  let _ ← timeit s!"generic {label} full right contraction" warmup positive fun i =>
    let idx := i % samples
    productDataChecksum <| genericRightContractFullData sig
      (packedA.getD idx defaultPackedA) (packedB.getD idx defaultPackedB)
  IO.println ""

/-- Reproducible full-layout baseline for the remaining generic product kernels. -/
def runGenericProducts (iters : Nat := defaultGenericProductIters) : IO Unit := do
  let positive := positiveIters iters
  runGenericProductSignature "R3" R3 denseR3 positive
  runGenericProductSignature "PGA3" PGA3 densePGA3 positive
  runGenericProductSignature "CGA3" CGA3 denseCGA3 positive

/-! ### Dense-to-packed ingress allocation baselines -/

/-- Exact pre-ALOK-770 boxed dense-to-packed conversion shape. -/
@[inline]
def boxedDenseIngress {n : Nat} {sig : Signature n}
    (m : Multivector sig Float) (p : Parity) : MV sig p :=
  let sz := storageSize n p
  let coeffs := DataArray.ofArray ((Array.range sz).map fun pi =>
    let mask := MV.unpackIdxValid n p pi
    if hmask : mask < 2 ^ n then
      m.coeffs ⟨mask, hmask⟩
    else
      0.0)
  (MV.ofDataArray? sig p coeffs).getD (MV.zero sig p)

@[noinline]
def boxedDenseIngressFullData (m : Multivector CGA3 Float) : DataArray :=
  (boxedDenseIngress m .full).coeffs

@[noinline]
def boxedDenseIngressEvenData (m : Multivector CGA3 Float) : DataArray :=
  (boxedDenseIngress m .even).coeffs

@[noinline]
def boxedDenseIngressOddData (m : Multivector CGA3 Float) : DataArray :=
  (boxedDenseIngress m .odd).coeffs

@[noinline]
def directDenseIngressFullData (m : @& Multivector CGA3 Float) : DataArray :=
  (MV.ofMultivector m .full).coeffs

@[noinline]
def directDenseIngressEvenData (m : @& Multivector CGA3 Float) : DataArray :=
  (MV.ofMultivector m .even).coeffs

@[noinline]
def directDenseIngressOddData (m : @& Multivector CGA3 Float) : DataArray :=
  (MV.ofMultivector m .odd).coeffs

def denseIngressBaselineDiff
    (samples : Nat) (values : Array (Multivector CGA3 Float))
    (fallback : Multivector CGA3 Float)
    (boxed direct : Multivector CGA3 Float → DataArray) : Float :=
  (List.range samples).foldl (init := 0.0) fun acc i =>
    let value := values.getD i fallback
    acc + dataL1Diff (boxed value) (direct value)

/-- Compare one-buffer CGA3 dense ingress with its former boxed-array shape. -/
def runDenseIngress (iters : Nat := defaultDenseIngressIters) : IO Unit := do
  IO.println "=== CGA3 dense-to-packed ingress ==="
  let samples : Nat := 16
  let dense : Array (Multivector CGA3 Float) :=
    Array.ofFn (n := samples) fun k => denseCGA3 (Float.ofNat (k.val + 1))
  let defaultDense := denseCGA3 1.0
  -- Preflight every sample and every physically stored coefficient.
  let fullDiff := denseIngressBaselineDiff samples dense defaultDense
    boxedDenseIngressFullData directDenseIngressFullData
  let evenDiff := denseIngressBaselineDiff samples dense defaultDense
    boxedDenseIngressEvenData directDenseIngressEvenData
  let oddDiff := denseIngressBaselineDiff samples dense defaultDense
    boxedDenseIngressOddData directDenseIngressOddData
  IO.println s!"  full ingress l1 diff: {fullDiff}"
  IO.println s!"  even ingress l1 diff: {evenDiff}"
  IO.println s!"  odd ingress l1 diff: {oddDiff}"
  let diffs := [fullDiff, evenDiff, oddDiff]
  if diffs.any fun diff => diff.isNaN || diff > tolerance then
    throw <| IO.userError "dense-to-packed ingress baseline mismatch"
  let positive := positiveIters iters
  let warmup := positiveIters (positive / 10)
  let boxedFullNs ← timeit "boxed CGA3 full dense ingress" warmup positive fun i =>
    packedDataProbe
      (boxedDenseIngressFullData (dense.getD (i % samples) defaultDense))
  let directFullNs ← timeit "direct CGA3 full dense ingress" warmup positive fun i =>
    packedDataProbe
      (directDenseIngressFullData (dense.getD (i % samples) defaultDense))
  let boxedEvenNs ← timeit "boxed CGA3 even dense ingress" warmup positive fun i =>
    packedHalfDataProbe
      (boxedDenseIngressEvenData (dense.getD (i % samples) defaultDense))
  let directEvenNs ← timeit "direct CGA3 even dense ingress" warmup positive fun i =>
    packedHalfDataProbe
      (directDenseIngressEvenData (dense.getD (i % samples) defaultDense))
  let boxedOddNs ← timeit "boxed CGA3 odd dense ingress" warmup positive fun i =>
    packedHalfDataProbe
      (boxedDenseIngressOddData (dense.getD (i % samples) defaultDense))
  let directOddNs ← timeit "direct CGA3 odd dense ingress" warmup positive fun i =>
    packedHalfDataProbe
      (directDenseIngressOddData (dense.getD (i % samples) defaultDense))
  IO.println s!"  full ingress speedup: {boxedFullNs / directFullNs}x"
  IO.println s!"  even ingress speedup: {boxedEvenNs / directEvenNs}x"
  IO.println s!"  odd ingress speedup: {boxedOddNs / directOddNs}x"
  IO.println ""

/-! ### Packed linear-arithmetic allocation baselines -/

/-- Pre-ALOK-766 addition shape retained only as a benchmark baseline. -/
@[noinline]
def boxedAddData (a b : @& MV CGA3 .full) : DataArray :=
  let size := storageSize 5 .full
  DataArray.ofArray <| (Array.range size).map fun i => a.coeffs.get! i + b.coeffs.get! i

/-- Pre-ALOK-766 negation shape retained only as a benchmark baseline. -/
@[noinline]
def boxedNegData (a : @& MV CGA3 .full) : DataArray :=
  let size := storageSize 5 .full
  DataArray.ofArray <| (Array.range size).map fun i => -a.coeffs.get! i

/-- Pre-ALOK-766 scalar-multiplication shape retained only as a benchmark baseline. -/
@[noinline]
def boxedSmulData (s : Float) (a : @& MV CGA3 .full) : DataArray :=
  let size := storageSize 5 .full
  DataArray.ofArray <| (Array.range size).map fun i => s * a.coeffs.get! i

@[noinline]
def directAddData (a b : @& MV CGA3 .full) : DataArray :=
  (MV.add a b).coeffs

@[noinline]
def directNegData (a : @& MV CGA3 .full) : DataArray :=
  (MV.neg a).coeffs

@[noinline]
def directSmulData (s : Float) (a : @& MV CGA3 .full) : DataArray :=
  (MV.smul s a).coeffs

/-- Compare one-buffer CGA3 full linear kernels with their old boxed-array shape. -/
def runPackedLinearArithmetic
    (iters : Nat := defaultLinearArithmeticIters) : IO Unit := do
  IO.println "=== CGA3 full packed linear arithmetic ==="
  let samples : Nat := 16
  let denseA : Array (Multivector CGA3 Float) :=
    Array.ofFn (n := samples) fun k => denseCGA3 (Float.ofNat (k.val + 1))
  let denseB : Array (Multivector CGA3 Float) :=
    Array.ofFn (n := samples) fun k => denseCGA3 (Float.ofNat (k.val + 17))
  let packedA : Array (MV CGA3 .full) := denseA.map fun m => MV.ofMultivector m .full
  let packedB : Array (MV CGA3 .full) := denseB.map fun m => MV.ofMultivector m .full
  let defaultA : MV CGA3 .full := MV.ofMultivector (denseCGA3 1.0) .full
  let defaultB : MV CGA3 .full := MV.ofMultivector (denseCGA3 2.0) .full
  let scale : Float := 1.75
  let addDiff := (List.range samples).foldl (init := 0.0) fun acc i =>
    let a := packedA.getD i defaultA
    let b := packedB.getD i defaultB
    acc + dataL1Diff (boxedAddData a b) (directAddData a b)
  let negDiff := (List.range samples).foldl (init := 0.0) fun acc i =>
    let a := packedA.getD i defaultA
    acc + dataL1Diff (boxedNegData a) (directNegData a)
  let smulDiff := (List.range samples).foldl (init := 0.0) fun acc i =>
    let a := packedA.getD i defaultA
    acc + dataL1Diff (boxedSmulData scale a) (directSmulData scale a)
  IO.println s!"  add l1 diff: {addDiff}"
  IO.println s!"  neg l1 diff: {negDiff}"
  IO.println s!"  smul l1 diff: {smulDiff}"
  if addDiff.isNaN || negDiff.isNaN || smulDiff.isNaN ||
      addDiff > tolerance || negDiff > tolerance || smulDiff > tolerance then
    throw <| IO.userError "packed linear-arithmetic baseline mismatch"
  let positive := positiveIters iters
  let warmup := positiveIters (positive / 10)
  let boxedAddNs ← timeit "boxed CGA3 full add" warmup positive fun i =>
    let idx := i % samples
    packedDataProbe (boxedAddData (packedA.getD idx defaultA) (packedB.getD idx defaultB))
  let directAddNs ← timeit "direct CGA3 full add" warmup positive fun i =>
    let idx := i % samples
    packedDataProbe (directAddData (packedA.getD idx defaultA) (packedB.getD idx defaultB))
  let boxedNegNs ← timeit "boxed CGA3 full neg" warmup positive fun i =>
    packedDataProbe (boxedNegData (packedA.getD (i % samples) defaultA))
  let directNegNs ← timeit "direct CGA3 full neg" warmup positive fun i =>
    packedDataProbe (directNegData (packedA.getD (i % samples) defaultA))
  let boxedSmulNs ← timeit "boxed CGA3 full smul" warmup positive fun i =>
    packedDataProbe (boxedSmulData scale (packedA.getD (i % samples) defaultA))
  let directSmulNs ← timeit "direct CGA3 full smul" warmup positive fun i =>
    packedDataProbe (directSmulData scale (packedA.getD (i % samples) defaultA))
  IO.println s!"  add speedup: {boxedAddNs / directAddNs}x"
  IO.println s!"  neg speedup: {boxedNegNs / directNegNs}x"
  IO.println s!"  smul speedup: {boxedSmulNs / directSmulNs}x"
  IO.println ""

/-! ### Packed unary-involution allocation baselines -/

/-- Pre-ALOK-767 reverse shape retained only as a benchmark baseline. -/
@[always_inline]
def boxedReverseData {p : Parity} (a : @& MV CGA3 p) : DataArray :=
  let size := storageSize 5 p
  DataArray.ofArray <| (Array.range size).map fun i =>
    let mask := MV.unpackIdx 5 p i
    let grade := popcount mask
    let sign := if (grade * (grade - 1) / 2) % 2 == 0 then 1.0 else -1.0
    sign * a.coeffs.get! i

/-- Pre-ALOK-767 grade-involution shape retained only as a benchmark baseline. -/
@[always_inline]
def boxedInvoluteData {p : Parity} (a : @& MV CGA3 p) : DataArray :=
  let size := storageSize 5 p
  DataArray.ofArray <| (Array.range size).map fun i =>
    let grade := popcount (MV.unpackIdx 5 p i)
    let sign := if grade % 2 == 0 then 1.0 else -1.0
    sign * a.coeffs.get! i

/-- Pre-ALOK-767 Clifford-conjugation shape retained only as a benchmark baseline. -/
@[always_inline]
def boxedConjugateData {p : Parity} (a : @& MV CGA3 p) : DataArray :=
  let size := storageSize 5 p
  DataArray.ofArray <| (Array.range size).map fun i =>
    let mask := MV.unpackIdx 5 p i
    let grade := popcount mask
    let sign := if (grade * (grade + 1) / 2) % 2 == 0 then 1.0 else -1.0
    sign * a.coeffs.get! i

@[noinline] def boxedRevFullData (a : @& MV CGA3 .full) : DataArray :=
  boxedReverseData a
@[noinline] def boxedRevEvenData (a : @& MV CGA3 .even) : DataArray :=
  boxedReverseData a
@[noinline] def boxedRevOddData (a : @& MV CGA3 .odd) : DataArray :=
  boxedReverseData a

@[noinline] def boxedInvoluteFullData (a : @& MV CGA3 .full) : DataArray :=
  boxedInvoluteData a
@[noinline] def boxedInvoluteEvenData (a : @& MV CGA3 .even) : DataArray :=
  boxedInvoluteData a
@[noinline] def boxedInvoluteOddData (a : @& MV CGA3 .odd) : DataArray :=
  boxedInvoluteData a

@[noinline] def boxedConjugateFullData (a : @& MV CGA3 .full) : DataArray :=
  boxedConjugateData a
@[noinline] def boxedConjugateEvenData (a : @& MV CGA3 .even) : DataArray :=
  boxedConjugateData a
@[noinline] def boxedConjugateOddData (a : @& MV CGA3 .odd) : DataArray :=
  boxedConjugateData a

@[noinline] def directRevFullData (a : @& MV CGA3 .full) : DataArray :=
  (MV.rev a).coeffs
@[noinline] def directRevEvenData (a : @& MV CGA3 .even) : DataArray :=
  (MV.rev a).coeffs
@[noinline] def directRevOddData (a : @& MV CGA3 .odd) : DataArray :=
  (MV.rev a).coeffs

@[noinline] def directInvoluteFullData (a : @& MV CGA3 .full) : DataArray :=
  (MV.involute a).coeffs
@[noinline] def directInvoluteEvenData (a : @& MV CGA3 .even) : DataArray :=
  (MV.involute a).coeffs
@[noinline] def directInvoluteOddData (a : @& MV CGA3 .odd) : DataArray :=
  (MV.involute a).coeffs

@[noinline] def directConjugateFullData (a : @& MV CGA3 .full) : DataArray :=
  (MV.conjugate a).coeffs
@[noinline] def directConjugateEvenData (a : @& MV CGA3 .even) : DataArray :=
  (MV.conjugate a).coeffs
@[noinline] def directConjugateOddData (a : @& MV CGA3 .odd) : DataArray :=
  (MV.conjugate a).coeffs

def unaryBaselineDiff {p : Parity}
    (samples : Nat) (values : Array (MV CGA3 p)) (fallback : MV CGA3 p)
    (boxed direct : MV CGA3 p → DataArray) : Float :=
  (List.range samples).foldl (init := 0.0) fun acc i =>
    let value := values.getD i fallback
    acc + dataL1Diff (boxed value) (direct value)

/-- Compare packed CGA3 unary kernels with their former boxed-array shapes. -/
def runPackedUnaryInvolutions
    (iters : Nat := defaultUnaryInvolutionIters) : IO Unit := do
  IO.println "=== CGA3 packed unary involutions ==="
  let samples : Nat := 16
  let dense : Array (Multivector CGA3 Float) :=
    Array.ofFn (n := samples) fun k => denseCGA3 (Float.ofNat (k.val + 1))
  let full : Array (MV CGA3 .full) := dense.map fun m => MV.ofMultivector m .full
  let even : Array (MV CGA3 .even) := dense.map fun m => MV.ofMultivector m .even
  let odd : Array (MV CGA3 .odd) := dense.map fun m => MV.ofMultivector m .odd
  let defaultDense := denseCGA3 1.0
  let defaultFull : MV CGA3 .full := MV.ofMultivector defaultDense .full
  let defaultEven : MV CGA3 .even := MV.ofMultivector defaultDense .even
  let defaultOdd : MV CGA3 .odd := MV.ofMultivector defaultDense .odd
  -- Preflight every operation, layout, sample, and stored coefficient.
  let revFullDiff := unaryBaselineDiff samples full defaultFull
    boxedRevFullData directRevFullData
  let revEvenDiff := unaryBaselineDiff samples even defaultEven
    boxedRevEvenData directRevEvenData
  let revOddDiff := unaryBaselineDiff samples odd defaultOdd
    boxedRevOddData directRevOddData
  let involuteFullDiff := unaryBaselineDiff samples full defaultFull
    boxedInvoluteFullData directInvoluteFullData
  let involuteEvenDiff := unaryBaselineDiff samples even defaultEven
    boxedInvoluteEvenData directInvoluteEvenData
  let involuteOddDiff := unaryBaselineDiff samples odd defaultOdd
    boxedInvoluteOddData directInvoluteOddData
  let conjugateFullDiff := unaryBaselineDiff samples full defaultFull
    boxedConjugateFullData directConjugateFullData
  let conjugateEvenDiff := unaryBaselineDiff samples even defaultEven
    boxedConjugateEvenData directConjugateEvenData
  let conjugateOddDiff := unaryBaselineDiff samples odd defaultOdd
    boxedConjugateOddData directConjugateOddData
  IO.println s!"  reverse full l1 diff: {revFullDiff}"
  IO.println s!"  reverse even l1 diff: {revEvenDiff}"
  IO.println s!"  reverse odd l1 diff: {revOddDiff}"
  IO.println s!"  involute full l1 diff: {involuteFullDiff}"
  IO.println s!"  involute even l1 diff: {involuteEvenDiff}"
  IO.println s!"  involute odd l1 diff: {involuteOddDiff}"
  IO.println s!"  conjugate full l1 diff: {conjugateFullDiff}"
  IO.println s!"  conjugate even l1 diff: {conjugateEvenDiff}"
  IO.println s!"  conjugate odd l1 diff: {conjugateOddDiff}"
  let diffs := [
    revFullDiff, revEvenDiff, revOddDiff,
    involuteFullDiff, involuteEvenDiff, involuteOddDiff,
    conjugateFullDiff, conjugateEvenDiff, conjugateOddDiff]
  if diffs.any fun diff => diff.isNaN || diff > tolerance then
    throw <| IO.userError "packed unary-involution baseline mismatch"
  -- Time matching no-inline boxed and direct producers.
  let positive := positiveIters iters
  let warmup := positiveIters (positive / 10)
  let boxedRevFullNs ← timeit "boxed CGA3 full reverse" warmup positive fun i =>
    packedDataProbe (boxedRevFullData (full.getD (i % samples) defaultFull))
  let directRevFullNs ← timeit "direct CGA3 full reverse" warmup positive fun i =>
    packedDataProbe (directRevFullData (full.getD (i % samples) defaultFull))
  let boxedRevEvenNs ← timeit "boxed CGA3 even reverse" warmup positive fun i =>
    packedHalfDataProbe (boxedRevEvenData (even.getD (i % samples) defaultEven))
  let directRevEvenNs ← timeit "direct CGA3 even reverse" warmup positive fun i =>
    packedHalfDataProbe (directRevEvenData (even.getD (i % samples) defaultEven))
  let boxedRevOddNs ← timeit "boxed CGA3 odd reverse" warmup positive fun i =>
    packedHalfDataProbe (boxedRevOddData (odd.getD (i % samples) defaultOdd))
  let directRevOddNs ← timeit "direct CGA3 odd reverse" warmup positive fun i =>
    packedHalfDataProbe (directRevOddData (odd.getD (i % samples) defaultOdd))
  -- Grade involution includes its even identity and odd negation fast paths.
  let boxedInvoluteFullNs ←
    timeit "boxed CGA3 full involute" warmup positive fun i =>
      packedDataProbe
        (boxedInvoluteFullData (full.getD (i % samples) defaultFull))
  let directInvoluteFullNs ←
    timeit "direct CGA3 full involute" warmup positive fun i =>
      packedDataProbe
        (directInvoluteFullData (full.getD (i % samples) defaultFull))
  let boxedInvoluteEvenNs ←
    timeit "boxed CGA3 even involute" warmup positive fun i =>
      packedHalfDataProbe
        (boxedInvoluteEvenData (even.getD (i % samples) defaultEven))
  let directInvoluteEvenNs ←
    timeit "direct CGA3 even involute" warmup positive fun i =>
      packedHalfDataProbe
        (directInvoluteEvenData (even.getD (i % samples) defaultEven))
  let boxedInvoluteOddNs ←
    timeit "boxed CGA3 odd involute" warmup positive fun i =>
      packedHalfDataProbe
        (boxedInvoluteOddData (odd.getD (i % samples) defaultOdd))
  let directInvoluteOddNs ←
    timeit "direct CGA3 odd involute" warmup positive fun i =>
      packedHalfDataProbe
        (directInvoluteOddData (odd.getD (i % samples) defaultOdd))
  -- Clifford conjugation stays one pass for all three layouts.
  let boxedConjugateFullNs ←
    timeit "boxed CGA3 full conjugate" warmup positive fun i =>
      packedDataProbe
        (boxedConjugateFullData (full.getD (i % samples) defaultFull))
  let directConjugateFullNs ←
    timeit "direct CGA3 full conjugate" warmup positive fun i =>
      packedDataProbe
        (directConjugateFullData (full.getD (i % samples) defaultFull))
  let boxedConjugateEvenNs ←
    timeit "boxed CGA3 even conjugate" warmup positive fun i =>
      packedHalfDataProbe
        (boxedConjugateEvenData (even.getD (i % samples) defaultEven))
  let directConjugateEvenNs ←
    timeit "direct CGA3 even conjugate" warmup positive fun i =>
      packedHalfDataProbe
        (directConjugateEvenData (even.getD (i % samples) defaultEven))
  let boxedConjugateOddNs ←
    timeit "boxed CGA3 odd conjugate" warmup positive fun i =>
      packedHalfDataProbe
        (boxedConjugateOddData (odd.getD (i % samples) defaultOdd))
  let directConjugateOddNs ←
    timeit "direct CGA3 odd conjugate" warmup positive fun i =>
      packedHalfDataProbe
        (directConjugateOddData (odd.getD (i % samples) defaultOdd))
  -- Keep human-readable ratios alongside the parseable timing labels.
  IO.println s!"  full reverse speedup: {boxedRevFullNs / directRevFullNs}x"
  IO.println s!"  even reverse speedup: {boxedRevEvenNs / directRevEvenNs}x"
  IO.println s!"  odd reverse speedup: {boxedRevOddNs / directRevOddNs}x"
  IO.println s!"  full involute speedup: {boxedInvoluteFullNs / directInvoluteFullNs}x"
  IO.println s!"  even involute speedup: {boxedInvoluteEvenNs / directInvoluteEvenNs}x"
  IO.println s!"  odd involute speedup: {boxedInvoluteOddNs / directInvoluteOddNs}x"
  IO.println s!"  full conjugate speedup: {boxedConjugateFullNs / directConjugateFullNs}x"
  IO.println s!"  even conjugate speedup: {boxedConjugateEvenNs / directConjugateEvenNs}x"
  IO.println s!"  odd conjugate speedup: {boxedConjugateOddNs / directConjugateOddNs}x"
  IO.println ""

/-! ### Packed Hodge-dual allocation baseline -/

/-- Exact pre-ALOK-768 boxed Hodge shape retained only as a benchmark baseline. -/
@[noinline]
def boxedHodgeFullData (m : @& MV CGA3 .full) : DataArray :=
  let size := storageSize 5 .full
  DataArray.ofArray <| (Array.range size).map fun mask =>
    let outBlade : Blade CGA3 := ⟨BitVec.ofNat 5 mask⟩
    let dualBits := outBlade.bits ^^^ pseudoscalar
    let dualIdx := dualBits.toNat
    let sign := leftComplementSign CGA3 ⟨dualBits⟩
    let coeff := m.coeffs.get! dualIdx
    if sign < 0 then -coeff else coeff

@[noinline]
def directHodgeFullData (m : @& MV CGA3 .full) : DataArray :=
  (MV.hodgeDual m).coeffs

/-- Compare the packed CGA3 Hodge kernel with its former boxed-array shape. -/
def runPackedHodgeDual (iters : Nat := defaultHodgeDualIters) : IO Unit := do
  IO.println "=== CGA3 packed Hodge dual ==="
  let samples : Nat := 16
  let dense : Array (Multivector CGA3 Float) :=
    Array.ofFn (n := samples) fun k => denseCGA3 (Float.ofNat (k.val + 1))
  let full : Array (MV CGA3 .full) := dense.map fun m => MV.ofMultivector m .full
  let defaultFull : MV CGA3 .full := MV.ofMultivector (denseCGA3 1.0) .full
  let diff := unaryBaselineDiff samples full defaultFull
    boxedHodgeFullData directHodgeFullData
  IO.println s!"  hodge dual l1 diff: {diff}"
  if diff.isNaN || diff > tolerance then
    throw <| IO.userError "packed Hodge-dual baseline mismatch"
  let positive := positiveIters iters
  let warmup := positiveIters (positive / 10)
  let boxedNs ← timeit "boxed CGA3 full hodge dual" warmup positive fun i =>
    packedDataProbe (boxedHodgeFullData (full.getD (i % samples) defaultFull))
  let directNs ← timeit "direct CGA3 full hodge dual" warmup positive fun i =>
    packedDataProbe (directHodgeFullData (full.getD (i % samples) defaultFull))
  IO.println s!"  hodge dual speedup: {boxedNs / directNs}x"
  IO.println ""

/-! ### Packed projection and parity-widening allocation baselines -/

/-- Exact pre-ALOK-769 boxed full-grade-projection shape. -/
@[noinline]
def boxedFullGrade2ProjectionData (m : @& MV CGA3 .full) : DataArray :=
  let sz := storageSize 5 .full
  DataArray.ofArray ((Array.range sz).map fun pi =>
    let mask := MV.unpackIdx 5 .full pi
    if popcount mask == 2 then m.coeffs.get! pi else 0.0)

/-- Exact pre-ALOK-769 boxed even-grade-projection shape. -/
@[noinline]
def boxedEvenGrade2ProjectionData (m : @& MV CGA3 .even) : DataArray :=
  let sz := storageSize 5 .even
  DataArray.ofArray ((Array.range sz).map fun pi =>
    let mask := MV.unpackIdx 5 .even pi
    if popcount mask == 2 then m.coeffs.get! pi else 0.0)

/-- Exact pre-ALOK-769 boxed odd-grade-projection shape. -/
@[noinline]
def boxedOddGrade3ProjectionData (m : @& MV CGA3 .odd) : DataArray :=
  let sz := storageSize 5 .odd
  DataArray.ofArray ((Array.range sz).map fun pi =>
    let mask := MV.unpackIdx 5 .odd pi
    if popcount mask == 3 then m.coeffs.get! pi else 0.0)

/-- Exact pre-ALOK-769 boxed full-to-even projection shape. -/
@[noinline]
def boxedEvenPartData (m : @& MV CGA3 .full) : DataArray :=
  let szEven := storageSize 5 .even
  DataArray.ofArray ((Array.range szEven).map fun pi =>
    let mask := MV.unpackIdx 5 .even pi
    m.coeffs.get! mask)

/-- Exact pre-ALOK-769 boxed full-to-odd projection shape. -/
@[noinline]
def boxedOddPartData (m : @& MV CGA3 .full) : DataArray :=
  let szOdd := storageSize 5 .odd
  DataArray.ofArray ((Array.range szOdd).map fun pi =>
    let mask := MV.unpackIdx 5 .odd pi
    m.coeffs.get! mask)

/-- Exact pre-ALOK-769 boxed even-to-full widening shape. -/
@[noinline]
def boxedEvenToFullData (m : @& MV CGA3 .even) : DataArray :=
  let szFull := storageSize 5 .full
  DataArray.ofArray ((Array.range szFull).map fun mask =>
    if Parity.containsMask .even mask then
      let pi := MV.packIdx 5 .even mask
      m.coeffs.get! pi
    else 0.0)

/-- Exact pre-ALOK-769 boxed odd-to-full widening shape. -/
@[noinline]
def boxedOddToFullData (m : @& MV CGA3 .odd) : DataArray :=
  let szFull := storageSize 5 .full
  DataArray.ofArray ((Array.range szFull).map fun mask =>
    if Parity.containsMask .odd mask then
      let pi := MV.packIdx 5 .odd mask
      m.coeffs.get! pi
    else 0.0)

@[noinline]
def directFullGrade2ProjectionData (m : @& MV CGA3 .full) : DataArray :=
  (MV.gradeProject m 2).coeffs

@[noinline]
def directEvenGrade2ProjectionData (m : @& MV CGA3 .even) : DataArray :=
  (MV.gradeProject m 2).coeffs

@[noinline]
def directOddGrade3ProjectionData (m : @& MV CGA3 .odd) : DataArray :=
  (MV.gradeProject m 3).coeffs

@[noinline]
def directEvenPartData (m : @& MV CGA3 .full) : DataArray :=
  (MV.evenPart m).coeffs

@[noinline]
def directOddPartData (m : @& MV CGA3 .full) : DataArray :=
  (MV.oddPart m).coeffs

@[noinline]
def directEvenToFullData (m : @& MV CGA3 .even) : DataArray :=
  (MV.evenToFull m).coeffs

@[noinline]
def directOddToFullData (m : @& MV CGA3 .odd) : DataArray :=
  (MV.oddToFull m).coeffs

@[noinline]
def projectionFullProbe (a : @& DataArray) : Float :=
  packedDataProbe a

@[noinline]
def projectionHalfProbe (a : @& DataArray) : Float :=
  packedHalfDataProbe a

def projectionBaselineDiff {p : Parity}
    (samples : Nat) (values : Array (MV CGA3 p)) (fallback : MV CGA3 p)
    (boxed direct : MV CGA3 p → DataArray) : Float :=
  (List.range samples).foldl (init := 0.0) fun acc i =>
    let value := values.getD i fallback
    acc + dataL1Diff (boxed value) (direct value)

/-- Compare the one-buffer CGA3 projection and widening kernels with their
former boxed-array shapes. -/
def runPackedProjectionsWidening
    (iters : Nat := defaultProjectionWideningIters) : IO Unit := do
  IO.println "=== CGA3 packed projections and parity widening ==="
  let samples : Nat := 16
  let dense : Array (Multivector CGA3 Float) :=
    Array.ofFn (n := samples) fun k => denseCGA3 (Float.ofNat (k.val + 1))
  let full : Array (MV CGA3 .full) := dense.map fun m => MV.ofMultivector m .full
  let even : Array (MV CGA3 .even) := dense.map fun m => MV.ofMultivector m .even
  let odd : Array (MV CGA3 .odd) := dense.map fun m => MV.ofMultivector m .odd
  let defaultDense := denseCGA3 1.0
  let defaultFull : MV CGA3 .full := MV.ofMultivector defaultDense .full
  let defaultEven : MV CGA3 .even := MV.ofMultivector defaultDense .even
  let defaultOdd : MV CGA3 .odd := MV.ofMultivector defaultDense .odd
  -- Preflight every operation, sample, and stored output coefficient.
  let fullGrade2Diff := projectionBaselineDiff samples full defaultFull
    boxedFullGrade2ProjectionData directFullGrade2ProjectionData
  let evenGrade2Diff := projectionBaselineDiff samples even defaultEven
    boxedEvenGrade2ProjectionData directEvenGrade2ProjectionData
  let oddGrade3Diff := projectionBaselineDiff samples odd defaultOdd
    boxedOddGrade3ProjectionData directOddGrade3ProjectionData
  let evenPartDiff := projectionBaselineDiff samples full defaultFull
    boxedEvenPartData directEvenPartData
  let oddPartDiff := projectionBaselineDiff samples full defaultFull
    boxedOddPartData directOddPartData
  let evenToFullDiff := projectionBaselineDiff samples even defaultEven
    boxedEvenToFullData directEvenToFullData
  let oddToFullDiff := projectionBaselineDiff samples odd defaultOdd
    boxedOddToFullData directOddToFullData
  IO.println s!"  projection full grade2 l1 diff: {fullGrade2Diff}"
  IO.println s!"  projection even grade2 l1 diff: {evenGrade2Diff}"
  IO.println s!"  projection odd grade3 l1 diff: {oddGrade3Diff}"
  IO.println s!"  projection even part l1 diff: {evenPartDiff}"
  IO.println s!"  projection odd part l1 diff: {oddPartDiff}"
  IO.println s!"  widening even to full l1 diff: {evenToFullDiff}"
  IO.println s!"  widening odd to full l1 diff: {oddToFullDiff}"
  let diffs := [
    fullGrade2Diff, evenGrade2Diff, oddGrade3Diff,
    evenPartDiff, oddPartDiff, evenToFullDiff, oddToFullDiff]
  if diffs.any fun diff => diff.isNaN || diff > tolerance then
    throw <| IO.userError "packed projection/widening baseline mismatch"
  let positive := positiveIters iters
  let warmup := positiveIters (positive / 10)
  let boxedFullGrade2Ns ←
    timeit "boxed CGA3 full grade-2 projection" warmup positive fun i =>
      projectionFullProbe
        (boxedFullGrade2ProjectionData (full.getD (i % samples) defaultFull))
  let directFullGrade2Ns ←
    timeit "direct CGA3 full grade-2 projection" warmup positive fun i =>
      projectionFullProbe
        (directFullGrade2ProjectionData (full.getD (i % samples) defaultFull))
  let boxedEvenGrade2Ns ←
    timeit "boxed CGA3 even grade-2 projection" warmup positive fun i =>
      projectionHalfProbe
        (boxedEvenGrade2ProjectionData (even.getD (i % samples) defaultEven))
  let directEvenGrade2Ns ←
    timeit "direct CGA3 even grade-2 projection" warmup positive fun i =>
      projectionHalfProbe
        (directEvenGrade2ProjectionData (even.getD (i % samples) defaultEven))
  let boxedOddGrade3Ns ←
    timeit "boxed CGA3 odd grade-3 projection" warmup positive fun i =>
      projectionHalfProbe
        (boxedOddGrade3ProjectionData (odd.getD (i % samples) defaultOdd))
  let directOddGrade3Ns ←
    timeit "direct CGA3 odd grade-3 projection" warmup positive fun i =>
      projectionHalfProbe
        (directOddGrade3ProjectionData (odd.getD (i % samples) defaultOdd))
  let boxedEvenPartNs ←
    timeit "boxed CGA3 even part" warmup positive fun i =>
      projectionHalfProbe (boxedEvenPartData (full.getD (i % samples) defaultFull))
  let directEvenPartNs ←
    timeit "direct CGA3 even part" warmup positive fun i =>
      projectionHalfProbe (directEvenPartData (full.getD (i % samples) defaultFull))
  let boxedOddPartNs ←
    timeit "boxed CGA3 odd part" warmup positive fun i =>
      projectionHalfProbe (boxedOddPartData (full.getD (i % samples) defaultFull))
  let directOddPartNs ←
    timeit "direct CGA3 odd part" warmup positive fun i =>
      projectionHalfProbe (directOddPartData (full.getD (i % samples) defaultFull))
  let boxedEvenToFullNs ←
    timeit "boxed CGA3 even-to-full widening" warmup positive fun i =>
      projectionFullProbe
        (boxedEvenToFullData (even.getD (i % samples) defaultEven))
  let directEvenToFullNs ←
    timeit "direct CGA3 even-to-full widening" warmup positive fun i =>
      projectionFullProbe
        (directEvenToFullData (even.getD (i % samples) defaultEven))
  let boxedOddToFullNs ←
    timeit "boxed CGA3 odd-to-full widening" warmup positive fun i =>
      projectionFullProbe
        (boxedOddToFullData (odd.getD (i % samples) defaultOdd))
  let directOddToFullNs ←
    timeit "direct CGA3 odd-to-full widening" warmup positive fun i =>
      projectionFullProbe
        (directOddToFullData (odd.getD (i % samples) defaultOdd))
  IO.println s!"  full grade-2 projection speedup: {boxedFullGrade2Ns / directFullGrade2Ns}x"
  IO.println s!"  even grade-2 projection speedup: {boxedEvenGrade2Ns / directEvenGrade2Ns}x"
  IO.println s!"  odd grade-3 projection speedup: {boxedOddGrade3Ns / directOddGrade3Ns}x"
  IO.println s!"  even part speedup: {boxedEvenPartNs / directEvenPartNs}x"
  IO.println s!"  odd part speedup: {boxedOddPartNs / directOddPartNs}x"
  IO.println s!"  even-to-full widening speedup: {boxedEvenToFullNs / directEvenToFullNs}x"
  IO.println s!"  odd-to-full widening speedup: {boxedOddToFullNs / directOddToFullNs}x"
  IO.println ""

/-- Compare the one-buffer subtraction kernel with the old add-neg composition.

CGA3 full storage exercises 32 contiguous coefficients, the largest standard
signature in the packed benchmark matrix. -/
def runPackedSubtraction (iters : Nat := defaultSubtractionIters) : IO Unit := do
  IO.println "=== CGA3 packed subtraction ==="
  let samples : Nat := 16
  let denseA : Array (Multivector CGA3 Float) :=
    Array.ofFn (n := samples) fun k => denseCGA3 (Float.ofNat (k.val + 1))
  let denseB : Array (Multivector CGA3 Float) :=
    Array.ofFn (n := samples) fun k => denseCGA3 (Float.ofNat (k.val + 17))
  let packedA : Array (MV CGA3 .full) := denseA.map fun m => MV.ofMultivector m .full
  let packedB : Array (MV CGA3 .full) := denseB.map fun m => MV.ofMultivector m .full
  let defaultA : MV CGA3 .full := MV.ofMultivector (denseCGA3 1.0) .full
  let defaultB : MV CGA3 .full := MV.ofMultivector (denseCGA3 2.0) .full
  let positive := positiveIters iters
  let warmup := positiveIters (positive / 10)
  let composedNs ← timeit "packed add-neg subtraction" warmup positive fun i =>
    let idx := i % samples
    let a := packedA.getD idx defaultA
    let b := packedB.getD idx defaultB
    packedProbe (MV.add a (MV.neg b))
  let directNs ← timeit "packed direct subtraction" warmup positive fun i =>
    let idx := i % samples
    packedProbe (MV.sub (packedA.getD idx defaultA) (packedB.getD idx defaultB))
  IO.println s!"  speedup: {composedNs / directNs}x"
  IO.println ""

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

def runPGA3MotorPointTransform (iters : Nat) : IO Unit := do
  IO.println "=== PGA3 motor point transforms ==="
  let samples : Nat := 16
  let denseMotors : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k => densePGA3Motor (Float.ofNat (k.val + 1))
  let packedMotors : Array (PGA.Motor PGA3) :=
    Array.ofFn (n := samples) fun k => packedPGA3Motor (Float.ofNat (k.val + 1))
  let densePoints : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k => densePGA3Point (Float.ofNat (k.val + 1))
  let packedPoints : Array (PGA.Point PGA3) :=
    Array.ofFn (n := samples) fun k => packedPGA3Point (Float.ofNat (k.val + 1))
  let defaultDenseMotor := densePGA3Motor 1.0
  let defaultPackedMotor := packedPGA3Motor 1.0
  let defaultDensePoint := densePGA3Point 1.0
  let defaultPackedPoint := packedPGA3Point 1.0
  let warmup := positiveIters (iters / 10)
  compare "dense motor point transform" "packed MV motor point transform" warmup iters
    (fun i =>
      let idx := i % samples
      let motor := denseMotors.getD idx defaultDenseMotor
      let point := densePoints.getD idx defaultDensePoint
      coordProbe (PGA.Proof.extractPoint (PGA.Proof.applyMotor motor point)))
    (fun i =>
      let idx := i % samples
      let motor := packedMotors.getD idx defaultPackedMotor
      let point := packedPoints.getD idx defaultPackedPoint
      coordProbe (PGA.extractPoint3 (PGA.Motor.transformPoint motor point)))

/-- Run only the dense PGA3 motor-point transform loop.

This is intentionally quiet so external profilers such as `hwatch`, `hyperfine`,
or `/usr/bin/time -l` can measure the operation without mixed benchmark noise. -/
def runDensePGA3MotorPointTransformOnly (iters : Nat := defaultMotorPointIters) : IO Unit := do
  let samples : Nat := 16
  let denseMotors : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k => densePGA3Motor (Float.ofNat (k.val + 1))
  let densePoints : Array (Multivector PGA3 Float) :=
    Array.ofFn (n := samples) fun k => densePGA3Point (Float.ofNat (k.val + 1))
  let defaultDenseMotor := densePGA3Motor 1.0
  let defaultDensePoint := densePGA3Point 1.0
  let result := runN (positiveIters iters) fun i =>
    let idx := i % samples
    let motor := denseMotors.getD idx defaultDenseMotor
    let point := densePoints.getD idx defaultDensePoint
    coordProbe (PGA.Proof.extractPoint (PGA.Proof.applyMotor motor point))
  blackhole result

/-- Run only the packed MV PGA3 motor-point transform loop.

This is intentionally quiet so external profilers such as `hwatch`, `hyperfine`,
or `/usr/bin/time -l` can measure the operation without mixed benchmark noise. -/
def runPackedPGA3MotorPointTransformOnly (iters : Nat := defaultMotorPointIters) : IO Unit := do
  let samples : Nat := 16
  let packedMotors : Array (PGA.Motor PGA3) :=
    Array.ofFn (n := samples) fun k => packedPGA3Motor (Float.ofNat (k.val + 1))
  let packedPoints : Array (PGA.Point PGA3) :=
    Array.ofFn (n := samples) fun k => packedPGA3Point (Float.ofNat (k.val + 1))
  let defaultPackedMotor := packedPGA3Motor 1.0
  let defaultPackedPoint := packedPGA3Point 1.0
  let result := runN (positiveIters iters) fun i =>
    let idx := i % samples
    let motor := packedMotors.getD idx defaultPackedMotor
    let point := packedPoints.getD idx defaultPackedPoint
    coordProbe (PGA.extractPoint3 (PGA.Motor.transformPoint motor point))
  blackhole result

@[noinline]
def scalarXYZTransformProbe
    (motor : @& PGA.Motor PGA3) (xyz : @& FloatArray) : Float := Id.run do
  let pointCount := xyz.size / 3
  let mut sum := 0.0
  for i in [0:pointCount] do
    let base := i * 3
    let point := PGA.point3
      (xyz.get! base) (xyz.get! (base + 1)) (xyz.get! (base + 2))
    sum := sum + coordProbe
      (PGA.extractPoint3 (PGA.Motor.transformPoint motor point))
  return sum

@[noinline]
def batchedXYZTransformProbe
    (motor : @& PGA.Motor PGA3) (xyz : @& FloatArray) : Float := Id.run do
  let transformed :=
    (PGA.Motor.transformXYZBatch3? motor xyz).getD FloatArray.empty
  let mut sum := 0.0
  for i in [0:transformed.size] do
    sum := sum + transformed.get! i
  return sum

/-- Compare one public packed transform per point with the flat checked batch path. -/
def runPGA3XYZBatch
    (pointCount : Nat := defaultXYZBatchPoints)
    (iters : Nat := defaultXYZBatchIters) : IO Unit := do
  if pointCount == 0 then
    throw <| IO.userError "PGA3 XYZ batch benchmark requires at least one point"
  let motor := PGA.rigidMotor3 0.0 0.0 1.0 0.7 2.0 (-3.0) 4.0
  let sampleCount := 16
  let inputs : Array FloatArray :=
    Array.ofFn (n := sampleCount) fun i =>
      packedXYZInput pointCount (Float.ofNat i.val * 0.03125)
  let xyz := inputs.getD 0 (packedXYZInput pointCount)
  let scalarProbe := scalarXYZTransformProbe motor xyz
  let batchProbe := batchedXYZTransformProbe motor xyz
  let probeDiff := Float.abs (scalarProbe - batchProbe)
  if probeDiff > 1.0e-6 * Float.ofNat pointCount then
    throw <| IO.userError s!"PGA3 XYZ batch probe mismatch: {probeDiff}"
  IO.println s!"=== PGA3 XYZ batch transforms ({pointCount} points) ==="
  let positive := positiveIters iters
  let warmup := positiveIters (positive / 10)
  let scalarNs ← timeit "scalar public loop" warmup positive fun i =>
    scalarXYZTransformProbe motor (inputs.getD (i % sampleCount) xyz)
  let batchNs ← timeit "flat checked batch" warmup positive fun i =>
    batchedXYZTransformProbe motor (inputs.getD (i % sampleCount) xyz)
  let speedup := scalarNs / batchNs
  IO.println s!"  scalar: {scalarNs / Float.ofNat pointCount} ns/point"
  IO.println s!"  batch: {batchNs / Float.ofNat pointCount} ns/point"
  IO.println s!"  speedup: {speedup}x"
  if speedup < 3.0 then
    throw <| IO.userError s!"PGA3 XYZ batch speedup {speedup}x is below 3x"

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
  IO.println "                 Packed MV Benchmarks"
  IO.println "===================================================="
  IO.println ""
  verifyCorrectness
  runPackedSubtraction (positiveIters baseIters)
  runPackedLinearArithmetic (positiveIters baseIters)
  runPackedUnaryInvolutions (positiveIters baseIters)
  runPackedHodgeDual (positiveIters baseIters)
  runPackedProjectionsWidening (positiveIters baseIters)
  runDenseIngress (positiveIters baseIters)
  runR3 (positiveIters baseIters)
  runPGA3 (positiveIters (baseIters / 2))
  runPGA3MotorPointTransform (positiveIters (baseIters / 2))
  runCGA3 (positiveIters (baseIters / 5))
  IO.println "Done!"

end Grassmann.PackedMVBench

def parseItersArg (s : String) : IO Nat := do
  match s.toNat? with
  | some iters => pure iters
  | none => throw <| IO.userError s!"Invalid iteration count: {s}"

def usage : String :=
  String.intercalate "\n" [
    "Usage: packedmvbench [base-iters]",
    "       packedmvbench all [base-iters]",
    "       packedmvbench subtraction [iters]",
    "       packedmvbench linear-arithmetic [iters]",
    "       packedmvbench unary-involutions [iters]",
    "       packedmvbench hodge-dual [iters]",
    "       packedmvbench projections-widening [iters]",
    "       packedmvbench dense-ingress [iters]",
    "       packedmvbench generic-products [iters]",
    "       packedmvbench pga-motor-point [iters]",
    "       packedmvbench pga-motor-point-dense [iters]",
    "       packedmvbench pga-motor-point-packed [iters]",
    "       packedmvbench pga-xyz-batch [point-count] [iters]"
  ]

def main (args : List String) : IO Unit := do
  match args with
  | [] => Grassmann.PackedMVBench.runAll
  | ["all"] => Grassmann.PackedMVBench.runAll
  | ["all", itersStr] =>
      Grassmann.PackedMVBench.runAll (← parseItersArg itersStr)
  | ["subtraction"] =>
      Grassmann.PackedMVBench.runPackedSubtraction
  | ["subtraction", itersStr] =>
      Grassmann.PackedMVBench.runPackedSubtraction (← parseItersArg itersStr)
  | ["linear-arithmetic"] =>
      Grassmann.PackedMVBench.runPackedLinearArithmetic
  | ["linear-arithmetic", itersStr] =>
      Grassmann.PackedMVBench.runPackedLinearArithmetic (← parseItersArg itersStr)
  | ["unary-involutions"] =>
      Grassmann.PackedMVBench.runPackedUnaryInvolutions
  | ["unary-involutions", itersStr] =>
      Grassmann.PackedMVBench.runPackedUnaryInvolutions (← parseItersArg itersStr)
  | ["hodge-dual"] =>
      Grassmann.PackedMVBench.runPackedHodgeDual
  | ["hodge-dual", itersStr] =>
      Grassmann.PackedMVBench.runPackedHodgeDual (← parseItersArg itersStr)
  | ["projections-widening"] =>
      Grassmann.PackedMVBench.runPackedProjectionsWidening
  | ["projections-widening", itersStr] =>
      Grassmann.PackedMVBench.runPackedProjectionsWidening (← parseItersArg itersStr)
  | ["dense-ingress"] =>
      Grassmann.PackedMVBench.runDenseIngress
  | ["dense-ingress", itersStr] =>
      Grassmann.PackedMVBench.runDenseIngress (← parseItersArg itersStr)
  | ["generic-products"] =>
      Grassmann.PackedMVBench.runGenericProducts
  | ["generic-products", itersStr] =>
      Grassmann.PackedMVBench.runGenericProducts (← parseItersArg itersStr)
  | ["pga-motor-point"] =>
      Grassmann.PackedMVBench.runPGA3MotorPointTransform
        Grassmann.PackedMVBench.defaultMotorPointIters
  | ["pga-motor-point", itersStr] =>
      Grassmann.PackedMVBench.runPGA3MotorPointTransform (← parseItersArg itersStr)
  | ["pga-motor-point-dense"] =>
      Grassmann.PackedMVBench.runDensePGA3MotorPointTransformOnly
  | ["pga-motor-point-dense", itersStr] =>
      Grassmann.PackedMVBench.runDensePGA3MotorPointTransformOnly (← parseItersArg itersStr)
  | ["pga-motor-point-packed"] =>
      Grassmann.PackedMVBench.runPackedPGA3MotorPointTransformOnly
  | ["pga-motor-point-packed", itersStr] =>
      Grassmann.PackedMVBench.runPackedPGA3MotorPointTransformOnly (← parseItersArg itersStr)
  | ["pga-xyz-batch"] =>
      Grassmann.PackedMVBench.runPGA3XYZBatch
  | ["pga-xyz-batch", pointCountStr] =>
      Grassmann.PackedMVBench.runPGA3XYZBatch (← parseItersArg pointCountStr)
  | ["pga-xyz-batch", pointCountStr, itersStr] =>
      Grassmann.PackedMVBench.runPGA3XYZBatch
        (← parseItersArg pointCountStr)
        (← parseItersArg itersStr)
  | [itersStr] =>
      match itersStr.toNat? with
      | some iters => Grassmann.PackedMVBench.runAll iters
      | none => throw <| IO.userError usage
  | _ =>
      throw <| IO.userError usage

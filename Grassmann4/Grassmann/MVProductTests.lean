/-
  Grassmann/MVProductTests.lean - Independent packed-product regressions

  These compile-time checks enumerate the physical input buffers directly and
  accumulate every blade pair through the scalar blade-product definitions.
  They deliberately do not call any packed multivector product kernel while
  constructing the expected buffers.
-/
import Grassmann.MVDense

namespace Grassmann.MVProductTests

set_option linter.hashCommand false

/-! ## Independent packed-layout model -/

/-- The physical buffer size, restated independently of `MV.storageSize`. -/
private def physicalSize (n : Nat) : Parity → Nat
  | .full => 2 ^ n
  | .even | .odd => 2 ^ (n - 1)

/-- Whether a logical blade mask belongs to one packed parity. -/
private def containsMask : Parity → Nat → Bool
  | .full, _ => true
  | .even, mask => popcount mask % 2 == 0
  | .odd, mask => popcount mask % 2 == 1

/--
Decode a physical slot without using the production rank/unrank functions.

For positive dimensions, parity-packed order is obtained by appending the bit
that makes the resulting mask even or odd. Dimension-zero odd storage retains
the historical one-slot phantom layout and therefore decodes its raw slot as
mask zero even though that mask is not logically visible through `MV.coeff`.
-/
private def physicalMask (n : Nat) (p : Parity) (rank : Nat) : Nat :=
  match p with
  | .full => rank
  | .even =>
      if n == 0 then 0
      else
        let parityBit := popcount rank % 2
        rank * 2 + parityBit
  | .odd =>
      if n == 0 then 0
      else
        let parityBit := popcount rank % 2
        rank * 2 + (1 - parityBit)

/-- Rank a valid result mask without using the production pack map. -/
private def physicalRank (p : Parity) (mask : Nat) : Nat :=
  match p with
  | .full => mask
  | .even | .odd => mask / 2

/-- Small nonzero integral fixture values keep every accumulated Float exact. -/
private def fixtureValue (seed rank : Nat) : Float :=
  let magnitude := Float.ofNat ((seed + rank) % 5 + 1)
  if (seed + rank) % 2 == 0 then magnitude else -magnitude

/-- Construct a physical coefficient buffer without logical blade setters. -/
private def fixtureData (n : Nat) (p : Parity) (seed : Nat) : DataArray := Id.run do
  let size := physicalSize n p
  let mut out := FloatArray.emptyWithCapacity size
  for rank in [0:size] do
    out := out.push (fixtureValue seed rank)
  return out

/-- Import an exact-size fixture through the checked raw-buffer boundary. -/
private def fixtureMV {n : Nat} (sig : Signature n) (p : Parity) (seed : Nat) : MV sig p :=
  let data := fixtureData n p seed
  (MV.ofDataArray? sig p data).getD (MV.zero sig p)

/-- Exact equality of two physical Float buffers. -/
private def buffersEqual (a b : DataArray) : Bool :=
  a.size == b.size && (List.range a.size).all fun i => a.get! i == b.get! i

/-- Read one logical coefficient from the independent physical-layout model. -/
private def oracleCoeff (n : Nat) (p : Parity) (data : DataArray) (mask : Nat) : Float :=
  if mask < 2 ^ n && containsMask p mask then
    data.get! (physicalRank p mask)
  else
    0.0

/-! ## Forward all-pairs blade oracle -/

private inductive ProductKind where
  | geometric
  | wedge
  | leftContract
  | rightContract

/-- Select a scalar blade-product definition, never a packed product kernel. -/
private def bladeProduct {n : Nat} {sig : Signature n} (kind : ProductKind)
    (a b : Blade sig) : BladeProduct sig :=
  match kind with
  | .geometric => geometricProductBlades a b
  | .wedge => wedgeProductBlades a b
  | .leftContract => leftContractionBlades a b
  | .rightContract => rightContractionBlades a b

/--
Accumulate every physical input pair in forward order into the expected packed
output. No zero skipping, cached sign table, packed rank map, or production
multivector product appears in this oracle.
-/
private def forwardOracle {n : Nat} (sig : Signature n) (p1 p2 : Parity)
    (kind : ProductKind) (a b : DataArray) : DataArray := Id.run do
  let pOut := p1 * p2
  let size1 := physicalSize n p1
  let size2 := physicalSize n p2
  let mut out := DataArray.zeros (physicalSize n pOut)
  for rankA in [0:size1] do
    let maskA := physicalMask n p1 rankA
    let bladeA : Blade sig := ⟨BitVec.ofNat n maskA⟩
    let coeffA := a.get! rankA
    for rankB in [0:size2] do
      let maskB := physicalMask n p2 rankB
      let bladeB : Blade sig := ⟨BitVec.ofNat n maskB⟩
      match bladeProduct kind bladeA bladeB with
      | .zero => pure ()
      | .nonzero sign resultBlade =>
          let resultMask := resultBlade.bits.toNat
          let resultRank := physicalRank pOut resultMask
          let coeffB := b.get! rankB
          let contribution := Float.ofInt sign * coeffA * coeffB
          out := out.set! resultRank (out.get! resultRank + contribution)
  return out

/-! ## Result and parity-matrix checks -/

/-- Check physical size, raw slots, and every logically exposed coefficient. -/
private def resultMatches {n : Nat} {sig : Signature n} {p : Parity}
    (result : MV sig p) (expected : DataArray) : Bool :=
  result.isWellFormed &&
    result.coeffs.size == physicalSize n p &&
    expected.size == physicalSize n p &&
    buffersEqual result.coeffs expected &&
    (List.range (2 ^ n)).all fun mask =>
      result.coeff mask == oracleCoeff n p expected mask

/-- Check all four products for one ordered pair of physical layouts. -/
private def checkPair {n : Nat} (sig : Signature n) (p1 p2 : Parity) : Bool :=
  let dataA := fixtureData n p1 1
  let dataB := fixtureData n p2 3
  let a := fixtureMV sig p1 1
  let b := fixtureMV sig p2 3
  let inputsExact :=
    a.isWellFormed && b.isWellFormed &&
      buffersEqual a.coeffs dataA && buffersEqual b.coeffs dataB
  let geometric := MV.mulDirect a b
  let wedge := MV.wedge a b
  let left := MV.leftContract a b
  let right := MV.rightContract a b
  inputsExact &&
    resultMatches geometric (forwardOracle sig p1 p2 .geometric dataA dataB) &&
    resultMatches wedge (forwardOracle sig p1 p2 .wedge dataA dataB) &&
    resultMatches left (forwardOracle sig p1 p2 .leftContract dataA dataB) &&
    resultMatches right (forwardOracle sig p1 p2 .rightContract dataA dataB)

/-- Exhaust the ordered full/even/odd input-layout matrix. -/
private def checkAllParityPairs {n : Nat} (sig : Signature n) : Bool :=
  checkPair sig .full .full &&
    checkPair sig .full .even &&
    checkPair sig .full .odd &&
    checkPair sig .even .full &&
    checkPair sig .even .even &&
    checkPair sig .even .odd &&
    checkPair sig .odd .full &&
    checkPair sig .odd .even &&
    checkPair sig .odd .odd

/-! ## Exact dimensions and representative signatures -/

#guard checkAllParityPairs (Signature.euclidean 0)
#guard checkAllParityPairs R1
#guard checkAllParityPairs R2
#guard checkAllParityPairs R3
#guard checkAllParityPairs PGA3
#guard checkAllParityPairs CGA3
#guard checkAllParityPairs (Signature.euclidean 6)

/-! ## Non-finite geometric zero policy -/

/--
The geometric kernel historically skips a zero left coefficient, but does not
skip a zero right coefficient after a nonzero left coefficient. Preserve that
asymmetry for both physical scan directions: `nonFinite * 0` is `NaN`, while
`0 * nonFinite` is skipped and remains zero.
-/
private def checkGeometricNonFiniteZeroPolicy {n : Nat} (sig : Signature n)
    (p1 p2 : Parity) (nonFinite : Float) : Bool :=
  let leftNonFinite :=
    (DataArray.zeros (physicalSize n p1)).set! 0 nonFinite
  let rightZero := DataArray.zeros (physicalSize n p2)
  let leftZero := DataArray.zeros (physicalSize n p1)
  let rightNonFinite :=
    (DataArray.zeros (physicalSize n p2)).set! 0 nonFinite
  let nonFiniteTimesZero :=
    MV.mulKernelGeneric sig p1 p2 leftNonFinite rightZero
  let zeroTimesNonFinite :=
    MV.mulKernelGeneric sig p1 p2 leftZero rightNonFinite
  nonFiniteTimesZero.size == physicalSize n (p1 * p2) &&
    zeroTimesNonFinite.size == physicalSize n (p1 * p2) &&
    (nonFiniteTimesZero.get! 0).isNaN &&
    !(zeroTimesNonFinite.get! 0).isNaN &&
    zeroTimesNonFinite.get! 0 == 0.0

-- R3 uses closed plans. These layouts force the left-scan and right-scan paths.
#guard
  let infinity := 1.0 / 0.0
  let nan := 0.0 / 0.0
  checkGeometricNonFiniteZeroPolicy R3 .even .full infinity &&
    checkGeometricNonFiniteZeroPolicy R3 .even .full nan &&
    checkGeometricNonFiniteZeroPolicy R3 .full .even infinity &&
    checkGeometricNonFiniteZeroPolicy R3 .full .even nan

-- R1 has no closed plan and therefore exercises both direct fallback scans.
#guard
  let infinity := 1.0 / 0.0
  let nan := 0.0 / 0.0
  checkGeometricNonFiniteZeroPolicy R1 .even .full infinity &&
    checkGeometricNonFiniteZeroPolicy R1 .even .full nan &&
    checkGeometricNonFiniteZeroPolicy R1 .full .even infinity &&
    checkGeometricNonFiniteZeroPolicy R1 .full .even nan

/-! ## Dimension-zero odd phantom slot -/

/-
The physical odd slot is logically invisible at dimension zero but remains an
operand of the packed kernels. Two phantom values therefore multiply as scalar
raw slots in all four products, producing a visible even scalar result.
-/
#guard
  let sig := Signature.euclidean 0
  let oddA : MV sig .odd :=
    (MV.ofDataArray? sig .odd (DataArray.ofArray #[2.0])).getD (MV.zero sig .odd)
  let oddB : MV sig .odd :=
    (MV.ofDataArray? sig .odd (DataArray.ofArray #[-3.0])).getD (MV.zero sig .odd)
  let geometric := MV.mulDirect oddA oddB
  let wedge := MV.wedge oddA oddB
  let left := MV.leftContract oddA oddB
  let right := MV.rightContract oddA oddB
  oddA.isWellFormed && oddB.isWellFormed &&
    oddA.coeff 0 == 0.0 && oddB.coeff 0 == 0.0 &&
    oddA.coeffPacked 0 == 2.0 && oddB.coeffPacked 0 == -3.0 &&
    geometric.isWellFormed && wedge.isWellFormed &&
    left.isWellFormed && right.isWellFormed &&
    geometric.coeffPacked 0 == -6.0 && geometric.coeff 0 == -6.0 &&
    wedge.coeffPacked 0 == -6.0 && wedge.coeff 0 == -6.0 &&
    left.coeffPacked 0 == -6.0 && left.coeff 0 == -6.0 &&
    right.coeffPacked 0 == -6.0 && right.coeff 0 == -6.0

end Grassmann.MVProductTests

/-
  Grassmann/MVProjectionTests.lean - Focused packed projection regressions

  These compile-time checks pin the packed rank/unrank maps, projection and
  widening semantics, generic-dimension fallback, and full-storage typeclass
  surface independently of the randomized runtime suite.
-/
import Grassmann.MVDense

namespace Grassmann.MVProjectionTests

set_option linter.hashCommand false

open scoped Grassmann

/-! ## Shared exact checks -/

/-- Compare every blade coefficient exposed by two possibly different layouts. -/
private def coefficientsEqual {n : Nat} {sig : Signature n} {p q : Parity}
    (a : MV sig p) (b : MV sig q) : Bool :=
  (List.range (2 ^ n)).all fun mask => a.coeff mask == b.coeff mask

/-- The distinct, exactly represented, nonzero value assigned to one blade. -/
private def slotValue (mask : Nat) : Float :=
  let magnitude := Float.ofNat (mask + 1)
  if mask % 2 == 0 then magnitude else -magnitude

/-- Distinct, exactly represented, nonzero coefficients for every blade mask. -/
private def allSlotPairs (size : Nat) : List (Nat × Float) :=
  (List.range size).map fun mask => (mask, slotValue mask)

/-- Confirm that construction preserved every member of the all-slot fixture. -/
private def hasAllSlotFixture {n : Nat} {sig : Signature n} (m : MV sig .full) : Bool :=
  (List.range (2 ^ n)).all fun mask => m.coeff mask == slotValue mask

/-- Check an exact grade projection without relying on a dense implementation. -/
private def isExactGradeProjection {n : Nat} {sig : Signature n} {p : Parity}
    (source projected : MV sig p) (grade : Nat) : Bool :=
  projected.isWellFormed && (List.range (2 ^ n)).all fun mask =>
    projected.coeff mask ==
      (if popcount mask == grade then source.coeff mask else 0.0)

/-- The public packed maps enumerate precisely the masks admitted by a parity. -/
private def rankUnrankExact (n : Nat) (p : Parity) : Bool :=
  let expected := MV.computeIndices n p
  let packedRoundTrips := (List.range expected.size).all fun rank =>
    let mask := expected.getD rank 0
    MV.unpackIdxValid n p rank == mask &&
      MV.unpackIdx n p rank == mask &&
      MV.packIdxValid n p mask == rank &&
      MV.packIdx n p mask == rank &&
      MV.computePackIdx n p mask == rank
  let admittedMasksRoundTrip := (List.range (2 ^ n)).all fun mask =>
    if Parity.containsMask p mask then
      MV.unpackIdx n p (MV.packIdx n p mask) == mask
    else
      MV.packIdx n p mask == 0
  let firstInvalidRank := storageSize n p
  let firstInvalidMask := 2 ^ n
  let boundaryBehavior := match p with
    | .full =>
        MV.unpackIdx n .full firstInvalidRank == firstInvalidRank &&
          MV.packIdx n .full firstInvalidMask == firstInvalidMask &&
          MV.computePackIdx n .full firstInvalidMask == 0
    | .even =>
        MV.unpackIdx n .even firstInvalidRank == 0 &&
          MV.packIdx n .even firstInvalidMask == 0 &&
          MV.computePackIdx n .even firstInvalidMask == 0
    | .odd =>
        MV.unpackIdx n .odd firstInvalidRank == 0 &&
          MV.packIdx n .odd firstInvalidMask == 0 &&
          MV.computePackIdx n .odd firstInvalidMask == 0
  MV.indices n p == expected &&
    expected.size == storageSize n p &&
    packedRoundTrips && admittedMasksRoundTrip && boundaryBehavior

/-! ## Rank/unrank maps -/

/- Cached and generic rank/unrank paths are exhaustive through dimension twelve. -/
#guard
  (List.range 12).all fun offset =>
    let n := offset + 1
    rankUnrankExact n .full &&
      rankUnrankExact n .even &&
      rankUnrankExact n .odd

/- Dimension zero and invalid inputs retain their exact total-function behavior. -/
#guard
  MV.indices 0 .full == #[0] &&
    MV.indices 0 .even == #[0] &&
    MV.indices 0 .odd == #[] &&
    storageSize 0 .full == 1 &&
    storageSize 0 .even == 1 &&
    storageSize 0 .odd == 1 &&
    MV.unpackIdx 0 .full 0 == 0 && MV.unpackIdx 0 .full 7 == 7 &&
    MV.unpackIdx 0 .even 0 == 0 && MV.unpackIdx 0 .even 1 == 0 &&
    MV.unpackIdx 0 .odd 0 == 0 &&
    MV.packIdx 0 .full 0 == 0 && MV.packIdx 0 .full 7 == 7 &&
    MV.computePackIdx 0 .full 0 == 0 && MV.computePackIdx 0 .full 7 == 0 &&
    MV.packIdx 0 .even 0 == 0 && MV.packIdx 0 .even 1 == 0 &&
    MV.computePackIdx 0 .even 0 == 0 && MV.computePackIdx 0 .even 1 == 0 &&
    MV.packIdx 0 .odd 0 == 0 && MV.packIdx 0 .odd 1 == 0 &&
    MV.computePackIdx 0 .odd 0 == 0 && MV.computePackIdx 0 .odd 1 == 0 &&
    MV.unpackIdx 3 .full 8 == 8 &&
    MV.unpackIdx 3 .even 4 == 0 && MV.unpackIdx 3 .odd 4 == 0 &&
    MV.packIdx 3 .full 8 == 8 && MV.computePackIdx 3 .full 8 == 0 &&
    MV.packIdx 3 .even 1 == 0 && MV.computePackIdx 3 .even 1 == 0 &&
    MV.packIdx 3 .even 7 == 0 && MV.computePackIdx 3 .even 7 == 0 &&
    MV.packIdx 3 .even 8 == 0 && MV.computePackIdx 3 .even 8 == 0 &&
    MV.packIdx 3 .odd 0 == 0 && MV.computePackIdx 3 .odd 0 == 0 &&
    MV.packIdx 3 .odd 6 == 0 && MV.computePackIdx 3 .odd 6 == 0 &&
    MV.packIdx 3 .odd 8 == 0 && MV.computePackIdx 3 .odd 8 == 0

/- Dimension-zero projectors expose the scalar only through full/even storage. -/
#guard
  let sig := Signature.euclidean 0
  let full : MV sig .full := MV.ofPairs sig .full [(0, 3.0)]
  let even := MV.evenPart full
  let odd := MV.oddPart full
  let evenFull := MV.evenToFull even
  let oddFull := MV.oddToFull odd
  let oddFromDense := MV.ofMultivector (MV.toMultivector full) .odd
  full.isWellFormed && even.isWellFormed && odd.isWellFormed &&
    evenFull.isWellFormed && oddFull.isWellFormed && oddFromDense.isWellFormed &&
    full.coeff 0 == 3.0 && even.coeff 0 == 3.0 && odd.coeff 0 == 0.0 &&
    odd.coeffPacked 0 == 3.0 && oddFromDense.coeffPacked 0 == 3.0 &&
    evenFull.coeff 0 == 3.0 && oddFull.coeff 0 == 0.0 &&
    oddFull.coeffPacked 0 == 0.0 &&
    (MV.gradeProject full 0).coeff 0 == 3.0 &&
    (MV.gradeProject full 1).coeff 0 == 0.0 &&
    (MV.gradeProject odd 0).coeffPacked 0 == 3.0 &&
    (MV.gradeProject odd 1).coeffPacked 0 == 0.0

/-! ## Exact CGA3 projection and widening fixture -/

/- Every CGA3 slot survives its parity projection, widening, and round trip. -/
#guard
  let full : MV CGA3 .full := MV.ofPairs CGA3 .full (allSlotPairs 32)
  let even := MV.evenPart full
  let odd := MV.oddPart full
  let evenFull := MV.evenToFull even
  let oddFull := MV.oddToFull odd
  let evenCoerced : MV CGA3 .full := even
  let oddCoerced : MV CGA3 .full := odd
  hasAllSlotFixture full &&
    full.isWellFormed && even.isWellFormed && odd.isWellFormed &&
    evenFull.isWellFormed && oddFull.isWellFormed &&
    coefficientsEqual (MV.evenPart evenFull) even &&
    coefficientsEqual (MV.oddPart oddFull) odd &&
    coefficientsEqual evenFull evenCoerced &&
    coefficientsEqual oddFull oddCoerced &&
    coefficientsEqual (MV.add evenFull oddFull) full &&
    (List.range 32).all fun mask =>
      even.coeff mask ==
          (if Parity.containsMask .even mask then full.coeff mask else 0.0) &&
        odd.coeff mask ==
          (if Parity.containsMask .odd mask then full.coeff mask else 0.0)

/- Grades zero through six are exact in full, even, and odd storage. -/
#guard
  let full : MV CGA3 .full := MV.ofPairs CGA3 .full (allSlotPairs 32)
  let even := MV.evenPart full
  let odd := MV.oddPart full
  let gradesExact := (List.range 7).all fun grade =>
    isExactGradeProjection full (MV.gradeProject full grade) grade &&
      isExactGradeProjection even (MV.gradeProject even grade) grade &&
      isExactGradeProjection odd (MV.gradeProject odd grade) grade
  let reconstructed := (List.range 7).foldl
    (fun acc grade => MV.add acc (MV.gradeProject full grade))
    (MV.zero CGA3 .full)
  gradesExact && coefficientsEqual reconstructed full

/-! ## Generic dimension-six fallback -/

/- The first uncached layout preserves all 64 slots through projection and widening. -/
#guard
  let sig := Signature.euclidean 6
  let full : MV sig .full := MV.ofPairs sig .full (allSlotPairs 64)
  let even := MV.evenPart full
  let odd := MV.oddPart full
  let evenFull := MV.evenToFull even
  let oddFull := MV.oddToFull odd
  let reconstructed := (List.range 7).foldl
    (fun acc grade => MV.add acc (MV.gradeProject full grade))
    (MV.zero sig .full)
  hasAllSlotFixture full &&
    full.isWellFormed && even.isWellFormed && odd.isWellFormed &&
    evenFull.isWellFormed && oddFull.isWellFormed &&
    coefficientsEqual (MV.evenPart evenFull) even &&
    coefficientsEqual (MV.oddPart oddFull) odd &&
    coefficientsEqual (MV.add evenFull oddFull) full &&
    coefficientsEqual reconstructed full &&
    (List.range 7).all fun grade =>
      isExactGradeProjection full (MV.gradeProject full grade) grade &&
        isExactGradeProjection even (MV.gradeProject even grade) grade &&
        isExactGradeProjection odd (MV.gradeProject odd grade) grade

/-! ## Full-storage typeclass and scoped notation -/

/- Named `GAlgebra` projection and scoped grade notation dispatch to packed `MV`. -/
#guard
  let full : MV CGA3 .full := MV.ofPairs CGA3 .full (allSlotPairs 32)
  let namedExact := (List.range 7).all fun grade =>
    coefficientsEqual
      (GAlgebra.gradeProject CGA3 Float full grade)
      (MV.gradeProject full grade)
  namedExact &&
    coefficientsEqual (⟨full⟩₀) (MV.gradeProject full 0) &&
    coefficientsEqual (⟨full⟩₁) (MV.gradeProject full 1) &&
    coefficientsEqual (⟨full⟩₂) (MV.gradeProject full 2) &&
    coefficientsEqual (⟨full⟩₃) (MV.gradeProject full 3)

end Grassmann.MVProjectionTests

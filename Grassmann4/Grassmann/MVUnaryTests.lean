/-
  Grassmann/MVUnaryTests.lean - Focused packed unary-operation regressions

  These compile-time checks pin packed index decoding and the exact unary
  layouts used by reverse, involution, conjugation, and projections.
-/
import Grassmann.Spinor

namespace Grassmann.MVUnaryTests

set_option linter.hashCommand false

/-! ## Shared exact checks -/

/-- Compare every blade coefficient exposed by two packed values. -/
private def packedCoefficientsEqual {n : Nat} {sig : Signature n} {p : Parity}
    (a b : MV sig p) : Bool :=
  (List.range (2 ^ n)).all fun mask => a.coeff mask == b.coeff mask

/-- Compare every packed coefficient with an independent dense result. -/
private def matchesDenseExact {n : Nat} {sig : Signature n} {p : Parity}
    (packed : MV sig p) (dense : Multivector sig Float) : Bool :=
  packed.isWellFormed && (List.finRange (2 ^ n)).all fun i =>
    packed.coeff i.val == dense.coeffs i

/-- Check unary semantics, buffer shape, and involution laws. -/
private def checkUnary {n : Nat} {sig : Signature n} {p : Parity}
    (m : MV sig p) : Bool :=
  let dense := MV.toMultivector m
  let reversed := MV.rev m
  let involuted := MV.involute m
  let conjugated := MV.conjugate m
  matchesDenseExact reversed dense.reverse &&
    matchesDenseExact involuted dense.involute &&
    matchesDenseExact conjugated dense.conjugate &&
    packedCoefficientsEqual (MV.rev reversed) m &&
    packedCoefficientsEqual (MV.involute involuted) m &&
    packedCoefficientsEqual (MV.conjugate conjugated) m &&
    packedCoefficientsEqual conjugated (MV.involute reversed)

/-- Every CGA3 blade slot receives a distinct, nonzero coefficient. -/
private def cga3AllSlotPairs : List (Nat × Float) :=
  (List.range 32).map fun mask =>
    let magnitude := Float.ofNat (mask + 1)
    (mask, if mask % 2 == 0 then magnitude else -magnitude)

/-! ## Full-storage index identity -/

/- Every valid full packed index is already its blade mask. -/
#guard
  (List.range 7).all fun n =>
    (List.range (2 ^ n)).all fun i =>
      MV.unpackIdx n .full i == i && MV.packIdx n .full i == i

/-! ## Deterministic all-slot unary checks -/

/- Full, even, and odd CGA3 storage observe every packed slot and grade sign. -/
#guard
  let full : MV CGA3 .full := MV.ofPairs CGA3 .full cga3AllSlotPairs
  let even : MV CGA3 .even := MV.ofPairs CGA3 .even cga3AllSlotPairs
  let odd : MV CGA3 .odd := MV.ofPairs CGA3 .odd cga3AllSlotPairs
  checkUnary full && checkUnary even && checkUnary odd

/- The R2 odd layout used by the curve-shortening port remains covered. -/
#guard
  let odd : MV R2 .odd := MV.ofPairs R2 .odd [(1, 3.0), (2, -4.0)]
  checkUnary odd

/- Full typeclass methods and thin Spinor/PGA motor wrappers use packed unary operations. -/
#guard
  let full : MV CGA3 .full := MV.ofPairs CGA3 .full cga3AllSlotPairs
  let even : MV CGA3 .even := MV.ofPairs CGA3 .even cga3AllSlotPairs
  let spinor := Spinor.ofMV even
  let motor : PGA.Motor PGA3 := MV.ofPairs PGA3 .even
    [(0, 1.0), (3, 2.0), (5, -3.0), (6, 4.0),
     (9, 5.0), (10, -6.0), (12, 7.0), (15, -8.0)]
  packedCoefficientsEqual (GAlgebra.reverse CGA3 Float full) (MV.rev full) &&
    packedCoefficientsEqual (GAlgebra.involute CGA3 Float full) (MV.involute full) &&
    packedCoefficientsEqual (GAlgebra.conjugate CGA3 Float full) (MV.conjugate full) &&
    packedCoefficientsEqual (Spinor.reverse spinor).mv (MV.rev even) &&
    packedCoefficientsEqual (PGA.Motor.rev motor) (MV.rev motor)

end Grassmann.MVUnaryTests

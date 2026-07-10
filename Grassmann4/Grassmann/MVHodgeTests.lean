/-
  Grassmann/MVHodgeTests.lean - Focused packed Hodge-dual regressions

  These compile-time checks pin every stored slot, cached/fallback dispatch,
  degenerate PGA3 orientation, and second-dual behavior independently of the
  randomized runtime suite.
-/
import Grassmann.MVDense

namespace Grassmann.MVHodgeTests

set_option linter.hashCommand false

/-- Distinct, exactly represented nonzero coefficients for every blade mask. -/
private def allSlotPairs (size : Nat) : List (Nat × Float) :=
  (List.range size).map fun mask =>
    let magnitude := Float.ofNat (mask + 1)
    (mask, if mask % 2 == 0 then magnitude else -magnitude)

/-- Compare every packed coefficient with an independent dense result. -/
private def matchesDenseExact {n : Nat} {sig : Signature n}
    (packed : MV sig .full) (dense : Multivector sig Float) : Bool :=
  packed.isWellFormed && (List.finRange (2 ^ n)).all fun i =>
    packed.coeff i.val == dense.coeffs i

/-- Check the first and second packed dual against the dense implementation. -/
private def checkHodge {n : Nat} (sig : Signature n) : Bool :=
  let m : MV sig .full := MV.ofPairs sig .full (allSlotPairs (2 ^ n))
  let dense := MV.toMultivector m
  let first := MV.hodgeDual m
  let second := MV.hodgeDual first
  matchesDenseExact first dense.hodgeDual &&
    matchesDenseExact second dense.hodgeDual.hodgeDual

/-! ## Small-mask and generic dispatch -/

/- Standard signatures and both ends of the fixed UInt64 mask path observe every slot. -/
#guard
  checkHodge (Signature.euclidean 0) && checkHodge R1 && checkHodge R2 &&
    checkHodge R3 && checkHodge R4 && checkHodge STA && checkHodge PGA3 &&
    checkHodge CGA3 && checkHodge (Signature.euclidean 6)

/- Dimension seven is the first generic sign-computation fallback. -/
#guard checkHodge (Signature.euclidean 7)

/-! ## Exact orientation and second-dual laws -/

/- The odd-dimensional CGA3 left complement squares to the identity. -/
#guard
  let m : MV CGA3 .full := MV.ofPairs CGA3 .full (allSlotPairs 32)
  let twice := MV.hodgeDual (MV.hodgeDual m)
  (List.range 32).all fun mask => twice.coeff mask == m.coeff mask

/- PGA3 orientation is metric-degenerate but complement signs remain exact. -/
#guard
  let projectiveAxis : MV PGA3 .full := MV.ofPairs PGA3 .full [(8, 1.0)]
  let euclideanVolume : MV PGA3 .full := MV.ofPairs PGA3 .full [(7, 1.0)]
  let m : MV PGA3 .full := MV.ofPairs PGA3 .full (allSlotPairs 16)
  let twice := MV.hodgeDual (MV.hodgeDual m)
  (MV.hodgeDual projectiveAxis).coeff 7 == -1.0 &&
    (MV.hodgeDual euclideanVolume).coeff 8 == 1.0 &&
    (List.range 16).all fun mask =>
      twice.coeff mask == (MV.involute m).coeff mask

end Grassmann.MVHodgeTests

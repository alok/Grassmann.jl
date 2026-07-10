/-
  Grassmann/MVDenseTests.lean - Exact dense/packed conversion regressions

  These compile-time checks pin dense-to-packed ingress independently of the
  arithmetic rank/unrank helpers used by the optimized implementation.  The
  fixtures deliberately give every dense blade a distinct nonzero coefficient.
-/
import Grassmann.MVDense

namespace Grassmann.MVDenseTests

set_option linter.hashCommand false

/-! ## Independent conversion oracle -/

/-- A distinct, exactly represented, nonzero coefficient for every blade. -/
private def slotValue (mask : Nat) : Float :=
  let magnitude := Float.ofNat (mask + 1)
  if mask % 2 == 0 then magnitude else -magnitude

/-- Independent parity predicate used by the expected-value oracle. -/
private def expectedContains (p : Parity) (mask : Nat) : Bool :=
  match p with
  | .full => true
  | .even => popcount mask % 2 == 0
  | .odd => popcount mask % 2 == 1

/-- Dense source whose closure computes a different nonzero value at each mask. -/
private def denseFixture {n : Nat} (sig : Signature n) : Multivector sig Float :=
  ⟨fun i => slotValue i.val⟩

/-- Expected packed mask order, defined without any `MV` indexing helper. -/
private def expectedMasks (n : Nat) (p : Parity) : Array Nat :=
  (Array.range (2 ^ n)).filter fun mask => expectedContains p mask

/-- The physical packed buffer agrees with the independent mask enumeration. -/
private def physicalIngressExact {n : Nat} {sig : Signature n} {p : Parity}
    (packed : MV sig p) : Bool :=
  let masks := expectedMasks n p
  masks.size == storageSize n p &&
    (Array.range masks.size).all fun rank =>
      packed.coeffPacked rank == slotValue (masks.getD rank 0)

/-- Public packed coefficients expose the parity projection of the dense source. -/
private def publicCoefficientsExact {n : Nat} {sig : Signature n} {p : Parity}
    (packed : MV sig p) : Bool :=
  (List.range (2 ^ n)).all fun mask =>
    packed.coeff mask ==
      (if expectedContains p mask then slotValue mask else 0.0)

/-- Exercise the closure returned by `toMultivector` at every dense coefficient. -/
private def denseClosureExact {n : Nat} {sig : Signature n} {p : Parity}
    (packed : MV sig p) : Bool :=
  let dense := MV.toMultivector packed
  (List.finRange (2 ^ n)).all fun i =>
    dense.coeffs i ==
      (if expectedContains p i.val then slotValue i.val else 0.0)

/-- Two packed values have identical physical buffers. -/
private def physicalBuffersEqual {n : Nat} {sig : Signature n} {p : Parity}
    (a b : MV sig p) : Bool :=
  (List.range (storageSize n p)).all fun rank =>
    a.coeffPacked rank == b.coeffPacked rank

/-- Exact ingress, projection, closure, shape, and packed round-trip checks. -/
private def checkIngress {n : Nat} (sig : Signature n) (p : Parity) : Bool :=
  let source := denseFixture sig
  let packed := MV.ofMultivector source p
  let denseRoundTrip := MV.toMultivector packed
  let packedRoundTrip := MV.ofMultivector denseRoundTrip p
  packed.isWellFormed && packedRoundTrip.isWellFormed &&
    packed.coeffs.size == storageSize n p &&
    packedRoundTrip.coeffs.size == storageSize n p &&
    packed.coefficientCount == storageSize n p &&
    physicalIngressExact packed &&
    publicCoefficientsExact packed &&
    denseClosureExact packed &&
    physicalBuffersEqual packedRoundTrip packed

/-! ## Dimension-zero edge layout -/

/- All dimension-zero layouts own one physical slot.  Odd ingress retains the
   dense scalar only in that hidden slot; its public and dense views are zero. -/
#guard
  let sig := Signature.euclidean 0
  let source := denseFixture sig
  let full : MV sig .full := MV.ofMultivector source .full
  let even : MV sig .even := MV.ofMultivector source .even
  let odd : MV sig .odd := MV.ofMultivector source .odd
  let fullDense := MV.toMultivector full
  let evenDense := MV.toMultivector even
  let oddDense := MV.toMultivector odd
  let fullRoundTrip : MV sig .full := MV.ofMultivector fullDense .full
  let evenRoundTrip : MV sig .even := MV.ofMultivector evenDense .even
  let oddRoundTrip : MV sig .odd := MV.ofMultivector oddDense .odd
  storageSize 0 .full == 1 && storageSize 0 .even == 1 && storageSize 0 .odd == 1 &&
    full.coeffs.size == 1 && even.coeffs.size == 1 && odd.coeffs.size == 1 &&
    full.isWellFormed && even.isWellFormed && odd.isWellFormed &&
    fullRoundTrip.isWellFormed && evenRoundTrip.isWellFormed && oddRoundTrip.isWellFormed &&
    full.coeffPacked 0 == 1.0 && even.coeffPacked 0 == 1.0 && odd.coeffPacked 0 == 1.0 &&
    full.coeff 0 == 1.0 && even.coeff 0 == 1.0 && odd.coeff 0 == 0.0 &&
    fullDense.coeffs ⟨0, by decide⟩ == 1.0 &&
    evenDense.coeffs ⟨0, by decide⟩ == 1.0 &&
    oddDense.coeffs ⟨0, by decide⟩ == 0.0 &&
    fullRoundTrip.coeffPacked 0 == 1.0 && evenRoundTrip.coeffPacked 0 == 1.0 &&
    oddRoundTrip.coeffPacked 0 == 0.0

/-! ## Cached and generic dimensions -/

/- Dimension one pins the smallest nontrivial parity split. -/
#guard
  let sig := Signature.euclidean 1
  checkIngress sig .full && checkIngress sig .even && checkIngress sig .odd

/- CGA3 pins all thirty-two coefficients of the largest cached layout. -/
#guard
  checkIngress CGA3 .full && checkIngress CGA3 .even && checkIngress CGA3 .odd

/- Dimension six pins the first generic, non-cached layout. -/
#guard
  let sig := Signature.euclidean 6
  checkIngress sig .full && checkIngress sig .even && checkIngress sig .odd

/- Dimension twelve stress-tests exact ingress and closure round trips over all
   4096 dense blades and both 2048-coefficient packed parity layouts. -/
#guard
  let sig := Signature.euclidean 12
  checkIngress sig .full && checkIngress sig .even && checkIngress sig .odd

end Grassmann.MVDenseTests

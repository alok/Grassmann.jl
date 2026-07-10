/-
  Grassmann/MVArithmeticTests.lean - Focused packed arithmetic regressions

  These compile-time checks keep packed subtraction aligned with its dense
  reference across full, even, and odd storage layouts.
-/
import Grassmann.MVDense

namespace Grassmann.MVArithmeticTests

set_option linter.hashCommand false

/-! ## Shared exact checks -/

/-- Compare every blade coefficient exposed by two packed values. -/
private def packedCoefficientsEqual {n : Nat} {sig : Signature n} {p : Parity}
    (a b : MV sig p) : Bool :=
  (List.range (2 ^ n)).all fun mask => a.coeff mask == b.coeff mask

/-- Compare packed subtraction with the independent dense implementation. -/
private def matchesDenseSubtraction {n : Nat} {sig : Signature n} {p : Parity}
    (a b result : MV sig p) : Bool :=
  let denseResult := MV.toMultivector a - MV.toMultivector b
  (List.finRange (2 ^ n)).all fun i =>
    result.coeff i.val == denseResult.coeffs i

/-- Check the direct API, operator instance, expected coefficients, and layout invariant. -/
private def checkSubtraction {n : Nat} {sig : Signature n} {p : Parity}
    (a b : MV sig p) (expected : List (Nat × Float)) : Bool :=
  let direct := MV.sub a b
  let operator := a - b
  direct.isWellFormed && operator.isWellFormed &&
    expected.all (fun (mask, value) => direct.coeff mask == value) &&
    packedCoefficientsEqual direct operator &&
    matchesDenseSubtraction a b direct &&
    matchesDenseSubtraction a b operator

/-! ## Representative layouts and signatures -/

/- The R2 odd layout used by the MV-backed curve-shortening port. -/
#guard
  let a : MV R2 .odd := MV.ofPairs R2 .odd [(1, 7.5), (2, -3.0)]
  let b : MV R2 .odd := MV.ofPairs R2 .odd [(1, 2.5), (2, 4.0)]
  checkSubtraction a b [(1, 5.0), (2, -7.0)]

/- Full R3 storage checks every one of its eight blade slots. -/
#guard
  let a : MV R3 .full := MV.ofPairs R3 .full
    [(0, 10.0), (1, -2.0), (2, 7.0), (3, 0.5),
     (4, -8.0), (5, 3.25), (6, 12.0), (7, -1.5)]
  let b : MV R3 .full := MV.ofPairs R3 .full
    [(0, 3.0), (1, 5.0), (2, -1.0), (3, -1.5),
     (4, -2.0), (5, 0.25), (6, 4.0), (7, 2.5)]
  checkSubtraction a b
    [(0, 7.0), (1, -7.0), (2, 8.0), (3, 2.0),
     (4, -6.0), (5, 3.0), (6, 8.0), (7, -4.0)]

/- Packed PGA3 even storage checks all scalar, bivector, and pseudoscalar slots. -/
#guard
  let a : MV PGA3 .even := MV.ofPairs PGA3 .even
    [(0, 1.0), (3, 2.0), (5, -3.0), (6, 4.0),
     (9, 5.0), (10, -6.0), (12, 7.0), (15, 8.0)]
  let b : MV PGA3 .even := MV.ofPairs PGA3 .even
    [(0, -1.0), (3, 0.5), (5, -1.0), (6, 10.0),
     (9, 2.0), (10, -2.0), (12, 9.0), (15, -4.0)]
  checkSubtraction a b
    [(0, 2.0), (3, 1.5), (5, -2.0), (6, -6.0),
     (9, 3.0), (10, -4.0), (12, -2.0), (15, 12.0)]

/- The sixteen-slot CGA3 odd layout exercises the largest cached pack map. -/
#guard
  let a : MV CGA3 .odd := MV.ofPairs CGA3 .odd
    [(1, 16.0), (2, -15.0), (4, 14.0), (7, -13.0),
     (8, 12.0), (11, -11.0), (13, 10.0), (14, -9.0),
     (16, 8.0), (19, -7.0), (21, 6.0), (22, -5.0),
     (25, 4.0), (26, -3.0), (28, 2.0), (31, -1.0)]
  let b : MV CGA3 .odd := MV.ofPairs CGA3 .odd
    [(1, 1.0), (2, -2.0), (4, 3.0), (7, -4.0),
     (8, 5.0), (11, -6.0), (13, 7.0), (14, -8.0),
     (16, 9.0), (19, -10.0), (21, 11.0), (22, -12.0),
     (25, 13.0), (26, -14.0), (28, 15.0), (31, -16.0)]
  checkSubtraction a b
    [(1, 15.0), (2, -13.0), (4, 11.0), (7, -9.0),
     (8, 7.0), (11, -5.0), (13, 3.0), (14, -1.0),
     (16, -1.0), (19, 3.0), (21, -5.0), (22, 7.0),
     (25, -9.0), (26, 11.0), (28, -13.0), (31, 15.0)]

end Grassmann.MVArithmeticTests

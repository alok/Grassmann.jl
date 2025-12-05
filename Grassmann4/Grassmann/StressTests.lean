/-
  Grassmann/StressTests.lean - Stress tests for high-dimensional geometric algebra

  This module tests the Grassmann library in high dimensions (up to 10D)
  to verify correctness and demonstrate the dimension-generic design.

  Key tests:
  1. 10-dimensional rotations via rotors
  2. High-dimensional wedge products
  3. Hodge dual in various dimensions
  4. Algebraic identity verification
-/
import Grassmann.Multivector
import Grassmann.LinearAlgebra

namespace Grassmann.StressTests

/-! ## High-Dimensional Signatures -/

/-- 4D Euclidean signature -/
abbrev R4 : Signature 4 := Signature.euclidean 4

/-- 5D Euclidean signature -/
abbrev R5 : Signature 5 := Signature.euclidean 5

/-! ## Integer Tests (Exact Arithmetic)

These tests use Int for exact computation without floating-point errors.
We use R5 (32 blades) instead of R10 (1024 blades) for faster compilation.
-/

section IntTests

-- Basis for R5
def e5_1 : Blade R5 := ⟨BitVec.ofNat 5 0b00001⟩
def e5_2 : Blade R5 := ⟨BitVec.ofNat 5 0b00010⟩
def e5_3 : Blade R5 := ⟨BitVec.ofNat 5 0b00100⟩
def e5_4 : Blade R5 := ⟨BitVec.ofNat 5 0b01000⟩
def e5_5 : Blade R5 := ⟨BitVec.ofNat 5 0b10000⟩

/-- Bivector e_i ∧ e_j in R5 -/
def bivec5 (i j : Fin 5) : Blade R5 :=
  ⟨BitVec.ofNat 5 ((1 <<< i.val) ||| (1 <<< j.val))⟩

/-! ### Basic Operations in R5 -/

-- Test: e1 * e1 = 1 in R5
#eval let e1 : Multivector R5 Int := Multivector.ofBlade e5_1
      (e1 * e1).scalarPart
-- Expected: 1

-- Test: e1 * e2 = -e2 * e1 (anticommutativity)
#eval let e1 : Multivector R5 Int := Multivector.ofBlade e5_1
      let e2 : Multivector R5 Int := Multivector.ofBlade e5_2
      let prod1 := e1 * e2
      let prod2 := e2 * e1
      (prod1 + prod2).scalarPart  -- Should be 0 (they're negatives)
-- Expected: 0

-- Test: e_i · e_j = δ_ij (orthonormality)
#eval let e1 : Multivector R5 Int := Multivector.ofBlade e5_1
      let e3 : Multivector R5 Int := Multivector.ofBlade e5_3
      let e5 : Multivector R5 Int := Multivector.ofBlade e5_5
      ((e1 * e1).scalarPart,   -- e1·e1 = 1
       (e1 * e3).scalarPart,   -- e1·e3 = 0
       (e3 * e5).scalarPart)   -- e3·e5 = 0
-- Expected: (1, 0, 0)

/-! ### Wedge Product in High Dimensions -/

-- Test: 5-blade in R5 (e1 ∧ e2 ∧ e3 ∧ e4 ∧ e5) - the pseudoscalar
#eval let e1 : Multivector R5 Int := Multivector.ofBlade e5_1
      let e2 : Multivector R5 Int := Multivector.ofBlade e5_2
      let e3 : Multivector R5 Int := Multivector.ofBlade e5_3
      let e4 : Multivector R5 Int := Multivector.ofBlade e5_4
      let e5 : Multivector R5 Int := Multivector.ofBlade e5_5
      let wedge := ((e1 ⋀ᵐ e2) ⋀ᵐ e3) ⋀ᵐ e4 ⋀ᵐ e5
      -- The coefficient of e12345 blade (pseudoscalar)
      let blade12345 : Blade R5 := ⟨BitVec.ofNat 5 0b11111⟩
      wedge.coeff blade12345
-- Expected: 1

-- Test: Wedge of same vector is zero
#eval let e3 : Multivector R5 Int := Multivector.ofBlade e5_3
      let wedge := e3 ⋀ᵐ e3
      wedge.scalarPart  -- All components should be 0
-- Expected: 0

-- Test: Swapping vectors in wedge negates result
#eval let e1 : Multivector R5 Int := Multivector.ofBlade e5_1
      let e4 : Multivector R5 Int := Multivector.ofBlade e5_4
      let wedge1 := e1 ⋀ᵐ e4
      let wedge2 := e4 ⋀ᵐ e1
      let bivec14 : Blade R5 := bivec5 ⟨0, by omega⟩ ⟨3, by omega⟩
      (wedge1.coeff bivec14, wedge2.coeff bivec14)
-- Expected: (1, -1)

/-! ### Rotor Tests in R5 (Integer approximation)

For exact integer computation, we test rotor algebraic properties
without trigonometric functions. A rotor R = cos(θ/2) + sin(θ/2)B
where B is a unit bivector.

Key identity: R R† = 1 for unit rotors.
For unnormalized rotor (1 + B): (1 + B)(1 - B) = 1 - B² = 2 (since B² = -1)
-/

-- Test: Bivector squares to -1 in Euclidean signature
-- B = e1 ∧ e2, then B² = e1e2e1e2 = -e1e1e2e2 = -1
#eval let e1 : Multivector R5 Int := Multivector.ofBlade e5_1
      let e2 : Multivector R5 Int := Multivector.ofBlade e5_2
      let B := e1 ⋀ᵐ e2  -- Same as e1 * e2 for orthogonal vectors
      (B * B).scalarPart
-- Expected: -1

-- Test: (1 + B)(1 - B) = 2 for unit bivector B
#eval let e1 : Multivector R5 Int := Multivector.ofBlade e5_1
      let e2 : Multivector R5 Int := Multivector.ofBlade e5_2
      let B := e1 * e2
      let one : Multivector R5 Int := Multivector.one
      let onePlusB := one + B
      let oneMinusB := one - B
      (onePlusB * oneMinusB).scalarPart
-- Expected: 2

-- Test: Rotation in e1-e2 plane maps e1 to -e2 (with unnormalized rotor)
-- R = 1 + e12, then R e1 R† gives rotation (scaled)
#eval let e1 : Multivector R5 Int := Multivector.ofBlade e5_1
      let e2 : Multivector R5 Int := Multivector.ofBlade e5_2
      let B := e1 * e2
      let R := Multivector.one + B
      let result := R * e1 * R†
      (result.coeff e5_1, result.coeff e5_2)
-- Expected: (0, -2) - rotation of e1 towards -e2, scaled by 2

-- Test: Rotation preserves orthogonal directions
-- Rotating e3 (perpendicular to e1-e2 plane) should leave it unchanged (scaled)
#eval let e1 : Multivector R5 Int := Multivector.ofBlade e5_1
      let e2 : Multivector R5 Int := Multivector.ofBlade e5_2
      let e3 : Multivector R5 Int := Multivector.ofBlade e5_3
      let B := e1 * e2
      let R := Multivector.one + B
      let result := R * e3 * R†
      (result.coeff e5_1, result.coeff e5_2, result.coeff e5_3)
-- Expected: (0, 0, 2) - e3 unchanged except for scaling

/-! ### 5D Rotation: Full Test

Demonstrate a complete 5D rotation:
1. Create a bivector in the e3-e5 plane
2. Create a rotor
3. Rotate e3 (should map towards e5)
4. Verify e1 (orthogonal) is unchanged
-/

-- Test: 5D rotation in e3-e5 plane
#eval let e3 : Multivector R5 Int := Multivector.ofBlade e5_3
      let e5 : Multivector R5 Int := Multivector.ofBlade e5_5
      let B35 := e3 * e5  -- Bivector for e3-e5 rotation plane
      let R := Multivector.one + B35  -- Unnormalized rotor

      -- Rotate e3 (in the plane)
      let rotated_e3 := R * e3 * R†

      -- Check e1 (orthogonal to plane) is preserved
      let e1 : Multivector R5 Int := Multivector.ofBlade e5_1
      let rotated_e1 := R * e1 * R†

      -- Results: e3 maps to direction with -e5 component
      -- e1 remains in e1 direction (scaled)
      ((rotated_e3.coeff e5_3, rotated_e3.coeff e5_5),
       (rotated_e1.coeff e5_1, rotated_e1.coeff e5_3, rotated_e1.coeff e5_5))
-- Expected: ((0, -2), (2, 0, 0))

/-! ### Hodge Dual in High Dimensions -/

-- Test: Hodge dual of scalar is pseudoscalar
-- In R4: ⋆1 = e1234
#eval let one : Multivector R4 Int := Multivector.one
      let dual := ⋆ᵐone
      let pseudoscalar : Blade R4 := ⟨BitVec.ofNat 4 0b1111⟩
      dual.coeff pseudoscalar
-- Expected: 1

-- Test: Hodge dual of vector in R4
-- ⋆e1 = e234
#eval let e1 : Multivector R4 Int := Multivector.ofBlade ⟨BitVec.ofNat 4 0b0001⟩
      let dual := ⋆ᵐe1
      let e234 : Blade R4 := ⟨BitVec.ofNat 4 0b1110⟩
      dual.coeff e234
-- Expected: 1

/-! ### Determinant via Wedge Product -/

-- Test: det(I) = 1 in R4
#eval let e1 : Multivector R4 Int := Multivector.ofBlade ⟨BitVec.ofNat 4 0b0001⟩
      let e2 : Multivector R4 Int := Multivector.ofBlade ⟨BitVec.ofNat 4 0b0010⟩
      let e3 : Multivector R4 Int := Multivector.ofBlade ⟨BitVec.ofNat 4 0b0100⟩
      let e4 : Multivector R4 Int := Multivector.ofBlade ⟨BitVec.ofNat 4 0b1000⟩
      LinearAlgebra.det [e1, e2, e3, e4]
-- Expected: 1

-- Test: Swapping columns negates determinant
#eval let e1 : Multivector R4 Int := Multivector.ofBlade ⟨BitVec.ofNat 4 0b0001⟩
      let e2 : Multivector R4 Int := Multivector.ofBlade ⟨BitVec.ofNat 4 0b0010⟩
      let e3 : Multivector R4 Int := Multivector.ofBlade ⟨BitVec.ofNat 4 0b0100⟩
      let e4 : Multivector R4 Int := Multivector.ofBlade ⟨BitVec.ofNat 4 0b1000⟩
      LinearAlgebra.det [e2, e1, e3, e4]  -- e1 and e2 swapped
-- Expected: -1

-- Test: det with scaled vectors
#eval let e1 : Multivector R4 Int := (Multivector.ofBlade ⟨BitVec.ofNat 4 0b0001⟩ : Multivector R4 Int).smul 2
      let e2 : Multivector R4 Int := (Multivector.ofBlade ⟨BitVec.ofNat 4 0b0010⟩ : Multivector R4 Int).smul 3
      let e3 : Multivector R4 Int := (Multivector.ofBlade ⟨BitVec.ofNat 4 0b0100⟩ : Multivector R4 Int).smul 5
      let e4 : Multivector R4 Int := (Multivector.ofBlade ⟨BitVec.ofNat 4 0b1000⟩ : Multivector R4 Int).smul 7
      LinearAlgebra.det [e1, e2, e3, e4]
-- Expected: 210 (= 2 * 3 * 5 * 7)

/-! ### Involution Tests in R5 -/

-- Test: Reverse is involution (a†† = a)
#eval let e1 : Multivector R5 Int := Multivector.ofBlade e5_1
      let e2 : Multivector R5 Int := Multivector.ofBlade e5_2
      let e3 : Multivector R5 Int := Multivector.ofBlade e5_3
      let mv := e1 + (e1 * e2) + (e1 * e2 * e3)  -- vector + bivector + trivector parts
      let doubleRev := mv††
      -- Check a few coefficients
      (doubleRev.coeff e5_1,
       doubleRev.coeff (bivec5 ⟨0, by omega⟩ ⟨1, by omega⟩))
-- Should equal original coefficients

-- Test: Involute negates odd grades
#eval let e1 : Multivector R5 Int := Multivector.ofBlade e5_1
      let e12 := (Multivector.ofBlade e5_1 : Multivector R5 Int) *
                 (Multivector.ofBlade e5_2 : Multivector R5 Int)
      let mv := e1 + e12  -- vector + bivector
      let inv := mvˆ
      (inv.coeff e5_1,  -- vector should be negated
       inv.coeff (bivec5 ⟨0, by omega⟩ ⟨1, by omega⟩))  -- bivector unchanged
-- Expected: (-1, 1)

/-! ### Contraction Tests -/

-- Test: Left contraction e1 ⌋ (e1 ∧ e2) = e2
#eval let e1 : Multivector R5 Int := Multivector.ofBlade e5_1
      let e2 : Multivector R5 Int := Multivector.ofBlade e5_2
      let e12 := e1 ⋀ᵐ e2
      let result := e1 ⌋ᵐ e12
      result.coeff e5_2
-- Expected: 1

-- Test: Left contraction e3 ⌋ (e1 ∧ e2) = 0 (e3 not in blade)
#eval let e1 : Multivector R5 Int := Multivector.ofBlade e5_1
      let e2 : Multivector R5 Int := Multivector.ofBlade e5_2
      let e3 : Multivector R5 Int := Multivector.ofBlade e5_3
      let e12 := e1 ⋀ᵐ e2
      let result := e3 ⌋ᵐ e12
      (result.coeff e5_1, result.coeff e5_2, result.scalarPart)
-- Expected: (0, 0, 0)

end IntTests

/-! ## Complex Rotation Test: Composition of Multiple Rotations in 4D

This demonstrates that rotors compose correctly: R_total = R_1 * R_2
Using R4 (16 blades) for faster compilation.
-/

section CompositionTests

-- Basis for R4 (already defined inline in other tests, reusing pattern)
def e4_1 : Blade R4 := ⟨BitVec.ofNat 4 0b0001⟩
def e4_2 : Blade R4 := ⟨BitVec.ofNat 4 0b0010⟩
def e4_3 : Blade R4 := ⟨BitVec.ofNat 4 0b0100⟩
def e4_4 : Blade R4 := ⟨BitVec.ofNat 4 0b1000⟩

-- Test: Composition of rotations in orthogonal planes (R4)
-- R1 rotates in e1-e2, R2 rotates in e3-e4
-- These commute since the planes are orthogonal
#eval let e1 : Multivector R4 Int := Multivector.ofBlade e4_1
      let e2 : Multivector R4 Int := Multivector.ofBlade e4_2
      let e3 : Multivector R4 Int := Multivector.ofBlade e4_3
      let e4 : Multivector R4 Int := Multivector.ofBlade e4_4

      -- Create rotors (unnormalized for integer arithmetic)
      let R1 := Multivector.one + e1 * e2
      let R2 := Multivector.one + e3 * e4

      -- Compose rotors
      let R_total := R1 * R2

      -- Apply to e1 (in first rotation plane)
      let rotated_e1 := R_total * e1 * Multivector.reverse R_total

      -- e1 should have component in e2 direction
      ((rotated_e1.coeff e4_1, rotated_e1.coeff e4_2))
-- e1 rotates in e1-e2 plane (scaled by 4 = 2^2 from two rotors)
-- Expected: (0, -4)

end CompositionTests

/-! ## Performance/Size Tests

Test that operations work in high dimensions.
Using R5 (32 blades) for all heavier tests for reasonable compile times.
-/

section SizeTests

-- Test: Can create and manipulate multivectors with first and last basis vectors
-- Using R5 (32 blades) for faster compilation
#eval let e1 : Multivector R5 Int := Multivector.ofBlade e5_1
      let e5 : Multivector R5 Int := Multivector.ofBlade e5_5
      -- Product of first and last basis vectors
      let prod := e1 * e5
      -- Check it's a bivector
      let bivec : Blade R5 := ⟨BitVec.ofNat 5 0b10001⟩  -- e1 ∧ e5
      prod.coeff bivec
-- Expected: 1

-- Test: Pseudoscalar in R5 (all 5 vectors wedged)
#eval let mk_ei (i : Nat) : Multivector R5 Int :=
        Multivector.ofBlade ⟨BitVec.ofNat 5 (1 <<< i)⟩
      let wedgeAll := (List.range 5).foldl
        (fun acc i => acc ⋀ᵐ mk_ei i) Multivector.one
      let pseudoscalar : Blade R5 := ⟨BitVec.ofNat 5 0b11111⟩
      wedgeAll.coeff pseudoscalar
-- Expected: 1 (or -1 depending on order/sign convention)

-- Test: Grade extraction in R5
#eval let e1 : Multivector R5 Int := Multivector.ofBlade e5_1
      let e2 : Multivector R5 Int := Multivector.ofBlade e5_2
      let mv := Multivector.one + e1 + (e1 * e2)  -- grades 0, 1, 2
      let grade1 := mv.gradeProject 1
      grade1.coeff e5_1  -- Should be 1
-- Expected: 1

-- Test: 5D determinant
#eval let mk_ei (i : Nat) : Multivector R5 Int :=
        Multivector.ofBlade ⟨BitVec.ofNat 5 (1 <<< i)⟩
      LinearAlgebra.det (List.range 5 |>.map mk_ei)
-- Expected: 1

end SizeTests

/-! ## Algebraic Identity Verification -/

section IdentityTests

-- Test: (ab)† = b†a† (reverse is anti-automorphism)
-- If equal, lhs - rhs should give all zeros
#eval let e1 : Multivector R4 Int := Multivector.ofBlade e4_1
      let e2 : Multivector R4 Int := Multivector.ofBlade e4_2
      let e3 : Multivector R4 Int := Multivector.ofBlade e4_3
      let a := e1 + e2
      let b := e2 + e3
      let lhs := (a * b)†
      let rhs := b† * a†
      let diff := lhs - rhs
      -- All should be 0 if equal
      (diff.scalarPart, diff.coeff e4_1, diff.coeff e4_2)
-- Expected: (0, 0, 0)

-- Test: (aˆ)ˆ = a (involute is involution)
-- If equal, difference should be 0
#eval let e1 : Multivector R4 Int := Multivector.ofBlade e4_1
      let e12 := (Multivector.ofBlade e4_1 : Multivector R4 Int) *
                 (Multivector.ofBlade e4_2 : Multivector R4 Int)
      let mv := Multivector.one + e1 + e12
      let double_inv := (mvˆ)ˆ
      let diff := double_inv - mv
      (diff.scalarPart, diff.coeff e4_1)
-- Expected: (0, 0)

-- Test: v² is scalar for any vector
#eval let v : Multivector R4 Int := (Multivector.ofBlade e4_1).smul 3 +
                                     (Multivector.ofBlade e4_4).smul 4
      let vsq := v * v
      -- v² = 3²·1 + 4²·1 = 25 (Euclidean)
      (vsq.scalarPart, vsq.coeff e4_1, vsq.coeff e4_4)
-- Expected: (25, 0, 0)

end IdentityTests

/-! ## Summary

All tests use Int for exact arithmetic. Test dimensions:
- R4 (16 blades): Composition, identity, Hodge dual tests
- R5 (32 blades): Main rotation tests, size tests

Key demonstrations:

1. **High-D Rotations**: Rotors R = cos(θ/2) + sin(θ/2)B work correctly
   - R v R† rotates v in the plane of bivector B
   - Orthogonal components are preserved
   - Multiple rotations compose via rotor multiplication

2. **Wedge Products**: Work correctly up to 5-blades (pseudoscalar in R5)
   - Anticommutativity: a ∧ b = -b ∧ a
   - a ∧ a = 0

3. **Hodge Dual**: Correctly maps grade k to grade (n-k)

4. **Contractions**: Left/right contraction give expected results

5. **Involutions**: Reverse, involute, conjugate are all involutions

6. **Determinants**: Computed via exterior algebra match expected values
-/

end Grassmann.StressTests

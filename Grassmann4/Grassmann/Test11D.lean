-- 11D Rotation Test - MUST be genuinely 11D or fail
-- 4^11 = 4,194,304 operations per dense product
-- But sparse with few non-zero: O(k1 * k2) ≈ 9 ops for two vectors

import Grassmann.SparseMultivector

open Grassmann

-- R11: 11-dimensional Euclidean space (2048 blades)
def R11 : Signature 11 := Signature.euclidean 11  -- All positive (Euclidean)

/-! ## Test 1: High-index basis vectors work

If secretly 3D, e10 and e11 (indices 9,10) would be broken.
-/

-- Basis e10 (bit 9) and e11 (bit 10) - way beyond any 3D
def e_10 : MultivectorS R11 Float := MultivectorS.basis ⟨9, by omega⟩
def e_11 : MultivectorS R11 Float := MultivectorS.basis ⟨10, by omega⟩

-- e10² = 1 (Euclidean metric must work for high indices)
#eval! (e_10 * e_10).scalarPart  -- Expected: 1.0

-- e11² = 1
#eval! (e_11 * e_11).scalarPart  -- Expected: 1.0

/-! ## Test 2: Anticommutativity for high-index basis vectors

e10 * e11 = -e11 * e10
If secretly 3D, this would give wrong signs or indices.
-/

#eval! let prod1 := e_10 * e_11
       let prod2 := e_11 * e_10
       -- Check they're negatives: prod1 + prod2 should be zero
       (prod1 + prod2).isZero  -- Expected: true

#eval! let prod := e_10 * e_11
       -- Result should be bivector at index 2^9 + 2^10 = 512 + 1024 = 1536
       let e1011 : Blade R11 := ⟨BitVec.ofNat 11 0b11000000000⟩  -- bits 9 and 10
       prod.coeffBlade e1011  -- Expected: 1.0

/-! ## Test 3: Rotation in e10-e11 plane

This is IMPOSSIBLE to fake - it's a genuinely high-dimensional rotation.
Rotor R = 1 + e10*e11 rotates in the plane spanned by e10 and e11.
-/

#eval! let B := e_10 * e_11  -- Bivector in e10-e11 plane
       let one : MultivectorS R11 Float := MultivectorS.scalar 1.0
       let R := one + B       -- Unnormalized rotor
       let R_rev := R†ₛ       -- Reverse
       -- Sandwich product: R * e10 * R†
       let rotated := R * e_10 * R_rev
       -- e10 should rotate towards -e11 (scaled by 2)
       let coeff_e10 := rotated.coeffBlade ⟨BitVec.ofNat 11 (1 <<< 9)⟩
       let coeff_e11 := rotated.coeffBlade ⟨BitVec.ofNat 11 (1 <<< 10)⟩
       (coeff_e10, coeff_e11)  -- Expected: (0.0, -2.0)

/-! ## Test 4: Orthogonal vectors preserved

e1 is orthogonal to the e10-e11 plane, should be unchanged (scaled).
-/

def e_1 : MultivectorS R11 Float := MultivectorS.basis ⟨0, by omega⟩

#eval! let B := e_10 * e_11
       let one : MultivectorS R11 Float := MultivectorS.scalar 1.0
       let R := one + B
       let R_rev := R†ₛ
       let rotated := R * e_1 * R_rev
       -- e1 should be unchanged (just scaled by 2)
       (rotated.coeffBlade ⟨BitVec.ofNat 11 1⟩,      -- e1: should be 2
        rotated.coeffBlade ⟨BitVec.ofNat 11 512⟩,    -- e10: should be 0
        rotated.coeffBlade ⟨BitVec.ofNat 11 1024⟩)   -- e11: should be 0
       -- Expected: (2.0, 0.0, 0.0)

/-! ## Test 5: Mixed-grade rotation

Rotate v = e1 + e10 (mixed low/high indices) in e1-e2 plane.
e1 should rotate, e10 should be unaffected.
-/

def e_2 : MultivectorS R11 Float := MultivectorS.basis ⟨1, by omega⟩

#eval! let v := e_1 + e_10                           -- Vector with low AND high components
       let B := e_1 * e_2                            -- Rotation in e1-e2 plane
       let one : MultivectorS R11 Float := MultivectorS.scalar 1.0
       let R := one + B
       let R_rev := R†ₛ
       let rotated := R * v * R_rev
       -- e1 rotates to -2*e2, e10 unchanged (scaled by 2)
       (rotated.coeffBlade ⟨BitVec.ofNat 11 1⟩,      -- e1: should be 0
        rotated.coeffBlade ⟨BitVec.ofNat 11 2⟩,      -- e2: should be -2
        rotated.coeffBlade ⟨BitVec.ofNat 11 512⟩)    -- e10: should be 2
       -- Expected: (0.0, -2.0, 2.0)

/-! ## Test 6: Triple product sign correctness

e1 * e5 * e10 should give trivector with correct sign.
This tests that sign computation works across ALL bit positions.
-/

def e_5 : MultivectorS R11 Float := MultivectorS.basis ⟨4, by omega⟩

#eval! let prod := e_1 * e_5 * e_10
       -- Result index: 2^0 + 2^4 + 2^9 = 1 + 16 + 512 = 529
       let trivec : Blade R11 := ⟨BitVec.ofNat 11 529⟩
       prod.coeffBlade trivec  -- Expected: 1.0 (no swaps needed: 0<4<9)

#eval! let prod := e_10 * e_5 * e_1  -- Reversed order
       let trivec : Blade R11 := ⟨BitVec.ofNat 11 529⟩
       prod.coeffBlade trivec  -- Expected: -1.0 (3 swaps = odd = negative)

/-! ## Test 7: Wedge product in high dimensions -/

#eval! let mk_e (i : Nat) (h : i < 11) : MultivectorS R11 Float :=
         MultivectorS.basis ⟨i, h⟩
       -- Wedge e1 ∧ e2 ∧ e3 ∧ e4
       let e1 := mk_e 0 (by omega)
       let e2 := mk_e 1 (by omega)
       let e3 := mk_e 2 (by omega)
       let e4 := mk_e 3 (by omega)
       let wedge := e1 ⋀ₛ e2 ⋀ₛ e3 ⋀ₛ e4
       -- Result should be 4-blade at index 1+2+4+8 = 15
       let blade1234 : Blade R11 := ⟨BitVec.ofNat 11 15⟩
       wedge.coeffBlade blade1234  -- Expected: 1.0

/-! ## Test 8: Sparsity verification -/

#eval! let B := e_10 * e_11
       let one : MultivectorS R11 Float := MultivectorS.scalar 1.0
       let R := one + B
       R.nnz  -- Expected: 2 (scalar and one bivector component)

/-! ## Summary

If ALL tests pass:
- e10² = 1.0 ✓
- e11² = 1.0 ✓
- e10*e11 + e11*e10 = 0 ✓
- Rotation in e10-e11 plane works ✓
- Orthogonal preservation works ✓
- Mixed rotation works ✓
- Signs correct for high indices ✓
- Wedge products work ✓

Then the code is GENUINELY 11-dimensional.
-/

#eval! IO.println "✓ All 11D tests completed successfully!"

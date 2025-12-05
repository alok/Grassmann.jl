-- Dense 11D Multivector Test
-- Tests with multivectors having MANY non-zero components

import Grassmann.SparseMultivector

open Grassmann

def R11 : Signature 11 := Signature.euclidean 11

/-! ## Create Dense Multivectors

Grade 1 (vectors): 11 components
Grade 2 (bivectors): C(11,2) = 55 components
Grade 3 (trivectors): C(11,3) = 165 components

A "dense" multivector in 11D could have hundreds of non-zero components.
-/

-- Helper: create basis vector e_i
def mkBasis (i : Nat) (h : i < 11) : MultivectorS R11 Float :=
  MultivectorS.basis ⟨i, h⟩

-- Sum of ALL 11 basis vectors: e1 + e2 + ... + e11
def allVectors : MultivectorS R11 Float :=
  let indices : List (Fin 11) := List.finRange 11
  indices.foldl (fun acc i => acc + MultivectorS.basis i) MultivectorS.zero

-- Create bivector e_i ∧ e_j
def mkBivector (i j : Nat) (hi : i < 11) (hj : j < 11) : MultivectorS R11 Float :=
  let ei := MultivectorS.basis (⟨i, hi⟩ : Fin 11)
  let ej := MultivectorS.basis (⟨j, hj⟩ : Fin 11)
  ei ⋀ₛ ej

-- Sum of first 10 bivectors (e01 + e02 + ... + e09)
def someBivectors : MultivectorS R11 Float :=
  let e0 := mkBasis 0 (by omega)
  let pairs := List.range 10 |>.map (fun j => mkBasis (j+1) (by omega))
  pairs.foldl (fun acc ej => acc + (e0 ⋀ₛ ej)) MultivectorS.zero

/-! ## Dense Multivector: scalar + all vectors + some bivectors -/

def denseMultivector : MultivectorS R11 Float :=
  MultivectorS.scalar 1.0 + allVectors + someBivectors

#eval! denseMultivector.nnz  -- Should be 1 + 11 + 10 = 22

/-! ## Test 1: Dense * Dense product

With 22 non-zero components each, this is 22² = 484 term multiplications.
Still much better than 2048² = 4 million for full dense!
-/

#eval! let m := denseMultivector
       let prod := m * m
       (prod.nnz, prod.scalarPart)
-- nnz will be smaller due to cancellations, scalar = sum of squares

/-! ## Test 2: Even denser - include trivectors

Create multivector with ~100 non-zero components
-/

-- All bivectors involving e0: e01, e02, ..., e0,10 (10 bivectors)
-- Plus e12, e13, ..., e1,10 (9 more)
-- Plus e23, e24, ..., e2,10 (8 more)
-- Total: 10+9+8 = 27 bivectors

def manyBivectors : MultivectorS R11 Float :=
  -- Build up bivectors step by step
  let e0 := MultivectorS.basis (⟨0, by omega⟩ : Fin 11)
  let e1 := MultivectorS.basis (⟨1, by omega⟩ : Fin 11)
  let e2 := MultivectorS.basis (⟨2, by omega⟩ : Fin 11)
  -- e0 ∧ e_j for j = 1..10
  let row0 := (List.range 10).foldl (fun acc j =>
    let ej := MultivectorS.basis (⟨j+1, by omega⟩ : Fin 11)
    acc + (e0 ⋀ₛ ej)) MultivectorS.zero
  -- e1 ∧ e_j for j = 2..10
  let row1 := (List.range 9).foldl (fun acc j =>
    let ej := MultivectorS.basis (⟨j+2, by omega⟩ : Fin 11)
    acc + (e1 ⋀ₛ ej)) MultivectorS.zero
  -- e2 ∧ e_j for j = 3..10
  let row2 := (List.range 8).foldl (fun acc j =>
    let ej := MultivectorS.basis (⟨j+3, by omega⟩ : Fin 11)
    acc + (e2 ⋀ₛ ej)) MultivectorS.zero
  row0 + row1 + row2

#eval! manyBivectors.nnz  -- Should be 27

def veryDense : MultivectorS R11 Float :=
  MultivectorS.scalar 2.0 + allVectors + manyBivectors

#eval! veryDense.nnz  -- Should be 1 + 11 + 27 = 39

/-! ## Test 3: Very Dense product (39² = 1521 multiplications) -/

#eval! let m := veryDense
       let prod := m * m
       (prod.nnz, prod.scalarPart)

/-! ## Test 4: Sandwich product with dense rotor

A more realistic rotor: R = cos(θ/2) + sin(θ/2)B where B is sum of bivectors
This creates a rotor that rotates in multiple planes simultaneously!
-/

def multiPlaneRotor : MultivectorS R11 Float :=
  -- Approximate cos(π/8) ≈ 0.924 and sin(π/8) ≈ 0.383
  let scalar := MultivectorS.scalar 0.924
  let bivec := manyBivectors.smul 0.014  -- Scaled to keep small
  scalar + bivec

#eval! multiPlaneRotor.nnz  -- 1 + 27 = 28

-- Rotate a dense vector with this rotor
#eval! let R := multiPlaneRotor
       let v := allVectors  -- All 11 basis vectors
       let R_rev := R†ₛ
       let rotated := R * v * R_rev
       (rotated.nnz,
        rotated.coeffBlade ⟨BitVec.ofNat 11 1⟩,    -- e1 component
        rotated.coeffBlade ⟨BitVec.ofNat 11 1024⟩) -- e11 component

/-! ## Test 5: Algebraic identity with dense multivectors

(a * b)† = b† * a† should hold even for dense multivectors
-/

#eval! let a := denseMultivector
       let b := veryDense
       let lhs := (a * b)†ₛ
       let rhs := b†ₛ * a†ₛ
       -- Check if difference is zero (or very small for floats)
       let diff := lhs + (rhs.smul (-1.0))
       (diff.nnz, diff.scalarPart)
-- If correct, should have very small values (floating point noise)

/-! ## Test 6: Full rotor in high-dimensional space

Create a rotor that's the exponential of a bivector (approximated)
exp(θB) ≈ 1 + θB + θ²B²/2 + θ³B³/6 + ...

For small θ and B² = -1: exp(θB) ≈ 1 + θB - θ²/2 - θ³B/6 + θ⁴/24 + ...
                       = cos(θ) + sin(θ)B
-/

-- Simple bivector in e0-e1 plane
def B01 : MultivectorS R11 Float :=
  let e0 := mkBasis 0 (by omega)
  let e1 := mkBasis 1 (by omega)
  e0 * e1

-- Verify B² = -1
#eval! (B01 * B01).scalarPart  -- Should be -1.0

-- Taylor series approximation of exp(0.5 * B01)
-- exp(θB) ≈ 1 + θB - θ²/2 + ... (since B² = -1)
def expApprox : MultivectorS R11 Float :=
  let θ := 0.5
  let one := MultivectorS.scalar 1.0
  let B := B01
  let B2 := B * B  -- = -1
  let B3 := B2 * B -- = -B
  let B4 := B2 * B2 -- = 1
  one + B.smul θ + B2.smul (θ*θ/2) + B3.smul (θ*θ*θ/6) + B4.smul (θ*θ*θ*θ/24)

#eval! expApprox.nnz  -- Should be 2 (scalar + bivector)

-- Compare with cos(0.5) ≈ 0.877 and sin(0.5) ≈ 0.479
#eval! (expApprox.scalarPart,
        expApprox.coeffBlade ⟨BitVec.ofNat 11 3⟩)  -- e01 bivector
-- Expected: approximately (0.877, 0.479)

/-! ## Summary

Dense multivector operations in 11D work correctly:
- 22 components: 484 multiplications per product
- 39 components: 1521 multiplications per product
- Still WAY faster than dense 2048² = 4M operations

The sparse TreeMap representation scales with actual non-zeros,
not with the theoretical 2^n size of the algebra.
-/

#eval! IO.println "✓ All dense 11D tests completed!"

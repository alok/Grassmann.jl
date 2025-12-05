/-
  Grassmann/DSLDemo.lean - Demonstration of the Grassmann DSL

  This file showcases the elegant domain-specific language for Grassmann algebra:
  - Subscript notation: e₁, e₂, e₁₂, e₁₂₃
  - Algebra context blocks: Cl(p,q,r) { ... }, R3 { ... }
  - Polymorphic operations via GAlgebra typeclass
-/
import Grassmann.DSL
import Grassmann.SparseMultivector

open Grassmann Grassmann.DSL

/-! ## Scalar Multiplication -/

-- Method syntax: e₁.smul 2.0
#eval R3 {
  let v := e₁.smul 2.0
  v.coeff 1  -- 2.0
}

#eval R3 {
  let v := e₂.smul 3.0
  v.coeff 2  -- 3.0
}

-- Scalar times sum of basis vectors
#eval R3 {
  let v := (e₁ + e₂).smul 2.5
  (v.coeff 1, v.coeff 2)  -- (2.5, 2.5)
}

-- Building vectors with scalar multiplication
#eval R3 {
  let v := e₁.smul 3.0 + e₂.smul 4.0
  -- This is vector (3, 4, 0)
  (v * v).scalarPart  -- 25.0 = 3² + 4²
}

-- Using SMul's • notation (from Mathlib-style SMul instance)
section SMulNotation
variable (sig : Signature 3)

-- Test SMul • notation works for sparse multivectors
def testSMulNotation : MultivectorS (Signature.euclidean 3) Float :=
  (2.0 : Float) • (MultivectorS.basis ⟨0, by omega⟩)

#eval testSMulNotation.coeff 1  -- 2.0

-- Build a 3D vector using SMul
def vec3d : MultivectorS (Signature.euclidean 3) Float :=
  let e1 := MultivectorS.basis (sig := Signature.euclidean 3) ⟨0, by omega⟩
  let e2 := MultivectorS.basis (sig := Signature.euclidean 3) ⟨1, by omega⟩
  let e3 := MultivectorS.basis (sig := Signature.euclidean 3) ⟨2, by omega⟩
  (3.0 : Float) • e1 + (4.0 : Float) • e2 + (0.0 : Float) • e3

#eval (vec3d * vec3d).scalarPart  -- 25.0 = 3² + 4²

end SMulNotation

/-! ## Basic DSL Usage -/

-- R3 context: Cl(3,0,0) - 3D Euclidean space
#eval R3 {
  let v := e₁ + e₂
  v.scalarPart  -- 0 (vectors have no scalar part)
}

#eval R3 {
  let biv := e₁₂  -- Bivector
  biv.coeff 3  -- Coefficient at index 3 = 0b011 = e₁₂
}

-- Geometric product: e₁ * e₁ = 1
#eval R3 {
  (e₁ * e₁).scalarPart
}

-- Geometric product: e₁ * e₂ = e₁₂
#eval R3 {
  (e₁ * e₂).coeff 3  -- e₁₂ has bitmask 0b011 = 3
}

-- Anti-commutativity: e₂ * e₁ = -e₁₂
#eval R3 {
  (e₂ * e₁).coeff 3  -- Should be -1
}

-- Wedge product (using sparse wedge operator ⋀ₛ)
#eval R3 {
  let v1 := e₁
  let v2 := e₂
  (v1 ⋀ₛ v2).coeff 3  -- e₁ ∧ e₂ = e₁₂
}

-- Wedge of same vector = 0
#eval R3 {
  (e₁ ⋀ₛ e₁).coeff 3  -- Should be 0
}

/-! ## Higher Dimensional Algebras -/

-- R4: Cl(4,0,0)
#eval Cl(4,0,0) {
  let v := e₁ + e₂ + e₃ + e₄
  v.scalarPart
}

-- R2: 2D plane
#eval R2 {
  (e₁ * e₂ * e₁ * e₂).scalarPart  -- Should be -1 (i² = -1 analog)
}

/-! ## Using Different Signatures -/

-- Cl(2,0,0) - 2D Euclidean
#eval Cl(2) {
  let i := e₁₂  -- Unit bivector, squares to -1
  (i * i).scalarPart  -- -1
}

-- Cl(1,1) - Hyperbolic plane (1 positive, 1 negative)
#eval Cl(1,1) {
  -- e₁² = 1, e₂² = -1
  let v1 := e₁
  (v1 * v1).scalarPart  -- 1
}

#eval Cl(1,1) {
  let v2 := e₂
  (v2 * v2).scalarPart  -- -1 (negative signature)
}

/-! ## Pseudoscalar and Grade Operations -/

#eval R3 {
  let I := e₁₂₃  -- Pseudoscalar (unit trivector)
  I.coeff 7  -- Bitmask 0b111 = 7
}

-- Grade projection
#eval R3 {
  let mv := e₁ + e₂ + e₁₂
  let grade1 := mv.gradeProject 1  -- Vector part
  grade1.coeff 1  -- e₁ coefficient
}

/-! ## High-Dimensional Sparse Example -/

-- For high dimensions (n > 8), use MultivectorS directly with explicit signature
section HighDim

def R10 : Signature 10 := Signature.euclidean 10

-- Create basis vectors in R10
def e1_R10 : MultivectorS R10 Float := MultivectorS.basis ⟨0, by omega⟩
def e2_R10 : MultivectorS R10 Float := MultivectorS.basis ⟨1, by omega⟩
def e10_R10 : MultivectorS R10 Float := MultivectorS.basis ⟨9, by omega⟩

-- Test: vectors are sparse (1 non-zero coefficient)
#eval e1_R10.nnz  -- 1

-- Test: e1 * e1 = 1
#eval (e1_R10 * e1_R10).scalarPart  -- 1.0

-- Test: e1 * e10 gives bivector e1∧e10
#eval (e1_R10 * e10_R10).nnz  -- 1

-- Sum of all 10 basis vectors
def sumVec : MultivectorS R10 Float :=
  (List.finRange 10).foldl (init := MultivectorS.zero) fun acc i =>
    acc + MultivectorS.basis i

#eval sumVec.nnz  -- 10

-- v² = sum of all e_i² = 10 (all positive signature)
#eval (sumVec * sumVec).scalarPart  -- 10.0

end HighDim

/-! ## GAlgebra Typeclass Polymorphism -/

section Polymorphic

-- Generic function that works with any GAlgebra representation
def squareAndExtractScalar {n : ℕ} {sig : Signature n} {M F : Type*}
    [inst : GAlgebra sig M F] (v : M) : F :=
  inst.scalarPart (inst.mul v v)

-- The GAlgebra typeclass allows polymorphic algorithms
-- Inside DSL context, use direct operations (v * v).scalarPart
#eval R3 {
  let v := e₁ + e₂
  (v * v).scalarPart  -- 2.0 = 1² + 1² (Euclidean norm squared)
}

-- For explicit R10 usage, use direct operations
#eval (e1_R10 * e1_R10).scalarPart  -- 1.0

end Polymorphic

/-! ## Summary

The DSL provides:
1. **Subscript notation**: e₁, e₂, e₃, e₁₂, e₂₃, e₁₂₃
2. **Context blocks**: Cl(p,q,r) { ... }, R3 { ... }, PGA3 { ... }
3. **Auto-binding**: Basis vectors automatically available in context
4. **Polymorphism**: Same operations work across Dense/Sparse/Truncated representations
5. **Type safety**: Invalid dimensions cause compile errors

Example usage:
```
R3 {
  let v := 2 • e₁ + 3 • e₂
  let biv := e₁₂
  (v * biv).scalarPart
}
```
-/

#eval IO.println "DSL Demo loaded successfully"

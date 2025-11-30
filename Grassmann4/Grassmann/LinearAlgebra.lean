/-
  Grassmann/LinearAlgebra.lean - Linear algebra via geometric algebra

  Port of Grassmann.jl's linear algebra operations.

  Key insight: The exterior algebra provides a coordinate-free approach
  to linear algebra that works in ANY dimension:
  - Determinant: det(A) = (Ae₁ ∧ Ae₂ ∧ ... ∧ Aeₙ) / I where I = e₁∧...∧eₙ
  - Linear maps represented by their action on basis vectors
  - Solve systems via Cramer's rule using meet/join

  ALL operations are generic over signature - no dimension hardcoding!
-/
import Grassmann.Multivector

namespace Grassmann

namespace LinearAlgebra

variable {n : ℕ} {sig : Signature n} {F : Type*}
variable [Zero F] [One F] [Add F] [Neg F] [Mul F] [Sub F] [Div F]

/-! ## Pseudoscalar Blade -/

/-- The pseudoscalar blade: all basis vectors wedged together (e₁∧e₂∧...∧eₙ) -/
def pseudoscalarBlade : Blade sig := ⟨pseudoscalar⟩

/-! ## Generic Determinant

The determinant of n vectors in n-dimensional space is the coefficient
of the pseudoscalar in their wedge product:
  det([v₁ v₂ ... vₙ]) = coeff_I(v₁ ∧ v₂ ∧ ... ∧ vₙ)

This works for ANY dimension!
-/

/-- Determinant from a list of column vectors.
    Works for any dimension - just provide n vectors for Cl(p,q) where p+q=n -/
def det (vectors : List (Multivector sig F)) : F :=
  let wedgeAll := vectors.foldl (· ⋀ᵐ ·) Multivector.one
  wedgeAll.coeff pseudoscalarBlade

/-- Determinant from a function giving column vectors -/
def detFn (columns : Fin n → Multivector sig F) : F :=
  det ((List.finRange n).map columns)

/-! ## Generic Dot Product

For vectors a, b: a · b = ½(ab + ba) = scalar part of ab (in Euclidean signature)
-/

/-- Dot product of two multivectors: scalar part of geometric product -/
def dot (a b : Multivector sig F) : F :=
  (a * b).scalarPart

/-- Squared norm: a · a -/
def normSq (a : Multivector sig F) : F :=
  dot a a

/-! ## Generic Linear Maps

A linear map on n-dimensional space is determined by images of n basis vectors.
-/

/-- A linear map represented by images of basis vectors.
    Works for any signature! -/
structure LinearMap (sig : Signature n) (F : Type*) where
  /-- Image of basis vector eᵢ (0-indexed) -/
  columns : Fin n → Multivector sig F

namespace LinearMap

variable [Zero F] [One F] [Add F] [Neg F] [Mul F] [Sub F] [Div F]

/-- Get the i-th basis blade (single bit set) -/
def basisBlade (i : Fin n) : Blade sig :=
  ⟨BitVec.ofNat n (1 <<< i.val)⟩

/-- Apply a linear map to a vector: L(v) = Σᵢ vᵢ L(eᵢ) -/
def apply (L : LinearMap sig F) (v : Multivector sig F) : Multivector sig F :=
  (List.finRange n).foldl (init := Multivector.zero) fun acc i =>
    let coeff := v.coeff (basisBlade i)
    acc.add ((L.columns i).smul coeff)

/-- Identity linear map -/
def id : LinearMap sig F where
  columns := fun i => Multivector.ofBlade (basisBlade i)

/-- Compose two linear maps: (L₁ ∘ L₂)(eᵢ) = L₁(L₂(eᵢ)) -/
def compose (L1 L2 : LinearMap sig F) : LinearMap sig F where
  columns := fun i => L1.apply (L2.columns i)

/-- Determinant of a linear map -/
def det (L : LinearMap sig F) : F :=
  detFn L.columns

/-- Scale a linear map by a scalar -/
def scale (s : F) (L : LinearMap sig F) : LinearMap sig F where
  columns := fun i => (L.columns i).smul s

/-- Add two linear maps -/
def add (L1 L2 : LinearMap sig F) : LinearMap sig F where
  columns := fun i => (L1.columns i).add (L2.columns i)

end LinearMap

/-! ## Cramer's Rule (Generic)

Solve Lx = b using:
  xᵢ = det(L with column i replaced by b) / det(L)
-/

/-- Replace column i of L with vector b -/
def replaceColumn (L : LinearMap sig F) (i : Fin n) (b : Multivector sig F) :
    LinearMap sig F where
  columns := fun j => if j = i then b else L.columns j

/-- Solve linear system Lx = b using Cramer's rule.
    Returns coefficients of solution as a list. -/
def cramer (L : LinearMap sig F) (b : Multivector sig F) : List F :=
  let d := L.det
  (List.finRange n).map fun i =>
    (replaceColumn L i b).det / d

/-- Solve linear system and return as multivector (grade-1 part) -/
def solveSystem (L : LinearMap sig F) (b : Multivector sig F) : Multivector sig F :=
  let coeffs := cramer L b
  (List.finRange n).zip coeffs |>.foldl (init := Multivector.zero) fun acc (i, c) =>
    acc.add ((Multivector.ofBlade (LinearMap.basisBlade i)).smul c)

/-! ## Projection and Rejection (Generic) -/

/-- Project multivector a onto multivector b: (a·b / b·b) * b -/
def projectOnto (a b : Multivector sig F) : Multivector sig F :=
  b.smul (dot a b / dot b b)

/-- Reject a from b: a - proj_b(a) -/
def rejectFrom (a b : Multivector sig F) : Multivector sig F :=
  a.sub (projectOnto a b)

/-! ## Cross Product (Hodge dual of wedge)

The "cross product" a × b = ⋆(a ∧ b) is the Hodge dual of the wedge.
In 3D this gives a vector. In other dimensions it gives grade (n-2).
-/

/-- Generalized cross product: Hodge dual of wedge product.
    In 3D: gives the traditional cross product (a vector).
    In nD: gives a grade-(n-2) multivector. -/
def cross (a b : Multivector sig F) : Multivector sig F :=
  ⋆ᵐ(a ⋀ᵐ b)

/-! ## Gram Determinant

The Gram determinant of vectors v₁,...,vₖ is det(⟨vᵢ,vⱼ⟩).
It measures the k-dimensional volume² spanned by the vectors.
-/

/-- Compute Gram matrix entry: ⟨vᵢ, vⱼ⟩ -/
def gramEntry (vectors : List (Multivector sig F)) (i j : Nat) : F :=
  match vectors[i]?, vectors[j]? with
  | some vi, some vj => dot vi vj
  | _, _ => 0

/-! ## Outermorphism

An outermorphism extends a linear map to the full exterior algebra:
  F(a ∧ b) = F(a) ∧ F(b)
-/

/-- Apply linear map as outermorphism to a blade.
    For blade e_{i₁...iₖ}, compute L(e_{i₁}) ∧ ... ∧ L(e_{iₖ}) -/
def outermorphismBlade (L : LinearMap sig F) (b : Blade sig) : Multivector sig F :=
  let indices := b.basisIndices  -- List (Fin n) of set bits
  indices.foldl (init := Multivector.one) fun acc i =>
    acc ⋀ᵐ (L.columns i)

/-- Apply linear map as outermorphism to full multivector -/
def outermorphism (L : LinearMap sig F) (m : Multivector sig F) : Multivector sig F :=
  (List.finRange (2^n)).foldl (init := Multivector.zero) fun acc i =>
    let blade : Blade sig := ⟨BitVec.ofNat n i.val⟩
    let coeff := m.coeffs i
    let transformed := outermorphismBlade L blade
    acc.add (transformed.smul coeff)

end LinearAlgebra

/-! ## Tests -/

section Tests

open LinearAlgebra

-- Test generic determinant in R2
#eval let v1 : Multivector R2 Float := Multivector.ofBlade (e1 : Blade R2)
      let v2 : Multivector R2 Float := Multivector.ofBlade (e2 : Blade R2)
      det [v1, v2]  -- Should be 1 (identity)

-- Test generic determinant in R3
#eval let v1 : Multivector R3 Float := Multivector.ofBlade (e1 : Blade R3)
      let v2 : Multivector R3 Float := Multivector.ofBlade (e2 : Blade R3)
      let v3 : Multivector R3 Float := Multivector.ofBlade (e3 : Blade R3)
      det [v1, v2, v3]  -- Should be 1 (identity)

-- Test generic determinant in R4
#eval let v1 : Multivector R4 Float := Multivector.ofBlade (e1 : Blade R4)
      let v2 : Multivector R4 Float := Multivector.ofBlade (e2 : Blade R4)
      let v3 : Multivector R4 Float := Multivector.ofBlade (e3 : Blade R4)
      let v4 : Multivector R4 Float := Multivector.ofBlade (e4 : Blade R4)
      det [v1, v2, v3, v4]  -- Should be 1 (identity)

-- Test swapping columns negates determinant (R3)
#eval let v1 : Multivector R3 Float := Multivector.ofBlade (e1 : Blade R3)
      let v2 : Multivector R3 Float := Multivector.ofBlade (e2 : Blade R3)
      let v3 : Multivector R3 Float := Multivector.ofBlade (e3 : Blade R3)
      det [v2, v1, v3]  -- Should be -1 (one swap)

-- Test swapping columns negates determinant (R4)
#eval let v1 : Multivector R4 Float := Multivector.ofBlade (e1 : Blade R4)
      let v2 : Multivector R4 Float := Multivector.ofBlade (e2 : Blade R4)
      let v3 : Multivector R4 Float := Multivector.ofBlade (e3 : Blade R4)
      let v4 : Multivector R4 Float := Multivector.ofBlade (e4 : Blade R4)
      det [v2, v1, v3, v4]  -- Should be -1 (one swap)

-- Test scaled diagonal determinant (R3)
#eval let v1 : Multivector R3 Float := (Multivector.ofBlade (e1 : Blade R3)).smul 2
      let v2 : Multivector R3 Float := (Multivector.ofBlade (e2 : Blade R3)).smul 3
      let v3 : Multivector R3 Float := (Multivector.ofBlade (e3 : Blade R3)).smul 4
      det [v1, v2, v3]  -- Should be 24

-- Test LinearMap identity determinant (R3)
#eval (LinearMap.id : LinearMap R3 Float).det  -- Should be 1

-- Test LinearMap identity determinant (R4)
#eval (LinearMap.id : LinearMap R4 Float).det  -- Should be 1

-- Test LinearMap identity determinant (R2)
#eval (LinearMap.id : LinearMap R2 Float).det  -- Should be 1

-- Test dot product
#eval let e1v : Multivector R3 Float := Multivector.ofBlade (e1 : Blade R3)
      let e2v : Multivector R3 Float := Multivector.ofBlade (e2 : Blade R3)
      (dot e1v e1v, dot e1v e2v)  -- Should be (1, 0)

-- Test cross product in R3: e1 × e2 = e3
#eval let e1v : Multivector R3 Float := Multivector.ofBlade (e1 : Blade R3)
      let e2v : Multivector R3 Float := Multivector.ofBlade (e2 : Blade R3)
      let c := cross e1v e2v
      (c.coeff (e1 : Blade R3), c.coeff (e2 : Blade R3), c.coeff (e3 : Blade R3))

-- Test LinearMap apply (R3)
#eval let L : LinearMap R3 Float := LinearMap.id
      let v : Multivector R3 Float := vector3 1 2 3
      let Lv := L.apply v
      (Lv.coeff (e1 : Blade R3), Lv.coeff (e2 : Blade R3), Lv.coeff (e3 : Blade R3))

-- Test Cramer's rule (R2)
#eval let L : LinearMap R2 Float := LinearMap.id
      let b : Multivector R2 Float :=
        (Multivector.ofBlade (e1 : Blade R2)).smul 3 |>.add
        ((Multivector.ofBlade (e2 : Blade R2)).smul 4)
      cramer L b  -- Should be [3, 4]

end Tests

end Grassmann

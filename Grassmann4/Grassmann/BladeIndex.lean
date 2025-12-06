/-
  Grassmann/BladeIndex.lean - Compile-time blade index tables

  For grade-restricted operations, we don't need to iterate over all 2^n indices.
  This module provides precomputed index lists for common grade patterns:

  - Grade k indices: Just blades of a specific grade
  - Even indices: Grades 0, 2, 4, ...
  - Odd indices: Grades 1, 3, 5, ...

  These enable O(binomial(n,k)) iteration instead of O(2^n) when we know
  we're working with homogeneous-grade multivectors.

  ## Example Savings

  For n=5 (32 coefficients total):
  - Grade 0: 1 index
  - Grade 1: 5 indices
  - Grade 2: 10 indices
  - Even grades: 16 indices (50% savings)
  - Single grade k: binomial(5,k) indices

  For rotors (scalar + bivector in R3):
  - Naive: 8 indices
  - Grade {0,2}: 1 + 3 = 4 indices (50% savings)
-/
import Grassmann.Multivector
import Grassmann.GradeSet
import Mathlib.Algebra.Ring.Defs

namespace Grassmann

/-! ## Precomputed Grade Index Lists

These are computed once and reused for all operations.
-/

/-- Get all blade indices of grade k for dimension n.
    Returns indices in ascending order. -/
def gradeIndices (n k : ℕ) : List (Fin (2^n)) :=
  (List.finRange (2^n)).filter fun i =>
    grade (BitVec.ofNat n i.val) = k

/-- Get all even-grade indices for dimension n. -/
def evenIndices (n : ℕ) : List (Fin (2^n)) :=
  (List.finRange (2^n)).filter fun i =>
    grade (BitVec.ofNat n i.val) % 2 = 0

/-- Get all odd-grade indices for dimension n. -/
def oddIndices (n : ℕ) : List (Fin (2^n)) :=
  (List.finRange (2^n)).filter fun i =>
    grade (BitVec.ofNat n i.val) % 2 = 1

/-- Get indices for a grade set (bitmask). -/
def gradeSetIndices (n : ℕ) (gs : GradeSet) : List (Fin (2^n)) :=
  (List.finRange (2^n)).filter fun i =>
    gs.contains (grade (BitVec.ofNat n i.val))

/-! ## Precomputed Tables for Common Signatures -/

/-- R3 scalar indices (grade 0): just index 0 -/
def R3ScalarIdx : List (Fin 8) := gradeIndices 3 0
/-- R3 vector indices (grade 1): indices 1, 2, 4 -/
def R3VectorIdx : List (Fin 8) := gradeIndices 3 1
/-- R3 bivector indices (grade 2): indices 3, 5, 6 -/
def R3BivectorIdx : List (Fin 8) := gradeIndices 3 2
/-- R3 pseudoscalar indices (grade 3): just index 7 -/
def R3PseudoIdx : List (Fin 8) := gradeIndices 3 3
/-- R3 even indices (rotors): grades 0 and 2 -/
def R3EvenIdx : List (Fin 8) := evenIndices 3
/-- R3 odd indices: grades 1 and 3 -/
def R3OddIdx : List (Fin 8) := oddIndices 3

/-- PGA3 even indices (motors) -/
def PGA3EvenIdx : List (Fin 16) := evenIndices 4
/-- PGA3 odd indices -/
def PGA3OddIdx : List (Fin 16) := oddIndices 4

/-- CGA3 even indices -/
def CGA3EvenIdx : List (Fin 32) := evenIndices 5

/-! ## Index-Optimized Operations

These use precomputed index lists to skip zero grades.
-/

variable {n : ℕ} {sig : Signature n} {F : Type*} [Ring F]

/-- Extract coefficients at given indices as an array -/
def extractCoeffs (m : Multivector sig F) (indices : List (Fin (2^n))) : Array F :=
  indices.foldl (init := #[]) fun arr i => arr.push (m.coeffs i)

/-- Build multivector from coefficients at given indices (others are zero) -/
def fromCoeffs (coeffs : Array F) (indices : List (Fin (2 ^ n))) : Multivector sig F :=
  -- Simple O(k) lookup for small index lists
  ⟨fun i =>
    match indices.findIdx? (· == i) with
    | some pos => coeffs.getD pos 0
    | none => 0⟩

/-- Grade-k projection using precomputed indices.
    More efficient than checking grade for each index. -/
def gradeProjectFast (m : Multivector sig F) (indices : List (Fin (2^n))) :
    Multivector sig F :=
  fromCoeffs (extractCoeffs m indices) indices

/-- Even part using precomputed indices -/
def evenPartFast (m : Multivector sig F) (evenIdx : List (Fin (2^n))) :
    Multivector sig F :=
  fromCoeffs (extractCoeffs m evenIdx) evenIdx

/-- Odd part using precomputed indices -/
def oddPartFast (m : Multivector sig F) (oddIdx : List (Fin (2^n))) :
    Multivector sig F :=
  fromCoeffs (extractCoeffs m oddIdx) oddIdx

/-! ## Sparse Iteration Products

When both operands have known grade structure, iterate only over non-zero pairs.
-/

/-- Geometric product iterating only over given index pairs.
    For even × even, this is ~4x faster. -/
def geometricProductSparse (a b : Multivector sig F)
    (aIndices bIndices : List (Fin (2^n))) : Multivector sig F :=
  let size := 2^n
  let resultArray := aIndices.foldl (init := Array.replicate size (0 : F)) fun arr i =>
    bIndices.foldl (init := arr) fun arr2 j =>
      let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
      let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
      let sign := geometricSign sig bi bj
      if sign == 0 then arr2
      else
        let resultIdx := (bi.bits ^^^ bj.bits).toNat
        if resultIdx < size then
          let coeff := a.coeffs i * b.coeffs j
          let contrib := if sign < 0 then -coeff else coeff
          arr2.modify resultIdx (· + contrib)
        else arr2
  ⟨fun k => resultArray.getD k.val 0⟩

/-- Wedge product iterating only over given index pairs -/
def wedgeProductSparse (a b : Multivector sig F)
    (aIndices bIndices : List (Fin (2^n))) : Multivector sig F :=
  let size := 2^n
  let resultArray := aIndices.foldl (init := Array.replicate size (0 : F)) fun arr i =>
    bIndices.foldl (init := arr) fun arr2 j =>
      let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
      let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
      -- Wedge is zero if blades share basis vectors
      if (bi.bits &&& bj.bits) != 0 then arr2
      else
        let resultIdx := (bi.bits ||| bj.bits).toNat
        if resultIdx < size then
          let sign := wedgeSign sig bi bj
          if sign == 0 then arr2
          else
            let coeff := a.coeffs i * b.coeffs j
            let contrib := if sign < 0 then -coeff else coeff
            arr2.modify resultIdx (· + contrib)
        else arr2
  ⟨fun k => resultArray.getD k.val 0⟩

/-! ## R3-Specific Optimized Operations -/

namespace R3Fast

/-- R3 rotor indices: 0 (scalar), 3, 5, 6 (bivectors e12, e13, e23) -/
private def r3RotorIdx : List (Fin 8) :=
  [⟨0, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩]

/-- R3 vector indices: 1, 2, 4 (e1, e2, e3) -/
private def r3VectorIdx : List (Fin 8) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩]

/-- R3 odd indices: 1, 2, 4, 7 (grades 1 and 3) -/
private def r3OddIdx : List (Fin 8) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨7, by decide⟩]

/-- R3 rotor × rotor using sparse indices.
    Rotors are scalar+bivector, so iterate only over 4 indices. -/
def rotorMul (r1 r2 : Multivector R3 Float) : Multivector R3 Float :=
  geometricProductSparse r1 r2 r3RotorIdx r3RotorIdx

/-- R3 rotor × vector using sparse indices.
    Rotor is 4 indices, vector is 3 indices → 12 pairs instead of 64. -/
def rotorVectorMul (r v : Multivector R3 Float) : Multivector R3 Float :=
  geometricProductSparse r v r3RotorIdx r3VectorIdx

/-- R3 vector × rotor using sparse indices -/
def vectorRotorMul (v r : Multivector R3 Float) : Multivector R3 Float :=
  geometricProductSparse v r r3VectorIdx r3RotorIdx

/-- R3 sandwich: R * v * R† with sparse indices.
    R×v: 4×3 = 12 pairs → odd result
    (R×v)×R†: 4×4 = 16 pairs (odd×even = odd → vector)
    Total: 28 pairs instead of 128 (64+64) = 4.5x speedup -/
def sandwichFast (rotor v : Multivector R3 Float) : Multivector R3 Float :=
  let rv := rotorVectorMul rotor v
  -- rv is odd (has grades 1 and 3)
  geometricProductSparse rv (rotor†) r3OddIdx r3RotorIdx

/-- R3 vector wedge product: v ∧ w produces bivector.
    3×3 = 9 pairs, but many are zero due to shared indices. -/
def vectorWedge (v w : Multivector R3 Float) : Multivector R3 Float :=
  wedgeProductSparse v w r3VectorIdx r3VectorIdx

end R3Fast

/-! ## Tests -/

-- Verify index counts
#eval R3ScalarIdx.length    -- 1
#eval R3VectorIdx.length    -- 3
#eval R3BivectorIdx.length  -- 3
#eval R3PseudoIdx.length    -- 1
#eval R3EvenIdx.length      -- 4
#eval R3OddIdx.length       -- 4

-- Verify indices are correct
#eval R3VectorIdx.map (·.val)     -- [1, 2, 4]
#eval R3BivectorIdx.map (·.val)   -- [3, 5, 6]
#eval R3EvenIdx.map (·.val)       -- [0, 3, 5, 6, 7] -- wait, 7 is grade 3

-- Actually test the indices
#eval (gradeIndices 3 0).map (·.val)  -- [0]
#eval (gradeIndices 3 1).map (·.val)  -- [1, 2, 4]
#eval (gradeIndices 3 2).map (·.val)  -- [3, 5, 6]
#eval (gradeIndices 3 3).map (·.val)  -- [7]
#eval (evenIndices 3).map (·.val)     -- [0, 3, 5, 6] - correct for grades 0,2

-- Test sparse product
#eval
  let v : Multivector R3 Float := ⟨fun i =>
    if i.val = 1 then 1.0  -- e1
    else 0.0⟩
  let w : Multivector R3 Float := ⟨fun i =>
    if i.val = 2 then 1.0  -- e2
    else 0.0⟩
  let wedge := R3Fast.vectorWedge v w
  wedge.coeffs ⟨3, by decide⟩  -- e12, should be 1.0

end Grassmann

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
import Grassmann.SignTables
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

/-! ## Cached GradeSet → Indices Tables

`GradedMV` (grade-annotated multivectors) are meant to be a *performance* feature:
if the grade structure is known, operations should avoid iterating over provably-zero
coefficients.

However, naively computing `gradeSetIndices n gs` inside every multiplication would
scan `2^n` blades each time, which can erase any win from sparsity.

So for the small `n` we care about in real-time geometry (R3/PGA3/CGA3), we precompute
the index list for *every* grade-set bitmask once and cache it.
-/

/-- Precompute `gradeSetIndices n gs` for all `gs < 2^(n+1)` in one table. -/
private def buildGradeSetIndexTable (n : ℕ) : Array (List (Fin (2^n))) :=
  let tableSize : Nat := 2 ^ (n + 1)
  Array.ofFn (n := tableSize) fun gsFin =>
    gradeSetIndices n gsFin.val

private def gradeSetIndexTable2 : Array (List (Fin 4)) := buildGradeSetIndexTable 2
private def gradeSetIndexTable3 : Array (List (Fin 8)) := buildGradeSetIndexTable 3
private def gradeSetIndexTable4 : Array (List (Fin 16)) := buildGradeSetIndexTable 4
private def gradeSetIndexTable5 : Array (List (Fin 32)) := buildGradeSetIndexTable 5

/-- Fast grade-set index lookup for small `n` (cached); falls back to recomputing. -/
@[inline]
def gradeSetIndicesFast (n : ℕ) (gs : GradeSet) : List (Fin (2^n)) :=
  match n with
  | 2 =>
      if gs < gradeSetIndexTable2.size then gradeSetIndexTable2.getD gs []
      else gradeSetIndices 2 gs
  | 3 =>
      if gs < gradeSetIndexTable3.size then gradeSetIndexTable3.getD gs []
      else gradeSetIndices 3 gs
  | 4 =>
      if gs < gradeSetIndexTable4.size then gradeSetIndexTable4.getD gs []
      else gradeSetIndices 4 gs
  | 5 =>
      if gs < gradeSetIndexTable5.size then gradeSetIndexTable5.getD gs []
      else gradeSetIndices 5 gs
  | n' => gradeSetIndices n' gs

/-- Precompute `gradeSetIndices n gs` for all `gs < 2^(n+1)` as arrays. -/
private def buildGradeSetIndexTableArray (n : ℕ) : Array (Array (Fin (2^n))) :=
  let tableSize : Nat := 2 ^ (n + 1)
  Array.ofFn (n := tableSize) fun gsFin =>
    (gradeSetIndices n gsFin.val).toArray

private def gradeSetIndexTableArr2 : Array (Array (Fin 4)) := buildGradeSetIndexTableArray 2
private def gradeSetIndexTableArr3 : Array (Array (Fin 8)) := buildGradeSetIndexTableArray 3
private def gradeSetIndexTableArr4 : Array (Array (Fin 16)) := buildGradeSetIndexTableArray 4
private def gradeSetIndexTableArr5 : Array (Array (Fin 32)) := buildGradeSetIndexTableArray 5

/-- Fast grade-set index lookup (cached arrays for n=2..5). -/
@[inline]
def gradeSetIndicesFastArray (n : ℕ) (gs : GradeSet) : Array (Fin (2^n)) :=
  match n with
  | 2 =>
      if gs < gradeSetIndexTableArr2.size then gradeSetIndexTableArr2.getD gs #[]
      else (gradeSetIndices 2 gs).toArray
  | 3 =>
      if gs < gradeSetIndexTableArr3.size then gradeSetIndexTableArr3.getD gs #[]
      else (gradeSetIndices 3 gs).toArray
  | 4 =>
      if gs < gradeSetIndexTableArr4.size then gradeSetIndexTableArr4.getD gs #[]
      else (gradeSetIndices 4 gs).toArray
  | 5 =>
      if gs < gradeSetIndexTableArr5.size then gradeSetIndexTableArr5.getD gs #[]
      else (gradeSetIndices 5 gs).toArray
  | n' => (gradeSetIndices n' gs).toArray

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
def extractCoeffs (m : Multivector sig F) (indices : List (Fin (2 ^ n))) : Array F :=
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
def gradeProjectFast (m : Multivector sig F) (indices : List (Fin (2 ^ n))) :
    Multivector sig F :=
  fromCoeffs (extractCoeffs m indices) indices

/-- Even part using precomputed indices -/
def evenPartFast (m : Multivector sig F) (evenIdx : List (Fin (2 ^ n))) :
    Multivector sig F :=
  fromCoeffs (extractCoeffs m evenIdx) evenIdx

/-- Odd part using precomputed indices -/
def oddPartFast (m : Multivector sig F) (oddIdx : List (Fin (2 ^ n))) :
    Multivector sig F :=
  fromCoeffs (extractCoeffs m oddIdx) oddIdx

/-! ## Sparse Iteration Products

When both operands have known grade structure, iterate only over non-zero pairs.
-/

/-- Geometric product iterating only over given index pairs.
    For even × even, this is ~4x faster. -/
@[specialize]
def geometricProductSparse (a b : Multivector sig F)
    (aIndices bIndices : List (Fin (2 ^ n))) : Multivector sig F :=
  let size := 2 ^ n
  let table? : Option (SignTable n) := cachedSignTable (n := n) sig
  let resultArray :=
    match table? with
    | some table =>
        aIndices.foldl (init := Array.replicate size (0 : F)) fun (arr : Array F) (i : Fin (2^n)) =>
          bIndices.foldl (init := arr) fun (arr2 : Array F) (j : Fin (2^n)) =>
            let sign := table.lookup i.val j.val
            if sign == 0 then arr2
            else
              let resultIdx := i.val ^^^ j.val
              let coeff := a.coeffs i * b.coeffs j
              let contrib := if sign < 0 then -coeff else coeff
              let old := arr2.getD resultIdx 0
              arr2.set! resultIdx (old + contrib)
    | none =>
        aIndices.foldl (init := Array.replicate size (0 : F)) fun (arr : Array F) (i : Fin (2^n)) =>
          bIndices.foldl (init := arr) fun (arr2 : Array F) (j : Fin (2^n)) =>
            let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
            let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
            let sign := geometricSign sig bi bj
            if sign == 0 then arr2
            else
              let resultIdx := (bi.bits ^^^ bj.bits).toNat
              let coeff := a.coeffs i * b.coeffs j
              let contrib := if sign < 0 then -coeff else coeff
              let old := arr2.getD resultIdx 0
              arr2.set! resultIdx (old + contrib)
  ⟨fun k => resultArray.getD k.val 0⟩

/-- Array-based geometric product iterating only over given index pairs.
    This avoids list recursion overhead in tight loops. -/
@[specialize]
def geometricProductSparseArray (a b : Multivector sig F)
    (aIndices bIndices : Array (Fin (2 ^ n))) : Multivector sig F :=
  let size := 2 ^ n
  let table? : Option (SignTable n) := cachedSignTable (n := n) sig
  let resultArray : Array F := Id.run do
    let mut resultArray : Array F := Array.replicate size (0 : F)
    match table? with
    | some table =>
        for i in aIndices do
          for j in bIndices do
            let sign := table.lookup i.val j.val
            if sign != 0 then
              let resultIdx := i.val ^^^ j.val
              let coeff := a.coeffs i * b.coeffs j
              let contrib := if sign < 0 then -coeff else coeff
              let old := resultArray.getD resultIdx 0
              resultArray := resultArray.set! resultIdx (old + contrib)
    | none =>
        for i in aIndices do
          for j in bIndices do
            let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
            let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
            let sign := geometricSign sig bi bj
            if sign != 0 then
              let resultIdx := (bi.bits ^^^ bj.bits).toNat
              let coeff := a.coeffs i * b.coeffs j
              let contrib := if sign < 0 then -coeff else coeff
              let old := resultArray.getD resultIdx 0
              resultArray := resultArray.set! resultIdx (old + contrib)
    return resultArray
  ⟨fun k => resultArray.getD k.val 0⟩

/-- Wedge product iterating only over given index pairs -/
@[specialize]
def wedgeProductSparse (a b : Multivector sig F)
    (aIndices bIndices : List (Fin (2 ^ n))) : Multivector sig F :=
  let size := 2 ^ n
  let resultArray := aIndices.foldl (init := Array.replicate size (0 : F)) fun arr i =>
    bIndices.foldl (init := arr) fun arr2 j =>
      let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
      let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
      -- Wedge is zero if blades share basis vectors
      if (bi.bits &&& bj.bits) != 0 then arr2
      else
        let resultIdx := (bi.bits ||| bj.bits).toNat
        let sign := wedgeSign sig bi bj
        if sign == 0 then arr2
        else
          let coeff := a.coeffs i * b.coeffs j
          let contrib := if sign < 0 then -coeff else coeff
          let old := arr2.getD resultIdx 0
          arr2.set! resultIdx (old + contrib)
  ⟨fun k => resultArray.getD k.val 0⟩

/-- Array-based wedge product iterating only over given index pairs. -/
@[specialize]
def wedgeProductSparseArray (a b : Multivector sig F)
    (aIndices bIndices : Array (Fin (2 ^ n))) : Multivector sig F :=
  let size := 2 ^ n
  let resultArray : Array F := Id.run do
    let mut resultArray : Array F := Array.replicate size (0 : F)
    for i in aIndices do
      for j in bIndices do
        let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
        let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
        -- Wedge is zero if blades share basis vectors
        if (bi.bits &&& bj.bits) == 0 then
          let resultIdx := (bi.bits ||| bj.bits).toNat
          let sign := wedgeSign sig bi bj
          if sign != 0 then
            let coeff := a.coeffs i * b.coeffs j
            let contrib := if sign < 0 then -coeff else coeff
            let old := resultArray.getD resultIdx 0
            resultArray := resultArray.set! resultIdx (old + contrib)
    return resultArray
  ⟨fun k => resultArray.getD k.val 0⟩

/-! ## GradedMV Sparse Products

These use type-level grade sets (`GradedMV`) to automatically choose
sparse index lists. This is the “long-term right thing”: dependent types
carry structure that becomes fewer iterations at runtime.

Correctness assumes the grade annotations are honest upper bounds.
-/

namespace GradedMV

variable {gs1 gs2 : GradeSet}

/-- Sparse geometric product for graded multivectors. -/
@[inline, specialize]
def mulSparse (a : GradedMV sig F gs1) (b : GradedMV sig F gs2) :
    GradedMV sig F (geometricGradeSet gs1 gs2 n) :=
  let aIdx := gradeSetIndicesFastArray n gs1
  let bIdx := gradeSetIndicesFastArray n gs2
  ⟨geometricProductSparseArray (sig := sig) (n := n) a.mv b.mv aIdx bIdx⟩

-- Heterogeneous `*` for graded multivectors.
-- This wires dependent grade info into performance: multiplication
-- automatically uses sparse iteration based on compile‑time grade bounds.
instance : HMul (GradedMV sig F gs1) (GradedMV sig F gs2)
    (GradedMV sig F (geometricGradeSet gs1 gs2 n)) where
  hMul := mulSparse (sig := sig) (n := n) (gs1 := gs1) (gs2 := gs2)

end GradedMV

/-! ## R3-Specific Optimized Operations -/

namespace R3Fast

/-- R3 rotor indices: 0 (scalar), 3, 5, 6 (bivectors e12, e13, e23) -/
private def r3RotorIdx : Array (Fin 8) :=
  #[⟨0, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩]

/-- R3 vector indices: 1, 2, 4 (e1, e2, e3) -/
private def r3VectorIdx : Array (Fin 8) :=
  #[⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩]

/-- R3 odd indices: 1, 2, 4, 7 (grades 1 and 3) -/
private def r3OddIdx : Array (Fin 8) :=
  #[⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨7, by decide⟩]

/-- R3 rotor × rotor using sparse indices.
    Rotors are scalar+bivector, so iterate only over 4 indices. -/
def rotorMul (r1 r2 : Multivector R3 Float) : Multivector R3 Float :=
  geometricProductSparseArray r1 r2 r3RotorIdx r3RotorIdx

/-- R3 rotor × vector using sparse indices.
    Rotor is 4 indices, vector is 3 indices → 12 pairs instead of 64. -/
def rotorVectorMul (r v : Multivector R3 Float) : Multivector R3 Float :=
  geometricProductSparseArray r v r3RotorIdx r3VectorIdx

/-- R3 vector × rotor using sparse indices -/
def vectorRotorMul (v r : Multivector R3 Float) : Multivector R3 Float :=
  geometricProductSparseArray v r r3VectorIdx r3RotorIdx

/-- R3 sandwich: R * v * R† with sparse indices.
    R×v: 4×3 = 12 pairs → odd result
    (R×v)×R†: 4×4 = 16 pairs (odd×even = odd → vector)
    Total: 28 pairs instead of 128 (64+64) = 4.5x speedup -/
def sandwichFast (rotor v : Multivector R3 Float) : Multivector R3 Float :=
  let rv := rotorVectorMul rotor v
  -- rv is odd (has grades 1 and 3)
  geometricProductSparseArray rv (rotor†) r3OddIdx r3RotorIdx

/-- R3 vector wedge product: v ∧ w produces bivector.
    3×3 = 9 pairs, but many are zero due to shared indices. -/
def vectorWedge (v w : Multivector R3 Float) : Multivector R3 Float :=
  wedgeProductSparseArray v w r3VectorIdx r3VectorIdx

end R3Fast

/-! ## PGA3-Specific Optimized Operations

In PGA3 (Cl(3,0,1)):
- e0 is the degenerate (null) basis vector (e0² = 0)
- Motors (rigid transforms) are even-grade: scalar + bivector + pseudoscalar
- Points are grade-3: p = e123 + x*e023 + y*e013 + z*e003
- Lines are grade-2 bivectors
- Planes are grade-1 vectors
-/

namespace PGA3Fast

/-- PGA3 motor indices (even grades 0, 2, 4) -/
private def pga3MotorIdx : Array (Fin 16) := (evenIndices 4).toArray

/-- PGA3 point indices (grade 3): 4 components -/
private def pga3PointIdx : Array (Fin 16) := (gradeIndices 4 3).toArray

/-- PGA3 plane indices (grade 1): 4 components -/
private def pga3PlaneIdx : Array (Fin 16) := (gradeIndices 4 1).toArray

/-- PGA3 line indices (grade 2): 6 components -/
private def pga3LineIdx : Array (Fin 16) := (gradeIndices 4 2).toArray

private def pga3OddIdx : Array (Fin 16) := (oddIndices 4).toArray

/-- PGA3 motor × motor using sparse indices.
    Motors are even (8 components), so 8×8 = 64 pairs instead of 256. -/
def motorMul (m1 m2 : Multivector PGA3 Float) : Multivector PGA3 Float :=
  geometricProductSparseArray m1 m2 pga3MotorIdx pga3MotorIdx

/-- PGA3 motor × point sandwich: M * p * M̃
    Motor is 8 indices, point is 4 indices.
    M×p: 8×4 = 32 pairs → odd result
    (M×p)×M̃: odd×even, iterate over odd×even indices -/
def transformPoint (motor p : Multivector PGA3 Float) : Multivector PGA3 Float :=
  let mp := geometricProductSparseArray motor p pga3MotorIdx pga3PointIdx
  geometricProductSparseArray mp (motor†) pga3OddIdx pga3MotorIdx

/-- PGA3 motor × plane sandwich: M * π * M̃
    Similar structure to point transform. -/
def transformPlane (motor plane : Multivector PGA3 Float) : Multivector PGA3 Float :=
  let mp := geometricProductSparseArray motor plane pga3MotorIdx pga3PlaneIdx
  geometricProductSparseArray mp (motor†) pga3OddIdx pga3MotorIdx

/-- PGA3 motor × line sandwich: M * L * M̃
    Line is grade 2 (6 components), motor is even (8). -/
def transformLine (motor line : Multivector PGA3 Float) : Multivector PGA3 Float :=
  let ml := geometricProductSparseArray motor line pga3MotorIdx pga3LineIdx
  -- ml is even (line is grade 2, motor is even → even result)
  geometricProductSparseArray ml (motor†) pga3MotorIdx pga3MotorIdx

/-- PGA3 point ∨ point (regressive product via duality).
    Two points define a line. -/
def joinPoints (p1 p2 : Multivector PGA3 Float) : Multivector PGA3 Float :=
  -- In PGA: p1 ∨ p2 = (p1* ∧ p2*)*
  -- For now, use wedge of duals
  let d1 := p1.hodgeDual
  let d2 := p2.hodgeDual
  (wedgeProductSparseArray d1 d2 pga3PlaneIdx pga3PlaneIdx).hodgeDual

/-- PGA3 plane ∧ plane: two planes meet at a line -/
def meetPlanes (π1 π2 : Multivector PGA3 Float) : Multivector PGA3 Float :=
  wedgeProductSparseArray π1 π2 pga3PlaneIdx pga3PlaneIdx

/-- PGA3 plane ∧ line: plane and line meet at a point -/
def meetPlaneLine (plane line : Multivector PGA3 Float) : Multivector PGA3 Float :=
  wedgeProductSparseArray plane line pga3PlaneIdx pga3LineIdx

end PGA3Fast

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

-- PGA3 index counts
#eval PGA3EvenIdx.length      -- 8 (motor: scalar + 6 bivectors + pseudoscalar)
#eval PGA3OddIdx.length       -- 8 (planes + points)
#eval (gradeIndices 4 1).length  -- 4 (planes)
#eval (gradeIndices 4 2).length  -- 6 (lines)
#eval (gradeIndices 4 3).length  -- 4 (points)

end Grassmann

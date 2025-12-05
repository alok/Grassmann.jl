/-
  Grassmann/TruncatedMV.lean - Truncated Grade Multivector for High Dimensions

  For high-dimensional latent spaces (n=64, 128, 256, etc.), full 2^n storage
  is impossible. Instead, we truncate to only store grades 0, 1, 2 (and optionally
  a few sparse higher grades).

  Applications:
  - Neural network latent spaces with geometric structure
  - Equivariant neural networks on high-dimensional data
  - Scalable geometric algebra for ML

  Design:
  - Store only grades 0 through maxGrade
  - Use sparse representation within each grade
  - Grade k has (n choose k) basis elements - store sparsely via TreeMap
-/
import Grassmann.SparseMultivector
import Grassmann.GATypeclass
import Grassmann.Proof
import Std.Data.TreeMap

open Grassmann.Proof

namespace Grassmann

variable {n : ℕ} {sig : Signature n}

/-! ## Truncated Multivector

For dimension n, a grade-k element has (n choose k) components.
For n=128:
- Grade 0: 1 component (scalar)
- Grade 1: 128 components (vector)
- Grade 2: 8128 components (bivector)
- Grade 3: 341,376 components (trivector) - too many!

So we truncate at grade 2 for practical high-dim work.
-/

/-- Truncated multivector storing only grades 0 through maxGrade.
    Each grade is stored sparsely via TreeMap (blade index → coefficient).
    Blade index is the full n-bit mask, not a compressed index. -/
structure TruncatedMV (sig : Signature n) (maxGrade : ℕ) (F : Type*) where
  /-- Sparse storage for each grade. gradeData[k] stores grade-k terms. -/
  gradeData : Fin (maxGrade + 1) → Std.TreeMap ℕ F

namespace TruncatedMV

variable {maxGrade : ℕ} {F : Type*}

/-! ### Constructors -/

/-- Zero truncated multivector -/
def zero : TruncatedMV sig maxGrade F :=
  ⟨fun _ => Std.TreeMap.empty⟩

/-- Scalar truncated multivector (requires maxGrade ≥ 0) -/
def scalar [Ring F] [BEq F] (x : F) : TruncatedMV sig maxGrade F :=
  if x == 0 then zero
  else ⟨fun k => if k.val = 0 then Std.TreeMap.empty.insert 0 x else Std.TreeMap.empty⟩

/-- One (scalar 1) -/
def one [Ring F] [BEq F] : TruncatedMV sig maxGrade F := scalar 1

/-- Basis vector e_i (requires maxGrade ≥ 1) -/
def basis [Ring F] [BEq F] (i : Fin n) (_h : 1 ≤ maxGrade := by omega) : TruncatedMV sig maxGrade F :=
  let idx := 1 <<< i.val
  ⟨fun k => if k.val = 1 then Std.TreeMap.empty.insert idx (1 : F) else Std.TreeMap.empty⟩

/-- Bivector basis e_i ∧ e_j (requires maxGrade ≥ 2) -/
def bivectorBasis [Ring F] [BEq F] (i j : Fin n) (_h : 2 ≤ maxGrade := by omega) : TruncatedMV sig maxGrade F :=
  if i == j then zero
  else
    let idx := (1 <<< i.val) ||| (1 <<< j.val)
    let sign : F := if i.val < j.val then 1 else -1
    ⟨fun k => if k.val = 2 then Std.TreeMap.empty.insert idx sign else Std.TreeMap.empty⟩

/-! ### Coefficient Access -/

/-- Get coefficient for a specific blade index -/
def coeff [Ring F] (m : TruncatedMV sig maxGrade F) (bladeIdx : ℕ) : F :=
  let g := grade (BitVec.ofNat n bladeIdx)
  if h : g ≤ maxGrade then
    (m.gradeData ⟨g, by omega⟩).get? bladeIdx |>.getD 0
  else 0

/-- Scalar part (grade 0 coefficient at index 0) -/
def scalarPart [Ring F] (m : TruncatedMV sig maxGrade F) : F :=
  m.coeff 0

/-- Get all non-zero terms in a grade as (index, coeff) pairs -/
def gradeTerms (m : TruncatedMV sig maxGrade F) (g : ℕ) (h : g ≤ maxGrade) : List (ℕ × F) :=
  (m.gradeData ⟨g, by omega⟩).toList

/-- Number of stored (non-zero) coefficients -/
def nnz (m : TruncatedMV sig maxGrade F) : ℕ :=
  (List.finRange (maxGrade + 1)).foldl (fun acc k => acc + (m.gradeData k).size) 0

/-! ### Arithmetic -/

/-- Add two truncated multivectors -/
def add [Ring F] [BEq F] (a b : TruncatedMV sig maxGrade F) : TruncatedMV sig maxGrade F :=
  ⟨fun k =>
    let aData := a.gradeData k
    let bData := b.gradeData k
    bData.foldl (init := aData) fun acc idx coeff =>
      let oldVal := acc.get? idx |>.getD 0
      let newVal := oldVal + coeff
      if newVal == 0 then acc.erase idx else acc.insert idx newVal⟩

/-- Negate -/
def neg [Ring F] (m : TruncatedMV sig maxGrade F) : TruncatedMV sig maxGrade F :=
  ⟨fun k =>
    (m.gradeData k).foldl (init := Std.TreeMap.empty) fun acc idx coeff =>
      acc.insert idx (-coeff)⟩

/-- Subtract -/
def sub [Ring F] [BEq F] (a b : TruncatedMV sig maxGrade F) : TruncatedMV sig maxGrade F :=
  a.add b.neg

/-- Scale by scalar -/
def smul [Ring F] [BEq F] (x : F) (m : TruncatedMV sig maxGrade F) : TruncatedMV sig maxGrade F :=
  if x == 0 then zero
  else ⟨fun k =>
    (m.gradeData k).foldl (init := Std.TreeMap.empty) fun acc idx coeff =>
      let newVal := x * coeff
      if newVal == 0 then acc else acc.insert idx newVal⟩

instance [Ring F] [BEq F] : Zero (TruncatedMV sig maxGrade F) := ⟨zero⟩
instance [Ring F] [BEq F] : One (TruncatedMV sig maxGrade F) := ⟨one⟩
instance [Ring F] [BEq F] : Add (TruncatedMV sig maxGrade F) := ⟨add⟩
instance [Ring F] : Neg (TruncatedMV sig maxGrade F) := ⟨neg⟩
instance [Ring F] [BEq F] : Sub (TruncatedMV sig maxGrade F) := ⟨sub⟩
instance [Ring F] [BEq F] : SMul F (TruncatedMV sig maxGrade F) := ⟨smul⟩

/-! ### Products (Truncated)

Products are computed but results above maxGrade are discarded.
This is the key truncation behavior.
-/

/-- Helper: compute result grade and check if within bounds -/
private def productGrade (ga gb : ℕ) (productType : String) : Option ℕ :=
  match productType with
  | "wedge" => some (ga + gb)  -- Wedge always increases grade
  | "scalar" => if ga == gb then some 0 else none
  | "geometric" => some (ga + gb)  -- Simplified: actual grade depends on overlap
  | _ => none

/-- Geometric product (truncated).
    Terms producing grades > maxGrade are discarded. -/
def geometricProduct [Ring F] [BEq F] [DecidableEq F]
    (a b : TruncatedMV sig maxGrade F) : TruncatedMV sig maxGrade F :=
  let result := (List.finRange (maxGrade + 1)).foldl (init := zero) fun acc1 ga =>
    (List.finRange (maxGrade + 1)).foldl (init := acc1) fun acc2 gb =>
      -- For each pair of grades, compute contributions
      let aTerms := (a.gradeData ga).toList
      let bTerms := (b.gradeData gb).toList
      aTerms.foldl (init := acc2) fun acc3 (idxA, coeffA) =>
        bTerms.foldl (init := acc3) fun acc4 (idxB, coeffB) =>
          let bladeA : Blade sig := ⟨BitVec.ofNat n idxA⟩
          let bladeB : Blade sig := ⟨BitVec.ofNat n idxB⟩
          let resultIdx := (bladeA.bits ^^^ bladeB.bits).toNat
          let resultGrade := grade (BitVec.ofNat n resultIdx)
          if h : resultGrade ≤ maxGrade then
            let sign := geometricSign sig bladeA bladeB
            let contrib := if sign < 0 then -(coeffA * coeffB) else coeffA * coeffB
            let gradeMap := acc4.gradeData ⟨resultGrade, by omega⟩
            let oldVal := gradeMap.get? resultIdx |>.getD 0
            let newVal := oldVal + contrib
            let newGradeMap := if newVal == 0 then gradeMap.erase resultIdx
                               else gradeMap.insert resultIdx newVal
            ⟨fun k => if k.val = resultGrade then newGradeMap else acc4.gradeData k⟩
          else acc4
  result

/-- Wedge product (truncated).
    Grade(a ∧ b) = grade(a) + grade(b), so truncation is natural. -/
def wedgeProduct [Ring F] [BEq F] [DecidableEq F]
    (a b : TruncatedMV sig maxGrade F) : TruncatedMV sig maxGrade F :=
  let result := (List.finRange (maxGrade + 1)).foldl (init := zero) fun acc1 ga =>
    (List.finRange (maxGrade + 1)).foldl (init := acc1) fun acc2 gb =>
      let targetGrade := ga.val + gb.val
      if h : targetGrade ≤ maxGrade then
        let aTerms := (a.gradeData ga).toList
        let bTerms := (b.gradeData gb).toList
        aTerms.foldl (init := acc2) fun acc3 (idxA, coeffA) =>
          bTerms.foldl (init := acc3) fun acc4 (idxB, coeffB) =>
            let bladeA : Blade sig := ⟨BitVec.ofNat n idxA⟩
            let bladeB : Blade sig := ⟨BitVec.ofNat n idxB⟩
            -- Wedge is zero if blades share any basis vectors
            if (bladeA.bits &&& bladeB.bits) != 0 then acc4
            else
              let resultIdx := (bladeA.bits ||| bladeB.bits).toNat
              let sign := wedgeSign sig bladeA bladeB
              if sign == 0 then acc4
              else
                let contrib := if sign < 0 then -(coeffA * coeffB) else coeffA * coeffB
                let gradeMap := acc4.gradeData ⟨targetGrade, by omega⟩
                let oldVal := gradeMap.get? resultIdx |>.getD 0
                let newVal := oldVal + contrib
                let newGradeMap := if newVal == 0 then gradeMap.erase resultIdx
                                   else gradeMap.insert resultIdx newVal
                ⟨fun k => if k.val = targetGrade then newGradeMap else acc4.gradeData k⟩
      else acc2
  result

instance [Ring F] [BEq F] [DecidableEq F] : Mul (TruncatedMV sig maxGrade F) := ⟨geometricProduct⟩

infixl:65 " ⋀ₜ " => wedgeProduct

/-! ### Involutions -/

/-- Reverse (dagger) -/
def reverse [Ring F] (m : TruncatedMV sig maxGrade F) : TruncatedMV sig maxGrade F :=
  ⟨fun k =>
    let g := k.val
    let sign : Int := if (g * (g - 1) / 2) % 2 == 0 then 1 else -1
    (m.gradeData k).foldl (init := Std.TreeMap.empty) fun acc idx coeff =>
      let newCoeff := if sign < 0 then -coeff else coeff
      acc.insert idx newCoeff⟩

postfix:max "†ₜ" => reverse

/-- Grade involution: multiplies grade k by (-1)^k -/
def involute [Ring F] (m : TruncatedMV sig maxGrade F) : TruncatedMV sig maxGrade F :=
  ⟨fun k =>
    let g := k.val
    let sign : Int := if g % 2 == 0 then 1 else -1
    (m.gradeData k).foldl (init := Std.TreeMap.empty) fun acc idx coeff =>
      let newCoeff := if sign < 0 then -coeff else coeff
      acc.insert idx newCoeff⟩

/-- Clifford conjugate: reverse composed with involute -/
def conjugate [Ring F] (m : TruncatedMV sig maxGrade F) : TruncatedMV sig maxGrade F :=
  ⟨fun k =>
    let g := k.val
    let sign : Int := if (g * (g + 1) / 2) % 2 == 0 then 1 else -1
    (m.gradeData k).foldl (init := Std.TreeMap.empty) fun acc idx coeff =>
      let newCoeff := if sign < 0 then -coeff else coeff
      acc.insert idx newCoeff⟩

/-- Left contraction (truncated) -/
def leftContract [Ring F] [BEq F] [DecidableEq F]
    (a b : TruncatedMV sig maxGrade F) : TruncatedMV sig maxGrade F :=
  let result := (List.finRange (maxGrade + 1)).foldl (init := zero) fun acc1 ga =>
    (List.finRange (maxGrade + 1)).foldl (init := acc1) fun acc2 gb =>
      let aTerms := (a.gradeData ga).toList
      let bTerms := (b.gradeData gb).toList
      aTerms.foldl (init := acc2) fun acc3 (idxA, coeffA) =>
        bTerms.foldl (init := acc3) fun acc4 (idxB, coeffB) =>
          let bladeA : Blade sig := ⟨BitVec.ofNat n idxA⟩
          let bladeB : Blade sig := ⟨BitVec.ofNat n idxB⟩
          if (bladeA.bits &&& bladeB.bits) == bladeA.bits && bladeA.grade ≤ bladeB.grade then
            let resultIdx := (bladeA.bits ^^^ bladeB.bits).toNat
            let resultGrade := grade (BitVec.ofNat n resultIdx)
            if h : resultGrade ≤ maxGrade then
              let sign := geometricSign sig bladeA bladeB
              let contrib := if sign < 0 then -(coeffA * coeffB) else coeffA * coeffB
              let gradeMap := acc4.gradeData ⟨resultGrade, by omega⟩
              let oldVal := gradeMap.get? resultIdx |>.getD 0
              let newVal := oldVal + contrib
              let newGradeMap := if newVal == 0 then gradeMap.erase resultIdx
                                 else gradeMap.insert resultIdx newVal
              ⟨fun k => if k.val = resultGrade then newGradeMap else acc4.gradeData k⟩
            else acc4
          else acc4
  result

/-- Right contraction (truncated) -/
def rightContract [Ring F] [BEq F] [DecidableEq F]
    (a b : TruncatedMV sig maxGrade F) : TruncatedMV sig maxGrade F :=
  let result := (List.finRange (maxGrade + 1)).foldl (init := zero) fun acc1 ga =>
    (List.finRange (maxGrade + 1)).foldl (init := acc1) fun acc2 gb =>
      let aTerms := (a.gradeData ga).toList
      let bTerms := (b.gradeData gb).toList
      aTerms.foldl (init := acc2) fun acc3 (idxA, coeffA) =>
        bTerms.foldl (init := acc3) fun acc4 (idxB, coeffB) =>
          let bladeA : Blade sig := ⟨BitVec.ofNat n idxA⟩
          let bladeB : Blade sig := ⟨BitVec.ofNat n idxB⟩
          if (bladeB.bits &&& bladeA.bits) == bladeB.bits && bladeB.grade ≤ bladeA.grade then
            let resultIdx := (bladeA.bits ^^^ bladeB.bits).toNat
            let resultGrade := grade (BitVec.ofNat n resultIdx)
            if h : resultGrade ≤ maxGrade then
              let sign := geometricSign sig bladeA bladeB
              let contrib := if sign < 0 then -(coeffA * coeffB) else coeffA * coeffB
              let gradeMap := acc4.gradeData ⟨resultGrade, by omega⟩
              let oldVal := gradeMap.get? resultIdx |>.getD 0
              let newVal := oldVal + contrib
              let newGradeMap := if newVal == 0 then gradeMap.erase resultIdx
                                 else gradeMap.insert resultIdx newVal
              ⟨fun k => if k.val = resultGrade then newGradeMap else acc4.gradeData k⟩
            else acc4
          else acc4
  result

/-- Grade projection: extract grade-k component -/
def gradeProject [Ring F] [BEq F] (m : TruncatedMV sig maxGrade F) (k : ℕ) : TruncatedMV sig maxGrade F :=
  if _ : k ≤ maxGrade then
    ⟨fun g => if g.val == k then m.gradeData g else Std.TreeMap.empty⟩
  else zero

/-- Basis vector without proof requirement (returns zero if maxGrade < 1) -/
def basisVec [Ring F] [BEq F] (i : Fin n) : TruncatedMV sig maxGrade F :=
  if _ : 1 ≤ maxGrade then
    let idx := 1 <<< i.val
    ⟨fun k => if k.val = 1 then Std.TreeMap.empty.insert idx (1 : F) else Std.TreeMap.empty⟩
  else zero

/-- Blade from bitmask (truncated if grade > maxGrade) -/
def ofBladeBits [Ring F] [BEq F] (bits : BitVec n) : TruncatedMV sig maxGrade F :=
  let g := grade bits
  if _ : g ≤ maxGrade then
    let idx := bits.toNat
    ⟨fun k => if k.val = g then Std.TreeMap.empty.insert idx (1 : F) else Std.TreeMap.empty⟩
  else zero

/-! ### Conversion -/

/-- Convert from sparse multivector (truncating high grades) -/
def ofSparse [Ring F] [BEq F] (m : MultivectorS sig F) : TruncatedMV sig maxGrade F :=
  let terms := m.toList
  terms.foldl (init := zero) fun acc (idx, coeff) =>
    let g := grade (BitVec.ofNat n idx)
    if h : g ≤ maxGrade then
      let gradeMap := acc.gradeData ⟨g, by omega⟩
      let newGradeMap := gradeMap.insert idx coeff
      ⟨fun k => if k.val = g then newGradeMap else acc.gradeData k⟩
    else acc

/-- Convert to sparse multivector -/
def toSparse [Ring F] (m : TruncatedMV sig maxGrade F) : MultivectorS sig F :=
  (List.finRange (maxGrade + 1)).foldl (init := MultivectorS.zero) fun acc k =>
    let terms := (m.gradeData k).toList
    terms.foldl (init := acc) fun acc2 (idx, coeff) =>
      ⟨acc2.coeffs.insert idx coeff⟩

end TruncatedMV

/-! ## GAlgebra Instance for TruncatedMV -/

instance (maxGrade : ℕ) [Ring F] [BEq F] [DecidableEq F] : GAlgebra sig (TruncatedMV sig maxGrade F) F where
  basisVector := TruncatedMV.basisVec
  scalar := TruncatedMV.scalar
  zero := TruncatedMV.zero
  one := TruncatedMV.one
  blade bits := TruncatedMV.ofBladeBits bits
  mul := TruncatedMV.geometricProduct
  wedge := TruncatedMV.wedgeProduct
  leftContract := TruncatedMV.leftContract
  rightContract := TruncatedMV.rightContract
  reverse := TruncatedMV.reverse
  involute := TruncatedMV.involute
  conjugate := TruncatedMV.conjugate
  scalarPart := TruncatedMV.scalarPart
  add := TruncatedMV.add
  neg := TruncatedMV.neg
  smul := TruncatedMV.smul
  gradeProject := TruncatedMV.gradeProject

/-! ## Common Type Aliases -/

/-- ScalarVectorBivector: grades 0, 1, 2 only.
    Good for geometric neural networks. -/
abbrev SVB (sig : Signature n) (F : Type*) := TruncatedMV sig 2 F

/-- ScalarVector: grades 0, 1 only.
    Even more compact. -/
abbrev SV (sig : Signature n) (F : Type*) := TruncatedMV sig 1 F

/-! ## High-Dimensional Signatures -/

/-- Euclidean signature for dimension n (all +1) -/
def euclideanSig (n : ℕ) : Signature n := Signature.euclidean n

/-- High-dimensional CGA signature: R^{n+1,1} -/
def cgaHighDimSig (n : ℕ) : Signature (n + 2) :=
  ⟨BitVec.ofNat (n + 2) (1 <<< (n + 1)), 0⟩  -- Only e_{n+1} is negative

/-! ## Float DecidableEq for tests -/

instance : DecidableEq Float := fun a b =>
  if a == b then isTrue sorry_proof else isFalse sorry_proof

/-! ## Tests -/

section Tests

-- Small dimension for fast testing
def R8T : Signature 8 := euclideanSig 8

-- Create a vector in R8
def v1T : SVB R8T Float := TruncatedMV.basis ⟨0, by omega⟩
def v2T : SVB R8T Float := TruncatedMV.basis ⟨1, by omega⟩

-- Test: vectors have nnz = 1
#eval! v1T.nnz  -- 1

-- Test: v1 + v2 has nnz = 2
#eval! (v1T + v2T).nnz  -- 2

-- Test: scalar part of vector is 0
#eval! v1T.scalarPart  -- 0.0

-- Test: bivector basis
def b12T : SVB R8T Float := TruncatedMV.bivectorBasis ⟨0, by omega⟩ ⟨1, by omega⟩
#eval! b12T.nnz  -- 1

-- Test: geometric product (using explicit call)
#eval! let prod := TruncatedMV.geometricProduct v1T v2T
       prod.nnz  -- 1 (just bivector)

-- Test: v1 * v1 = 1 (scalar)
#eval! (TruncatedMV.geometricProduct v1T v1T).scalarPart  -- 1.0

-- High dimensional example: R128 with SVB representation
def R128 : Signature 128 := euclideanSig 128

-- This compiles even though R128 has 2^128 basis blades!
-- We only store up to grade 2 (scalar + 128 vector + 8128 bivector)
def v1_128 : SVB R128 Float := TruncatedMV.basis ⟨0, by omega⟩
#eval! v1_128.nnz  -- 1

#eval IO.println "✓ TruncatedMV module loaded"

end Tests

end Grassmann

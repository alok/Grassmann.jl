/-
  Grassmann/GradeSet.lean - Compile-time grade tracking for algebraic optimization

  This module provides type-level tracking of which grades are present in a multivector.
  This enables:
  1. Static sparsity: Skip grades known to be zero at compile time
  2. Product grade bounds: Wedge product of grade j and k has grade j+k
  3. Algebraic simplification: v² is scalar for vectors, B² is scalar+4vector for bivectors

  The grade set is a bitmask where bit i indicates grade i may be present.
  For n-dimensional algebra, grades range from 0 to n.

  Examples:
  - Scalar: grades = {0} = 0b1
  - Vector: grades = {1} = 0b10
  - Bivector: grades = {2} = 0b100
  - Rotor (even): grades = {0,2,4,...} = 0b...10101
  - Full multivector: grades = {0,1,...,n} = 2^(n+1) - 1
-/
import Grassmann.Multivector

namespace Grassmann

/-! ## Grade Set as Natural Number Bitmask -/

/-- A grade set is a bitmask indicating which grades may be present.
    Bit i is set iff grade i may have non-zero coefficients.
    We use Nat directly for simplicity. -/
abbrev GradeSet := Nat

namespace GradeSet

/-- Empty grade set (zero multivector) -/
def empty : GradeSet := 0

/-- Singleton grade set {k} -/
def singleton (k : Nat) : GradeSet := 1 <<< k

/-- Grade 0 (scalar) -/
def scalar : GradeSet := singleton 0

/-- Grade 1 (vector) -/
def vector : GradeSet := singleton 1

/-- Grade 2 (bivector) -/
def bivector : GradeSet := singleton 2

/-- Full grade set {0,1,...,n} -/
def full (n : Nat) : GradeSet := (1 <<< (n + 1)) - 1

/-- Even grades {0,2,4,...} up to n -/
def even (n : Nat) : GradeSet :=
  (List.range (n + 1)).filter (· % 2 = 0) |>.foldl (fun acc k => acc ||| (1 <<< k)) 0

/-- Odd grades {1,3,5,...} up to n -/
def odd (n : Nat) : GradeSet :=
  (List.range (n + 1)).filter (· % 2 = 1) |>.foldl (fun acc k => acc ||| (1 <<< k)) 0

/-- Check if grade k is in the set -/
def contains (gs : GradeSet) (k : Nat) : Bool := (gs &&& (1 <<< k)) != 0

/-- Union of grade sets -/
def union (a b : GradeSet) : GradeSet := a ||| b

/-- Intersection of grade sets -/
def inter (a b : GradeSet) : GradeSet := a &&& b

/-- Convert to list of grades -/
def toList (gs : GradeSet) (maxGrade : Nat := 16) : List Nat :=
  (List.range (maxGrade + 1)).filter (gs.contains ·)

/-- Pretty-print as a set of grade numbers.

Do not make this a `ToString GradeSet` instance: `GradeSet` is an abbrev for `Nat`,
so such an instance would globally change `Nat` string interpolation. -/
def toString (gs : GradeSet) : String :=
  s!"\{{String.intercalate ", " (gs.toList.map Nat.repr)}}"

instance : BEq GradeSet := inferInstanceAs (BEq Nat)
instance : Repr GradeSet := inferInstanceAs (Repr Nat)

end GradeSet

/-! ## Grade Bounds for Products

These compute the possible output grades given input grades.
-/

/-- Wedge product grade: grade(a ∧ b) = grade(a) + grade(b) if ≤ n, else 0 -/
def wedgeGradeSet (a b : GradeSet) (n : Nat) : GradeSet :=
  (List.range (n + 1)).foldl (init := 0) fun acc i =>
    (List.range (n + 1)).foldl (init := acc) fun acc2 j =>
      if a.contains i && b.contains j && i + j ≤ n then
        acc2 ||| (1 <<< (i + j))
      else acc2

/-- Left contraction grade: grade(a ⌋ b) = grade(b) - grade(a) if ≥ 0, else 0 -/
def leftContractGradeSet (a b : GradeSet) (n : Nat) : GradeSet :=
  (List.range (n + 1)).foldl (init := 0) fun acc i =>
    (List.range (n + 1)).foldl (init := acc) fun acc2 j =>
      if a.contains i && b.contains j && j ≥ i then
        acc2 ||| (1 <<< (j - i))
      else acc2

/-- Geometric product grade: all grades |i-j| to min(i+j, n) are possible -/
def geometricGradeSet (a b : GradeSet) (n : Nat) : GradeSet :=
  (List.range (n + 1)).foldl (init := 0) fun acc i =>
    (List.range (n + 1)).foldl (init := acc) fun acc2 j =>
      if a.contains i && b.contains j then
        -- Grades that can appear in the geometric product of a grade-i and grade-j blade are
        --   i + j, i + j - 2, i + j - 4, ...
        -- equivalently the interval [|i-j|, min(i+j,n)] but only the parity class of (i+j).
        --
        -- Keeping parity here makes grade-tracking *useful* for performance: e.g. vector*vector
        -- stays even (scalar+bivector), and even*even stays even, so sparse kernels skip the
        -- odd grades entirely.
        let minGrade := if i ≥ j then i - j else j - i
        let maxGradeRaw := min (i + j) n
        let maxGrade :=
          if (maxGradeRaw % 2) = (minGrade % 2) then maxGradeRaw
          else maxGradeRaw - 1
        let count : Nat := (maxGrade - minGrade) / 2 + 1
        (List.range count).foldl (init := acc2) fun acc3 t =>
          acc3 ||| (1 <<< (minGrade + 2 * t))
      else acc2

/-! ## Graded Multivector Type

A multivector annotated with compile-time grade information.
-/

/-- A multivector with compile-time known grade set.
    The grade set is an upper bound: actual grades present may be fewer.

**DEPRECATED**: Use `MV sig p` from `Grassmann.MV` instead with `p ∈ {.even, .odd, .full}`.
The unified MV type provides a cleaner API with simpler parity tracking. -/
structure GradedMV (sig : Signature n) (F : Type*) (grades : GradeSet) where
  mv : Multivector sig F

namespace GradedMV

variable {n : ℕ} {sig : Signature n} {F : Type*} [CoeffOps F]
variable {gs gs1 gs2 : GradeSet}

/-- Create from multivector (full grade set) -/
def ofMV (m : Multivector sig F) : GradedMV sig F (GradeSet.full n) := ⟨m⟩

/-- Scalar (grade 0) -/
def scalar (x : F) : GradedMV sig F GradeSet.scalar := ⟨Multivector.scalar x⟩

/-- From a vector (grade 1) -/
def ofVector (v : Multivector sig F) : GradedMV sig F GradeSet.vector := ⟨v.gradeProject 1⟩

/-- From a bivector (grade 2) -/
def ofBivector (b : Multivector sig F) : GradedMV sig F GradeSet.bivector := ⟨b.gradeProject 2⟩

/-- Even multivector (grades 0,2,4,...) like rotors -/
def ofEven (m : Multivector sig F) : GradedMV sig F (GradeSet.even n) := ⟨m.evenPart⟩

/-- Odd multivector (grades 1,3,5,...) -/
def ofOdd (m : Multivector sig F) : GradedMV sig F (GradeSet.odd n) := ⟨m.oddPart⟩

/-- Forget grade information -/
def toMultivector (gm : GradedMV sig F gs) : Multivector sig F := gm.mv

/-- Widen grade set (always safe) -/
def widen (gm : GradedMV sig F gs) (gs' : GradeSet) : GradedMV sig F (gs.union gs') := ⟨gm.mv⟩

/-- Add graded multivectors -/
def add (a : GradedMV sig F gs1) (b : GradedMV sig F gs2) :
    GradedMV sig F (gs1.union gs2) := ⟨a.mv + b.mv⟩

/-- Negate preserves grades -/
def neg (gm : GradedMV sig F gs) : GradedMV sig F gs := ⟨-gm.mv⟩

/-- Wedge product with grade tracking -/
def wedge (a : GradedMV sig F gs1) (b : GradedMV sig F gs2) :
    GradedMV sig F (wedgeGradeSet gs1 gs2 n) := ⟨a.mv ⋀ᵐ b.mv⟩

/-- Geometric product with grade tracking -/
def mul (a : GradedMV sig F gs1) (b : GradedMV sig F gs2) :
    GradedMV sig F (geometricGradeSet gs1 gs2 n) := ⟨a.mv * b.mv⟩

/-- Left contraction with grade tracking -/
def leftContract (a : GradedMV sig F gs1) (b : GradedMV sig F gs2) :
    GradedMV sig F (leftContractGradeSet gs1 gs2 n) := ⟨a.mv ⌋ᵐ b.mv⟩

/-- Reverse preserves grades -/
def reverse (gm : GradedMV sig F gs) : GradedMV sig F gs := ⟨gm.mv†⟩

/-- Involute preserves grades -/
def involute (gm : GradedMV sig F gs) : GradedMV sig F gs := ⟨gm.mvˆ⟩

end GradedMV

/-! ### Coercions

`GradedMV` is a zero-cost wrapper around `Multivector` carrying extra
compile-time grade metadata. Coercions keep the API ergonomic: you can pass a
`GradedMV` anywhere a `Multivector` is expected without calling `.mv`. -/

instance {n : ℕ} {sig : Signature n} {F : Type*} {gs : GradeSet} :
    CoeTC (GradedMV sig F gs) (Multivector sig F) :=
  ⟨fun gm => gm.mv⟩

/-! ## Algebraic Identities with Grade Info

Key identities that can be proven/used with grade tracking:
-/

-- Vector squared produces scalar + bivector in the general case.
-- In Euclidean R3, v² = scalar (but type system tracks upper bound).
#eval geometricGradeSet GradeSet.vector GradeSet.vector 3  -- 5 = {0, 2}

-- Bivector squared produces grades 0, 2, 4 in general
#eval geometricGradeSet GradeSet.bivector GradeSet.bivector 3  -- 5 = {0, 2}

-- Even * even stays even
#eval geometricGradeSet (GradeSet.even 3) (GradeSet.even 3) 3

-- Odd * odd produces even
#eval geometricGradeSet (GradeSet.odd 3) (GradeSet.odd 3) 3

/-! ## Tests -/

-- Grade set tests
#eval GradeSet.toString (GradeSet.vector : GradeSet)  -- {1}
#eval GradeSet.toString (GradeSet.even 3 : GradeSet)  -- {0, 2}
#eval GradeSet.toString (GradeSet.odd 3 : GradeSet)   -- {1, 3}
#eval GradeSet.toString (GradeSet.full 3 : GradeSet)  -- {0, 1, 2, 3}

-- Product grade bounds
#eval GradeSet.toString (wedgeGradeSet GradeSet.vector GradeSet.vector 3)  -- {2}
#eval GradeSet.toString (geometricGradeSet GradeSet.vector GradeSet.vector 3)  -- {0, 2}
#eval GradeSet.toString (geometricGradeSet (GradeSet.even 3) (GradeSet.even 3) 3)  -- {0, 2}
#eval GradeSet.toString (leftContractGradeSet GradeSet.vector GradeSet.bivector 3)  -- {1}

-- Rotor * rotor stays even
#eval GradeSet.toString (geometricGradeSet (GradeSet.scalar ||| GradeSet.bivector)
                         (GradeSet.scalar ||| GradeSet.bivector) 3)  -- {0, 2}

end Grassmann

/-
  Grassmann/Blade.lean - Basis blades (Submanifold in Julia)

  Port of DirectSum.jl's Submanifold{V, n, Indices} type.

  A basis blade is a wedge product of basis vectors, e.g., e₁∧e₂∧e₃.
  It is represented by:
  - A signature (which algebra we're in)
  - A bitmask of which basis vectors are present

  Key insight: In Julia, grade is a type parameter but can be recovered from popcount.
  In Lean 4, we can either:
  1. Store grade explicitly for O(1) access
  2. Compute it from the bitmask (our popcount is O(log n))

  We choose option 1 for efficiency, with a proof that it matches the bitmask.
-/
import Grassmann.Manifold

namespace Grassmann

/-! ## Basis Blade Type

A basis blade in Cl(V) where V has signature `sig`.
The blade is determined by a bitmask of which basis vectors are present.
-/

/-- A basis blade in the Clifford algebra with signature `sig`.
    `bits` encodes which basis vectors are present via set bits.
    Grade is computed from the bitmask. -/
structure Blade (sig : Signature n) where
  /-- Bitmask of basis vectors in this blade -/
  bits : BitVec n
  deriving DecidableEq, Repr

namespace Blade

variable {n : ℕ} {sig : Signature n}

/-- The grade (number of basis vectors) of a blade -/
def grade (b : Blade sig) : ℕ := Grassmann.grade b.bits

/-- The scalar (grade 0) blade -/
def scalar : Blade sig := ⟨0⟩

/-- The pseudoscalar (grade n) blade -/
def pseudoscalar : Blade sig := ⟨Grassmann.pseudoscalar⟩

/-- Single basis vector e_i -/
def basis (i : Fin n) : Blade sig := ⟨singleBit i⟩

/-- Check if this is the scalar blade -/
def isScalar (b : Blade sig) : Bool := b.bits == 0

/-- Check if this is the pseudoscalar -/
def isPseudoscalar (b : Blade sig) : Bool := b.bits == Grassmann.pseudoscalar

/-- Check if this is a vector (grade 1) -/
def isVector (b : Blade sig) : Bool := b.grade == 1

/-- Check if this is a bivector (grade 2) -/
def isBivector (b : Blade sig) : Bool := b.grade == 2

/-- Get the list of basis vector indices in this blade -/
def basisIndices (b : Blade sig) : List (Fin n) := indices b.bits

/-- Check if basis vector i is in this blade -/
def hasBasis (b : Blade sig) (i : Fin n) : Bool := b.bits.getLsbD i

/-- The complement blade (XOR with pseudoscalar) -/
def complement (b : Blade sig) : Blade sig := ⟨b.bits ^^^ Grassmann.pseudoscalar⟩

/-- Reverse the blade (reverses order of basis vectors).
    For a k-blade, this multiplies by (-1)^(k(k-1)/2). -/
def reverseSign (b : Blade sig) : Int :=
  let k := b.grade
  if (k * (k - 1) / 2) % 2 == 0 then 1 else -1

/-- The square of this basis blade under the metric.
    For a simple blade e_i₁∧...∧e_iₖ, this is the product of the e_iⱼ² values,
    times the reversal sign. -/
def squareSign (b : Blade sig) : Int :=
  sig.bladeSquareSign b.bits * b.reverseSign

end Blade

/-! ## Scaled Blade (Single in Julia)

A Single is a scalar coefficient times a basis blade.
This is the building block for multivectors.
-/

/-- A scaled blade: coefficient × basis blade -/
structure Single (sig : Signature n) (F : Type*) where
  /-- The scalar coefficient -/
  coeff : F
  /-- The basis blade -/
  blade : Blade sig
  deriving Repr

namespace Single

variable {n : ℕ} {sig : Signature n} {F : Type*}

/-- Grade of a single is the grade of its blade -/
def grade (s : Single sig F) : ℕ := s.blade.grade

/-- Create a scalar single -/
def ofScalar [Zero F] (x : F) : Single sig F := ⟨x, Blade.scalar⟩

/-- Create a single from coefficient and basis index -/
def ofBasis [One F] (i : Fin n) : Single sig F := ⟨1, Blade.basis i⟩

/-- Check if this single is zero (either coeff is zero or conceptually) -/
def isZeroCoeff [DecidableEq F] [Zero F] (s : Single sig F) : Bool := s.coeff == 0

/-- Negate the coefficient -/
def neg [Neg F] (s : Single sig F) : Single sig F := ⟨-s.coeff, s.blade⟩

/-- Scale by a scalar -/
def smul [Mul F] (x : F) (s : Single sig F) : Single sig F := ⟨x * s.coeff, s.blade⟩

instance [Zero F] : Zero (Single sig F) := ⟨⟨0, Blade.scalar⟩⟩
instance [Neg F] : Neg (Single sig F) := ⟨Single.neg⟩

end Single

/-! ## Standard Basis Blades

Convenient accessors for common basis blades in specific dimensions.
-/

section StandardBasis

variable {sig : Signature n}

/-- e₁ basis vector -/
def e1 (h : 1 ≤ n := by omega) : Blade sig := Blade.basis ⟨0, by omega⟩

/-- e₂ basis vector -/
def e2 (h : 2 ≤ n := by omega) : Blade sig := Blade.basis ⟨1, by omega⟩

/-- e₃ basis vector -/
def e3 (h : 3 ≤ n := by omega) : Blade sig := Blade.basis ⟨2, by omega⟩

/-- e₄ basis vector -/
def e4 (h : 4 ≤ n := by omega) : Blade sig := Blade.basis ⟨3, by omega⟩

/-- e₁₂ = e₁∧e₂ bivector -/
def e12 (_ : 2 ≤ n := by omega) : Blade sig := ⟨BitVec.ofNat n 0b11⟩

/-- e₁₃ = e₁∧e₃ bivector -/
def e13 (_ : 3 ≤ n := by omega) : Blade sig := ⟨BitVec.ofNat n 0b101⟩

/-- e₂₃ = e₂∧e₃ bivector -/
def e23 (_ : 3 ≤ n := by omega) : Blade sig := ⟨BitVec.ofNat n 0b110⟩

/-- e₁₂₃ = e₁∧e₂∧e₃ trivector -/
def e123 (_ : 3 ≤ n := by omega) : Blade sig := ⟨BitVec.ofNat n 0b111⟩

end StandardBasis

/-! ## Tests -/

#eval (Blade.scalar : Blade R3).grade  -- 0
#eval (Blade.pseudoscalar : Blade R3).grade  -- 3
#eval (e1 : Blade R3).grade  -- 1
#eval (e12 : Blade R3).grade  -- 2
#eval (e123 : Blade R3).grade  -- 3
#eval (e123 : Blade R3).basisIndices  -- [0, 1, 2]
#eval (e13 : Blade R3).basisIndices  -- [0, 2]

-- Reverse signs
#eval (Blade.scalar : Blade R3).reverseSign  -- 1
#eval (e1 : Blade R3).reverseSign  -- 1
#eval (e12 : Blade R3).reverseSign  -- -1 (bivector reverses)
#eval (e123 : Blade R3).reverseSign  -- -1 (trivector reverses)

-- Square signs in Euclidean space (all positive)
#eval (e1 : Blade R3).squareSign  -- 1
#eval (e12 : Blade R3).squareSign  -- -1 (because reversal)
#eval (e123 : Blade R3).squareSign  -- -1

end Grassmann

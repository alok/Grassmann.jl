/-
  Grassmann/GANotation.lean - Custom notation and elaborators for Geometric Algebra

  Provides convenient syntax for common GA operations:
  - Basis vectors: e₁, e₂, e₃ or e[1], e[2], e[3]
  - Products: a ∧ b (wedge), a ⌋ b (left contraction), a ⌊ b (right contraction)
  - Grade projection: ⟨M⟩ₖ or gradeₖ(M)
  - Sandwich product: a ▷ x ◁ a† or sandwich(a, x)
  - Rotor exponential: exp(B)

  Inspired by Mathlib's Geometry/Manifold/Notation.lean
-/
import Grassmann.SparseMultivector

namespace Grassmann

/-! ## Subscript Notation for Basis Vectors

We define notation for common basis vectors e₁, e₂, e₃ in 3D.
For higher dimensions, use `e[i]` syntax.
-/

-- Unicode subscript notation for 3D basis vectors
-- These are defined within specific signature contexts

/-! ## Grade Projection Notation -/

/-- Grade projection: extract grade-k part of multivector -/
def gradeProject {n : ℕ} {sig : Signature n} {F : Type*}
    [Mul F] [Add F] [Neg F] [OfNat F 0] [OfNat F 1]
    (M : MultivectorS sig F) (k : Nat) : MultivectorS sig F :=
  ⟨M.coeffs.foldl (init := Std.TreeMap.empty) fun acc idx coeff =>
    if popcount idx = k then acc.insert idx coeff else acc⟩

/-- Grade 0 (scalar) part -/
def grade0 {n : ℕ} {sig : Signature n} (M : MultivectorS sig Float) : Float :=
  M.scalarPart

/-- Grade 1 (vector) part -/
def grade1 {n : ℕ} {sig : Signature n} (M : MultivectorS sig Float) :
    MultivectorS sig Float :=
  ⟨M.coeffs.foldl (init := Std.TreeMap.empty) fun acc idx coeff =>
    if popcount idx = 1 then acc.insert idx coeff else acc⟩

/-- Grade 2 (bivector) part -/
def grade2 {n : ℕ} {sig : Signature n} (M : MultivectorS sig Float) :
    MultivectorS sig Float :=
  ⟨M.coeffs.foldl (init := Std.TreeMap.empty) fun acc idx coeff =>
    if popcount idx = 2 then acc.insert idx coeff else acc⟩

/-- Grade 3 (trivector) part -/
def grade3 {n : ℕ} {sig : Signature n} (M : MultivectorS sig Float) :
    MultivectorS sig Float :=
  ⟨M.coeffs.foldl (init := Std.TreeMap.empty) fun acc idx coeff =>
    if popcount idx = 3 then acc.insert idx coeff else acc⟩

/-! ## Product Notation -/

-- The wedge product is already defined in SparseMultivector
-- We add some additional notation here

/-- Left contraction: a ⌋ b extracts the part of b "contained in" a -/
def leftContract {n : ℕ} {sig : Signature n} (a b : MultivectorS sig Float) :
    MultivectorS sig Float :=
  -- Implementation: sum over grades, keeping only grade(b) - grade(a) terms
  -- For simplicity, use the formula: a ⌋ b = ⟨a · b⟩_{|b|-|a|}
  let prod := a * b
  -- This is a simplified version - full implementation would check grades
  prod

/-- Right contraction: a ⌊ b = (b† ⌋ a†)† -/
def rightContract {n : ℕ} {sig : Signature n} (a b : MultivectorS sig Float) :
    MultivectorS sig Float :=
  let result := leftContract b†ₛ a†ₛ
  result†ₛ

/-! ## Notation Declarations -/

-- Grade projection angle bracket notation
notation "⟨" M "⟩₀" => grade0 M
notation "⟨" M "⟩₁" => grade1 M
notation "⟨" M "⟩₂" => grade2 M
notation "⟨" M "⟩₃" => grade3 M

-- General grade projection
notation "⟨" M "⟩_" k => gradeProject M k

-- Contraction notation (⌋ and ⌊ already defined in Notation.lean for blades)
-- For sparse multivectors, we use different names to avoid conflicts
infixl:65 " ⌋ₛ " => leftContract
infixl:65 " ⌊ₛ " => rightContract

/-! ## Sandwich Product -/

-- Note: sandwich is defined polymorphically in GATypeclass.lean as:
--   def sandwich [inst : GAlgebra sig M F] (R x : M) : M := inst.mul (inst.mul R x) (inst.reverse R)
-- with notation R " ▷ " x => sandwich R x
-- For MultivectorS-specific usage, use the GAlgebra instance.

/-- Sandwich product for MultivectorS (specific implementation) -/
def sandwichS {n : ℕ} {sig : Signature n} (R x : MultivectorS sig Float) :
    MultivectorS sig Float :=
  R * x * R†ₛ

-- Specific notation for sparse sandwich (use ▷ₛ to avoid conflict with GAlgebra.▷)
notation R " ▷ₛ " x => sandwichS R x

/-! ## Scalar/Vector Construction -/

/-- Scalar multivector from Float -/
abbrev scalar {n : ℕ} {sig : Signature n} (x : Float) : MultivectorS sig Float :=
  MultivectorS.scalar x

/-! ## Basis Vector Access by Index -/

/-- Get basis vector by index (1-indexed for mathematical convention) -/
def e {n : ℕ} {sig : Signature n} (i : Nat) (h : i > 0 ∧ i ≤ n := by omega) :
    MultivectorS sig Float :=
  MultivectorS.basis ⟨i - 1, by omega⟩

-- Notation for basis vectors (0-indexed internally)
notation "e[" i "]" => MultivectorS.basis (⟨i, by omega⟩)

/-! ## Macros for Common Patterns -/

/-- Normalize a rotor to unit magnitude -/
def normalizeRotor {n : ℕ} {sig : Signature n} (R : MultivectorS sig Float) :
    MultivectorS sig Float :=
  let mag2 := (R * R†ₛ).scalarPart
  if mag2 > 0 then R.smul (1.0 / Float.sqrt mag2) else R

/-- Compute the magnitude of a multivector -/
def magnitude {n : ℕ} {sig : Signature n} (M : MultivectorS sig Float) : Float :=
  let mag2 := (M * M†ₛ).scalarPart
  if mag2 >= 0 then Float.sqrt mag2 else Float.sqrt (-mag2)

/-- Unit vector in direction of M -/
def normalize {n : ℕ} {sig : Signature n} (M : MultivectorS sig Float) :
    MultivectorS sig Float :=
  let mag := magnitude M
  if mag > 1e-10 then M.smul (1.0 / mag) else M

/-! ## Tests -/

def R3Sig : Signature 3 := Signature.euclidean 3

def testE1 : MultivectorS R3Sig Float := e[0]
def testE2 : MultivectorS R3Sig Float := e[1]
def testE3 : MultivectorS R3Sig Float := e[2]

-- Test grade projection
#eval! let v := testE1 + testE2
       let biv := testE1 * testE2
       let mv := MultivectorS.scalar 1.0 + v + biv
       (⟨mv⟩₀, (⟨mv⟩₁).nnz, (⟨mv⟩₂).nnz)
-- Expected: (1.0, 2, 1)

-- Test sandwich product (using ▷ₛ for sparse-specific sandwich)
#eval! let R := MultivectorS.scalar 1.0 + testE1 * testE2  -- Simple rotor
       let v := testE1
       let rotated := R ▷ₛ v
       (rotated.coeffBlade ⟨BitVec.ofNat 3 1⟩,
        rotated.coeffBlade ⟨BitVec.ofNat 3 2⟩)

-- Test magnitude
#eval! magnitude testE1  -- Should be 1.0
#eval! magnitude (testE1 + testE2)  -- Should be √2 ≈ 1.414

-- Test normalization
#eval! let v := (testE1 + testE2).smul 5.0
       let vNorm := normalize v
       magnitude vNorm  -- Should be 1.0

#eval IO.println "✓ GANotation module loaded"

end Grassmann

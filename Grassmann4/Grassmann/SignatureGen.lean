/-
  Grassmann/SignatureGen.lean - Generalized metric signatures over arbitrary rings

  Supports:
  - Euclidean: eᵢ² = 1
  - Anti-Euclidean: eᵢ² = -1
  - Degenerate (PGA): eᵢ² = 0
  - Mixed signatures (CGA, Minkowski)
  - Arbitrary field coefficients

  The key insight: the signature is a function `Fin n → R` where R is a ring,
  giving the square of each basis vector. This generalizes the BitVec approach.
-/
import Mathlib.Algebra.Ring.Defs
-- import Mathlib.Data.Fin.Basic  -- WORKAROUND: runtime panic in Mathlib v4.26.0-rc2
import Grassmann.BitMask

namespace Grassmann

/-! ## Generalized Signature

A signature over ring R assigns a "square" value to each basis vector.
Standard cases:
- Euclidean Rⁿ: all squares = 1
- Minkowski R³,¹: three +1, one -1
- PGA R³,⁰,¹: three +1, one 0 (degenerate)
- CGA R⁴,¹: four +1, one -1
-/

/-- Generalized signature: assigns the square of each basis vector.
    `metric i` is the value of eᵢ² in the algebra. -/
structure SignatureG (n : ℕ) (R : Type*) [Ring R] where
  /-- The square of basis vector eᵢ -/
  metric : Fin n → R

namespace SignatureG

variable {n : ℕ} {R : Type*} [Ring R]

/-! ### Standard Signature Constructors -/

/-- Euclidean signature: all basis vectors square to 1 -/
def euclidean (n : ℕ) (R : Type*) [Ring R] : SignatureG n R := ⟨fun _ => 1⟩

/-- Anti-Euclidean signature: all basis vectors square to -1 -/
def antiEuclidean (n : ℕ) (R : Type*) [Ring R] : SignatureG n R := ⟨fun _ => -1⟩

/-- Degenerate signature: all basis vectors square to 0 -/
def degenerate (n : ℕ) (R : Type*) [Ring R] : SignatureG n R := ⟨fun _ => 0⟩

/-- Mixed signature R^{p,q}: first p positive, next q negative -/
def mixed (p q : ℕ) (_hp : p + q = n) (R : Type*) [Ring R] : SignatureG n R :=
  ⟨fun i => if i.val < p then 1 else -1⟩

/-- Mixed with degenerate R^{p,q,r}: p positive, q negative, r zero -/
def mixedDegen (p q r : ℕ) (_h : p + q + r = n) (R : Type*) [Ring R] : SignatureG n R :=
  ⟨fun i => if i.val < p then 1 else if i.val < p + q then -1 else 0⟩

/-! ### Named Signatures -/

/-- Minkowski spacetime R³,¹ (3 space + 1 time with signature +,+,+,-) -/
def minkowski (R : Type*) [Ring R] : SignatureG 4 R :=
  ⟨fun i => if i.val < 3 then 1 else -1⟩

/-- PGA 3D (Projective Geometric Algebra): R³,⁰,¹ -/
def pga3d (R : Type*) [Ring R] : SignatureG 4 R :=
  ⟨fun i => if i.val < 3 then 1 else 0⟩

/-- CGA 3D (Conformal Geometric Algebra): R⁴,¹ -/
def cga3d (R : Type*) [Ring R] : SignatureG 5 R :=
  ⟨fun i => if i.val < 4 then 1 else -1⟩

/-- Spacetime Algebra (STA): R¹,³ (first positive, rest negative) -/
def sta (R : Type*) [Ring R] : SignatureG 4 R :=
  ⟨fun i => if i.val = 0 then 1 else -1⟩

/-! ### Signature Properties -/

/-- Check if basis vector i is Euclidean (squares to 1) -/
def isEuclidean (sig : SignatureG n R) (i : Fin n) : Prop :=
  sig.metric i = 1

/-- Check if basis vector i is anti-Euclidean (squares to -1) -/
def isAntiEuclidean (sig : SignatureG n R) (i : Fin n) : Prop :=
  sig.metric i = -1

/-- Check if basis vector i is degenerate (squares to 0) -/
def isDegenerate (sig : SignatureG n R) (i : Fin n) : Prop :=
  sig.metric i = 0

/-- Count of positive-squared basis vectors -/
def positiveCount [DecidableEq R] (sig : SignatureG n R) : ℕ :=
  (List.finRange n).countP (fun i => sig.metric i = 1)

/-- Count of negative-squared basis vectors -/
def negativeCount [DecidableEq R] (sig : SignatureG n R) : ℕ :=
  (List.finRange n).countP (fun i => sig.metric i = -1)

/-- Count of zero-squared (degenerate) basis vectors -/
def degenerateCount [DecidableEq R] (sig : SignatureG n R) : ℕ :=
  (List.finRange n).countP (fun i => sig.metric i = 0)

end SignatureG

/-! ## Blade with Generalized Signature -/

/-- Blade in a Clifford algebra with generalized signature -/
structure BladeG {n : ℕ} {R : Type*} [Ring R] (sig : SignatureG n R) where
  /-- Bitmask representing which basis vectors are present -/
  bits : BitVec n
  deriving Repr, DecidableEq, Hashable

namespace BladeG

variable {n : ℕ} {R : Type*} [Ring R] {sig : SignatureG n R}

/-- Grade of a blade (number of basis vectors) -/
def grade (b : BladeG sig) : ℕ := popcount b.bits.toNat

/-- Scalar blade (grade 0) -/
def scalar : BladeG sig := ⟨0⟩

/-- Pseudoscalar blade (all basis vectors) -/
def pseudoscalar : BladeG sig := ⟨BitVec.allOnes n⟩

/-- Basis vector eᵢ -/
def basis (i : Fin n) : BladeG sig := ⟨BitVec.ofNat n (1 <<< i.val)⟩

/-- Check if basis vector i is in the blade -/
def hasBasis (b : BladeG sig) (i : Fin n) : Bool := b.bits.getLsbD i.val

end BladeG

/-! ## Geometric Product Sign with Generalized Metric -/

/-- Count transpositions needed to order basis vectors.
    Same as before - this is metric-independent. -/
def countSwapsG {n : ℕ} (a b : BitVec n) : ℕ :=
  let bitsA := (List.finRange n).filter fun i => a.getLsbD i.val
  let bitsB := (List.finRange n).filter fun i => b.getLsbD i.val
  bitsA.foldl (fun acc i =>
    acc + (bitsB.filter fun j => j.val < i.val).length
  ) 0

/-- Metric contribution: product of metric values for contracted basis vectors.
    For generalized signature, this is ∏_{i ∈ contracted} sig.metric(i) -/
def metricContributionG {n : ℕ} {R : Type*} [Ring R]
    (sig : SignatureG n R) (contracted : BitVec n) : R :=
  (List.finRange n).foldl (fun acc i =>
    if contracted.getLsbD i.val then acc * sig.metric i else acc
  ) 1

/-- Full geometric product sign/coefficient for generalized signature -/
def geometricSignG {n : ℕ} {R : Type*} [Ring R]
    (sig : SignatureG n R) (a b : BladeG sig) : R :=
  let swaps := countSwapsG a.bits b.bits
  let contracted := a.bits &&& b.bits
  let metricPart := metricContributionG sig contracted
  let swapSign : R := if swaps % 2 = 0 then 1 else -1
  swapSign * metricPart

/-! ## Sparse Multivector with Generalized Signature -/

/-- Sparse multivector over generalized signature using TreeMap -/
structure MultivectorG {n : ℕ} {R : Type*} [Ring R] (sig : SignatureG n R) (F : Type*)
    [Mul F] [Add F] [Neg F] [OfNat F 0] where
  coeffs : Std.TreeMap Nat F
  deriving Repr

namespace MultivectorG

variable {n : ℕ} {R : Type*} [Ring R] {sig : SignatureG n R}
variable {F : Type*} [Mul F] [Add F] [Neg F] [OfNat F 0] [OfNat F 1]

/-- Zero multivector -/
def zero : MultivectorG sig F := ⟨Std.TreeMap.empty⟩

/-- Scalar multivector -/
def scalar (x : F) : MultivectorG sig F :=
  ⟨Std.TreeMap.empty.insert 0 x⟩

/-- Basis vector eᵢ -/
def basis (i : Fin n) : MultivectorG sig F :=
  ⟨Std.TreeMap.empty.insert (1 <<< i.val) 1⟩

/-- Get coefficient of a blade -/
def coeffBlade (m : MultivectorG sig F) (b : BladeG sig) : F :=
  m.coeffs.get? b.bits.toNat |>.getD 0

/-- Number of non-zero terms -/
def nnz (m : MultivectorG sig F) : Nat := m.coeffs.size

end MultivectorG

end Grassmann

/-
  Grassmann/Manifold.lean - Manifold and Signature types

  Port of DirectSum.jl's TensorBundle and Signature types.

  Key insight: In Julia, Signature{N,M,S,F,D,L} uses type parameters to encode:
    - N: dimension
    - S: bitmask for which basis vectors square to -1

  In Lean 4, we use dependent types more directly:
    - `Signature n` has `metric : BitVec n` encoding the signature
    - We get compile-time dimension checking for free

  The signature determines the quadratic form Q(e_i) = metric[i] ? -1 : +1
-/
import Grassmann.BitMask

namespace Grassmann

/-! ## Metric Signature

A metric signature for an n-dimensional space determines which basis vectors
square to +1 (Euclidean) vs -1 (anti-Euclidean).

Standard signatures:
- ℝⁿ (Euclidean): all +1, metric = 0
- ℝⁿ⁻¹'¹ (Minkowski): one -1, metric = 1 (or 2^(n-1) for last basis)
- Cl(p,q): p positive, q negative
-/

/-- A metric signature for an n-dimensional vector space.
    `metric[i] = true` means e_i² = -1, `metric[i] = false` means e_i² = +1 -/
structure Signature (n : ℕ) where
  /-- Bitmask: bit i set means basis vector i squares to -1 -/
  metric : BitVec n
  deriving DecidableEq, Repr

namespace Signature

/-- Euclidean signature (all basis vectors square to +1) -/
def euclidean (n : ℕ) : Signature n := ⟨0⟩

/-- Anti-Euclidean signature (all basis vectors square to -1) -/
def antiEuclidean (n : ℕ) : Signature n := ⟨pseudoscalar⟩

/-- Minkowski signature with first basis vector timelike (squares to -1) -/
def minkowski (n : ℕ) (_ : n > 0 := by omega) : Signature n :=
  ⟨BitVec.ofNat n 1⟩

/-- Minkowski signature with last basis vector timelike -/
def minkowskiLast (n : ℕ) (_ : n > 0 := by omega) : Signature n :=
  ⟨BitVec.ofNat n (1 <<< (n - 1))⟩

/-- Cl(p,q) signature: p positive, q negative dimensions -/
def cl (p q : ℕ) : Signature (p + q) :=
  -- First p basis vectors are positive (0), next q are negative (1)
  ⟨BitVec.ofNat (p + q) ((1 <<< q) - 1) <<< p⟩

/-- Number of basis vectors that square to +1 -/
def numPositive (sig : Signature n) : ℕ := n - grade sig.metric

/-- Number of basis vectors that square to -1 -/
def numNegative (sig : Signature n) : ℕ := grade sig.metric

/-- Check if basis vector i squares to +1 -/
def isPositive (sig : Signature n) (i : Fin n) : Bool := !sig.metric.getLsbD i

/-- Check if basis vector i squares to -1 -/
def isNegative (sig : Signature n) (i : Fin n) : Bool := sig.metric.getLsbD i

/-- The sign of e_i²: +1 or -1 as an Int -/
def basisSquare (sig : Signature n) (i : Fin n) : Int :=
  if sig.isPositive i then 1 else -1

/-- Product of signs for a set of basis vectors (for computing blade squares) -/
def bladeSquareSign (sig : Signature n) (blade : BitVec n) : Int :=
  let negCount := grade (sig.metric &&& blade)
  if negCount % 2 = 0 then 1 else -1

end Signature

/-! ## Common Signatures -/

/-- The standard Euclidean spaces -/
abbrev R1 : Signature 1 := Signature.euclidean 1
abbrev R2 : Signature 2 := Signature.euclidean 2
abbrev R3 : Signature 3 := Signature.euclidean 3
abbrev R4 : Signature 4 := Signature.euclidean 4

/-- Complex numbers as Cl(0,1) -/
abbrev ℂ_sig : Signature 1 := Signature.antiEuclidean 1

/-- Quaternions as Cl(0,2) -/
abbrev ℍ_sig : Signature 2 := Signature.antiEuclidean 2

/-- Spacetime algebra Cl(1,3) with (+,-,-,-) convention -/
abbrev STA : Signature 4 := Signature.cl 1 3

/-- Conformal geometric algebra in 3D: Cl(4,1) -/
abbrev CGA3 : Signature 5 := Signature.cl 4 1

/-- Projective geometric algebra in 3D: Cl(3,0,1) with degenerate direction
    For now, represented as Cl(3,1) - proper PGA needs null vectors -/
abbrev PGA3 : Signature 4 := Signature.cl 3 1

/-! ## Manifold typeclass

This is the abstract interface that Signature implements.
Other representations (DiagonalForm, etc.) could also implement this.
-/

/-- Typeclass for types that represent a geometric algebra manifold -/
class Manifold (V : Type*) where
  /-- Dimension of the vector space -/
  dim : ℕ
  /-- Sign of basis vector i squared -/
  basisSign : Fin dim → Int

instance (n : ℕ) : Manifold (Signature n) where
  dim := n
  basisSign := fun i => Signature.basisSquare ⟨0⟩ i  -- Default to Euclidean

/-! ## Dimension and Signature Queries -/

/-- Get dimension from a signature -/
def Signature.dim (_ : Signature n) : ℕ := n

/-- Total dimension of the Clifford algebra (2^n) -/
def Signature.algebraDim (_ : Signature n) : ℕ := 2^n

/-- Number of basis blades of grade g -/
def Signature.gradeCount (_ : Signature n) (g : ℕ) : ℕ := gradesCount n g

/-! ## Tests -/

#eval R3.dim  -- 3
#eval R3.numPositive  -- 3
#eval R3.numNegative  -- 0
#eval STA.numPositive  -- 1
#eval STA.numNegative  -- 3
#eval Signature.cl 3 2 |>.numPositive  -- 3
#eval Signature.cl 3 2 |>.numNegative  -- 2

end Grassmann

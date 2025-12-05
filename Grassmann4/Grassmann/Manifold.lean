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
    Encodes the quadratic form: e_i² = +1, -1, or 0 (degenerate/null).

    - `metric[i] = true` means e_i² = -1 (anti-Euclidean)
    - `metric[i] = false` means e_i² = +1 (Euclidean)
    - `degenerate[i] = true` means e_i² = 0 (null, overrides metric)

    For Cl(p,q,r): p positive, q negative, r degenerate dimensions -/
structure Signature (n : ℕ) where
  /-- Bitmask: bit i set means basis vector i squares to -1 -/
  metric : BitVec n
  /-- Bitmask: bit i set means basis vector i is degenerate (squares to 0) -/
  degenerate : BitVec n := 0
  deriving DecidableEq, Repr

namespace Signature

/-- Euclidean signature (all basis vectors square to +1) -/
def euclidean (n : ℕ) : Signature n := ⟨0, 0⟩

/-- Anti-Euclidean signature (all basis vectors square to -1) -/
def antiEuclidean (n : ℕ) : Signature n := ⟨pseudoscalar, 0⟩

/-- Minkowski signature with first basis vector timelike (squares to -1) -/
def minkowski (n : ℕ) (_ : n > 0 := by omega) : Signature n :=
  ⟨BitVec.ofNat n 1, 0⟩

/-- Minkowski signature with last basis vector timelike -/
def minkowskiLast (n : ℕ) (_ : n > 0 := by omega) : Signature n :=
  ⟨BitVec.ofNat n (1 <<< (n - 1)), 0⟩

/-- Cl(p,q) signature: p positive, q negative dimensions -/
def cl (p q : ℕ) : Signature (p + q) :=
  -- First p basis vectors are positive (0), next q are negative (1)
  ⟨BitVec.ofNat (p + q) (((1 <<< q) - 1) <<< p), 0⟩

/-- Cl(p,q,r) signature: p positive, q negative, r degenerate dimensions.
    Layout: First p basis vectors are positive, next q are negative, last r are null. -/
def clr (p q r : ℕ) : Signature (p + q + r) :=
  let n := p + q + r
  -- Negative basis vectors are at positions p..p+q-1
  let metric := BitVec.ofNat n (((1 <<< q) - 1) <<< p)
  -- Degenerate basis vectors are at positions p+q..p+q+r-1 (the last r positions)
  let degenerate := BitVec.ofNat n (((1 <<< r) - 1) <<< (p + q))
  ⟨metric, degenerate⟩

/-- Number of basis vectors that square to +1 -/
def numPositive (sig : Signature n) : ℕ :=
  n - grade sig.metric - grade sig.degenerate

/-- Number of basis vectors that square to -1 -/
def numNegative (sig : Signature n) : ℕ :=
  grade (sig.metric &&& ~~~sig.degenerate)

/-- Number of degenerate (null) basis vectors that square to 0 -/
def numDegenerate (sig : Signature n) : ℕ := grade sig.degenerate

/-- Check if basis vector i is degenerate (squares to 0) -/
def isDegenerate (sig : Signature n) (i : Fin n) : Bool := sig.degenerate.getLsbD i

/-- Check if basis vector i squares to +1 (non-degenerate positive) -/
def isPositive (sig : Signature n) (i : Fin n) : Bool :=
  !sig.degenerate.getLsbD i && !sig.metric.getLsbD i

/-- Check if basis vector i squares to -1 (non-degenerate negative) -/
def isNegative (sig : Signature n) (i : Fin n) : Bool :=
  !sig.degenerate.getLsbD i && sig.metric.getLsbD i

/-- The sign of e_i²: +1, -1, or 0 as an Int -/
def basisSquare (sig : Signature n) (i : Fin n) : Int :=
  if sig.isDegenerate i then 0
  else if sig.isPositive i then 1 else -1

/-- Product of signs for a set of basis vectors (for computing blade squares).
    Returns 0 if any degenerate basis vector is included. -/
def bladeSquareSign (sig : Signature n) (blade : BitVec n) : Int :=
  -- If any degenerate basis vector is in the blade, the square is 0
  if (sig.degenerate &&& blade) != 0 then 0
  else
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
    e₁, e₂, e₃ square to +1, e₄ (the projective direction) squares to 0 -/
abbrev PGA3 : Signature 4 := Signature.clr 3 0 1

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
  basisSign := fun i => Signature.basisSquare ⟨0, 0⟩ i  -- Default to Euclidean

/-! ## Dimension and Signature Queries -/

/-- Get dimension from a signature -/
def Signature.dim (_ : Signature n) : ℕ := n

/-- Total dimension of the Clifford algebra (2^n) -/
def Signature.algebraDim (_ : Signature n) : ℕ := 2^n

/-- Number of basis blades of grade g -/
def Signature.gradeCount (_ : Signature n) (g : ℕ) : ℕ := gradesCount n g

/-! ## DiagonalForm - Non-Standard Metrics

For spaces where basis vectors don't square to ±1 or 0, but to arbitrary values.
Example: e₁² = 2, e₂² = -3, etc.

In Julia: `DiagonalForm{N,M,S,F,D,L}` where S indexes into a cache of diagonal values.
In Lean: We store the actual values directly in the structure.
-/

/-- A diagonal metric form where basis vectors can square to any Float value.
    `diag[i]` gives the value of e_i².
    This generalizes Signature which only allows ±1 and 0. -/
structure DiagonalForm (n : ℕ) where
  /-- The diagonal entries: diag[i] = e_i² -/
  diag : Fin n → Float

namespace DiagonalForm

/-- Create from a list of diagonal values -/
def ofList (vals : List Float) : DiagonalForm vals.length :=
  ⟨fun i => vals.get ⟨i.val, i.isLt⟩⟩

/-- Create a Euclidean DiagonalForm (all 1s) -/
def euclidean (n : ℕ) : DiagonalForm n := ⟨fun _ => 1.0⟩

/-- Create from a Signature (promote ±1/0 to floats) -/
def ofSignature (sig : Signature n) : DiagonalForm n :=
  ⟨fun i =>
    if sig.isDegenerate i then 0.0
    else if sig.isNegative i then -1.0 else 1.0⟩

/-- Number of positive-definite dimensions -/
def numPositive (d : DiagonalForm n) : ℕ :=
  (List.finRange n).countP fun i => d.diag i > 0

/-- Number of negative-definite dimensions -/
def numNegative (d : DiagonalForm n) : ℕ :=
  (List.finRange n).countP fun i => d.diag i < 0

/-- Number of degenerate (null) dimensions -/
def numDegenerate (d : DiagonalForm n) : ℕ :=
  (List.finRange n).countP fun i => d.diag i == 0

/-- Sign of e_i² (normalized to +1, -1, or 0) -/
def basisSign (d : DiagonalForm n) (i : Fin n) : Int :=
  let v := d.diag i
  if v > 0 then 1 else if v < 0 then -1 else 0

/-- Product of diagonal values for a blade (given as bitmask) -/
def bladeSquare (d : DiagonalForm n) (blade : BitVec n) : Float :=
  (List.finRange n).foldl (init := 1.0) fun acc (i : Fin n) =>
    if blade.getLsbD i.val then acc * d.diag i else acc

end DiagonalForm

/-- DiagonalForm also implements Manifold -/
instance (n : ℕ) : Manifold (DiagonalForm n) where
  dim := n
  basisSign := fun i => DiagonalForm.basisSign (DiagonalForm.euclidean n) i

/-! ## Conformal Geometry Support

For conformal geometric algebra, we need to track special null vectors:
- e∞ (point at infinity)
- e₀ (origin)

These are typically constructed from two extra dimensions e₊ and e₋.
-/

/-- Extended signature with conformal geometry markers -/
structure ConformalSignature (n : ℕ) extends Signature n where
  /-- Index of e₊ basis vector (positive extra dimension), if present -/
  ePlus : Option (Fin n) := none
  /-- Index of e₋ basis vector (negative extra dimension), if present -/
  eMinus : Option (Fin n) := none
  deriving Repr

namespace ConformalSignature

/-- Check if this is a conformal algebra (has both e₊ and e₋) -/
def hasConformal (cs : ConformalSignature n) : Bool :=
  cs.ePlus.isSome && cs.eMinus.isSome

/-- Check if it has the infinity point -/
def hasInf (cs : ConformalSignature n) : Bool := cs.hasConformal

/-- Check if it has the origin point -/
def hasOrigin (cs : ConformalSignature n) : Bool := cs.hasConformal

/-- Create CGA3 with explicit conformal markers -/
def cga3 : ConformalSignature 5 :=
  { toSignature := Signature.cl 4 1
    ePlus := some ⟨3, by omega⟩   -- e₄ (index 3) is e₊
    eMinus := some ⟨4, by omega⟩  -- e₅ (index 4) is e₋
  }

/-- Create a general conformal extension of Euclidean n-space: Cl(n+1, 1) -/
def conformal (euclideanDim : ℕ) : ConformalSignature (euclideanDim + 2) :=
  { toSignature := Signature.cl (euclideanDim + 1) 1
    ePlus := some ⟨euclideanDim, by omega⟩
    eMinus := some ⟨euclideanDim + 1, by omega⟩
  }

end ConformalSignature

/-! ## Projective Geometry Support -/

/-- Extended signature with projective geometry markers -/
structure ProjectiveSignature (n : ℕ) extends Signature n where
  /-- Index of the projective (degenerate) basis vector -/
  eProj : Option (Fin n) := none
  deriving Repr

namespace ProjectiveSignature

/-- Check if this is a projective algebra -/
def hasProjective (ps : ProjectiveSignature n) : Bool := ps.eProj.isSome

/-- Create PGA3 with explicit projective marker -/
def pga3 : ProjectiveSignature 4 :=
  { toSignature := Signature.clr 3 0 1
    eProj := some ⟨3, by omega⟩  -- e₄ (index 3) is the projective direction
  }

/-- Create a general projective extension of Euclidean n-space: Cl(n, 0, 1) -/
def projective (euclideanDim : ℕ) : ProjectiveSignature (euclideanDim + 1) :=
  { toSignature := Signature.clr euclideanDim 0 1
    eProj := some ⟨euclideanDim, by omega⟩
  }

end ProjectiveSignature

/-! ## Direct Sum of Signatures

The direct sum ⊕ combines two vector spaces into a larger one.
For signatures, this concatenates dimensions and metrics.

Examples:
- ℝ³ ⊕ ℝ¹ gives 4D Euclidean space
- ℝ' ⊕ ℝ³ gives Minkowski space (signature -+++)
- V ⊕ V' gives the "mother space" with dual
-/

namespace Signature

/-- Direct sum of two signatures: combines dimensions and concatenates metrics.
    The result has dimension n + m with the first n basis vectors from sig1
    and the next m basis vectors from sig2. -/
def directSum (sig1 : Signature n) (sig2 : Signature m) : Signature (n + m) :=
  -- Shift sig2's metrics to start after sig1's dimensions
  let metric1 := sig1.metric.zeroExtend (n + m)
  let metric2 := (sig2.metric.zeroExtend (n + m)).shiftLeft n
  let degen1 := sig1.degenerate.zeroExtend (n + m)
  let degen2 := (sig2.degenerate.zeroExtend (n + m)).shiftLeft n
  ⟨metric1 ||| metric2, degen1 ||| degen2⟩

/-- Infix notation for direct sum -/
scoped infixl:65 " ⊕ " => directSum

/-- Direct sum with power: V^n = V ⊕ V ⊕ ... ⊕ V (n times).
    Uses simple recursive definition. -/
def repeatSum (sig : Signature k) : (n : ℕ) → Signature (n * k)
  | 0 => ⟨0, 0⟩
  | n + 1 => by
    have h : (n + 1) * k = k + n * k := by
      simp only [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [h]
    exact sig.directSum (repeatSum sig n)

/-- Dual signature: flips all metric signs (but keeps degeneracy) -/
def dual (sig : Signature n) : Signature n :=
  -- XOR with all-ones flips the metric bits for non-degenerate bases
  let flipped := sig.metric ^^^ (~~~sig.degenerate)
  ⟨flipped, sig.degenerate⟩

/-- Notation for dual signature -/
scoped postfix:max "ᵈ" => dual

/-! ### Set Operations on Signatures

In DirectSum.jl, signatures support set operations:
- `∪` (union): combines compatible signatures
- `∩` (intersection): finds common subspace
- `⊆, ⊇` (subset): checks containment
-/

/-- Check if sig1 is a "subsignature" of sig2.
    True if every basis vector in sig1 has the same metric sign in sig2.
    Only makes sense for same-dimension signatures. -/
def isCompatible (sig1 sig2 : Signature n) : Bool :=
  sig1.metric == sig2.metric && sig1.degenerate == sig2.degenerate

/-- Subset relation: sig1 ⊆ sig2 if sig1's structure is preserved in sig2.
    For same-dimension signatures, this means identical metrics. -/
def subset (sig1 sig2 : Signature n) : Bool := isCompatible sig1 sig2

/-- Subset notation -/
scoped infix:50 " ⊆ₛ " => subset

/-- Superset notation -/
def superset (sig1 sig2 : Signature n) : Bool := subset sig2 sig1
scoped infix:50 " ⊇ₛ " => superset

/-- Union of signatures (same dimension): bitwise OR of metrics.
    Results in a signature where a basis is negative if negative in either input. -/
def union (sig1 sig2 : Signature n) : Signature n :=
  ⟨sig1.metric ||| sig2.metric, sig1.degenerate ||| sig2.degenerate⟩

/-- Union notation -/
scoped infix:60 " ∪ₛ " => union

/-- Intersection of signatures (same dimension): bitwise AND of metrics.
    Results in a signature where a basis is negative only if negative in both inputs. -/
def inter (sig1 sig2 : Signature n) : Signature n :=
  ⟨sig1.metric &&& sig2.metric, sig1.degenerate &&& sig2.degenerate⟩

/-- Intersection notation -/
scoped infix:60 " ∩ₛ " => inter

end Signature

/-! ## Grade Dimensions (gdims)

The number of basis blades at each grade.
gdims(n) = [C(n,0), C(n,1), ..., C(n,n)] = [1, n, n(n-1)/2, ...]

Total dimension of Cl(V) is 2^n = sum of gdims.
-/

/-- Number of basis blades of grade g in n-dimensional space: binomial(n, g) -/
def gdim (n g : ℕ) : ℕ := Nat.choose n g

/-- All grade dimensions as a list: [C(n,0), C(n,1), ..., C(n,n)] -/
def gdims (n : ℕ) : List ℕ := (List.range (n + 1)).map (Nat.choose n)

/-- Total dimension of Clifford algebra: 2^n (alias for Signature.algebraDim) -/
abbrev cliffordDim (n : ℕ) : ℕ := 2^n

/-- Helper to construct ℝⁿ with convenient exponentiation -/
def ℝ (n : ℕ) : Signature n := Signature.euclidean n

/-! ## SubManifold - Subspaces of a Signature

A SubManifold tracks a subset of basis vectors from a parent signature.
Useful for working with subspaces and for basis blade indexing.
-/

/-- A submanifold is a selection of basis vectors from a parent signature.
    The `mask` indicates which basis vectors are included. -/
structure SubManifold (sig : Signature n) where
  /-- Bitmask indicating which basis vectors are in this submanifold -/
  mask : BitVec n
  deriving DecidableEq, Repr

namespace SubManifold

variable {n : ℕ} {sig : Signature n}

/-- The full manifold (all basis vectors) -/
def full : SubManifold sig := ⟨pseudoscalar⟩

/-- Empty submanifold (no basis vectors) -/
def empty : SubManifold sig := ⟨0⟩

/-- Dimension (number of basis vectors) of the submanifold -/
def dim (sub : SubManifold sig) : ℕ := grade sub.mask

/-- Create from a list of basis indices -/
def ofIndices (indices : List (Fin n)) : SubManifold sig :=
  ⟨indices.foldl (init := (0 : BitVec n)) fun acc i =>
    acc ||| (1 <<< i.val)⟩

/-- Get the indices of basis vectors in this submanifold -/
def toIndices (sub : SubManifold sig) : List (Fin n) :=
  (List.finRange n).filter fun i => sub.mask.getLsbD i.val

/-- Get the metric signs for basis vectors in this submanifold as a list -/
def metricSigns (sub : SubManifold sig) : List Bool :=
  sub.toIndices.map fun i => sig.metric.getLsbD i.val

/-- Check if basis vector i is in this submanifold -/
def contains (sub : SubManifold sig) (i : Fin n) : Bool := sub.mask.getLsbD i.val

/-- Union of submanifolds -/
def union (a b : SubManifold sig) : SubManifold sig := ⟨a.mask ||| b.mask⟩

/-- Intersection of submanifolds -/
def inter (a b : SubManifold sig) : SubManifold sig := ⟨a.mask &&& b.mask⟩

/-- Subset relation -/
def subset (a b : SubManifold sig) : Bool := (a.mask &&& b.mask) == a.mask

instance : Union (SubManifold sig) := ⟨union⟩
instance : Inter (SubManifold sig) := ⟨inter⟩

end SubManifold

/-! ## Lowerbits and Expandbits

Note: `lowerbits` and `expandbits` are defined in BitMask.lean.
These are key helpers from Leibniz.jl for efficient basis indexing:
- lowerbits: Convert full-space blade indices to submanifold-local indices
- expandbits: Convert submanifold-local indices back to full-space indices
-/

/-! ## Tests -/

#eval R3.dim  -- 3
#eval R3.numPositive  -- 3
#eval R3.numNegative  -- 0
#eval STA.numPositive  -- 1
#eval STA.numNegative  -- 3
#eval Signature.cl 3 2 |>.numPositive  -- 3
#eval Signature.cl 3 2 |>.numNegative  -- 2

-- DiagonalForm tests
#eval! DiagonalForm.euclidean 3 |>.numPositive  -- 3
#eval! DiagonalForm.ofSignature STA |>.numNegative  -- 3

-- ConformalSignature tests
#eval ConformalSignature.cga3.hasConformal  -- true
#eval ConformalSignature.cga3.hasInf  -- true

-- ProjectiveSignature tests
#eval ProjectiveSignature.pga3.hasProjective  -- true

-- Direct sum tests
open Signature in
#eval (R2 ⊕ R1).dim  -- 3

open Signature in
#eval (R3 ⊕ R1).numPositive  -- 4

-- ℝᵈ ⊕ ℝ³ should give Minkowski-like signature (one negative, three positive)
open Signature in
#eval let mink := R1ᵈ ⊕ R3
      (mink.numPositive, mink.numNegative)  -- (3, 1)

-- Direct sum of Cl(0,1) and Cl(2,0) gives Cl(2,1)
open Signature in
#eval let c01 := Signature.cl 0 1  -- one negative
      let c20 := Signature.cl 2 0  -- two positive
      let sum := c01 ⊕ c20
      (sum.numPositive, sum.numNegative)  -- (2, 1)

-- Dual flips signs
open Signature in
#eval R3ᵈ.numNegative  -- 3 (all become negative)

-- RepeatSum creates repeated direct sums: ℝ² repeated 3 times = ℝ⁶
open Signature in
#eval! (Signature.repeatSum R2 3).dim  -- 6

-- Set operations on signatures
open Signature in
#eval (R3 ∪ₛ R3).numPositive  -- 3 (union of identical)

open Signature in
#eval (R3 ∩ₛ R3).numPositive  -- 3 (intersection of identical)

open Signature in
#eval R3 ⊆ₛ R3  -- true (reflexive)

-- gdims tests
#eval gdims 3  -- [1, 3, 3, 1] (Pascal's row)
#eval gdims 4  -- [1, 4, 6, 4, 1]
#eval gdim 4 2  -- 6 (number of bivectors in 4D)
#eval cliffordDim 3  -- 8 (2³)

-- SubManifold tests
#eval SubManifold.full (sig := R3) |>.dim  -- 3
#eval SubManifold.empty (sig := R3) |>.dim  -- 0
#eval SubManifold.ofIndices (sig := R3) [⟨0, by omega⟩, ⟨2, by omega⟩] |>.dim  -- 2

end Grassmann

/-
  Grassmann/Parity.lean - Sign computation for Clifford algebra products

  Port of Grassmann.jl's parity.jl.

  The key insight: When computing the geometric product of two basis blades,
  we need to track the sign from two sources:
  1. **Permutation sign (Koszul sign)**: From reordering basis vectors to canonical form
  2. **Metric sign**: From basis vectors that square to -1

  The `parityjoin` function computes this efficiently using bit manipulation.

  Algorithm explanation:
  Given blades a and b (as bitmasks), to compute the sign of a ∧ b or a · b:
  - Count how many basis vectors in `a` need to pass through basis vectors in `b`
  - Each transposition contributes a factor of -1
  - Additionally, for shared basis vectors (in a·b), check if they square to -1

  ## Performance Notes

  Hot path analysis:
  - `geometricSign` is called O(4^n) times per geometric product
  - `countTranspositions` is the inner loop - uses optimized bit-only version

  Optimization opportunities:
  1. **Precomputed sign tables**: Use `MetalCodegen.computeSignTable` at compile
     time for fixed signatures (R3, PGA3, CGA3). Trade O(4^n) memory for O(1) lookup.
  2. **SIMD/parallel**: The 4^n sign computations are independent
  3. **Sparse shortcuts**: Skip zero coefficients before computing signs
-/
import Grassmann.Blade

namespace Grassmann

/-! ## Bit Extraction Helpers -/

/-- Extract bit i from a natural number as 0 or 1 -/
def bitAt (n : ℕ) (i : ℕ) : ℕ := if n &&& (1 <<< i) != 0 then 1 else 0

/-- Extract bits of a natural number as a list (LSB first) up to position k -/
def bitsToList (n : ℕ) (k : ℕ) : List ℕ :=
  List.range k |>.map (bitAt n)

/-- Cumulative sum of a list -/
def cumsum : List ℕ → List ℕ
  | [] => []
  | x :: xs => scanl (· + ·) x xs
where
  scanl (f : ℕ → ℕ → ℕ) (acc : ℕ) : List ℕ → List ℕ
    | [] => [acc]
    | x :: xs => acc :: scanl f (f acc x) xs

/-- Dot product of two lists (padded with zeros if different lengths) -/
def dotProduct (xs ys : List ℕ) : ℕ :=
  List.zipWith (· * ·) xs ys |>.foldl (· + ·) 0

/-! ## Parity Join - The Core Algorithm

This is the heart of the sign computation.
Given two blade bitmasks a and b, compute whether their product has a sign flip.

The idea: To bring e_i from a past all basis vectors in b that come after i,
we count how many transpositions are needed.
-/

/-- Count the number of transpositions needed to merge two sorted basis sets.
    This is the Koszul sign exponent.

    Algorithm: For each bit in `a`, count how many bits in `b` are in positions
    that would require passing through.

    Original list-based version (for reference):
    ```
    let aBits := bitsToList a dim
    let bBitsShifted := bitsToList (b <<< 1) dim
    let bCumsum := cumsum bBitsShifted
    dotProduct aBits bCumsum
    ``` -/
@[specialize]
def countTranspositions (a b : ℕ) (dim : ℕ) : ℕ :=
  -- Optimized bit-only version: no list allocations
  -- For each bit position i in a, count bits in b at positions < i
  let rec loop (i : ℕ) (bBelow : ℕ) (acc : ℕ) : ℕ :=
    if i >= dim then acc
    else
      -- bBelow tracks cumulative popcount of b at positions < i
      let aBit := if a &&& (1 <<< i) != 0 then 1 else 0
      let contribution := aBit * bBelow
      let bBit := if b &&& (1 <<< i) != 0 then 1 else 0
      loop (i + 1) (bBelow + bBit) (acc + contribution)
  termination_by dim - i
  loop 0 0 0

/-- Parity join without metric: returns true if sign flip needed.
    This handles just the permutation sign. -/
@[specialize]
def parityJoinBasic (a b : ℕ) (dim : ℕ) : Bool :=
  (countTranspositions a b dim) % 2 == 1

/-- Parity join with metric: includes both permutation and metric signs.
    `metric` is the bitmask of basis vectors that square to -1.

    For the geometric product, shared basis vectors (in both a and b)
    that square to -1 contribute additional sign flips. -/
@[specialize]
def parityJoin (a b : ℕ) (dim : ℕ) (metric : ℕ) : Bool :=
  let permutationSign := countTranspositions a b dim
  let sharedNegative := popcount ((a &&& b) &&& metric)
  (permutationSign + sharedNegative) % 2 == 1

/-- Check if shared basis vectors include any degenerate (null) dimensions.
    If so, the geometric product is zero. -/
@[specialize]
def hasSharedDegenerate (a b : ℕ) (degenerate : ℕ) : Bool :=
  ((a &&& b) &&& degenerate) != 0

/-- Parity join with full signature (metric + degenerate).
    Returns `none` if the result is zero (shared degenerate basis vector).
    Returns `some true` for sign flip, `some false` for no flip. -/
@[specialize]
def parityJoinFull (a b : ℕ) (dim : ℕ) (metric degenerate : ℕ) : Option Bool :=
  if hasSharedDegenerate a b degenerate then
    none  -- Result is zero
  else
    some (parityJoin a b dim metric)

/-! ## Sign Computations for Blades -/

/-- Sign when multiplying blade a by blade b (geometric product).
    Returns 1, -1, or 0 (when shared degenerate basis vectors cause cancellation). -/
@[specialize]
def geometricSign (sig : Signature n) (a b : Blade sig) : Int :=
  -- Check for shared degenerate basis vectors (result is zero)
  if hasSharedDegenerate a.bits.toNat b.bits.toNat sig.degenerate.toNat then 0
  else if parityJoin a.bits.toNat b.bits.toNat n sig.metric.toNat then -1 else 1

/-! ## Precomputed Sign Tables

For small dimensions (n ≤ 5), we precompute the full sign table once and use
O(1) lookups instead of O(n) computation per sign. The table has 4^n entries
(2^n × 2^n), so memory is:
- n=3: 64 entries (512 bytes as Int8)
- n=4: 256 entries (2KB)
- n=5: 1024 entries (8KB)
-/

/-- Precomputed sign table for a signature. Stores signs as Int8 (-1, 0, 1).
    Table layout: signs[i * size + j] = geometricSign(blade_i, blade_j) -/
structure SignTable (n : ℕ) where
  signs : Array Int8
  size : Nat := 2^n
  deriving Repr

/-- Build precomputed sign table for a signature -/
def buildSignTable (sig : Signature n) : SignTable n :=
  let size := 2^n
  let signs := Array.ofFn (n := size * size) fun idx =>
    let i := idx / size
    let j := idx % size
    let bi : Blade sig := ⟨BitVec.ofNat n i⟩
    let bj : Blade sig := ⟨BitVec.ofNat n j⟩
    let s := geometricSign sig bi bj
    if s < 0 then (-1 : Int8) else if s > 0 then (1 : Int8) else (0 : Int8)
  { signs, size }

/-- Look up precomputed sign -/
@[inline]
def SignTable.lookup (table : SignTable n) (i j : Nat) : Int8 :=
  table.signs.getD (i * table.size + j) 0

/-- Geometric product using precomputed sign table (for n ≤ 5) -/
def geometricSignFromTable (table : SignTable n) (i j : Nat) : Int :=
  let s := table.lookup i j
  if s < 0 then -1 else if s > 0 then 1 else 0

/-- Sign for wedge product (exterior product).
    Zero if blades share any basis vectors. -/
@[specialize]
def wedgeSign (sig : Signature n) (a b : Blade sig) : Int :=
  if (a.bits &&& b.bits) != 0 then 0
  else if parityJoinBasic a.bits.toNat b.bits.toNat n then -1 else 1

/-- Sign for dot product (inner/scalar product).
    Only non-zero if one blade is contained in the other. -/
def dotSign (sig : Signature n) (a b : Blade sig) : Int :=
  -- For dot product, result grade is |grade(a) - grade(b)|
  -- Non-zero only when grades differ appropriately
  if a.grade ≤ b.grade then
    if (a.bits &&& b.bits) == a.bits then
      geometricSign sig a b
    else 0
  else
    if (a.bits &&& b.bits) == b.bits then
      geometricSign sig a b
    else 0

/-! ## Reverse and Involute Parities -/

/-- Sign of reverse operation on a k-blade: (-1)^(k(k-1)/2) -/
def reverseSign (k : ℕ) : Int :=
  if (k * (k - 1) / 2) % 2 == 0 then 1 else -1

/-- Sign of grade involute on a k-blade: (-1)^k -/
def involuteSign (k : ℕ) : Int :=
  if k % 2 == 0 then 1 else -1

/-- Sign of Clifford conjugate on a k-blade: (-1)^(k(k+1)/2) -/
def conjugateSign (k : ℕ) : Int :=
  if (k * (k + 1) / 2) % 2 == 0 then 1 else -1

/-! ## Complement (Hodge Star) -/

/-- The complement blade (XOR with pseudoscalar).
    This is related to the Hodge star operator. -/
def complementBits (bits : ℕ) (dim : ℕ) : ℕ :=
  bits ^^^ ((1 <<< dim) - 1)

/-- Sign for left complement: ⋆a = sign · a ∧ ⋆a = I -/
def leftComplementSign (sig : Signature n) (a : Blade sig) : Int :=
  let complement := ⟨a.bits ^^^ pseudoscalar⟩
  wedgeSign sig a complement

/-- Sign for right complement: a ∧ ⋆a = sign · I -/
def rightComplementSign (sig : Signature n) (a : Blade sig) : Int :=
  let complement := ⟨a.bits ^^^ pseudoscalar⟩
  wedgeSign sig complement a

/-! ## Tests -/

-- Test transposition counting
#eval countTranspositions 0b01 0b10 2  -- e1 past e2: 1 transposition
#eval countTranspositions 0b10 0b01 2  -- e2 past e1: 0 transpositions
#eval countTranspositions 0b001 0b110 3  -- e1 past e2,e3: 2 transpositions

-- Test parity join (permutation sign only)
#eval parityJoinBasic 0b01 0b10 2  -- e1 ∧ e2 = e12, no flip
#eval parityJoinBasic 0b10 0b01 2  -- e2 ∧ e1 = -e12, flip!

-- Test geometric sign in Euclidean space
#eval geometricSign R3 (e1 : Blade R3) (e1 : Blade R3)  -- e1·e1 = 1
#eval geometricSign R3 (e1 : Blade R3) (e2 : Blade R3)  -- e1·e2 = e12, sign +1
#eval geometricSign R3 (e2 : Blade R3) (e1 : Blade R3)  -- e2·e1 = -e12, sign -1
#eval geometricSign R3 (e12 : Blade R3) (e12 : Blade R3)  -- e12·e12 = -1

-- Test in Minkowski space (first basis squares to -1)
#eval geometricSign STA (e1 : Blade STA) (e1 : Blade STA)  -- e1·e1 = -1

-- Reverse signs by grade
#eval reverseSign 0  -- 1
#eval reverseSign 1  -- 1
#eval reverseSign 2  -- -1
#eval reverseSign 3  -- -1
#eval reverseSign 4  -- 1

end Grassmann

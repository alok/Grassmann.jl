/-
  Grassmann/BitMask.lean - BitVec utilities for basis blade indexing

  Port of Leibniz.jl/src/utilities.jl bit manipulation functions.
  Key insight: Use dependent types (BitVec n) to encode dimension at type level,
  eliminating runtime dimension checks from the Julia code.

  DESIGN: All definitions are COMPUTABLE. We use:
  - Fin n for bounded indices (computable)
  - Direct recursion for counting/enumeration
  - Avoid Finset.toList which is noncomputable

  In Grassmann.jl, basis blades are represented as bitmasks where bit i is set
  if basis vector e_i is present. For example in ℝ³:
    e₁ = 0b001, e₂ = 0b010, e₃ = 0b100
    e₁₂ = 0b011, e₁₃ = 0b101, e₂₃ = 0b110
    e₁₂₃ = 0b111
-/
import Mathlib.Data.Nat.Choose.Basic
-- import Mathlib.Data.Fin.Basic  -- WORKAROUND: This causes runtime panic in v4.26.0-rc2
-- Fin is available in Init.Data.Fin (prelude)

namespace Grassmann

/-! ## Popcount - Count set bits

Simple recursive implementation. There's a PR in lean4 repo for this,
but we define it here for now to ensure computability.
-/

/-- Count set bits in a natural number (popcount/Hamming weight) -/
def popcount : ℕ → ℕ
  | 0 => 0
  | n + 1 => (if (n + 1) % 2 = 1 then 1 else 0) + popcount ((n + 1) / 2)

/-! ## Basic BitVec Operations -/

/-- Grade of a blade = number of set bits -/
def grade (b : BitVec n) : ℕ := popcount b.toNat

/-- A blade bitmask where the i-th basis vector is set. -/
def singleBit (i : Fin n) : BitVec n := BitVec.ofNat n (1 <<< i.val)

/-- The zero blade (scalar). -/
def zeroBlade : BitVec n := 0

/-- The pseudoscalar blade (all bits set). -/
def pseudoscalar : BitVec n := BitVec.ofNat n ((1 <<< n) - 1)

/-- Check if bit i is set -/
def testBit (b : BitVec n) (i : ℕ) : Bool := b.getLsbD i

/-- Set bit i -/
def setBit (b : BitVec n) (i : Fin n) : BitVec n :=
  b ||| singleBit i

/-- Clear bit i -/
def clearBit (b : BitVec n) (i : Fin n) : BitVec n :=
  b &&& ~~~(singleBit i)

/-- Toggle bit i -/
def toggleBit (b : BitVec n) (i : Fin n) : BitVec n :=
  b ^^^ singleBit i

/-! ## Extract indices of set bits

Returns a list of indices where bits are set, in ascending order.
This is computable and replaces the noncomputable Finset-based version.
-/

/-- Helper: collect set bit indices from position k downward -/
def indicesAux (b : BitVec n) : (k : ℕ) → List (Fin n)
  | 0 => []
  | k + 1 =>
    let rest := indicesAux b k
    if h : k < n then
      if b.getLsbD k then ⟨k, h⟩ :: rest else rest
    else rest

/-- Get list of set bit positions in ascending order -/
def indices (b : BitVec n) : List (Fin n) := (indicesAux b n).reverse

/-- Convert list of indices to bitmask -/
def fromIndices (idxs : List (Fin n)) : BitVec n :=
  idxs.foldl (fun acc i => acc ||| singleBit i) 0

/-! ## Binomial Cumulative Sums

The blade indexing scheme groups blades by grade:
  - Grade 0: 1 scalar (index 0)
  - Grade 1: n vectors (indices 1 to n)
  - Grade 2: C(n,2) bivectors
  - ...
  - Grade n: 1 pseudoscalar

`binomsum n g` gives the starting index for grade-g blades.
-/

/-- Sum of C(n,k) for k in 0..g-1 -/
def binomsum (n g : ℕ) : ℕ :=
  match g with
  | 0 => 0
  | g + 1 => binomsum n g + Nat.choose n g

/-- `binomsum n 0 = 0` -/
@[simp]
theorem binomsum_zero (n : ℕ) : binomsum n 0 = 0 := rfl

/-- `binomsum n 1 = 1` (the scalar takes index 0) -/
@[simp]
theorem binomsum_one (n : ℕ) : binomsum n 1 = 1 := by simp [binomsum]

/-! ## Combinatorial enumeration

To index blades within a grade, we enumerate all g-element subsets of {0,...,n-1}
in lexicographic order. The position of a blade in this list is its "blade index".
-/

/-- Generate all ways to choose g elements from {0,...,n-1} as bitmasks.
    Returns list of BitVec n, each with exactly g bits set, in lex order. -/
partial def combinations (n g : ℕ) : List (BitVec n) :=
  if g = 0 then [0]
  else if g > n then []
  else
    -- Start with combinations that include bit (n-1), then those that don't
    let withLast := (combinations (n - 1) (g - 1)).map fun b =>
      (b.zeroExtend n) ||| (BitVec.ofNat n (1 <<< (n - 1)))
    let withoutLast := (combinations (n - 1) g).map (·.zeroExtend n)
    withoutLast ++ withLast

/-- Find index of a bitmask in the list of g-combinations.
    Returns 0 if not found (shouldn't happen for valid inputs). -/
def bladeIndexWithinGrade (b : BitVec n) : ℕ :=
  let g := grade b
  let combos := combinations n g
  combos.findIdx? (· == b) |>.getD 0

/-- The full basis index: offset for grade + index within grade.
    Maps a bitmask to its position in a flat array of all 2^n blades. -/
def basisIndex (b : BitVec n) : ℕ :=
  let g := grade b
  binomsum n g + bladeIndexWithinGrade b

/-- Get the bitmask for the k-th blade of grade g in dimension n. -/
def indexToBlade (n g k : ℕ) : BitVec n :=
  (combinations n g).getD k 0

/-! ## Combinatorial Helpers -/

/-- Number of blades of grade g in dimension n -/
abbrev gradesCount (n g : ℕ) : ℕ := Nat.choose n g

/-- Total dimension of the algebra (2^n) -/
abbrev algebraDim (n : ℕ) : ℕ := 2^n

/-- Even subalgebra dimension (2^(n-1) for n > 0) -/
def evenDim (n : ℕ) : ℕ := if n = 0 then 1 else 2^(n-1)

/-- Odd elements dimension (2^(n-1) for n > 0) -/
def oddDim (n : ℕ) : ℕ := if n = 0 then 0 else 2^(n-1)

/-! ## Lowerbits and Expandbits

These operations are crucial for computing products between SubManifolds.
Given a submanifold with basis indices S ⊆ {0..n-1}, we need to:
- `lowerbits`: Project a blade's bits to the submanifold's local indexing
- `expandbits`: Embed a local blade into the full space

Example: If n=4 and subspaceMask = 0b0101 (subspace spanned by e₀, e₂):
  lowerbits 0b0101 0b0101 = 0b11 (both e₀ and e₂ present → local e₀ and e₁)
  lowerbits 0b0001 0b0101 = 0b01 (only e₀ present → local e₀)
-/

/-- Project full-space bits to subspace local indexing.
    For each set bit in subspaceMask (in order), check if it's set in fullBits,
    and pack those results into a smaller bitvector. -/
def lowerbitsNat (fullBits subspaceMask : ℕ) : ℕ :=
  let rec go (mask : ℕ) (full : ℕ) (pos : ℕ) (result : ℕ) : ℕ :=
    if mask = 0 then result
    else
      let newResult := if mask % 2 = 1 && full % 2 = 1
                       then result ||| (1 <<< pos)
                       else result
      let newPos := if mask % 2 = 1 then pos + 1 else pos
      go (mask / 2) (full / 2) newPos newResult
  go subspaceMask fullBits 0 0

/-- Expand local subspace bits to full space.
    For each set bit in localBits, map it to the corresponding position in subspaceMask. -/
def expandbitsNat (localBits subspaceMask : ℕ) : ℕ :=
  let rec go (mask : ℕ) (local_ : ℕ) (fullPos : ℕ) (result : ℕ) : ℕ :=
    if mask = 0 then result
    else
      let newResult := if mask % 2 = 1 && local_ % 2 = 1
                       then result ||| (1 <<< fullPos)
                       else result
      let newLocal := if mask % 2 = 1 then local_ / 2 else local_
      go (mask / 2) newLocal (fullPos + 1) newResult
  go subspaceMask localBits 0 0

/-- Type-safe lowerbits with dependent return type -/
def lowerbits (fullBits subspaceMask : BitVec n) : BitVec (grade subspaceMask) :=
  BitVec.ofNat _ (lowerbitsNat fullBits.toNat subspaceMask.toNat)

/-- Type-safe expandbits -/
def expandbits (localBits : BitVec m) (subspaceMask : BitVec n) : BitVec n :=
  BitVec.ofNat n (expandbitsNat localBits.toNat subspaceMask.toNat)

/-! ## Basic tests (via #eval) -/

#eval grade (0b101 : BitVec 4)  -- Should be 2
#eval grade (0b111 : BitVec 4)  -- Should be 3
#eval indices (0b1010 : BitVec 4)  -- Should be [1, 3]
#eval combinations 3 2  -- Should be [0b011, 0b101, 0b110]
#eval binomsum 4 2  -- Should be 1 + 4 = 5
#eval lowerbitsNat 0b0101 0b0101  -- Should be 0b11
#eval expandbitsNat 0b11 0b0101  -- Should be 0b0101

end Grassmann

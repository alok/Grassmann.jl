/-
Combinatorics of the Grassmann basis, ported from Leibniz.jl `src/utilities.jl`.

The `2ⁿ` basis blades of `Λ(V)` are stored **grade-major**, and within a grade
in **lexicographic order of the ascending index list** (Combinatorics.jl
`combinations(1:n,g)` order). For `n = 4`:

```
position: 1  2  3  4  5  6   7   8   9   10  11  12   13   14   15   16
blade:    1  e1 e2 e3 e4 e12 e13 e14 e23 e24 e34 e123 e124 e134 e234 e1234
mask:     0  1  2  4  8  3   5   9   6   10  12  7    11   13   14   15
```

This is *not* numeric (colex) order within a grade.

Two layers:

* **Specification** (`binomial`, `binomsum`, `combos`, `bladeRank`, `unrank`, …):
  structural recursion only, so the kernel evaluates them and `decide` proves
  the bijections for small `n` (bottom of this file).
* **Runtime**: `choose` reads a 65×65 Pascal table, and the per-`n` index
  tables for `n ≤ 12` (Julia `cache_limit`) are memoized closed terms
  (`Thunk`s built on first use). Functions whose runtime implementation reads
  a table carry `@[implemented_by]`; the table is filled by calling the very
  specification function it replaces, and `Tests/DirectSum` checks the two
  agree exhaustively for `n ≤ 16`.

Julia returns 1-based positions (`bladeindex`, `basisindex`, …); we keep those
names with Julia semantics and add 0-based `…Rank` variants for storage.
-/
import DirectSum.Bits

namespace Leibniz

open DirectSum.Bits

/-! ## Binomial coefficients -/

/-- Binomial coefficient `C(n,k)`, multiplicative and structural in `k`
(kernel-reducible): `C(n,k+1) = C(n,k)·(n-k)/(k+1)`, exact at every step.
`binomial n k = 0` for `k > n`. (Julia `Base.binomial`, used by Leibniz
`gdims`/`binomsum`.) -/
def binomial (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => binomial n k * (n - k) / (k + 1)

theorem binomial_zero (n : Nat) : binomial n 0 = 1 := rfl

theorem binomial_eq_zero_of_lt {n : Nat} : ∀ {k : Nat}, n < k → binomial n k = 0
  | 0, h => absurd h (Nat.not_lt_zero _)
  | k + 1, h => by
    unfold binomial
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · rw [binomial_eq_zero_of_lt h']; simp
    · subst h'; simp

/-- Pascal table `binomTable[n*65+k] = C(n,k)` for `n, k ≤ 64` (entries with
`k > n` are 0). `C(64,32) < 2^63`, so every entry is an unboxed scalar. -/
def binomTable : Array Nat := Id.run do
  let mut t := Array.replicate (65 * 65) 0
  for n in [0:65] do
    t := t.set! (n * 65) 1
    for k in [1:n + 1] do
      t := t.set! (n * 65 + k) (t[(n - 1) * 65 + k - 1]! + t[(n - 1) * 65 + k]!)
  return t

/-- Runtime implementation of `choose`: table lookup for `n, k ≤ 64`. -/
def chooseImpl (n k : Nat) : Nat :=
  if n ≤ 64 && k ≤ 64 then binomTable[n * 65 + k]! else binomial n k

/-- `C(n,k)` for use in code: logically `binomial`, at runtime an O(1) table read. -/
@[implemented_by chooseImpl]
def choose (n k : Nat) : Nat := binomial n k

/-- Julia `gdims(n,g) = binomial(n,g)` (AbstractTensors). -/
@[inline] def gdims (n g : Nat) : Nat := choose n g

/-- Julia `gdimsall(n)`: `[C(n,0), …, C(n,n)]`. -/
def gdimsall (n : Nat) : Array Nat := (List.range (n + 1)).toArray.map (choose n)

/-! ## Grade offsets -/

/-- Julia `binomsum(n,i) = Σ_{q<i} C(n,q)`: 0-based start of grade `i` in the
multivector layout (`Leibniz.jl src/utilities.jl:135,147`). -/
def binomsum (n : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => binomsum n i + choose n i

/-- Julia `spinsum(n,i) = Σ_{q<i, q even} C(n,q)`: start of grade `i` in the
even (spinor) layout. -/
def spinsum (n : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => spinsum n i + (if i % 2 == 0 then choose n i else 0)

/-- Julia `antisum(n,i) = Σ_{q<i, q odd} C(n,q)`: start of grade `i` in the odd
(co-spinor) layout. -/
def antisum (n : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => antisum n i + (if i % 2 == 1 then choose n i else 0)

/-- Julia `binomcumsum(n) = [binomsum(n,0), …, binomsum(n,n+1)]` (length `n+2`).
Julia's cache returns wrong rows for `n ∈ {0,1}` (Leibniz quirk Q2); this is
the correct formula. -/
def binomcumsum (n : Nat) : Array Nat := (List.range (n + 2)).toArray.map (binomsum n)

/-- Julia `spincumsum(n)` (correct for every `n`, see `binomcumsum`). -/
def spincumsum (n : Nat) : Array Nat := (List.range (n + 2)).toArray.map (spinsum n)

/-- Julia `anticumsum(n)` (correct for every `n`, see `binomcumsum`). -/
def anticumsum (n : Nat) : Array Nat := (List.range (n + 2)).toArray.map (antisum n)

/-! ## Lexicographic combinations -/

/-- The `g`-subsets of the `m` generators at 0-based bit positions
`lo, lo+1, …, lo+m-1`, as `Nat` masks, in lexicographic order of their
ascending index lists: every subset containing `lo` comes first. -/
def combos : (m g lo : Nat) → List Nat
  | _, 0, _ => [0]
  | 0, _ + 1, _ => []
  | m + 1, g + 1, lo => (combos m g (lo + 1)).map (· + 2 ^ lo) ++ combos m (g + 1) (lo + 1)

/-- Specification of Julia `indexbasis(n,g)` as a list of `Nat` masks. -/
def indexBasisSpec (n g : Nat) : List Nat := combos n g 0

/-- Julia `combo(n,g)`: the lex-ordered `g`-subsets of `1..n` as index arrays
(`Leibniz.jl src/utilities.jl:114`). -/
def combo (n g : Nat) : Array (Array Nat) :=
  (indexBasisSpec n g).toArray.map fun b => (indicesList b.toUInt64).toArray

/-! ## Rank and unrank (closed forms) -/

/-- 0-based lexicographic rank of blade `b` among the grade-`popcount b` blades of
`n` generators (the combinatorial number system; O(popcount) with table reads):

`rank = C(n,k) - 1 - Σᵢ C(n - cᵢ, k - i + 1)` for ascending 1-based indices `cᵢ`.

Equals Julia `bladeindex(n,b) - 1` (`Leibniz.jl src/utilities.jl:181-184`). -/
def bladeRankCF (n : Nat) (b : UInt64) : Nat :=
  let k := popcount b
  go k b 1 (choose n k - 1) 64
where
  /-- Consume the set bits of `x` in ascending order; `i` is the 1-based rank of
  the next one among the bits of `b`. -/
  go (k : Nat) (x : UInt64) (i r : Nat) : Nat → Nat
    | 0 => r
    | fuel + 1 => if x == 0 then r else
        go k (x &&& (x - 1)) (i + 1) (r - choose (n - (ctz x + 1)) (k - i + 1)) fuel

/-- Inverse of `bladeRankCF`: the `r`-th (0-based) grade-`g` blade of `n`
generators in lex order (greedy walk of the combinatorial number system). -/
def unrank (n g r : Nat) : UInt64 := go 1 g r 0 n
where
  /-- At 1-based position `x` with `rem` generators still to choose. -/
  go (x rem r : Nat) (mask : UInt64) : Nat → UInt64
    | 0 => mask
    | fuel + 1 => if rem = 0 then mask else
        let c := choose (n - x) (rem - 1)
        if r < c then go (x + 1) (rem - 1) r (mask ||| bit x) fuel
        else go (x + 1) rem (r - c) mask fuel

/-! ## Memoized per-`n` tables (`n ≤ 12`) -/

/-- Julia `cache_limit`: index tables are precomputed for `n ≤ 12`. -/
def tableLimit : Nat := 12

/-- Every index table for one dimension `n`. All positions are 0-based. -/
structure IndexTables where
  /-- Multivector layout: position ↦ mask (Julia `indexbasis(n)`), size `2ⁿ`. -/
  basis : Array UInt64
  /-- Mask ↦ lex rank within its grade (Julia `bladeindex - 1`), size `2ⁿ`. -/
  rank : Array Nat
  /-- Grade offsets `binomcumsum n`. -/
  offsets : Array Nat
  /-- Mask ↦ position in the multivector layout (Julia `basisindex - 1`), size `2ⁿ`. -/
  pos : Array Nat
  /-- Even-grade offsets `spincumsum n`. -/
  spinOffsets : Array Nat
  /-- Odd-grade offsets `anticumsum n`. -/
  antiOffsets : Array Nat
  /-- Even-grade (spinor) layout: position ↦ mask, size `2ⁿ⁻¹` (1 if `n = 0`). -/
  even : Array UInt64
  /-- Odd-grade layout: position ↦ mask, size `2ⁿ⁻¹` (0 if `n = 0`). -/
  odd : Array UInt64
  deriving Inhabited

/-- Build the tables for dimension `n` from the specification functions. -/
def IndexTables.build (n : Nat) : IndexTables :=
  let grades := (List.range (n + 1)).map fun g => (indexBasisSpec n g).map (·.toUInt64)
  let evens := (List.range (n + 1)).filter (· % 2 == 0) |>.flatMap fun g => grades[g]!
  let odds := (List.range (n + 1)).filter (· % 2 == 1) |>.flatMap fun g => grades[g]!
  let rank := (List.range (2 ^ n)).toArray.map fun b => bladeRankCF n b.toUInt64
  let offsets := binomcumsum n
  { basis := grades.flatten.toArray
    rank
    offsets
    pos := (List.range (2 ^ n)).toArray.map fun b =>
      offsets[popcount b.toUInt64]! + rank[b]!
    spinOffsets := spincumsum n
    antiOffsets := anticumsum n
    even := evens.toArray
    odd := odds.toArray }

/-- Memoized tables for `n ≤ tableLimit`: an array of `Thunk`s, each forced (and
then cached by the runtime) on first use. -/
def tables : Array (Thunk IndexTables) :=
  (List.range (tableLimit + 1)).toArray.map fun n => Thunk.mk fun _ => IndexTables.build n

/-- The tables for `n ≤ tableLimit` (forces the thunk). -/
@[inline] def table (n : Nat) : IndexTables := (tables[n]?.getD default).get

/-! ## Julia index functions -/

/-- The table entry `a[i]`, `0` out of range (inline read, no panic path). -/
@[inline] private def natAt (a : Array Nat) (i : Nat) : Nat := if h : i < a.size then a[i] else 0

/-- Whether the tables of dimension `n` cover mask `b` (`n ≤ 12` and `b < 2ⁿ`); a shift, not
`2 ^ n` (which is a GMP call on `Nat`). -/
@[inline] private def tabled (n : Nat) (b : UInt64) : Bool := n ≤ tableLimit && b >>> n.toUInt64 == 0

/-- Runtime implementation of `bladeRank`: one table read for `n ≤ 12`. -/
def bladeRankImpl (n : Nat) (b : UInt64) : Nat :=
  if tabled n b then natAt (table n).rank b.toNat else bladeRankCF n b

/-- 0-based lex rank of `b` within its grade (Julia `bladeindex(n,b) - 1`). -/
@[implemented_by bladeRankImpl]
def bladeRank (n : Nat) (b : UInt64) : Nat := bladeRankCF n b

/-- Julia `bladeindex(n,b)` (1-based position of `b` in `indexbasis(n, popcount b)`,
`Leibniz.jl src/utilities.jl:181-184`). -/
@[inline] def bladeIndex (n : Nat) (b : UInt64) : Nat := bladeRank n b + 1

/-- Runtime implementation of `basisRank`: one table read for `n ≤ 12`. -/
def basisRankImpl (n : Nat) (b : UInt64) : Nat :=
  if tabled n b then natAt (table n).pos b.toNat else binomsum n (popcount b) + bladeRankCF n b

/-- 0-based position of `b` in the full multivector layout. -/
@[implemented_by basisRankImpl]
def basisRank (n : Nat) (b : UInt64) : Nat := binomsum n (popcount b) + bladeRank n b

/-- Julia `basisindex(n,b) = binomsum(n,popcount b) + bladeindex(n,b)` (1-based). -/
@[inline] def basisIndex (n : Nat) (b : UInt64) : Nat := basisRank n b + 1

/-- Runtime implementation of `spinRank`: two table reads for `n ≤ 12`. -/
def spinRankImpl (n : Nat) (b : UInt64) : Nat :=
  if tabled n b then
    let t := table n
    natAt t.spinOffsets (popcount b) + natAt t.rank b.toNat
  else spinsum n (popcount b) + bladeRankCF n b

/-- 0-based position of an even blade in the spinor layout. -/
@[implemented_by spinRankImpl]
def spinRank (n : Nat) (b : UInt64) : Nat := spinsum n (popcount b) + bladeRank n b

/-- Julia `spinindex(n,b)` (1-based; meaningful for even `b`). -/
@[inline] def spinIndex (n : Nat) (b : UInt64) : Nat := spinRank n b + 1

/-- Runtime implementation of `antiRank`: two table reads for `n ≤ 12`. -/
def antiRankImpl (n : Nat) (b : UInt64) : Nat :=
  if tabled n b then
    let t := table n
    natAt t.antiOffsets (popcount b) + natAt t.rank b.toNat
  else antisum n (popcount b) + bladeRankCF n b

/-- 0-based position of an odd blade in the co-spinor layout. -/
@[implemented_by antiRankImpl]
def antiRank (n : Nat) (b : UInt64) : Nat := antisum n (popcount b) + bladeRank n b

/-- Julia `antiindex(n,b)` (1-based; meaningful for odd `b`). Julia's cache gives
`antiindex(1,0b1) = 2` (quirk Q2); the correct value is 1. -/
@[inline] def antiIndex (n : Nat) (b : UInt64) : Nat := antiRank n b + 1

/-- Runtime implementation of `indexBasis`. -/
def indexBasisImpl (n g : Nat) : Array UInt64 :=
  if n ≤ tableLimit then
    let t := table n
    if g ≤ n then t.basis.extract t.offsets[g]! t.offsets[g + 1]! else #[]
  else (List.range (choose n g)).toArray.map (unrank n g)

/-- Julia `indexbasis(n,g)`: the grade-`g` masks in lex order
(`Leibniz.jl src/utilities.jl:221-244`); empty for `g > n`. -/
@[implemented_by indexBasisImpl]
def indexBasis (n g : Nat) : Array UInt64 := (indexBasisSpec n g).toArray.map (·.toUInt64)

/-- Runtime implementation of `indexBasisAll`. -/
def indexBasisAllImpl (n : Nat) : Array UInt64 :=
  if n ≤ tableLimit then (table n).basis
  else (List.range (n + 1)).toArray.flatMap (indexBasisImpl n)

/-- Julia `indexbasis(n)`: every mask in multivector (grade-major, lex) order. -/
@[implemented_by indexBasisAllImpl]
def indexBasisAll (n : Nat) : Array UInt64 :=
  (List.range (n + 1)).toArray.flatMap (indexBasis n)

/-- Runtime implementation of `indexEven`. -/
def indexEvenImpl (n : Nat) : Array UInt64 :=
  if n ≤ tableLimit then (table n).even
  else ((List.range (n + 1)).filter (· % 2 == 0)).toArray.flatMap (indexBasisImpl n)

/-- The even masks in spinor order (the *intended* Julia `indexeven`; Julia's
`indexeven_set` is unfiltered for `0 < n < 22`, Leibniz quirk Q3). -/
@[implemented_by indexEvenImpl]
def indexEven (n : Nat) : Array UInt64 :=
  ((List.range (n + 1)).filter (· % 2 == 0)).toArray.flatMap (indexBasis n)

/-- Runtime implementation of `indexOdd`. -/
def indexOddImpl (n : Nat) : Array UInt64 :=
  if n ≤ tableLimit then (table n).odd
  else ((List.range (n + 1)).filter (· % 2 == 1)).toArray.flatMap (indexBasisImpl n)

/-- The odd masks in co-spinor order (intended Julia `indexodd`). -/
@[implemented_by indexOddImpl]
def indexOdd (n : Nat) : Array UInt64 :=
  ((List.range (n + 1)).filter (· % 2 == 1)).toArray.flatMap (indexBasis n)

/-- Grade and 0-based lex rank of the blade at 0-based multivector position `p`
(the grade `g` with `binomsum n g ≤ p < binomsum n (g+1)`). -/
def gradeOfPos (n p : Nat) : Nat × Nat := go 0 p (n + 1)
where
  /-- Walk grades upward, subtracting each grade's size from `p`. -/
  go (g p : Nat) : Nat → Nat × Nat
    | 0 => (g, p)
    | fuel + 1 => if p < choose n g then (g, p) else go (g + 1) (p - choose n g) fuel

/-- The grade-`g` blade with 1-based `bladeindex` `i` (inverse of `bladeIndex`). -/
@[inline] def bladeOfIndex (n g i : Nat) : UInt64 := unrank n g (i - 1)

/-- Runtime implementation of `basisAt`. -/
def basisAtImpl (n p : Nat) : UInt64 :=
  if n ≤ tableLimit then (table n).basis[p]?.getD 0
  else let (g, r) := gradeOfPos n p; unrank n g r

/-- The blade at 0-based multivector position `p` (inverse of `basisRank`). -/
@[implemented_by basisAtImpl]
def basisAt (n p : Nat) : UInt64 := let (g, r) := gradeOfPos n p; unrank n g r

/-- The blade with 1-based Julia `basisindex` `i` (inverse of `basisIndex`). -/
@[inline] def basisOfIndex (n i : Nat) : UInt64 := basisAt n (i - 1)

/-- Grade and rank of the blade at 0-based position `p` of the spinor layout. -/
def spinGradeOfPos (n p : Nat) : Nat × Nat := go 0 p (n + 1)
where
  /-- Walk the even grades upward. -/
  go (g p : Nat) : Nat → Nat × Nat
    | 0 => (g, p)
    | fuel + 1 => if p < choose n g then (g, p) else go (g + 2) (p - choose n g) fuel

/-- Grade and rank of the blade at 0-based position `p` of the co-spinor layout. -/
def antiGradeOfPos (n p : Nat) : Nat × Nat := spinGradeOfPos.go n 1 p (n + 1)

/-- The even blade at 0-based spinor position `p` (inverse of `spinRank`). -/
def spinAt (n p : Nat) : UInt64 := let (g, r) := spinGradeOfPos n p; unrank n g r

/-- The odd blade at 0-based co-spinor position `p` (inverse of `antiRank`). -/
def antiAt (n p : Nat) : UInt64 := let (g, r) := antiGradeOfPos n p; unrank n g r

/-- The even blade with 1-based Julia `spinindex` `i`. -/
@[inline] def spinOfIndex (n i : Nat) : UInt64 := spinAt n (i - 1)

/-- The odd blade with 1-based Julia `antiindex` `i`. -/
@[inline] def antiOfIndex (n i : Nat) : UInt64 := antiAt n (i - 1)

/-! ## Kernel-checked facts

`decide +kernel` evaluates the specification (the `implemented_by` targets are
irrelevant to the kernel). These pin the Julia goldens and prove the index maps
are mutually inverse bijections for every `n ≤ 5`. -/

-- Julia goldens (port-notes/directsum.md §4.2, leibniz.md §6.3).
example : binomial 64 32 = 1832624140942590534 := by decide +kernel
example : gdimsall 4 = #[1, 4, 6, 4, 1] := by decide +kernel
example : binomcumsum 4 = #[0, 1, 5, 11, 15, 16] := by decide +kernel
example : spincumsum 4 = #[0, 1, 1, 7, 7, 8] := by decide +kernel
example : anticumsum 4 = #[0, 0, 4, 4, 8, 8] := by decide +kernel
example : spincumsum 5 = #[0, 1, 1, 11, 11, 16, 16] := by decide +kernel
example : anticumsum 5 = #[0, 0, 5, 5, 15, 15, 16] := by decide +kernel
example : indexBasis 4 2 = #[0x3, 0x5, 0x9, 0x6, 0xa, 0xc] := by decide +kernel
example : indexBasis 5 3 = #[0x07, 0x0b, 0x13, 0x0d, 0x15, 0x19, 0x0e, 0x16, 0x1a, 0x1c] := by decide +kernel
example : indexBasisAll 3 = #[0, 1, 2, 4, 3, 5, 6, 7] := by decide +kernel
example : (List.range 16).map (fun b => bladeIndex 4 b.toUInt64)
    = [1, 1, 2, 1, 3, 2, 4, 1, 4, 3, 5, 2, 6, 3, 4, 1] := by decide +kernel
example : (List.range 16).map (fun b => basisIndex 4 b.toUInt64)
    = [1, 2, 3, 6, 4, 7, 9, 12, 5, 8, 10, 13, 11, 14, 15, 16] := by decide +kernel
example : (List.range 16).map (fun b => spinIndex 4 b.toUInt64)
    = [1, 2, 3, 2, 4, 3, 5, 8, 5, 4, 6, 9, 7, 10, 11, 8] := by decide +kernel
example : combo 4 2 = #[#[1, 2], #[1, 3], #[1, 4], #[2, 3], #[2, 4], #[3, 4]] := by decide +kernel

/-- Pascal's rule for the multiplicative `binomial`, every `n, k < 24`. -/
theorem binomial_pascal_lt24 :
    ∀ n < 24, ∀ k < 24, binomial (n + 1) (k + 1) = binomial n k + binomial n (k + 1) := by
  decide +kernel

/-- Each grade has `C(n,g)` blades, for every `n ≤ 5` and `g ≤ n + 1`. -/
theorem indexBasis_size_le5 : ∀ n < 6, ∀ g < n + 2, (indexBasis n g).size = binomial n g := by
  decide +kernel

/-- The multivector layout has `2ⁿ` entries (`n ≤ 8`). -/
theorem indexBasisAll_size_le8 : ∀ n < 9, (indexBasisAll n).size = 2 ^ n := by
  decide +kernel

/-- `binomsum n (n+1) = 2ⁿ`, i.e. the grade offsets tile the layout (`n ≤ 24`). -/
theorem binomsum_total_le24 : ∀ n < 25, binomsum n (n + 1) = 2 ^ n := by
  decide +kernel

/-- `unrank` enumerates `indexBasis` (`n ≤ 5`). -/
theorem unrank_eq_indexBasis_le5 :
    ∀ n < 6, ∀ g < n + 1, ∀ r < binomial n g, unrank n g r = (indexBasis n g)[r]! := by
  decide +kernel

/-- `bladeRank ∘ unrank = id` on `Fin (C(n,g))` (`n ≤ 5`). -/
theorem bladeRank_unrank_le5 :
    ∀ n < 6, ∀ g < n + 1, ∀ r < binomial n g, bladeRank n (unrank n g r) = r := by
  decide +kernel

/-- `unrank ∘ bladeRank = id` on all `2ⁿ` masks (`n ≤ 5`). -/
theorem unrank_bladeRank_le5 :
    ∀ n < 6, ∀ b < 2 ^ n,
      unrank n (popcount b.toUInt64) (bladeRank n b.toUInt64) = b.toUInt64 := by
  decide +kernel

/-- `basisRank` and `basisAt` are inverse bijections of `[0, 2ⁿ)` (`n ≤ 5`). -/
theorem basisRank_basisAt_le5 :
    (∀ n < 6, ∀ p < 2 ^ n, basisRank n (basisAt n p) = p) ∧
    (∀ n < 6, ∀ b < 2 ^ n, basisAt n (basisRank n b.toUInt64) = b.toUInt64) := by
  decide +kernel

/-- Spinor / co-spinor layouts are bijections onto the even / odd masks (`n ≤ 5`). -/
theorem spin_anti_bij_le5 :
    (∀ n < 6, ∀ p < 2 ^ n / 2, spinRank n (spinAt n p) = p ∧ popcount (spinAt n p) % 2 = 0) ∧
    (∀ n < 6, ∀ p < 2 ^ n / 2, antiRank n (antiAt n p) = p ∧ popcount (antiAt n p) % 2 = 1) := by
  decide +kernel

end Leibniz

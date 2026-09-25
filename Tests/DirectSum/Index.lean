/-
Index-table consistency (no oracle needed): the memoized runtime tables and the
closed forms against the kernel-reducible specification (`combos`), exhaustively
for every `n ≤ 16`, then randomized properties of the closed forms up to
`n = 62` (SplitMix64, `Tests/Util/Random.lean`).
-/
import Tests.DirectSum.Common
import Tests.Util.Random

open DirectSum DirectSum.Bits Leibniz

namespace DirectSumTests.Index

/-- Lexicographic comparison of ascending index lists. -/
def lexLt : List Nat → List Nat → Bool
  | [], _ :: _ => true
  | x :: xs, y :: ys => x < y || (x == y && lexLt xs ys)
  | _, _ => false

/-- Exhaustive runtime-vs-specification checks for dimension `n`. -/
def checkDim (t : Tally) (n : Nat) : Tally := Id.run do
  let mut t := t
  let grades := (List.range (n + 1)).toArray.map fun g => (indexBasisSpec n g).toArray.map (·.toUInt64)
  let mut okBasis := true
  let mut okRank := true
  let mut okUnrank := true
  for g in [0:n + 1] do
    let spec := grades[g]!
    okBasis := okBasis && indexBasis n g == spec
    for (b, r) in spec.zipIdx do
      okRank := okRank && bladeRank n b == r && bladeRankCF n b == r && bladeIndex n b == r + 1
      okUnrank := okUnrank && unrank n g r == b && bladeOfIndex n g (r + 1) == b
  t := t.check okBasis s!"indexBasis {n} (runtime) ≠ spec"
  t := t.check okRank s!"bladeRank {n} (table/closed form) ≠ spec"
  t := t.check okUnrank s!"unrank {n} ≠ spec"
  let all := grades.flatten
  t := t.check (indexBasisAll n == all) s!"indexBasisAll {n}"
  t := t.check (all.size == 2 ^ n) s!"layout size {n}"
  let mut okPos := true
  for (b, p) in all.zipIdx do
    okPos := okPos && basisRank n b == p && basisAt n p == b && basisOfIndex n (p + 1) == b
      && basisIndex n b == p + 1
  t := t.check okPos s!"basisRank/basisAt {n}"
  let evens := (List.range (n + 1)).filter (· % 2 == 0) |>.toArray.flatMap (grades[·]!)
  let odds := (List.range (n + 1)).filter (· % 2 == 1) |>.toArray.flatMap (grades[·]!)
  t := t.check (indexEven n == evens && indexOdd n == odds) s!"indexEven/indexOdd {n}"
  let mut okSpin := true
  for (b, p) in evens.zipIdx do
    okSpin := okSpin && spinRank n b == p && spinAt n p == b && spinOfIndex n (p + 1) == b
  for (b, p) in odds.zipIdx do
    okSpin := okSpin && antiRank n b == p && antiAt n p == b && antiOfIndex n (p + 1) == b
  t := t.check okSpin s!"spin/anti layout {n}"
  t := t.check (binomcumsum n == (List.range (n + 2)).toArray.map fun g =>
      (List.range g).foldl (fun s q => s + (grades[q]?.map (·.size)).getD 0) 0) s!"binomcumsum {n}"
  return t

/-- Randomized properties of the closed forms for large `n`. -/
def checkLarge (t : Tally) : Tally := Id.run do
  let mut t := t
  let mut g : Tests.Rng := Tests.Rng.ofSeed 0x5eed
  for n in [20, 24, 30, 40, 50, 62] do
    let mut ok := true
    let mut okLex := true
    for _ in [0:2000] do
      let (x, g') := g.next
      let (y, g'') := g'.next
      g := g''
      let b := x &&& lowMask n
      let k := popcount b
      let r := bladeRank n b
      ok := ok && r < choose n k && unrank n k r == b && basisAt n (basisRank n b) == b
      -- a second blade of the same grade: ranks order like the index lists
      let c := unrank n k (y.toNat % choose n k)
      let rc := bladeRank n c
      okLex := okLex && (lexLt (indicesList b) (indicesList c) == decide (r < rc))
    t := t.check ok s!"closed-form rank/unrank round trip n={n}"
    t := t.check okLex s!"closed-form rank is lexicographic n={n}"
  return t

/-- Run the index-consistency suite. -/
def run : IO Tally := do
  let mut t : Tally := {}
  for n in [0:17] do t := checkDim t n
  return checkLarge t

end DirectSumTests.Index

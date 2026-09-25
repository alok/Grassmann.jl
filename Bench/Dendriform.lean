import Bench.Harness
import Dendriform
import DeMorgan

/-!
# `dendriform` and `demorgan`: tree, grove and truth-table algebra

Julia twins: `oracle/bench/dendriform.jl`, `oracle/bench/demorgan.jl` (run in
`oracle/bench/env2`, since Dendriform conflicts with AbstractAnalysis in the main environment).

`dendriform`:
* `grove_sum_4_3`, `grove_mul_3_2`, `grove_dashv_4_3`, `grove_vdash_4_3`: operations on the total
  groves `Y_p` (Julia `Grove(p)`, cached on both sides); the check is the result's size.
* `tree_pairs_d6`: `x + y`, `x ⊣ y`, `x ⊢ y` for every pair of trees of degrees `1 … 5` with
  `deg x + deg y ≤ 6` (ns per pair); the check is the total number of result trees.

`demorgan`:
* `tv_formula_N6`: `(p → q) ↔ ((p ∧ q) ∨ ¬p)` on 1000 random pairs of 64-row truth columns
  (`TruthValues{6}`: a `UInt64` in Julia, a `BitVec 64` in Lean).
* `truthtable_N4`: the named truth table of `((p ∧ q) → (r ∨ ¬s)) ↔ (¬(p ∧ q) ∨ r)` built from
  the projection tables (Julia `@truthtable` semantics, names included); the check is the
  length of the expression's name.
-/

namespace Bench.Dendriform

open _root_.Dendriform Bench

/-- Total number of result trees of `+`, `⊣`, `⊢` over all pairs. -/
def pairOps (ts : Array (Array Tree)) : Nat := Id.run do
  let mut acc := 0
  for dx in [1:6] do
    for dy in [1:6] do
      if dx + dy ≤ 6 then
        for x in ts[dx]! do
          for y in ts[dy]! do
            acc := acc + (Tree.sum x y).length + (Tree.dashv x y).length + (Tree.vdash x y).length
  return acc

/-- Number of pairs in `pairOps`. -/
def pairCount (ts : Array (Array Tree)) : Nat := Id.run do
  let mut acc := 0
  for dx in [1:6] do
    for dy in [1:6] do
      if dx + dy ≤ 6 then acc := acc + ts[dx]!.size * ts[dy]!.size
  return acc

/-- The `dendriform` suite. -/
def suite : Suite := ⟨"dendriform", do
  bench "grove_sum_4_3" fun s => ((Grove.total (blackBox s 4)).add (Grove.total 3)).size
  bench "grove_mul_3_2" fun s => ((Grove.total (blackBox s 3)).mul (Grove.total 2)).size
  bench "grove_dashv_4_3" fun s => ((Grove.total (blackBox s 4)).dashv (Grove.total 3)).size
  bench "grove_vdash_4_3" fun s => ((Grove.total (blackBox s 4)).vdash (Grove.total 3)).size
  let ts : Array (Array Tree) := (List.range 7).toArray.map fun d => (allTrees d).toArray
  let np := pairCount ts
  bench "tree_pairs_d6" (ops := np) (param := s!"{np} pairs") fun s => pairOps (blackBox s ts)⟩

end Bench.Dendriform

namespace Bench.DeMorgan

open _root_.DeMorgan Bench

/-- `∑ toNat ((p → q) ↔ ((p ∧ q) ∨ ¬p))` over pairs of 64-row columns. The column is
converted through `UInt64` (`Nat.toFloat` of a value `≥ 2^63` takes ~8 µs, which would swamp
the formula). -/
def formulaSum (ps : Array (TruthValues 6 × TruthValues 6)) : Float :=
  ps.foldl (fun acc (p, q) =>
    acc + ((p.imp q).iff ((p.and q).or p.not)).toNat.toUInt64.toFloat) 0

/-- The table of `((p ∧ q) → (r ∨ ¬s)) ↔ (¬(p ∧ q) ∨ r)`; returns the expression's name. -/
def table4 (vs : Array (TruthTable 4)) : String :=
  match vs with
  | #[p, q, r, s] =>
    let pq := p.and q
    ((pq.imp (r.or s.not)).iff (pq.not.or r)).toString
  | _ => ""

/-- The `demorgan` suite. -/
def suite : Suite := ⟨"demorgan", do
  let m := 1000
  let ws := randWords (2 * m) 0xDE3
  let ps := (Array.range m).map fun i =>
    (TruthValues.ofNat 6 ws[2 * i]!.toNat, TruthValues.ofNat 6 ws[2 * i + 1]!.toNat)
  bench "tv_formula_N6" (ops := m) (param := s!"n={m}") fun s => formulaSum (blackBox s ps)
  let names : Fin 4 → String := fun i => #["p", "q", "r", "s"][i.1]!
  let vs := TruthTable.vars 4 names
  bench "truthtable_N4" fun s => table4 (blackBox s vs)⟩

end Bench.DeMorgan

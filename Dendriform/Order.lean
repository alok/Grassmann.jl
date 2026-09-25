import Dendriform.Tree

/-!
# The canonical total order on trees: tree integers

Julia source: DF/morphism.jl:189-342. Julia sorts every total grove `Y_d` by the
**tree integer** `TreeInteger(υ) = ΘMax(d) - ΘInt(μ(υ))` (port-notes §4.4.2), which fixes
the tree index (1-based rank) and hence the grove index bitsets.

* `μ(υ)[ω]` (`BaseTree`, DF/morphism.jl:209-216) lists the positions carrying label
  `d + 1 - ω`, so `μ[1]` holds the root.
* `ΘInt(μ)` reads the concatenated positions as a decimal numeral (carrying when a
  position is ≥ 10), and `ΘMax(d)` is the numeral `d (d-1) … 1`.

Julia memoizes `ΘMax` with an off-by-degree bug when the memo grows by more than one
degree at a time (port-notes §4.4.2, Appendix A #8); the closed form below has no memo.
-/

namespace Dendriform

namespace Tree

/-- Julia `TreeBase(υ).μ` (DF/morphism.jl:209-216): for `ω = 1..d`, the ascending
1-based positions whose label is `d + 1 - ω`. -/
def mu (t : Tree) : List (List Nat) :=
  let y := t.name
  let d := y.length
  (List.range d).map fun w => ((List.range d).filter fun p => y.getD p 0 == d - w).map (· + 1)

/-- Julia `ΘInt(μ)` (DF/morphism.jl:252-261): the concatenated positions read as a
decimal numeral, `Σ_t seq[t] · 10^(d-t)`. -/
def thetaInt (μ : List (List Nat)) : Nat :=
  μ.flatten.foldl (fun acc x => 10 * acc + x) 0

/-- Julia `ΘMax(d) = Σ_{k=1}^{d} k · 10^(k-1)` (DF/morphism.jl:235-250), closed form. -/
def thetaMax (d : Nat) : Nat :=
  ((List.range d).reverse.map (· + 1)).foldl (fun acc x => 10 * acc + x) 0

/-- Julia `TreeInteger(υ) = ΘMax(d) - ΘInt(μ)` (DF/morphism.jl:284). -/
def treeInteger (t : Tree) : Nat := thetaMax t.deg - thetaInt t.mu

/-- Julia `TreeRational(υ)` (DF/morphism.jl:319) with the `treeshift` toggle made an
argument (default `true`, DF/morphism.jl:339-342): `TI/ΘMax` when shifted, else
`1 - TI/ΘMax`. -/
def treeRational (t : Tree) (treeshift : Bool := true) : Rat :=
  let r : Rat := (t.treeInteger : Rat) / (thetaMax t.deg : Rat)
  if treeshift then r else 1 - r

/-- Julia's grovedisplay rendering of `μ` (DF/Dendriform.jl:415-417): each `μ[ω]` as
`[a, b]`, or `∅` when empty, concatenated. -/
def muString (t : Tree) : String :=
  String.join (t.mu.map fun m =>
    if m.isEmpty then "∅" else "[" ++ ", ".intercalate (m.map toString) ++ "]")

end Tree

-- ΘMax(1..6) and the degree-3 tree integers of port-notes §6.4
example : (List.range 6).map (fun d => Tree.thetaMax (d + 1)) = [1, 21, 321, 4321, 54321, 654321] := by
  decide
example : isort (· ≤ ·) ((allTrees 3).map Tree.treeInteger) = [0, 9, 108, 189, 198] := by decide
-- tree integers separate the trees of each degree ≤ 5 (Julia checked d ≤ 12 exhaustively)
example : (List.range 6).all (fun n =>
    ((allTrees n).map Tree.treeInteger).eraseDups.length == catalan n) = true := by decide

end Dendriform

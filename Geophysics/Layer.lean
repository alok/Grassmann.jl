/-!
# Layer lookup and its specification

Julia `layer(h, W)` (`Geophysics.jl:571`):

    layer(h) = h ≤ A.h[1] ? 1 : (j = findfirst(x -> x ≥ h, A.h); j === nothing ? n : j-1)

`layerIdx` is this scan over any table with a decidable `≤`, returning a `Fin n`
(so it is total by construction). Its specification is proved for every such
table, in particular for `Float` with IEEE comparison (`NaN` included), because
it only uses the outcomes of the comparisons the scan performs:

* `layerIdx_of_le`: at or below the first base, the layer is `0`;
* `not_le_layerIdx`: above the first base, `h` is not `≤` the base of its layer;
* `le_layerIdx_succ`: `h` is `≤` the base of the next layer, when there is one
  (so an exact base belongs to the layer below it);
* `not_le_of_lt_layerIdx`: every earlier base is also not `≥ h`, i.e. the layer
  is the first one whose next base reaches `h`.
-/

namespace Geophysics

variable {α : Type} [LE α] [DecidableLE α] {n : Nat}

/-- The `findfirst` scan of `layerIdx` from index `j`: one below the first base
`≥ x` at or after `j`, or the last layer. -/
@[specialize] def layerScan (hs : Fin n → α) (pos : 0 < n) (x : α) (j : Nat) : Fin n :=
  if h : j < n then
    if x ≤ hs ⟨j, h⟩ then ⟨j - 1, by omega⟩ else layerScan hs pos x (j + 1)
  else ⟨n - 1, by omega⟩
termination_by n - j

/-- Julia's `layer` scan (0-based): `0` when `x ≤ hs 0`; otherwise one below the
first base `≥ x`, or the last layer if there is none. -/
@[inline] def layerIdx (hs : Fin n → α) (pos : 0 < n) (x : α) : Fin n :=
  if x ≤ hs ⟨0, pos⟩ then ⟨0, pos⟩ else layerScan hs pos x 1

variable (hs : Fin n → α) (pos : 0 < n) (x : α)

/-- At or below the first base the layer is `0`. -/
theorem layerIdx_of_le (h : x ≤ hs ⟨0, pos⟩) : layerIdx hs pos x = ⟨0, pos⟩ := by
  simp [layerIdx, h]

/-- The scan's invariant: started at `j` with every earlier base below `x`, it
returns a layer whose base is below `x` and whose successor base (if any) is not. -/
theorem layerScan_spec (j : Nat) (hj : 0 < j)
    (hprev : ∀ k (hk : k < n), k < j → ¬ x ≤ hs ⟨k, hk⟩) :
    (¬ x ≤ hs (layerScan hs pos x j)) ∧
    (∀ h : (layerScan hs pos x j).1 + 1 < n, x ≤ hs ⟨(layerScan hs pos x j).1 + 1, h⟩) ∧
    (∀ k (hk : k < n), k ≤ (layerScan hs pos x j).1 → ¬ x ≤ hs ⟨k, hk⟩) := by
  induction j using layerScan.induct hs x with
  | case1 j hjn hle =>
    rw [layerScan]
    simp only [hjn, hle, dite_true, ite_true]
    refine ⟨hprev _ _ (by omega), fun h => ?_, fun k hk hkj => hprev k hk (by omega)⟩
    have : j - 1 + 1 = j := by omega
    simp only [this]; exact hle
  | case2 j hjn hle ih =>
    rw [layerScan]
    simp only [hjn, hle, dite_true, ite_false]
    exact ih (by omega) fun k hk hkj => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hkj with hkj | rfl
      · exact hprev k hk hkj
      · exact hle
  | case3 j hjn =>
    rw [layerScan]
    simp only [hjn, dite_false]
    refine ⟨hprev _ _ (by omega), fun h => absurd h (by omega), fun k hk _ => hprev k hk (by omega)⟩

/-- Above the first base, `x` is not `≤` the base of its layer. -/
theorem not_le_layerIdx (h : ¬ x ≤ hs ⟨0, pos⟩) : ¬ x ≤ hs (layerIdx hs pos x) := by
  simp only [layerIdx, h, ite_false]
  exact (layerScan_spec hs pos x 1 (by omega) fun k hk hk1 => by
    obtain rfl : k = 0 := by omega
    exact h).1

/-- Above the first base, `x` is `≤` the base of the next layer when there is one:
an exact base belongs to the layer below it. -/
theorem le_layerIdx_succ (h : ¬ x ≤ hs ⟨0, pos⟩) (hn : (layerIdx hs pos x).1 + 1 < n) :
    x ≤ hs ⟨(layerIdx hs pos x).1 + 1, hn⟩ := by
  simp only [layerIdx, h, ite_false] at hn ⊢
  exact (layerScan_spec hs pos x 1 (by omega) fun k hk hk1 => by
    obtain rfl : k = 0 := by omega
    exact h).2.1 hn

/-- Every base up to the layer's is not `≥ x`: the scan finds the first base
reaching `x`. -/
theorem not_le_of_lt_layerIdx (h : ¬ x ≤ hs ⟨0, pos⟩) (k : Nat) (hk : k < n)
    (hkl : k ≤ (layerIdx hs pos x).1) : ¬ x ≤ hs ⟨k, hk⟩ := by
  simp only [layerIdx, h, ite_false] at hkl
  exact (layerScan_spec hs pos x 1 (by omega) fun k hk hk1 => by
    obtain rfl : k = 0 := by omega
    exact h).2.2 k hk hkl

end Geophysics

/-
Storage-layout facts the dynamic layer's correctness theorems rest on
(`Grassmann.Dynamic.Laws`).

The dynamic lattice builds its containers from coefficient functions
(`TA.chainOf`, `TA.halfOf`) and reads them back with the layouts' `rank`
(`Chain.coeff`, `Half.coeff`). That this round trip returns the coefficient is the
statement that `rank` is a left inverse of the layout's blade table on the blades it
contains; together with two popcount facts about the scalar and pseudoscalar blades,
it is `LayoutInv n`.

`LayoutInv n` is a property of Leibniz's index tables alone (lexicographic
`indexbasis`, the combinatorial-number-system `bladeRank`). It is checked by the
kernel over all `2ⁿ` blades for every `n ≤ 8` (`layoutInv_le8`, `decide +kernel`,
with the bound `blade < 2ⁿ` proved in general by `valid_toNat_lt`); a proof for all
`n` needs the correctness of the closed-form rank, which Leibniz states only up to
`n = 5` (`Leibniz.bladeRank_unrank_le5`).
-/
import Grassmann.Types.Dims

namespace Grassmann

open DirectSum DirectSum.Bits Leibniz

/-- Blade `β` round-trips through layout `L`: its `rank` is a storage position of `L`
and `L` stores `β` there. -/
def RoundTrip (n : Nat) (L : Layout) (β : UInt64) : Prop :=
  L.rank n β < L.size n ∧ (L.blades n)[L.rank n β]! = β

/-- The index-table facts behind the dynamic layer's theorems, for `n` generators:
the pseudoscalar `lowMask n` has grade `n`, every blade round-trips through its chain
layout and its half layout, the only grade-0 blade is `0`, and the only grade-`n` blade
is the pseudoscalar, at rank `0`. -/
def LayoutInv (n : Nat) : Prop :=
  popcount (lowMask n) = n ∧ ∀ β : UInt64, Layout.full.contains n β = true →
    RoundTrip n (.chain (popcount β)) β ∧ RoundTrip n (halfLayout (popcount β % 2 == 1)) β ∧
    (popcount β = 0 → β = 0) ∧ (popcount β = n → β = lowMask n ∧ bladeRank n β = 0)

/-- `LayoutInv`'s statement for one blade, as a kernel-evaluable Boolean. -/
def layoutCheck (n : Nat) (β : UInt64) : Bool :=
  let L1 := Layout.chain (popcount β)
  let L2 := halfLayout (popcount β % 2 == 1)
  decide (L1.rank n β < L1.size n) && (L1.blades n)[L1.rank n β]! == β &&
  decide (L2.rank n β < L2.size n) && (L2.blades n)[L2.rank n β]! == β &&
  (popcount β != 0 || β == 0) &&
  (popcount β != n || (β == lowMask n && bladeRank n β == 0))

/-- `LayoutInv n` from the Boolean check of the `2ⁿ` blades, given that a blade of
`n` generators is below `2ⁿ`. -/
theorem layoutInv_of_check (n : Nat) (hp : popcount (lowMask n) = n)
    (hv : ∀ b : UInt64, Layout.full.contains n b = true → b.toNat < 2 ^ n)
    (hc : ∀ k < 2 ^ n, layoutCheck n k.toUInt64 = true) : LayoutInv n := by
  refine ⟨hp, fun β hβ => ?_⟩
  have h := hc β.toNat (hv β hβ)
  simp only [Nat.toUInt64_eq, UInt64.ofNat_toNat, layoutCheck, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨⟨h1, h2⟩, ⟨h3, h4⟩, fun h0 => ?_, fun hn => ?_⟩
  · rcases h5 with h5 | h5
    · exact absurd h0 h5
    · exact h5
  · rcases h6 with h6 | h6
    · exact absurd hn h6
    · exact h6

/-- The pseudoscalar mask of `n < 64` generators is `2ⁿ - 1`. -/
theorem lowMask_toNat {n : Nat} (hn : n < 64) : (lowMask n).toNat = 2 ^ n - 1 := by
  simp only [lowMask, fullMask, show ¬ n ≥ 64 by omega, ite_false]
  have hp : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hn
  have hp1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h1 : ((1 : UInt64) <<< n.toUInt64).toNat = 2 ^ n := by
    simp [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hn, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hp]
  have h2 : (1 : UInt64) ≤ (1 : UInt64) <<< n.toUInt64 := by
    rw [UInt64.le_iff_toNat_le, h1]; simpa using hp1
  rw [UInt64.toNat_sub_of_le _ _ h2, h1]; rfl

/-- A blade of `n < 64` generators is below `2ⁿ`. -/
theorem valid_toNat_lt {n : Nat} (hn : n < 64) {b : UInt64} (h : Layout.full.contains n b = true) :
    b.toNat < 2 ^ n := by
  simp only [Layout.contains, Bool.and_true, beq_iff_eq] at h
  have h2 := congrArg UInt64.toNat h
  simp only [UInt64.toNat_and, UInt64.toNat_not, UInt64.toNat_zero, lowMask_toNat hn] at h2
  have hp : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hn
  have hx : 2 ^ n - 1 < 2 ^ 64 := by omega
  have e : UInt64.size - 1 - (2 ^ n - 1) = 2 ^ 64 - (2 ^ n - 1 + 1) := by
    have : UInt64.size = 2 ^ 64 := rfl
    omega
  rw [e] at h2
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_cases h64 : i < 64
  · have := congrArg (Nat.testBit · i) h2
    simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_succ hx, Nat.testBit_two_pow_sub_one,
      Nat.zero_testBit] at this
    simpa [h64, show ¬ i < n by omega] using this
  · have hb : b.toNat < 2 ^ 64 := UInt64.toNat_lt_size b
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))

/-- A blade of `n ≤ 8` generators is below `2ⁿ`. -/
theorem valid_lt_of_le8 (n : Nat) (hn : n ≤ 8) (b : UInt64) (h : Layout.full.contains n b = true) :
    b.toNat < 2 ^ n := valid_toNat_lt (by omega) h

/-- `LayoutInv n` for every `n ≤ 8`, checked by the kernel (all `2ⁿ` blades). -/
theorem layoutInv_le8 : ∀ n, n ≤ 8 → LayoutInv n := by
  intro n hn
  match n, hn with
  | 0, _ => exact layoutInv_of_check 0 (by decide) (valid_lt_of_le8 0 (by omega)) (by decide +kernel)
  | 1, _ => exact layoutInv_of_check 1 (by decide) (valid_lt_of_le8 1 (by omega)) (by decide +kernel)
  | 2, _ => exact layoutInv_of_check 2 (by decide) (valid_lt_of_le8 2 (by omega)) (by decide +kernel)
  | 3, _ => exact layoutInv_of_check 3 (by decide) (valid_lt_of_le8 3 (by omega)) (by decide +kernel)
  | 4, _ => exact layoutInv_of_check 4 (by decide) (valid_lt_of_le8 4 (by omega)) (by decide +kernel)
  | 5, _ => exact layoutInv_of_check 5 (by decide) (valid_lt_of_le8 5 (by omega)) (by decide +kernel)
  | 6, _ => exact layoutInv_of_check 6 (by decide) (valid_lt_of_le8 6 (by omega)) (by decide +kernel)
  | 7, _ => exact layoutInv_of_check 7 (by decide) (valid_lt_of_le8 7 (by omega)) (by decide +kernel)
  | 8, _ => exact layoutInv_of_check 8 (by decide) (valid_lt_of_le8 8 (by omega)) (by decide +kernel)

end Grassmann

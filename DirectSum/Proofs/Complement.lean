/-
The complement kernels on all masks.

The right complement `!e_a = (-1)^{σ(a, ā)} e_ā` is computed by the
implementation from the sum of the 1-based indices of `a` (`Bits.sumIndices`,
six masked popcounts) through Julia's closed form `parityrightRaw`, and the
complementary mask by Leibniz `complement`. This file proves, for all masks:

* `sumIndices_eq`: `Bits.sumIndices b = Σ_{i ∈ b} (i + 1)`, by an additive
  version of the basis argument of `DirectSum.Proofs.UInt64` (the six masked
  popcounts are additive over disjoint masks, and the 64 values on single bits
  are checked by the kernel);
* `parityrightRaw_eq_sigma`: Julia's closed form
  `(Σ(i+1) + k(k+1)/2) mod 2` is the reordering sign `σ(a, ā)` of a blade and its
  complement, in every width;
* `complement_eq`: `Leibniz.complement n b` (no tangent or null generators) is
  `b ^^^ (2ⁿ - 1)` on blades that fit.
-/
import DirectSum.Proofs.LowestBit
import DirectSum.Proofs.UInt64

namespace DirectSum.Proofs

open Bits

/-! ## Additive functionals -/

/-- A `Nat`-valued function on `UInt64` that is additive over disjoint masks is
the sum of its values on the set bits. -/
theorem additive_eq_fsum (F : UInt64 → Nat) (h0 : F 0 = 0)
    (hadd : ∀ x y, x &&& y = 0 → F (x ^^^ y) = F x + F y) (x : UInt64) :
    F x = fsum 64 (fun k => if x.toNat.testBit k then F ((1 : UInt64) <<< k.toUInt64) else 0) := by
  have key : ∀ m ≤ 64, F (UInt64.ofNat (x.toNat % 2 ^ m))
      = fsum m (fun k => if x.toNat.testBit k then F ((1 : UInt64) <<< k.toUInt64) else 0) := by
    intro m hm
    induction m with
    | zero =>
      show F (UInt64.ofNat (x.toNat % 2 ^ 0)) = 0
      rw [Nat.pow_zero, Nat.mod_one]; exact h0
    | succ m ih =>
      rw [low_succ x (by omega), fsum_succ_top, ← ih (by omega)]
      have hdis : UInt64.ofNat (x.toNat % 2 ^ m)
          &&& (if x.toNat.testBit m then (1 : UInt64) <<< m.toUInt64 else 0) = 0 := by
        split
        · apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_and, UInt64.toNat_ofNat', toNat_shl_one (by omega), UInt64.toNat_zero,
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos m))
              (Nat.pow_le_pow_right (by decide) (by omega)))]
          apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_two_pow, Nat.zero_testBit]
          by_cases hi : i < m <;> simp [hi] <;> omega
        · exact UInt64.and_zero
      rw [hadd _ _ hdis]
      split <;> simp [h0]
  have := key 64 (Nat.le_refl _)
  rwa [Nat.mod_eq_of_lt x.toNat_lt, UInt64.ofNat_toNat] at this

/-- The bit count is additive over disjoint masks. -/
theorem bitCount_xor_of_and_eq_zero {n x y : Nat} (h : x &&& y = 0) :
    bitCount n (x ^^^ y) = bitCount n x + bitCount n y := by
  have := bitCount_xor_add n x y
  rw [h, bitCount_zero_mask] at this; omega

private theorem popcount_and_additive (M x y : UInt64) (h : x &&& y = 0) :
    popcount ((x ^^^ y) &&& M) = popcount (x &&& M) + popcount (y &&& M) := by
  rw [popcount_eq_bitCount, popcount_eq_bitCount, popcount_eq_bitCount]
  have e : ((x ^^^ y) &&& M).toNat = (x &&& M).toNat ^^^ (y &&& M).toNat := by
    simp only [UInt64.toNat_and, UInt64.toNat_xor]
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Nat.testBit_xor]
    cases x.toNat.testBit i <;> cases y.toNat.testBit i <;> cases M.toNat.testBit i <;> rfl
  have hd : (x &&& M).toNat &&& (y &&& M).toNat = 0 := by
    have h' := congrArg UInt64.toNat h
    rw [UInt64.toNat_and, UInt64.toNat_zero] at h'
    simp only [UInt64.toNat_and]
    apply Nat.eq_of_testBit_eq; intro i
    have := congrArg (·.testBit i) h'
    simp only [Nat.testBit_and, Nat.zero_testBit] at this ⊢
    cases hx : x.toNat.testBit i <;> cases hy : y.toNat.testBit i <;> simp_all
  rw [e, bitCount_xor_of_and_eq_zero hd]

private theorem sumIndices_unit :
    ∀ k : Fin 64, sumIndices ((1 : UInt64) <<< k.1.toUInt64) = k.1 + 1 := by
  decide +kernel

/-- **`Bits.sumIndices` is the sum of the 1-based indices of the set bits**, for
every 64-bit mask. -/
theorem sumIndices_eq (b : UInt64) :
    sumIndices b = fsum 64 (fun k => if b.toNat.testBit k then k + 1 else 0) := by
  rw [additive_eq_fsum sumIndices (by decide) (fun x y h => by
    unfold sumIndices
    simp only [popcount_and_additive _ x y h]
    have : popcount (x ^^^ y) = popcount x + popcount y := by
      rw [popcount_eq_bitCount, popcount_eq_bitCount, popcount_eq_bitCount, UInt64.toNat_xor,
        bitCount_xor_of_and_eq_zero (by
          have := congrArg UInt64.toNat h; rwa [UInt64.toNat_and, UInt64.toNat_zero] at this)]
    rw [this]; omega) b]
  exact fsum_congr fun k hk => by rw [sumIndices_unit ⟨k, hk⟩]

/-! ## Julia's closed form of the complement sign -/

/-- `Σ_{i < n, i ∈ a} (i + 1)`. -/
def indexSum (n a : Nat) : Nat := fsum n (fun k => if a.testBit k then k + 1 else 0)

/-- Widening the space does not change the index sum of a blade that fits. -/
theorem indexSum_of_lt {n m x : Nat} (hx : x < 2 ^ n) (hm : n ≤ m) : indexSum m x = indexSum n x := by
  unfold indexSum
  induction m with
  | zero => rw [Nat.le_zero.mp hm]
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le hm with h | h
    · rw [fsum_succ_top, ih (by omega), Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]; simp
    · rw [h]

private theorem tri_succ (k : Nat) : (k + 1 + 1) * (k + 1) / 2 = (k + 1) * k / 2 + (k + 1) := by
  have : (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) := by grind
  rw [this, Nat.add_mul_div_left _ _ (by decide)]

/-- **Julia's closed form of the right-complement sign is `σ(a, ā)`**:
`parityrightRaw (Σ_{i∈a} (i+1)) |a| = σ(a, a ⊕ (2ⁿ - 1))`, in every width. -/
theorem parityrightRaw_eq_sigma (n a : Nat) :
    Leibniz.parityrightRaw (indexSum n a) (bitCount n a) = sigma n a (a ^^^ (2 ^ n - 1)) := by
  induction n with
  | zero => simp [indexSum, fsum, Leibniz.parityrightRaw]
  | succ n ih =>
    unfold indexSum at ih ⊢
    rw [fsum_succ_top, bitCount_succ, sigma_succ]
    have hsig : sigma n a (a ^^^ (2 ^ (n + 1) - 1)) = sigma n a (a ^^^ (2 ^ n - 1)) :=
      sigma_congr (fun _ _ => rfl) (fun i hi => by
        simp [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, show i < n + 1 by omega, hi])
    have hpar : bitParity n (a ^^^ (2 ^ (n + 1) - 1)) = ((n - bitCount n a) % 2 == 1) := by
      rw [bitParity_congr (a' := a ^^^ (2 ^ n - 1)) (fun i hi => by
        simp [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, show i < n + 1 by omega, hi])]
      have := bitCount_xor_allOnes n a
      unfold bitParity; congr 2; omega
    rw [hsig, hpar, ← ih]
    have hk := bitCount_le n a
    unfold Leibniz.parityrightRaw
    cases a.testBit n
    · simp
    · simp only [Bool.toNat_true, ite_true, Bool.true_and]
      rw [tri_succ]
      generalize fsum n (fun k => if a.testBit k then k + 1 else 0) = s at *
      generalize (bitCount n a + 1) * bitCount n a / 2 = T at *
      have e : (s + (n + 1) + (T + (bitCount n a + 1))) % 2 = ((s + T) + (n - bitCount n a)) % 2 := by omega
      rw [e, odd_add]

/-! ## The complement mask -/

/-- Leibniz `complement n b` without tangent or null generators is the xor with
`2ⁿ - 1` (the mask of the other generators). -/
theorem complement_eq {n : Nat} (hn : n ≤ 64) (b : UInt64) :
    (Leibniz.complement n b 0 0).toNat = (b.toNat % 2 ^ n) ^^^ (2 ^ n - 1) := by
  unfold Leibniz.complement
  have hup : (shl 1 (if (0 : Nat) == 1 then 0 else 0) - 1 : UInt64) = 0 := by decide
  simp only [hup, Nat.sub_zero]
  have hl0 : lowMask 0 = 0 := by decide
  have hs0 : shl 0 n = 0 := by unfold shl; split <;> simp
  rw [hl0, hs0]
  simp only [UInt64.zero_xor, UInt64.and_zero, UInt64.or_zero, UInt64.xor_zero]
  rw [ite_self, UInt64.toNat_and]
  have hlm : (lowMask n).toNat = 2 ^ n - 1 := by
    unfold lowMask fullMask
    by_cases h : n ≥ 64
    · have : n = 64 := by omega
      subst this; rw [ite_eq_left h]; decide
    · rw [ite_eq_right h]
      have hn' : n < 64 := by omega
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_shl_one hn']; exact Nat.one_le_two_pow),
        toNat_shl_one hn', UInt64.toNat_one]
  rw [hlm]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
  have hnot : (~~~b).toNat.testBit i = (decide (i < 64) && !b.toNat.testBit i) := by
    show (~~~b).toBitVec.toNat.testBit i = (decide (i < 64) && !b.toBitVec.toNat.testBit i)
    rw [UInt64.toBitVec_not, BitVec.testBit_toNat, BitVec.getLsbD_not, BitVec.testBit_toNat]
  rw [hnot]
  by_cases hi : i < n
  · simp [hi, show i < 64 by omega]
  · simp [hi]

end DirectSum.Proofs

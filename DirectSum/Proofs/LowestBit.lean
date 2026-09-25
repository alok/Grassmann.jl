/-
The lowest-set-bit kernels and the metric-factor loop, on all 64-bit masks.

`Bits.lowestBit x = x &&& (0 - x)` isolates the lowest set bit,
`x &&& (x - 1)` clears it, and `Bits.ctz x = popcount (lowestBit x - 1)` is its
index. `TensorBundle.metricProduct` multiplies the metric factors of the set
bits of a mask by popping them in that order. This file proves:

* `exists_lowBit`: every nonzero mask is `2^{t+1} Q + 2^t` for its lowest set
  bit `t`;
* `lowestBit_eq`, `and_sub_one_eq`, `ctz_eq`: the three kernels, for all
  nonzero `UInt64`s (with `popcount_eq_bitCount`);
* `metricProduct_eq`: the loop computes the metric factor
  `Π_{i ∈ b} V[i+1]` (`metricFactor`) of every mask, for every space.
-/
import DirectSum.Proofs.Popcount
import DirectSum.Proofs.Metric
import DirectSum.Parity

namespace DirectSum.Proofs

open Bits

/-! ## The lowest set bit, on `Nat` -/

/-- Every positive number is `2^{t+1} Q + 2^t`: `t` is its lowest set bit. -/
theorem exists_lowBit {X : Nat} (hX : 0 < X) : ∃ t Q, X = 2 ^ (t + 1) * Q + 2 ^ t := by
  induction X using Nat.strongRecOn with
  | _ X ih =>
    rcases Nat.mod_two_eq_zero_or_one X with h | h
    · have hY : 0 < X / 2 := by omega
      obtain ⟨t, Q, e⟩ := ih (X / 2) (by omega) hY
      refine ⟨t + 1, Q, ?_⟩
      rw [Nat.pow_succ 2 (t + 1), Nat.pow_succ 2 t]
      have : X = 2 * (X / 2) := by omega
      rw [this, e]; grind
    · exact ⟨0, X / 2, by simp; omega⟩

/-- Clearing the lowest set bit: `X &&& (X - 1) = X - 2^t`. -/
theorem and_sub_one_nat {t Q : Nat} :
    (2 ^ (t + 1) * Q + 2 ^ t) &&& (2 ^ (t + 1) * Q + 2 ^ t - 1) = 2 ^ (t + 1) * Q := by
  have hlt : 2 ^ t < 2 ^ (t + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have e : 2 ^ (t + 1) * Q + 2 ^ t - 1 = 2 ^ (t + 1) * Q + (2 ^ t - 1) := by
    have := Nat.one_le_two_pow (n := t); omega
  rw [e]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hlt, Nat.testBit_two_pow_mul_add _ (by omega),
    Nat.testBit_two_pow_mul]
  by_cases hi : i < t + 1
  · rw [ite_eq_left hi, ite_eq_left hi]
    have : ¬ (i ≥ t + 1) := by omega
    simp only [this, decide_false, Bool.false_and]
    rw [Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one]
    by_cases h : t = i <;> simp [h] <;> omega
  · rw [ite_eq_right hi, ite_eq_right hi]
    simp [show i ≥ t + 1 by omega]

/-- The two's-complement negative has the same lowest set bit and complementary
bits above it: `X &&& (2^64 - X) = 2^t`. -/
theorem and_neg_nat {t Q : Nat} (hX : 2 ^ (t + 1) * Q + 2 ^ t < 2 ^ 64) :
    (2 ^ (t + 1) * Q + 2 ^ t) &&& (2 ^ 64 - (2 ^ (t + 1) * Q + 2 ^ t)) = 2 ^ t := by
  have ht : t < 64 := by
    have : 2 ^ t < 2 ^ 64 := by omega
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp this
  have hlt : 2 ^ t < 2 ^ (t + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  let k := 63 - t
  have hk : 2 ^ (t + 1) * 2 ^ k = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  have hQ : Q < 2 ^ k := by
    have : 2 ^ (t + 1) * Q < 2 ^ (t + 1) * 2 ^ k := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  -- `2^64 - X = 2^{t+1} Q' + 2^t` with `Q' = 2^k - 1 - Q`, the complement of `Q`
  have e : 2 ^ 64 - (2 ^ (t + 1) * Q + 2 ^ t) = 2 ^ (t + 1) * (2 ^ k - 1 - Q) + 2 ^ t := by
    rw [← hk]
    have h1 : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ, Nat.mul_comm]
    have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_one]
    have h3 : 2 ^ (t + 1) * Q ≤ 2 ^ (t + 1) * (2 ^ k - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h4 : 2 ^ (t + 1) * (2 ^ k - 1) = 2 ^ (t + 1) * 2 ^ k - 2 ^ (t + 1) := by
      rw [Nat.mul_sub, Nat.mul_one]
    have h5 : 2 ^ (t + 1) ≤ 2 ^ (t + 1) * 2 ^ k := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)
    omega
  have hcomp : Q &&& (2 ^ k - 1 - Q) = 0 := by
    have := BitVec.and_not_self (BitVec.ofNat k Q)
    have h := congrArg BitVec.toNat this
    rw [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hQ] at h
    simpa using h
  rw [e]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hlt, Nat.testBit_two_pow_mul_add _ hlt]
  by_cases hi : i < t + 1
  · rw [ite_eq_left hi, ite_eq_left hi, Bool.and_self]
  · rw [ite_eq_right hi, ite_eq_right hi, ← Nat.testBit_and, hcomp, Nat.zero_testBit, Nat.testBit_two_pow]
    simp; omega

/-- `bitCount n (2^t - 1) = t` for `t ≤ n`. -/
theorem bitCount_two_pow_sub_one {n t : Nat} (h : t ≤ n) : bitCount n (2 ^ t - 1) = t := by
  induction n generalizing t with
  | zero => simp at h; subst h; rfl
  | succ n ih =>
    rw [bitCount_succ, Nat.testBit_two_pow_sub_one]
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · rw [ih (by omega)]; simp; omega
    · subst h'
      have : bitCount n (2 ^ (n + 1) - 1) = n := by
        rw [bitCount_congr (a' := 2 ^ n - 1) (fun i hi => by
          rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]; simp; omega)]
        exact ih (Nat.le_refl n)
      rw [this]; simp

/-! ## The `UInt64` kernels -/

/-- `Bits.lowestBit` isolates the lowest set bit. -/
theorem lowestBit_eq {x : UInt64} {t Q : Nat} (hx : x.toNat = 2 ^ (t + 1) * Q + 2 ^ t) :
    (lowestBit x).toNat = 2 ^ t := by
  unfold lowestBit
  have hpos : 0 < x.toNat := by rw [hx]; exact Nat.lt_of_lt_of_le (Nat.two_pow_pos t) (Nat.le_add_left _ _)
  rw [UInt64.toNat_and, UInt64.toNat_sub, UInt64.toNat_zero, Nat.add_zero,
    Nat.mod_eq_of_lt (by have := x.toNat_lt; omega), hx]
  exact and_neg_nat (hx ▸ x.toNat_lt)

/-- `x &&& (x - 1)` clears the lowest set bit. -/
theorem and_sub_one_eq {x : UInt64} {t Q : Nat} (hx : x.toNat = 2 ^ (t + 1) * Q + 2 ^ t) :
    (x &&& (x - 1)).toNat = 2 ^ (t + 1) * Q := by
  have h1 : (1 : UInt64) ≤ x := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_one, hx]; have := Nat.one_le_two_pow (n := t); omega
  rw [UInt64.toNat_and, UInt64.toNat_sub_of_le _ _ h1, UInt64.toNat_one, hx]
  exact and_sub_one_nat

/-- `Bits.ctz` is the index of the lowest set bit. -/
theorem ctz_eq {x : UInt64} {t Q : Nat} (hx : x.toNat = 2 ^ (t + 1) * Q + 2 ^ t) : ctz x = t := by
  unfold ctz
  have ht : t < 64 := by
    have h := x.toNat_lt
    have : 2 ^ t < 2 ^ 64 := by omega
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp this
  have hl := lowestBit_eq hx
  have h1 : (1 : UInt64) ≤ lowestBit x := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_one, hl]; exact Nat.one_le_two_pow
  rw [popcount_eq_bitCount, UInt64.toNat_sub_of_le _ _ h1, hl, UInt64.toNat_one,
    bitCount_two_pow_sub_one (by omega)]

/-! ## The metric-factor loop -/

private theorem bits_low {t Q : Nat} (i : Nat) :
    (2 ^ (t + 1) * Q + 2 ^ t).testBit i = (decide (i = t) || (2 ^ (t + 1) * Q).testBit i) := by
  have hlt : 2 ^ t < 2 ^ (t + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  rw [Nat.testBit_two_pow_mul_add _ hlt, Nat.testBit_two_pow_mul]
  by_cases hi : i < t + 1
  · rw [ite_eq_left hi, Nat.testBit_two_pow]
    have : decide (i ≥ t + 1) = false := by simp; omega
    rw [this, Bool.false_and, Bool.or_false]
    by_cases h : i = t
    · subst h; simp
    · have h' : ¬ t = i := fun e => h e.symm
      simp [h, h']
  · rw [ite_eq_right hi]
    have h1 : decide (i = t) = false := by simp; omega
    have h2 : decide (i ≥ t + 1) = true := by simp; omega
    rw [h1, h2, Bool.false_or, Bool.true_and]

private theorem bit_t_clear {t Q : Nat} : (2 ^ (t + 1) * Q).testBit t = false := by
  rw [Nat.testBit_two_pow_mul]
  have : decide (t ≥ t + 1) = false := by simp
  rw [this, Bool.false_and]

/-- Removing a set bit removes its factor. -/
theorem metricFactor_remove_bit {R : Type _} [Lean.Grind.CommRing R] (g : Nat → R) {n t Q : Nat}
    (ht : t < n) : metricFactor g n (2 ^ (t + 1) * Q + 2 ^ t) = g t * metricFactor g n (2 ^ (t + 1) * Q) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [metricFactor_succ, metricFactor_succ, bits_low n]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with h | h
    · rw [ih h, show decide (n = t) = false by simp; omega, Bool.false_or]
      grind
    · subst h
      rw [bit_t_clear, show decide (t = t) = true by simp, Bool.true_or]
      simp only [ite_true, Bool.false_eq_true, ite_false]
      rw [metricFactor_congr g (m' := 2 ^ (t + 1) * Q) (fun i hi => by
        rw [bits_low i]; simp [show i ≠ t by omega])]
      grind

/-- The bit count drops by one when a set bit is removed. -/
theorem bitCount_remove_bit {n t Q : Nat} (ht : t < n) :
    bitCount n (2 ^ (t + 1) * Q + 2 ^ t) = bitCount n (2 ^ (t + 1) * Q) + 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [bitCount_succ, bitCount_succ, bits_low n]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with h | h
    · rw [ih h, show decide (n = t) = false by simp; omega, Bool.false_or]; omega
    · subst h
      rw [bit_t_clear, show decide (t = t) = true by simp, Bool.true_or]
      rw [bitCount_congr (a' := 2 ^ (t + 1) * Q) (fun i hi => by
        rw [bits_low i]; simp [show i ≠ t by omega])]
      simp

/-- A mask has at most `n` generators among the first `n`. -/
theorem bitCount_le (n x : Nat) : bitCount n x ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => rw [bitCount_succ]; cases x.testBit n <;> simp <;> omega

/-- **`TensorBundle.metricProduct` is the metric factor** `Π_{i ∈ b} V[i+1]` of
every mask, for every space. -/
theorem metricProduct_eq (V : TensorBundle) (b : UInt64) :
    V.metricProduct b = metricFactor (fun i => V.metricAt (i + 1)) 64 b.toNat := by
  unfold TensorBundle.metricProduct
  have key : ∀ fuel (x : UInt64) (acc : Rat), bitCount 64 x.toNat ≤ fuel →
      TensorBundle.metricProduct.go V x acc fuel = acc * metricFactor (fun i => V.metricAt (i + 1)) 64 x.toNat := by
    intro fuel
    induction fuel with
    | zero =>
      intro x acc h
      have : x.toNat = 0 := (bitCount_eq_zero_iff x.toNat_lt).mp (by omega)
      rw [TensorBundle.metricProduct.go, this, metricFactor_zero_mask]; grind
    | succ fuel ih =>
      intro x acc h
      rw [TensorBundle.metricProduct.go]
      by_cases hx0 : x = 0
      · subst hx0; simp
      · rw [ite_eq_right (by simpa using hx0)]
        have hpos : 0 < x.toNat := by
          rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
          · exact absurd (UInt64.toNat_inj.mp (by rw [h0]; rfl)) hx0
          · exact h0
        obtain ⟨t, Q, hx⟩ := exists_lowBit hpos
        have ht : t < 64 := by
          have hlt := x.toNat_lt
          have : 2 ^ t < 2 ^ 64 := by omega
          exact (Nat.pow_lt_pow_iff_right (by decide)).mp this
        rw [ih (x &&& (x - 1)), and_sub_one_eq hx, ctz_eq hx, hx, metricFactor_remove_bit _ ht]
        · grind
        · rw [and_sub_one_eq hx]; rw [hx, bitCount_remove_bit ht] at h; omega
  rw [key 64 b 1 (bitCount_le 64 b.toNat)]
  grind

end DirectSum.Proofs

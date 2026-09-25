/-
Metric factors of diagonal metrics and the blade-product coefficient.

For a diagonal metric `g` (generator `i+1` squares to `g i`), the geometric
product of two basis blades is

  `e_a e_b = (-1)^{σ(a,b)} · Π_{i ∈ a ∧ b} gᵢ · e_{a ⊕ b}`

(`bladeCoef`). The coefficients live in any commutative ring
(`Lean.Grind.CommRing`, so `grind` normalizes ring expressions). The main
results:

* `metricFactor_cocycle`: `g(a∧b)·g((a⊕b)∧c) = g(b∧c)·g(a∧(b⊕c))`, the
  metric half of associativity (it holds generator by generator);
* `bladeCoef_cocycle`: the twisted 2-cocycle identity of the full blade
  coefficient, from `sigma_cocycle` and `metricFactor_cocycle`;
* the special metrics: signatures (`metricFactor_sigMetric`: the factor is the
  sign `(-1)^{#negative shared generators}`), the zero metric (the exterior
  algebra: `bladeCoef_zero`), and the determinant (`metricFactor_mul_compl`).
-/
import DirectSum.Proofs.Sign

namespace DirectSum.Proofs

open Lean.Grind

universe u

variable {R : Type u} [CommRing R]

/-! ## Signs -/

/-- `signOf s = (-1)^s`. -/
def signOf (s : Bool) : R := if s then -1 else 1

@[simp] theorem signOf_false : (signOf false : R) = 1 := rfl

@[simp] theorem signOf_true : (signOf true : R) = -1 := rfl

theorem signOf_xor (s t : Bool) : (signOf (s ^^ t) : R) = signOf s * signOf t := by
  cases s <;> cases t <;> simp [signOf] <;> grind

theorem signOf_mul_self (s : Bool) : (signOf s : R) * signOf s = 1 := by
  cases s <;> simp [signOf] <;> grind

theorem signOf_not (s : Bool) : (signOf (!s) : R) = -signOf s := by
  cases s <;> simp [signOf] <;> grind

/-- `(-1)^k` is the sign of the parity of `k`. -/
theorem neg_one_pow (k : Nat) : ((-1 : R) ^ k) = signOf (k % 2 == 1) := by
  induction k with
  | zero => simp [Semiring.pow_zero]
  | succ k ih =>
    rw [Semiring.pow_succ, ih, odd_add, signOf_xor]
    simp [signOf]

/-! ## Metric factors -/

/-- The metric factor `Π_{i < n, i ∈ m} g i` of the generators in mask `m`. -/
def metricFactor (g : Nat → R) : Nat → Nat → R
  | 0, _ => 1
  | n + 1, m => metricFactor g n m * (if m.testBit n then g n else 1)

theorem metricFactor_succ (g : Nat → R) (n m : Nat) :
    metricFactor g (n + 1) m = metricFactor g n m * (if m.testBit n then g n else 1) := rfl

theorem metricFactor_congr (g : Nat → R) {n m m' : Nat} (h : ∀ i < n, m.testBit i = m'.testBit i) :
    metricFactor g n m = metricFactor g n m' := by
  induction n with
  | zero => rfl
  | succ n ih => rw [metricFactor_succ, metricFactor_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- The metric factor only reads the metric below the width. -/
theorem metricFactor_congr_metric {g g' : Nat → R} {n : Nat} (h : ∀ i < n, g i = g' i) (m : Nat) :
    metricFactor g n m = metricFactor g' n m := by
  induction n with
  | zero => rfl
  | succ n ih => rw [metricFactor_succ, metricFactor_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- The metric factor of a single generator is its square. -/
theorem metricFactor_two_pow (g : Nat → R) {n i : Nat} (hi : i < n) : metricFactor g n (2 ^ i) = g i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [metricFactor_succ, Nat.testBit_two_pow]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
    · rw [ih h, ite_eq_right (by simp; omega), Semiring.mul_one]
    · subst h
      have hz : ∀ m ≤ i, metricFactor g m (2 ^ i) = 1 := by
        intro m hm
        induction m with
        | zero => rfl
        | succ m ihm =>
          rw [metricFactor_succ, ihm (by omega), Nat.testBit_two_pow, ite_eq_right (by simp; omega),
            Semiring.mul_one]
      rw [hz i (Nat.le_refl i), ite_eq_left (by simp), Semiring.one_mul]

@[simp] theorem metricFactor_zero_mask (g : Nat → R) (n : Nat) : metricFactor g n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [metricFactor_succ, ih, Semiring.mul_one]

/-- Widening the space does not change the metric factor of a blade that fits. -/
theorem metricFactor_of_lt (g : Nat → R) {n m a : Nat} (hnm : n ≤ m) (ha : a < 2 ^ n) :
    metricFactor g m a = metricFactor g n a := by
  induction m with
  | zero => rw [Nat.le_zero.mp hnm]
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le hnm with h | h
    · rw [metricFactor_succ, ih (by omega),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))]
      simp [Semiring.mul_one]
    · rw [h]

/-- **Multiplicativity of the metric factor** along the associativity square:
`g(a∧b)·g((a⊕b)∧c) = g(b∧c)·g(a∧(b⊕c))`. Generator by generator both sides
count the same factor (it is `gᵢ` exactly when at least two of `a, b, c`
contain `i`). -/
theorem metricFactor_cocycle (g : Nat → R) (n a b c : Nat) :
    metricFactor g n (a &&& b) * metricFactor g n ((a ^^^ b) &&& c)
      = metricFactor g n (b &&& c) * metricFactor g n (a &&& (b ^^^ c)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [metricFactor_succ, Nat.testBit_and, Nat.testBit_xor]
    cases a.testBit n <;> cases b.testBit n <;> cases c.testBit n <;> simp <;> grind

/-- The metric factors of a blade and of its complement make up the
determinant `Π_{i<n} gᵢ` (the factor of the pseudoscalar `2ⁿ - 1`). -/
theorem metricFactor_mul_compl (g : Nat → R) (n a : Nat) :
    metricFactor g n a * metricFactor g n (a ^^^ (2 ^ n - 1)) = metricFactor g n (2 ^ n - 1) := by
  have key : ∀ m ≤ n, metricFactor g m a * metricFactor g m (a ^^^ (2 ^ n - 1))
      = metricFactor g m (2 ^ n - 1) := by
    intro m hm
    induction m with
    | zero => exact Semiring.mul_one _
    | succ m ih =>
      have ih := ih (by omega)
      simp only [metricFactor_succ, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
        show m < n from by omega, decide_true]
      cases a.testBit m <;> simp <;> grind
  exact key n (Nat.le_refl n)

/-! ## The blade-product coefficient -/

/-- The coefficient of the geometric product of basis blades in the diagonal
metric `g`: `e_a e_b = bladeCoef g n a b · e_{a⊕b}`. -/
def bladeCoef (g : Nat → R) (n a b : Nat) : R := signOf (sigma n a b) * metricFactor g n (a &&& b)

/-- **The twisted 2-cocycle identity** of the blade coefficient, for every width,
every diagonal metric over every commutative ring, and all masks:
`c(a,b)·c(a⊕b,c) = c(b,c)·c(a,b⊕c)`. This *is* associativity of the geometric
product on basis blades: `(e_a e_b) e_c` and `e_a (e_b e_c)` are both multiples
of `e_{a⊕b⊕c}`, with exactly these coefficients. -/
theorem bladeCoef_cocycle (g : Nat → R) (n a b c : Nat) :
    bladeCoef g n a b * bladeCoef g n (a ^^^ b) c = bladeCoef g n b c * bladeCoef g n a (b ^^^ c) := by
  have hs : (signOf (sigma n a b) : R) * signOf (sigma n (a ^^^ b) c)
      = signOf (sigma n b c) * signOf (sigma n a (b ^^^ c)) := by
    rw [← signOf_xor, ← signOf_xor, sigma_cocycle]
  have hm := metricFactor_cocycle g n a b c
  unfold bladeCoef
  grind

theorem bladeCoef_zero_left (g : Nat → R) (n b : Nat) : bladeCoef g n 0 b = 1 := by
  simp [bladeCoef, Semiring.mul_one]

theorem bladeCoef_zero_right (g : Nat → R) (n a : Nat) : bladeCoef g n a 0 = 1 := by
  simp [bladeCoef, Semiring.mul_one]

theorem bladeCoef_congr (g : Nat → R) {n a a' b b' : Nat} (ha : ∀ i < n, a.testBit i = a'.testBit i)
    (hb : ∀ i < n, b.testBit i = b'.testBit i) : bladeCoef g n a b = bladeCoef g n a' b' := by
  unfold bladeCoef
  rw [sigma_congr ha hb, metricFactor_congr g (m' := a' &&& b') (fun i hi => by simp [ha i hi, hb i hi])]

/-! ## Special metrics -/

/-- The metric of a signature `s` (Julia `Signature`): generator `i+1` squares
to `-1` iff bit `i` of `s` is set. -/
def sigMetric (s : Nat) (i : Nat) : R := signOf (s.testBit i)

/-- In a signature metric the metric factor is the sign of the number of
negative generators in the mask. -/
theorem metricFactor_sigMetric (s n m : Nat) :
    metricFactor (sigMetric s : Nat → R) n m = signOf (bitParity n (m &&& s)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [metricFactor_succ, ih, bitParity_succ, signOf_xor, Nat.testBit_and]
    cases m.testBit n <;> simp [sigMetric, Semiring.mul_one]

/-- The blade coefficient of a signature metric is the sign
`(-1)^{σ(a,b) + #(a ∧ b ∧ s)}`: Julia's `parityjoin` (`DirectSum.parityjoin`). -/
theorem bladeCoef_sigMetric (s n a b : Nat) :
    bladeCoef (sigMetric s : Nat → R) n a b = signOf (sigma n a b ^^ bitParity n (a &&& b &&& s)) := by
  rw [bladeCoef, metricFactor_sigMetric, signOf_xor]

/-- The zero metric has factor `1` on the empty mask and `0` on every other. -/
theorem metricFactor_zero_metric (n m : Nat) :
    metricFactor (fun _ => (0 : R)) n m = if bitCount n m = 0 then 1 else 0 := by
  induction n with
  | zero => simp [metricFactor]
  | succ n ih =>
    rw [metricFactor_succ, ih, bitCount_succ]
    cases m.testBit n <;> by_cases h : bitCount n m = 0 <;> simp [h, Semiring.mul_one, Semiring.mul_zero]

/-- **The exterior algebra is the Clifford algebra of the zero metric**: its
blade coefficient is the reordering sign on disjoint blades and `0` otherwise. -/
theorem bladeCoef_zero_metric (n a b : Nat) :
    bladeCoef (fun _ => (0 : R)) n a b
      = if bitCount n (a &&& b) = 0 then signOf (sigma n a b) else 0 := by
  rw [bladeCoef, metricFactor_zero_metric]
  split <;> simp [Semiring.mul_one, Semiring.mul_zero]

/-- A blade has grade `0` exactly when it is empty (masks below `2ⁿ`). -/
theorem bitCount_eq_zero_iff {n m : Nat} (hm : m < 2 ^ n) : bitCount n m = 0 ↔ m = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    by_cases hi : i < n
    · have key : ∀ k ≤ n, bitCount k m = 0 → ∀ j < k, m.testBit j = false := by
        intro k _ hk
        induction k with
        | zero => intro j hj; omega
        | succ k ih =>
          rw [bitCount_succ] at hk
          intro j hj
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj' | hj'
          · exact ih (by omega) (by omega) j hj'
          · subst hj'; cases h' : m.testBit j <;> simp_all
      exact key n (Nat.le_refl n) h i hi
    · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega)))
  · intro h; subst h; exact bitCount_zero_mask n

end DirectSum.Proofs

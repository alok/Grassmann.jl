/-
The canonical reordering sign of basis blades, for every number of generators.

A basis blade `e_A` of an `n`-generator space is the bitmask `a` with bit `i`
set iff generator `i+1` occurs in `A` (`DirectSum.Bits`). Multiplying two blades
`e_A e_B` and sorting the concatenated index word takes a number of adjacent
transpositions of the same parity as the number of *inversions*

  `inv(a, b) = #{(i, j) | j < i < n, i ∈ a, j ∈ b}`,

and the reordering sign is `σ(a, b) = inv(a, b) mod 2`. Everything here is
stated for plain `Nat` masks and an arbitrary width `n`, with induction on the
highest generator. The main results:

* `sigma_xor_left`, `sigma_xor_right`: `σ` is bilinear over `𝔽₂` (xor in each
  argument). Everything else follows from this.
* `sigma_cocycle`: the 2-cocycle identity
  `σ(a,b) + σ(a⊕b,c) = σ(b,c) + σ(a,b⊕c)`, the combinatorial heart of the
  associativity of the geometric product.
* `sigma_swap`/`sigma_add_sigma_swap`: `σ(a,b) + σ(b,a) = |a||b| - |a∧b|`
  (mod 2), the source of every commutation sign (`eᵢeⱼ = -eⱼeᵢ`, graded
  commutativity of `∧`, the double complement).
* `sigma_self`: `σ(a,a)` is the reversion sign `parityreverse |a|`.
* `reorderParitySpec_eq_sigma`: the repository's naive specification
  (`Bits.reorderParitySpec`) is this `σ`.
-/
import DirectSum.Bits
import Leibniz.Generic

namespace DirectSum.Proofs

/-! ## Grade and grade parity -/

/-- `bitCount n a`: the number of set bits of `a` among positions `0, …, n-1`
(the grade of the blade `a` in an `n`-generator space). -/
def bitCount : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, a => bitCount n a + (a.testBit n).toNat

/-- `bitParity n a`: whether `bitCount n a` is odd. -/
def bitParity (n a : Nat) : Bool := bitCount n a % 2 == 1

/-- The inversion count `#{(i, j) | j < i < n, a has bit i, b has bit j}`: the
number of adjacent transpositions (mod 2) that sort the word `e_a e_b`. -/
def inversions : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, a, b => inversions n a b + (if a.testBit n then bitCount n b else 0)

/-- The canonical reordering sign `σ(a, b)` of `e_a e_b` in an `n`-generator
space: `true` iff the number of inversions is odd. -/
def sigma (n a b : Nat) : Bool := inversions n a b % 2 == 1

/-! ## Parity arithmetic -/

/-- Oddness of a sum is the xor of the oddnesses. -/
theorem odd_add (x y : Nat) : ((x + y) % 2 == 1) = ((x % 2 == 1) ^^ (y % 2 == 1)) := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one y with h' | h' <;> simp [Nat.add_mod, h, h']

/-- Oddness of a product is the conjunction of the oddnesses. -/
theorem odd_mul (x y : Nat) : ((x * y) % 2 == 1) = ((x % 2 == 1) && (y % 2 == 1)) := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one y with h' | h' <;> simp [Nat.mul_mod, h, h']

private theorem odd_ite (c : Bool) (k : Nat) :
    ((if c then k else 0) % 2 == 1) = (c && (k % 2 == 1)) := by
  cases c <;> simp

private theorem odd_toNat (c : Bool) : (c.toNat % 2 == 1) = c := by cases c <;> rfl

/-! ## Recursion on the highest generator -/

@[simp] theorem bitCount_zero (a : Nat) : bitCount 0 a = 0 := rfl

/-- The grade on `n+1` generators counts the top generator too. -/
theorem bitCount_succ (n a : Nat) : bitCount (n + 1) a = bitCount n a + (a.testBit n).toNat := rfl

/-- No generators, even grade. -/
@[simp] theorem bitParity_zero (a : Nat) : bitParity 0 a = false := rfl

/-- The grade parity on `n+1` generators flips with the top generator. -/
theorem bitParity_succ (n a : Nat) : bitParity (n + 1) a = (bitParity n a ^^ a.testBit n) := by
  simp only [bitParity, bitCount_succ, odd_add, odd_toNat]

/-- No generators, no inversions. -/
@[simp] theorem sigma_zero (a b : Nat) : sigma 0 a b = false := rfl

/-- `σ` on `n+1` generators: the new top generator of `a` jumps over the
generators of `b` below it. -/
theorem sigma_succ (n a b : Nat) :
    sigma (n + 1) a b = (sigma n a b ^^ (a.testBit n && bitParity n b)) := by
  simp only [sigma, inversions, odd_add, odd_ite, bitParity]

/-! ## Bits above the width do not matter -/

theorem bitCount_congr {n a a' : Nat} (h : ∀ i < n, a.testBit i = a'.testBit i) :
    bitCount n a = bitCount n a' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bitCount_succ, bitCount_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- The grade parity only reads the mask below the width. -/
theorem bitParity_congr {n a a' : Nat} (h : ∀ i < n, a.testBit i = a'.testBit i) :
    bitParity n a = bitParity n a' := by
  simp only [bitParity, bitCount_congr h]

/-- `σ` only reads the masks below the width. -/
theorem sigma_congr {n a a' b b' : Nat} (ha : ∀ i < n, a.testBit i = a'.testBit i)
    (hb : ∀ i < n, b.testBit i = b'.testBit i) : sigma n a b = sigma n a' b' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sigma_succ, sigma_succ, ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)),
      ha n (by omega), bitParity_congr (fun i hi => hb i (by omega))]

private theorem testBit_of_lt {a n i : Nat} (ha : a < 2 ^ n) (hi : n ≤ i) : a.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hi))

/-- Widening the space does not change the grade of a blade that fits. -/
theorem bitCount_of_lt {n m a : Nat} (hnm : n ≤ m) (ha : a < 2 ^ n) : bitCount m a = bitCount n a := by
  induction m with
  | zero => rw [Nat.le_zero.mp hnm]
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le hnm with h | h
    · rw [bitCount_succ, ih (by omega), testBit_of_lt ha (by omega)]; rfl
    · rw [h]

/-- Widening the space does not change the grade parity of a blade that fits. -/
theorem bitParity_of_lt {n m a : Nat} (hnm : n ≤ m) (ha : a < 2 ^ n) :
    bitParity m a = bitParity n a := by
  simp only [bitParity, bitCount_of_lt hnm ha]

/-- Widening the space does not change the reordering sign of blades that fit:
`σ` is really a function of the two blades, not of the ambient dimension. -/
theorem sigma_of_lt {n m a b : Nat} (hnm : n ≤ m) (ha : a < 2 ^ n) : sigma m a b = sigma n a b := by
  induction m with
  | zero => rw [Nat.le_zero.mp hnm]
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le hnm with h | h
    · rw [sigma_succ, ih (by omega), testBit_of_lt ha (by omega)]; simp
    · rw [h]

/-! ## Bilinearity over 𝔽₂ -/

private theorem bxor_xor_xor (p q x y : Bool) : ((p ^^ q) ^^ (x ^^ y)) = ((p ^^ x) ^^ (q ^^ y)) := by
  decide +revert

/-- The grade parity is additive: `|a ⊕ b| ≡ |a| + |b| (mod 2)`. -/
theorem bitParity_xor (n a b : Nat) : bitParity n (a ^^^ b) = (bitParity n a ^^ bitParity n b) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bitParity_succ, bitParity_succ, bitParity_succ, ih, Nat.testBit_xor, bxor_xor_xor]

private theorem bxor_left (s₁ s₂ x y p : Bool) :
    ((s₁ ^^ s₂) ^^ ((x ^^ y) && p)) = ((s₁ ^^ (x && p)) ^^ (s₂ ^^ (y && p))) := by
  decide +revert

private theorem bxor_right (s₁ s₂ x p q : Bool) :
    ((s₁ ^^ s₂) ^^ (x && (p ^^ q))) = ((s₁ ^^ (x && p)) ^^ (s₂ ^^ (x && q))) := by
  decide +revert

/-- `σ` is additive in its first argument. -/
theorem sigma_xor_left (n a a' b : Nat) : sigma n (a ^^^ a') b = (sigma n a b ^^ sigma n a' b) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sigma_succ, sigma_succ, sigma_succ, ih, Nat.testBit_xor, bxor_left]

/-- `σ` is additive in its second argument. -/
theorem sigma_xor_right (n a b b' : Nat) : sigma n a (b ^^^ b') = (sigma n a b ^^ sigma n a b') := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sigma_succ, sigma_succ, sigma_succ, ih, bitParity_xor, bxor_right]

/-- The unit blade reorders nothing on the left: `σ(0, b) = 0`. -/
@[simp] theorem sigma_zero_left (n b : Nat) : sigma n 0 b = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sigma_succ, ih]

/-- The empty blade has grade `0`. -/
@[simp] theorem bitCount_zero_mask (n : Nat) : bitCount n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bitCount_succ, ih]

/-- The unit blade reorders nothing on the right: `σ(a, 0) = 0`. -/
@[simp] theorem sigma_zero_right (n a : Nat) : sigma n a 0 = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sigma_succ, ih, bitParity]

/-- **The 2-cocycle identity** of the reordering sign, for every width `n` and
all masks: `σ(a,b) + σ(a⊕b, c) = σ(b,c) + σ(a, b⊕c)` in `𝔽₂`. Together with
the multiplicativity of the metric factor (`DirectSum.Proofs.Metric`) this is
exactly associativity of the geometric product on basis blades. -/
theorem sigma_cocycle (n a b c : Nat) :
    (sigma n a b ^^ sigma n (a ^^^ b) c) = (sigma n b c ^^ sigma n a (b ^^^ c)) := by
  rw [sigma_xor_left, sigma_xor_right]
  cases sigma n a b <;> cases sigma n b c <;> cases sigma n a c <;> rfl

/-! ## Commutation signs -/

private theorem bswap_step (s₁ s₂ α β pa pb pk : Bool) (ih : (s₁ ^^ s₂) = ((pa && pb) ^^ pk)) :
    ((s₁ ^^ (α && pb)) ^^ (s₂ ^^ (β && pa))) = (((pa ^^ α) && (pb ^^ β)) ^^ (pk ^^ (α && β))) := by
  revert ih; revert s₁ s₂ α β pa pb pk; decide

/-- **Swapping the factors**, parity form: `σ(a,b) + σ(b,a) ≡ |a|·|b| + |a∧b|`. -/
theorem sigma_swap (n a b : Nat) :
    (sigma n a b ^^ sigma n b a) = ((bitParity n a && bitParity n b) ^^ bitParity n (a &&& b)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sigma_succ, sigma_succ, bitParity_succ, bitParity_succ, bitParity_succ, Nat.testBit_and]
    exact bswap_step _ _ _ _ _ _ _ ih

/-- The common part of two blades has at most the grade of each. -/
theorem bitCount_and_le_left (n a b : Nat) : bitCount n (a &&& b) ≤ bitCount n a := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    rw [bitCount_succ, bitCount_succ, Nat.testBit_and]
    cases a.testBit n <;> cases b.testBit n <;> simp [Bool.toNat] <;> omega

/-- The common part of two blades is symmetric. -/
theorem bitCount_and_comm (n a b : Nat) : bitCount n (a &&& b) = bitCount n (b &&& a) := by
  rw [Nat.and_comm]

/-- `|a∧b| ≤ |a|·|b|`, so the Nat subtraction in `sigma_add_sigma_swap` is exact. -/
theorem bitCount_and_le_mul (n a b : Nat) : bitCount n (a &&& b) ≤ bitCount n a * bitCount n b := by
  have h₁ := bitCount_and_le_left n a b
  have h₂ : bitCount n (a &&& b) ≤ bitCount n b := by
    rw [bitCount_and_comm]; exact bitCount_and_le_left n b a
  rcases Nat.eq_zero_or_pos (bitCount n b) with h | h
  · omega
  · exact Nat.le_trans h₁ (Nat.le_mul_of_pos_right _ h)

/-- **Swapping the factors**: `σ(a,b) + σ(b,a) ≡ |a||b| - |a∧b| (mod 2)`. Two
blades commute up to the sign `(-1)^{|a||b| - |a∧b|}`: disjoint blades of grades
`p`, `q` pick up `(-1)^{pq}`, distinct generators anticommute. -/
theorem sigma_add_sigma_swap (n a b : Nat) :
    (sigma n a b ^^ sigma n b a) =
      ((bitCount n a * bitCount n b - bitCount n (a &&& b)) % 2 == 1) := by
  rw [sigma_swap]
  have hle := bitCount_and_le_mul n a b
  have : (bitCount n a * bitCount n b - bitCount n (a &&& b)) % 2
      = (bitCount n a * bitCount n b + bitCount n (a &&& b)) % 2 := by omega
  rw [this, odd_add, odd_mul]; rfl

/-! ## The reversion sign -/

private theorem odd_half_succ (k : Nat) :
    ((k + 1) / 2 % 2 == 1) = ((k / 2 % 2 == 1) ^^ (k % 2 == 1)) := by
  have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases h4 with h | h | h | h
  · have e1 : (k + 1) / 2 % 2 = 0 := by omega
    have e2 : k / 2 % 2 = 0 := by omega
    have e3 : k % 2 = 0 := by omega
    simp [e1, e2, e3]
  · have e1 : (k + 1) / 2 % 2 = 1 := by omega
    have e2 : k / 2 % 2 = 0 := by omega
    have e3 : k % 2 = 1 := by omega
    simp [e1, e2, e3]
  · have e1 : (k + 1) / 2 % 2 = 1 := by omega
    have e2 : k / 2 % 2 = 1 := by omega
    have e3 : k % 2 = 0 := by omega
    simp [e1, e2, e3]
  · have e1 : (k + 1) / 2 % 2 = 0 := by omega
    have e2 : k / 2 % 2 = 1 := by omega
    have e3 : k % 2 = 1 := by omega
    simp [e1, e2, e3]

private theorem parityreverse_eq (k : Nat) : Leibniz.parityreverse k = (k / 2 % 2 == 1) := by
  unfold Leibniz.parityreverse
  have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases h4 with h | h | h | h
  · have e : k / 2 % 2 = 0 := by omega
    simp [h, e]
  · have e : k / 2 % 2 = 0 := by omega
    simp [h, e]
  · have e : k / 2 % 2 = 1 := by omega
    simp [h, e]
  · have e : k / 2 % 2 = 1 := by omega
    simp [h, e]

/-- `σ(a,a)` counts the pairs inside `a`, `C(|a|,2)`, so it is the reversion
sign: `e_a e_a = (-1)^{σ(a,a)} Π gᵢ`, and reversing a grade-`k` blade gives
`(-1)^{k(k-1)/2}`, Julia's `parityreverse` (`Leibniz.parityreverse`). -/
theorem sigma_self (n a : Nat) : sigma n a a = Leibniz.parityreverse (bitCount n a) := by
  rw [parityreverse_eq]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sigma_succ, ih, bitCount_succ, bitParity]
    cases a.testBit n
    · simp
    · simp only [Bool.toNat_true, Bool.true_and]; rw [odd_half_succ]

/-! ## Grades of combined blades -/

/-- `|a ⊕ b| + 2|a ∧ b| = |a| + |b|`: the symmetric difference loses the common
generators twice. -/
theorem bitCount_xor_add (n a b : Nat) :
    bitCount n (a ^^^ b) + 2 * bitCount n (a &&& b) = bitCount n a + bitCount n b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bitCount_succ, Nat.testBit_xor, Nat.testBit_and]
    cases a.testBit n <;> cases b.testBit n <;> simp [Bool.toNat] <;> omega

/-- `|a ∧ b| = |b|` exactly when `b ⊆ a` (below the width). -/
theorem bitCount_and_eq_iff (n a b : Nat) :
    bitCount n (a &&& b) = bitCount n b ↔ ∀ i < n, b.testBit i = true → a.testBit i = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hle : bitCount n (a &&& b) ≤ bitCount n b := by
      rw [bitCount_and_comm]; exact bitCount_and_le_left n b a
    simp only [bitCount_succ, Nat.testBit_and]
    constructor
    · intro h i hi hb
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi' | hi'
      · have : bitCount n (a &&& b) = bitCount n b := by
          cases ha : a.testBit n <;> cases hb : b.testBit n <;> simp [ha, hb, Bool.toNat] at h <;> omega
        exact (ih.mp this) i hi' hb
      · subst hi'
        cases ha : a.testBit i <;> simp [ha, hb, Bool.toNat] at h ⊢; omega
    · intro h
      have h' := ih.mpr fun i hi => h i (by omega)
      have hn := h n (by omega)
      cases ha : a.testBit n <;> cases hb : b.testBit n <;> simp_all [Bool.toNat]

/-- The complement of a blade in `n` generators has the complementary grade. -/
theorem bitCount_xor_allOnes (n x : Nat) : bitCount n (x ^^^ (2 ^ n - 1)) + bitCount n x = n := by
  have key : ∀ m ≤ n, bitCount m (x ^^^ (2 ^ n - 1)) + bitCount m x = m := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      have ih := ih (by omega)
      simp only [bitCount_succ, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, show m < n from by omega,
        decide_true]
      cases x.testBit m <;> simp [Bool.toNat] <;> omega
  exact key n (Nat.le_refl n)

/-- A single generator has grade one. -/
theorem bitCount_two_pow {n i : Nat} (hi : i < n) : bitCount n (2 ^ i) = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [bitCount_succ, Nat.testBit_two_pow]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
    · rw [ih h]; simp; omega
    · subst h
      have : bitCount i (2 ^ i) = 0 := by
        -- `2 ^ i` has no bits below `i`
        have hz : ∀ m ≤ i, bitCount m (2 ^ i) = 0 := by
          intro m hm
          induction m with
          | zero => rfl
          | succ m ihm => rw [bitCount_succ, ihm (by omega), Nat.testBit_two_pow]; simp; omega
        exact hz i (Nat.le_refl i)
      rw [this]; simp

/-! ## Xor-sums

`xorSum f n = f 0 ^^ … ^^ f (n-1)`, the form in which the fast bit-parallel
implementations (`DirectSum.Proofs.UInt64`) compute `bitParity` and `σ`. -/

/-- `f 0 ^^ f 1 ^^ … ^^ f (n-1)`. -/
def xorSum (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => xorSum f n ^^ f n

/-- Xor-sums of summands that agree below `n` agree. -/
theorem xorSum_congr {f f' : Nat → Bool} {n : Nat} (h : ∀ i < n, f i = f' i) :
    xorSum f n = xorSum f' n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [xorSum]; rw [ih (fun i hi => h i (by omega)), h n (by omega)]

/-- Truncating the summand at `m` truncates the sum. -/
theorem xorSum_and_lt (f : Nat → Bool) {m n : Nat} (h : m ≤ n) :
    xorSum (fun k => f k && decide (k < m)) n = xorSum f m := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]; rfl
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · simp only [xorSum]; rw [ih (by omega)]; simp [show ¬ n < m by omega]
    · subst h'; simp only [xorSum]
      rw [xorSum_congr (f' := f) (fun i hi => by simp; omega)]; simp

/-- The grade parity is the xor of the bits. -/
theorem bitParity_eq_xorSum (n a : Nat) : bitParity n a = xorSum a.testBit n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bitParity_succ, ih]; rfl

/-- `σ` as a xor-sum: `⨁_{i<n} aᵢ ∧ (parity of the bits of b below i)`. -/
theorem sigma_eq_xorSum (n a b : Nat) :
    sigma n a b = xorSum (fun i => a.testBit i && bitParity i b) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sigma_succ, ih]; rfl

/-! ## The repository's naive specification -/

private theorem foldl_count (b : Nat) (l : List Nat) (c : Nat) :
    l.foldl (fun c j => if b.testBit j then c + 1 else c) c
      = c + l.foldl (fun c j => if b.testBit j then c + 1 else c) 0 := by
  induction l generalizing c with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih, ih (if b.testBit x then 0 + 1 else 0)]
    cases b.testBit x <;> simp <;> omega

private theorem foldl_range_count (b n : Nat) :
    (List.range n).foldl (fun c j => if b.testBit j then c + 1 else c) 0 = bitCount n b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, bitCount_succ]
    cases h : b.testBit n <;> simp [h]

private theorem foldl_inversions (a b n : Nat) :
    (List.range n).foldl (fun c i =>
      if a.testBit i then (List.range i).foldl (fun c j => if b.testBit j then c + 1 else c) c else c) 0
      = inversions n a b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, inversions]
    cases a.testBit n
    · simp
    · simp only [ite_true]; rw [foldl_count, foldl_range_count]

/-- The naive specification `Bits.reorderParitySpec` of the repository (pairs
counted with two nested folds) is `σ`. -/
theorem reorderParitySpec_eq_sigma (n a b : Nat) : Bits.reorderParitySpec n a b = sigma n a b := by
  unfold Bits.reorderParitySpec sigma
  rw [foldl_inversions]

end DirectSum.Proofs

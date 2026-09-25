/-
Ordered monomials in mathlib's `CliffordAlgebra` of a diagonal form.

Fix a quadratic form `Q` on `Rⁿ = Fin n → R` that is diagonal in the standard
basis with weights `g` (`hQ : ∀ v, Q v = Σᵢ gᵢ vᵢ²`, e.g.
`QuadraticMap.weightedSumSquares R g`). For a blade mask `a` the **ordered
monomial** is

  `monomial Q a = ι(e_{i₁}) ι(e_{i₂}) ⋯ ι(e_{iₖ})`,  `i₁ < i₂ < ⋯ < iₖ` the bits of `a`,

built by `monoBelow Q k m` (the bits of `m` below position `k`, multiplied on the
right one position at a time: the same recursion on the top generator as
`DirectSum.Proofs.inversions` and `metricFactor`).

The main theorem, `gen_mul_monomial`, is the multiplication table of a
generator against a monomial **inside mathlib's algebra**:

  `ι(eᵢ) · monomial a = coef g eᵢ a • monomial (eᵢ ⊕ a)`

with exactly the spec's blade coefficient `coef g` (reordering sign times metric
factor). It is proved by induction on the width from the Clifford relations
`ι(eᵢ)² = gᵢ` and `ι(eᵢ)ι(eⱼ) = -ι(eⱼ)ι(eᵢ)` alone, over every commutative ring
(no `Invertible 2`). This is the combinatorial half of the isomorphism
`CliffordAlgebra Q ≃ₐ[R] Cl g` (`GrassmannBridge.Clifford`).
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import GrassmannBridge.Algebra

namespace Grassmann.Bridge

open Grassmann.Spec DirectSum.Proofs

variable {R : Type*} [CommRing R] {n : ℕ} (Q : QuadraticForm R (Fin n → R)) {g : Fin n → R}

/-! ## Generators and monomials -/

/-- The generator `ι(eᵢ₊₁)` at the 0-based position `i` (`0` past the dimension). -/
noncomputable def genAt (i : ℕ) : CliffordAlgebra Q :=
  if h : i < n then CliffordAlgebra.ι Q (Pi.single ⟨i, h⟩ 1) else 0

/-- The factor at position `k` of the monomial of `m`: `ι(e_k)` if bit `k` of `m` is set, else `1`. -/
noncomputable def factor (k m : ℕ) : CliffordAlgebra Q := if m.testBit k then genAt Q k else 1

/-- `monoBelow Q k m`: the increasing product of the generators at the set bits of `m` below `k`. -/
noncomputable def monoBelow : ℕ → ℕ → CliffordAlgebra Q
  | 0, _ => 1
  | k + 1, m => monoBelow k m * factor Q k m

/-- **The ordered monomial** of the blade `a`: `ι(e_{i₁}) ⋯ ι(e_{iₖ})` over its bits in increasing order. -/
noncomputable def monomial (a : BitVec n) : CliffordAlgebra Q := monoBelow Q n a.toNat

theorem monoBelow_zero (m : ℕ) : monoBelow Q 0 m = 1 := rfl

theorem monoBelow_succ (k m : ℕ) : monoBelow Q (k + 1) m = monoBelow Q k m * factor Q k m := rfl

/-- The monomial below `k` only reads the bits below `k`. -/
theorem monoBelow_congr {k m m' : ℕ} (h : ∀ j < k, m.testBit j = m'.testBit j) :
    monoBelow Q k m = monoBelow Q k m' := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [monoBelow_succ, monoBelow_succ, ih (fun j hj => h j (by omega))]
    unfold factor
    rw [h k (by omega)]


/-- The monomial of the empty mask is `1`. -/
theorem monoBelow_zero_mask (k : ℕ) : monoBelow Q k 0 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [monoBelow_succ, ih]; simp [factor]

/-- The monomial of the empty blade is `1`. -/
@[simp] theorem monomial_zero : monomial Q (0 : BitVec n) = 1 :=
  monoBelow_zero_mask Q n

/-! ## The Clifford relations of the generators -/

section Relations

variable {Q}
variable (hQ : ∀ v, Q v = ∑ i, g i * (v i * v i))
include hQ

/-- `Q(eᵢ) = gᵢ`. -/
theorem Q_single (i : Fin n) : Q (Pi.single i 1) = g i := by
  rw [hQ]
  simp [Pi.single_apply]

/-- Distinct standard basis vectors are orthogonal for a diagonal form. -/
theorem isOrtho_single {i j : Fin n} (hij : i ≠ j) : Q.IsOrtho (Pi.single i 1) (Pi.single j 1) := by
  rw [QuadraticMap.isOrtho_def, hQ, hQ, hQ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.add_apply, ← mul_add]
  congr 1
  by_cases hk : k = i
  · subst hk; simp [hij]
  · by_cases hk' : k = j
    · subst hk'; simp [hk]
    · simp [hk, hk']

/-- `ι(eᵢ)² = gᵢ` in mathlib's Clifford algebra. -/
theorem genAt_mul_self {i : ℕ} (hi : i < n) :
    genAt Q i * genAt Q i = algebraMap R _ (g ⟨i, hi⟩) := by
  simp only [genAt, hi, ↓reduceDIte]
  rw [CliffordAlgebra.ι_sq_scalar, Q_single hQ]

/-- `ι(eᵢ) ι(eⱼ) = -ι(eⱼ) ι(eᵢ)` for distinct generators. -/
theorem genAt_mul_genAt_comm {i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    genAt Q i * genAt Q j = -(genAt Q j * genAt Q i) := by
  simp only [genAt, hi, hj, ↓reduceDIte]
  exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (isOrtho_single hQ fun h => hij (congrArg Fin.val h))

/-- A generator commutes past one factor, up to the sign of that factor. -/
theorem genAt_mul_factor {i k : ℕ} (hi : i < n) (hk : k < n) (hik : i ≠ k) (m : ℕ) :
    genAt Q i * factor Q k m = (signOf (m.testBit k) : R) • (factor Q k m * genAt Q i) := by
  unfold factor
  cases m.testBit k
  · simp
  · simp [genAt_mul_genAt_comm hQ hi hk hik]

/-- **Commuting a generator past a lower monomial**: for `k ≤ i`,
`ι(eᵢ) · monoBelow k m = (-1)^{|m below k|} · monoBelow k m · ι(eᵢ)`. -/
theorem genAt_mul_monoBelow_of_le {i k : ℕ} (hi : i < n) (hki : k ≤ i) (m : ℕ) :
    genAt Q i * monoBelow Q k m = (signOf (bitParity k m) : R) • (monoBelow Q k m * genAt Q i) := by
  induction k with
  | zero => simp [monoBelow_zero]
  | succ k ih =>
    rw [monoBelow_succ, ← mul_assoc, ih (by omega), smul_mul_assoc, mul_assoc,
      genAt_mul_factor hQ hi (by omega) (by omega), mul_smul_comm, smul_smul, ← mul_assoc,
      bitParity_succ, signOf_xor]

/-- **A generator times a monomial, below position `k`** (`i < k ≤ n`):
`ι(eᵢ) · monoBelow k m = (-1)^{σₖ(eᵢ, m)} · (gᵢ if i ∈ m) · monoBelow k (m ⊕ eᵢ)`,
by induction on `k` along the recursion of `σ` (`sigma_succ`). -/
theorem genAt_mul_monoBelow {i k : ℕ} (hik : i < k) (hkn : k ≤ n) (m : ℕ) :
    genAt Q i * monoBelow Q k m
      = ((signOf (sigma k (2 ^ i) m) : R) * (if m.testBit i then extendMetric g i else 1)) •
          monoBelow Q k (m ^^^ 2 ^ i) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [monoBelow_succ, monoBelow_succ, ← mul_assoc, sigma_succ, Nat.testBit_two_pow]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hik) with hlt | rfl
    · -- `i < k`: the top factor is untouched
      have hf : factor Q k (m ^^^ 2 ^ i) = factor Q k m := by
        unfold factor
        rw [Nat.testBit_xor, Nat.testBit_two_pow]
        simp [show i ≠ k by omega]
      rw [ih hlt (by omega), smul_mul_assoc, hf, show (decide (i = k)) = false by simp; omega]
      simp
    · -- `i = k`: commute past the lower monomial, then meet the top factor
      have hk : i < n := by omega
      have hlow : monoBelow Q i (m ^^^ 2 ^ i) = monoBelow Q i m :=
        monoBelow_congr Q fun j hj => by
          rw [Nat.testBit_xor, Nat.testBit_two_pow]; simp [show i ≠ j by omega]
      have hσ : sigma i (2 ^ i) m = false := by
        rw [sigma_congr (a' := 0) (b' := m) (fun j hj => by
          rw [Nat.testBit_two_pow]; simp [show i ≠ j by omega]) (fun _ _ => rfl)]
        exact sigma_zero_left i m
      have hext : extendMetric g i = g ⟨i, hk⟩ := by simp [extendMetric, hk]
      rw [genAt_mul_monoBelow_of_le hQ hk (Nat.le_refl i), smul_mul_assoc, mul_assoc, hlow, hσ]
      unfold factor
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      cases hm : m.testBit i
      · simp
      · simp only [decide_true, Bool.true_xor, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          Bool.true_and, Bool.false_xor, hext, genAt_mul_self hQ hk, mul_one]
        rw [← Algebra.commutes, ← Algebra.smul_def, smul_smul]

omit hQ in
/-- The metric factor of the shared generators of `eᵢ` and `m`. -/
theorem metricFactor_two_pow_and {i : ℕ} (hi : i < n) (m : ℕ) :
    metricFactor (extendMetric g) n (2 ^ i &&& m) = if m.testBit i then extendMetric g i else 1 := by
  cases hm : m.testBit i
  · have : 2 ^ i &&& m = 0 := Nat.eq_of_testBit_eq fun j => by
      rw [Nat.testBit_and, Nat.testBit_two_pow]
      by_cases hj : i = j
      · subst hj; simp [hm]
      · simp [hj]
    rw [this, metricFactor_zero_mask]; rfl
  · have : 2 ^ i &&& m = 2 ^ i := Nat.eq_of_testBit_eq fun j => by
      rw [Nat.testBit_and, Nat.testBit_two_pow]
      by_cases hj : i = j
      · subst hj; simp [hm]
      · simp [hj]
    rw [this, metricFactor_two_pow _ hi]; rfl

omit hQ in
theorem toNat_twoPow' (i : Fin n) : (BitVec.twoPow n i).toNat = 2 ^ i.1 := by
  rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) i.2)]

/-- **The generator-times-monomial table in mathlib's `CliffordAlgebra`**:
`ι(eᵢ) · monomial a = coef g eᵢ a • monomial (eᵢ ⊕ a)`, with the spec's blade
coefficient (`Grassmann.Spec.coef`: reordering sign times shared metric factor). -/
theorem genAt_mul_monomial (i : Fin n) (a : BitVec n) :
    genAt Q i * monomial Q a = coef g (BitVec.twoPow n i) a • monomial Q (BitVec.twoPow n i ^^^ a) := by
  unfold monomial
  rw [genAt_mul_monoBelow hQ i.2 (Nat.le_refl n), BitVec.toNat_xor, toNat_twoPow', Nat.xor_comm]
  congr 1
  show _ = signOf (sigma n (BitVec.twoPow n i).toNat a.toNat) *
    metricFactor (extendMetric g) n ((BitVec.twoPow n i).toNat &&& a.toNat)
  rw [toNat_twoPow', metricFactor_two_pow_and i.2]

end Relations

/-
**The spec algebra is mathlib's Clifford algebra.**

For a commutative ring `R`, a diagonal metric `g : Fin n → R` and any quadratic
form `Q` on `Rⁿ` with `Q v = Σᵢ gᵢ vᵢ²` (for instance
`QuadraticMap.weightedSumSquares R g`, see `GrassmannBridge.WeightedSumSquares`):

  `cliffordEquiv hQ : CliffordAlgebra Q ≃ₐ[R] Grassmann.Spec.Cl g`

with `ι(v) ↦ Σ vᵢ eᵢ` (`cliffordEquiv_ι`) and, backwards, each basis blade
`e_a ↦ ι(e_{i₁}) ⋯ ι(e_{iₖ})` (the ordered monomial, `cliffordEquiv_symm_blade`).
No hypothesis on `R`: characteristic 2 and non-invertible `2` are included.

The route:

1. `toCl`: the universal property (`CliffordAlgebra.lift`) applied to
   `v ↦ Σ vᵢ eᵢ`, which squares to `Q v` in `Cl g` (`toVec_mul_self`, from
   `eᵢ² = gᵢ` and `eᵢeⱼ = -eⱼeᵢ`: the cross terms cancel in pairs, so no
   division by 2 is needed).
2. `fromCl`: the linear map sending the blade `e_a` to the ordered monomial.
   The generator table `genAt_mul_monomial` (`GrassmannBridge.Monomial`) says
   `fromCl (eᵢ x) = ι(eᵢ) fromCl x`; hence `fromCl (toCl y · x) = y · fromCl x`
   for all `y` by induction on `y` (`CliffordAlgebra.induction`), and
   `fromCl ∘ toCl = id` (at `x = 1`).
3. `toCl ∘ fromCl = id`: `toCl` maps the ordered monomial of `a` to `e_a`, one
   generator at a time (`toCl_monoBelow`), with coefficient `1` because the
   new generator is above all the previous ones.

So `toCl` is bijective with inverse `fromCl`; injectivity is the part a
dimension count would give over a field, and the explicit inverse gives it over
every commutative ring.
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import GrassmannBridge.Monomial

namespace Grassmann.Bridge

open Grassmann.Spec DirectSum.Proofs

variable {R : Type*} [CommRing R] {n : ℕ} {Q : QuadraticForm R (Fin n → R)} {g : Fin n → R}

/-! ## Vectors and the Clifford relation in `Cl g` -/

section

variable (g)

/-- Vectors of `Rⁿ` as grade-1 multivectors: `v ↦ Σᵢ vᵢ eᵢ`. -/
noncomputable def toVec : (Fin n → R) →ₗ[R] Cl g := Fintype.linearCombination R fun i => Cl.gen i

end

theorem toVec_apply (v : Fin n → R) : toVec g v = ∑ i, v i • Cl.gen i := rfl

/-- `eᵢ` is the image of the `i`-th standard basis vector. -/
@[simp] theorem toVec_single (i : Fin n) : toVec g (Pi.single i 1) = Cl.gen i := by
  simp [toVec]

/-- **Squares of linear combinations of anticommuting elements**: if `eᵢ² = gᵢ`
and `eᵢeⱼ = -eⱼeᵢ` (`i ≠ j`), then `(Σ vᵢ eᵢ)² = Σ gᵢ vᵢ²`, in any `R`-algebra
over any commutative ring (the cross terms cancel in pairs). -/
theorem sum_smul_mul_self {A : Type*} [Ring A] [Algebra R A] (e : Fin n → A)
    (he : ∀ i, e i * e i = algebraMap R A (g i)) (hc : ∀ i j, i ≠ j → e i * e j = -(e j * e i))
    (v : Fin n → R) (s : Finset (Fin n)) :
    (∑ i ∈ s, v i • e i) * (∑ i ∈ s, v i • e i) = algebraMap R A (∑ i ∈ s, g i * (v i * v i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hx : (v j • e j) * (∑ i ∈ s, v i • e i) + (∑ i ∈ s, v i • e i) * (v j • e j) = 0 := by
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hij : j ≠ i := fun h => hj (h ▸ hi)
      rw [smul_mul_smul_comm, smul_mul_smul_comm, hc j i hij, mul_comm (v j), smul_neg,
        neg_add_cancel]
    have hjj : (v j • e j) * (v j • e j) = algebraMap R A (g j * (v j * v j)) := by
      rw [smul_mul_smul_comm, he, Algebra.smul_def, ← map_mul, mul_comm]
    rw [Finset.sum_insert hj, Finset.sum_insert hj, map_add, ← ih, ← hjj]
    calc (v j • e j + ∑ i ∈ s, v i • e i) * (v j • e j + ∑ i ∈ s, v i • e i)
        = (v j • e j) * (v j • e j) + ((v j • e j) * (∑ i ∈ s, v i • e i)
            + (∑ i ∈ s, v i • e i) * (v j • e j)) + (∑ i ∈ s, v i • e i) * (∑ i ∈ s, v i • e i) := by
          rw [add_mul, mul_add, mul_add]; abel
      _ = _ := by rw [hx, add_zero]

/-- In `Cl g`, a blade times a generator above all its bits is the bigger blade (coefficient `1`). -/
theorem blade_mul_gen_of_lt {k : ℕ} (hk : k < n) (L : BitVec n) (hL : L.toNat < 2 ^ k) :
    (Cl.blade L * Cl.gen ⟨k, hk⟩ : Cl g) = Cl.blade (L ^^^ BitVec.twoPow n k) := by
  rw [Cl.gen, Cl.blade_mul_blade']
  have hand : L.toNat &&& 2 ^ k = 0 := Nat.eq_of_testBit_eq fun j => by
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hj : k = j
    · subst hj; simp [Nat.testBit_lt_two_pow hL]
    · simp [hj]
  have hσ : sigma n L.toNat (2 ^ k) = false := by
    rw [sigma_of_lt (Nat.le_of_lt hk) hL, sigma_congr (a' := L.toNat) (b' := 0) (fun _ _ => rfl)
      (fun j hj => by rw [Nat.testBit_two_pow]; simp [show k ≠ j by omega])]
    exact sigma_zero_right k L.toNat
  have hc : coef g L (BitVec.twoPow n k) = 1 := by
    show signOf (sigma n L.toNat (BitVec.twoPow n k).toNat) *
      metricFactor (extendMetric g) n (L.toNat &&& (BitVec.twoPow n k).toNat) = 1
    rw [toNat_twoPow' ⟨k, hk⟩]
    simp only
    rw [hσ, hand, metricFactor_zero_mask, signOf_false, mul_one]
  rw [hc, one_smul]

private theorem mod_two_pow_succ_of_testBit {m k : ℕ} (h : m.testBit k = true) :
    m % 2 ^ k ^^^ 2 ^ k = m % 2 ^ (k + 1) :=
  Nat.eq_of_testBit_eq fun j => by
    rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
    rcases Nat.lt_trichotomy j k with hj | rfl | hj
    · simp [hj, show k ≠ j by omega, show j < k + 1 by omega]
    · simp [h]
    · simp [show ¬ j < k by omega, show k ≠ j by omega, show ¬ j < k + 1 by omega]

private theorem mod_two_pow_succ_of_not_testBit {m k : ℕ} (h : m.testBit k = false) :
    m % 2 ^ k = m % 2 ^ (k + 1) :=
  Nat.eq_of_testBit_eq fun j => by
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    rcases Nat.lt_trichotomy j k with hj | rfl | hj
    · simp [hj, show j < k + 1 by omega]
    · simp [h]
    · simp [show ¬ j < k by omega, show ¬ j < k + 1 by omega]

/-! ## The inverse map: blades to ordered monomials -/

section

variable (Q g)

/-- The linear map `Cl g → CliffordAlgebra Q` sending the blade `e_a` to the
ordered monomial `ι(e_{i₁}) ⋯ ι(e_{iₖ})` (defined on the blade basis). -/
noncomputable def fromCl : Cl g →ₗ[R] CliffordAlgebra Q := Cl.basis.constr R (monomial Q)

end

@[simp] theorem fromCl_blade (a : BitVec n) : fromCl Q g (Cl.blade a) = monomial Q a := by
  rw [← Cl.basis_apply, fromCl, Module.Basis.constr_basis]

@[simp] theorem fromCl_one : fromCl Q g 1 = 1 := by
  rw [show (1 : Cl g) = Cl.blade 0 from rfl, fromCl_blade, monomial_zero]

/-- `ι` in coordinates: `ι(v) = Σ vᵢ ι(eᵢ)`. -/
theorem ι_eq_sum (v : Fin n → R) : CliffordAlgebra.ι Q v = ∑ i, v i • genAt Q i := by
  have : CliffordAlgebra.ι Q = Fintype.linearCombination R fun i : Fin n => genAt Q i :=
    (Pi.basisFun R (Fin n)).ext fun i => by
      rw [Pi.basisFun_apply, Fintype.linearCombination_apply_single, one_smul]
      simp [genAt, i.2]
  rw [this]; rfl

variable (hQ : ∀ v, Q v = ∑ i, g i * (v i * v i))
include hQ

/-- **The Clifford relation in the spec algebra**: `(Σ vᵢ eᵢ)² = Q v`. -/
theorem toVec_mul_self (v : Fin n → R) : toVec g v * toVec g v = algebraMap R (Cl g) (Q v) := by
  rw [hQ, toVec_apply]
  exact sum_smul_mul_self (fun i => Cl.gen i) Cl.gen_mul_gen_self
    (fun _ _ h => Cl.gen_mul_gen_anticomm h) v Finset.univ

/-! ## The algebra map from the universal property -/

/-- **The lift**: the `R`-algebra map `CliffordAlgebra Q → Cl g` with
`ι(v) ↦ Σ vᵢ eᵢ`, from the universal property of the Clifford algebra. -/
noncomputable def toCl : CliffordAlgebra Q →ₐ[R] Cl g :=
  CliffordAlgebra.lift Q ⟨toVec g, toVec_mul_self hQ⟩

@[simp] theorem toCl_ι (v : Fin n → R) : toCl hQ (CliffordAlgebra.ι Q v) = toVec g v :=
  CliffordAlgebra.lift_ι_apply _ _ _

/-- `ι(eᵢ) ↦ eᵢ`. -/
theorem toCl_genAt {i : ℕ} (hi : i < n) : toCl hQ (genAt Q i) = Cl.gen ⟨i, hi⟩ := by
  simp [genAt, hi]

/-- `toCl` maps the ordered monomial below `k` to the blade of the bits of `m` below `k`. -/
theorem toCl_monoBelow {k : ℕ} (hk : k ≤ n) (m : ℕ) :
    toCl hQ (monoBelow Q k m) = Cl.blade (BitVec.ofNat n (m % 2 ^ k)) := by
  induction k with
  | zero => simp only [monoBelow_zero, map_one, Nat.pow_zero, Nat.mod_one]; rfl
  | succ k ih =>
    have hkn : k < n := by omega
    have hlt : m % 2 ^ k < 2 ^ n :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.pow_le_pow_right (by decide) (Nat.le_of_succ_le hk))
    rw [monoBelow_succ, map_mul, ih (by omega)]
    unfold factor
    cases hm : m.testBit k
    · simp only [Bool.false_eq_true, ↓reduceIte, map_one, mul_one]
      rw [mod_two_pow_succ_of_not_testBit hm]
    · simp only [↓reduceIte]
      rw [toCl_genAt hQ hkn, blade_mul_gen_of_lt hkn _ (by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; exact Nat.mod_lt _ (Nat.two_pow_pos k))]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
        toNat_twoPow' ⟨k, hkn⟩]
      simp only
      rw [mod_two_pow_succ_of_testBit hm, Nat.mod_eq_of_lt (a := m % 2 ^ (k + 1)) (b := 2 ^ n)
        (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) hk))]

/-- **`toCl` maps the ordered monomial of `a` to the blade `e_a`.** -/
@[simp] theorem toCl_monomial (a : BitVec n) : toCl hQ (monomial Q a) = Cl.blade a := by
  unfold monomial
  rw [toCl_monoBelow hQ (Nat.le_refl n), Nat.mod_eq_of_lt a.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## The inverse laws -/

/-- `fromCl` intertwines left multiplication by a generator (`genAt_mul_monomial`). -/
theorem fromCl_gen_mul (i : Fin n) (x : Cl g) :
    fromCl Q g (Cl.gen i * x) = genAt Q i * fromCl Q g x := by
  have : (fromCl Q g).comp (LinearMap.mulLeft R (Cl.gen i)) =
      (LinearMap.mulLeft R (genAt Q i)).comp (fromCl Q g) :=
    Cl.basis.ext fun a => by
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Cl.basis_apply, fromCl_blade]
      rw [Cl.gen, Cl.blade_mul_blade', map_smul, fromCl_blade, genAt_mul_monomial hQ]
  exact LinearMap.congr_fun this x

/-- `fromCl` intertwines left multiplication by a vector. -/
theorem fromCl_toVec_mul (v : Fin n → R) (x : Cl g) :
    fromCl Q g (toVec g v * x) = CliffordAlgebra.ι Q v * fromCl Q g x := by
  rw [toVec_apply, Finset.sum_mul, map_sum, ι_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, map_smul, fromCl_gen_mul hQ, smul_mul_assoc]

/-- `fromCl (toCl y · x) = y · fromCl x`, by induction on `y`. -/
theorem fromCl_toCl_mul (y : CliffordAlgebra Q) (x : Cl g) :
    fromCl Q g (toCl hQ y * x) = y * fromCl Q g x := by
  induction y using CliffordAlgebra.induction generalizing x with
  | algebraMap r => rw [AlgHom.commutes, ← Algebra.smul_def, map_smul, Algebra.smul_def]
  | ι v => rw [toCl_ι, fromCl_toVec_mul hQ]
  | mul a b ha hb => rw [map_mul (toCl hQ) a b, mul_assoc, ha, hb, mul_assoc]
  | add a b ha hb => rw [map_add, add_mul, map_add, ha, hb, add_mul]

/-- `fromCl` is a left inverse of `toCl`. -/
theorem fromCl_toCl (y : CliffordAlgebra Q) : fromCl Q g (toCl hQ y) = y := by
  simpa using fromCl_toCl_mul hQ y 1

/-- `fromCl` is a right inverse of `toCl`. -/
theorem toCl_fromCl (x : Cl g) : toCl hQ (fromCl Q g x) = x := by
  have : (toCl hQ).toLinearMap.comp (fromCl Q g) = LinearMap.id :=
    Cl.basis.ext fun a => by simp [toCl_monomial hQ]
  exact LinearMap.congr_fun this x

/-- The lift is injective: no relation beyond the Clifford relations holds in `Cl g`. -/
theorem toCl_injective : Function.Injective (toCl hQ) :=
  Function.LeftInverse.injective (fromCl_toCl hQ)

/-- The lift is surjective: the generators `eᵢ` generate `Cl g`. -/
theorem toCl_surjective : Function.Surjective (toCl hQ) :=
  Function.RightInverse.surjective (toCl_fromCl hQ)

/-! ## The isomorphism -/

/-- **`CliffordAlgebra Q ≃ₐ[R] Cl g`** for every quadratic form `Q` on `Rⁿ` that is
diagonal with weights `g`, over every commutative ring `R`. -/
noncomputable def cliffordEquiv : CliffordAlgebra Q ≃ₐ[R] Cl g :=
  { toCl hQ with
    invFun := fromCl Q g
    left_inv := fromCl_toCl hQ
    right_inv := toCl_fromCl hQ }

theorem cliffordEquiv_apply (y : CliffordAlgebra Q) : cliffordEquiv hQ y = toCl hQ y := rfl

theorem cliffordEquiv_symm_apply (x : Cl g) : (cliffordEquiv hQ).symm x = fromCl Q g x := rfl

/-- `ι(v) ↦ Σ vᵢ eᵢ`. -/
@[simp] theorem cliffordEquiv_ι (v : Fin n → R) :
    cliffordEquiv hQ (CliffordAlgebra.ι Q v) = ∑ i, v i • Cl.gen i :=
  toCl_ι hQ v

/-- `eᵢ ↦ ι(eᵢ)`. -/
@[simp] theorem cliffordEquiv_symm_gen (i : Fin n) :
    (cliffordEquiv hQ).symm (Cl.gen i) = CliffordAlgebra.ι Q (Pi.single i 1) := by
  rw [AlgEquiv.symm_apply_eq, cliffordEquiv_ι]
  simp [Pi.single_apply]

/-- `e_a ↦ ι(e_{i₁}) ⋯ ι(e_{iₖ})`: each blade is the ordered monomial of its generators. -/
@[simp] theorem cliffordEquiv_symm_blade (a : BitVec n) :
    (cliffordEquiv hQ).symm (Cl.blade a) = monomial Q a :=
  fromCl_blade a

/-- `ι(e_{i₁}) ⋯ ι(e_{iₖ}) ↦ e_a`. -/
@[simp] theorem cliffordEquiv_monomial (a : BitVec n) : cliffordEquiv hQ (monomial Q a) = Cl.blade a :=
  toCl_monomial hQ a

end Grassmann.Bridge

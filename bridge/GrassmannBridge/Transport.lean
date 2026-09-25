/-
Consequences of `CliffordAlgebra Q ≃ₐ[R] Cl g`, in both directions.

**Into mathlib** (new facts about `CliffordAlgebra` of a diagonal form, over
every commutative ring, characteristic 2 included):

* `weightedSumSquaresEquiv`: the isomorphism for mathlib's own diagonal form
  `QuadraticMap.weightedSumSquares R g`;
* `monomialBasis`: the `2ⁿ` ordered monomials `ι(e_{i₁}) ⋯ ι(e_{iₖ})` form a
  basis, so the Clifford algebra is free (`free`), finite (`finite`) and of
  rank `2ⁿ` (`finrank_eq`, for nontrivial `R`);
* `ι_injective`: the generating map `ι` is injective;
* `monomial_mul_monomial`: the full multiplication table of the monomial
  basis is the spec's blade table, `coef g a b = (-1)^{σ(a,b)} Π_{a∧b} gᵢ`,
  and `repr_mul` gives the product in coordinates (the twisted convolution
  `Cl.coeff_mul`).

**Out of mathlib** (the spec's operations are mathlib's): mathlib's reversion
and grade involution are the spec's Julia-semantics `Cl.reverse` and
`Cl.involute` (`cliffordEquiv_reverse`, `cliffordEquiv_involute`), so e.g.
`Cl.reverse_mul` and `CliffordAlgebra.reverse.map_mul` are the same theorem.
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import GrassmannBridge.Clifford

namespace Grassmann.Bridge

open Grassmann.Spec DirectSum.Proofs

variable {R : Type*} [CommRing R] {n : ℕ} {Q : QuadraticForm R (Fin n → R)} {g : Fin n → R}

/-! ## mathlib's diagonal form -/

/-- `weightedSumSquares R g` is diagonal with weights `g`. -/
theorem weightedSumSquares_apply' (g : Fin n → R) (v : Fin n → R) :
    QuadraticMap.weightedSumSquares R g v = ∑ i, g i * (v i * v i) := by
  simp [QuadraticMap.weightedSumSquares_apply]

/-- **The Clifford algebra of mathlib's diagonal form is the spec algebra**:
`CliffordAlgebra (weightedSumSquares R g) ≃ₐ[R] Cl g`, for every commutative ring. -/
noncomputable def weightedSumSquaresEquiv (g : Fin n → R) :
    CliffordAlgebra (QuadraticMap.weightedSumSquares R g) ≃ₐ[R] Cl g :=
  cliffordEquiv (weightedSumSquares_apply' g)

@[simp] theorem weightedSumSquaresEquiv_ι (g : Fin n → R) (v : Fin n → R) :
    weightedSumSquaresEquiv g (CliffordAlgebra.ι _ v) = ∑ i, v i • Cl.gen i :=
  cliffordEquiv_ι _ v

variable (hQ : ∀ v, Q v = ∑ i, g i * (v i * v i))
include hQ

/-! ## The monomial basis, freeness and rank -/

/-- **The ordered monomials form a basis of `CliffordAlgebra Q`** (the image of
the blade basis of `Cl g`). -/
noncomputable def monomialBasis : Module.Basis (BitVec n) R (CliffordAlgebra Q) :=
  Cl.basis.map (cliffordEquiv hQ).symm.toLinearEquiv

@[simp] theorem monomialBasis_apply (a : BitVec n) : monomialBasis hQ a = monomial Q a := by
  simp [monomialBasis]

/-- The coordinates of `y` in the monomial basis are the spec coefficients of its image. -/
@[simp] theorem monomialBasis_repr (y : CliffordAlgebra Q) (a : BitVec n) :
    (monomialBasis hQ).repr y a = (cliffordEquiv hQ y).coeff a := by
  simp [monomialBasis, AlgEquiv.toLinearEquiv_symm]

/-- The Clifford algebra of a diagonal form is a free module. -/
theorem free : Module.Free R (CliffordAlgebra Q) := Module.Free.of_basis (monomialBasis hQ)

/-- The Clifford algebra of a diagonal form is a finite module. -/
theorem finite : Module.Finite R (CliffordAlgebra Q) := Module.Finite.of_basis (monomialBasis hQ)

/-- **The Clifford algebra of an `n`-dimensional diagonal form has rank `2ⁿ`**, over
every nontrivial commutative ring. -/
theorem finrank_eq [Nontrivial R] : Module.finrank R (CliffordAlgebra Q) = 2 ^ n := by
  rw [Module.finrank_eq_card_basis (monomialBasis hQ), ← FinEnum.card_eq_fintypeCard,
    FinEnum.card_bitVec]

omit hQ in
/-- Distinct generators are distinct blades. -/
theorem twoPow_inj {i j : Fin n} : BitVec.twoPow n i = BitVec.twoPow n j ↔ i = j := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [toNat_twoPow', toNat_twoPow'] at this
    exact Fin.ext (Nat.pow_right_injective (le_refl 2) this)
  · rintro rfl; rfl

omit hQ in
/-- The coefficient of `eᵢ` in `Σ vⱼ eⱼ` is `vᵢ`. -/
theorem toVec_coeff_gen (v : Fin n → R) (i : Fin n) : (toVec g v).coeff (BitVec.twoPow n i) = v i := by
  rw [toVec_apply, ← Cl.equivFun_apply, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, Cl.equivFun_apply, Cl.gen, Cl.coeff_blade, twoPow_inj,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

/-- **`ι` is injective** for a diagonal form over every commutative ring (mathlib
proves injectivity in general only when `2` is invertible). -/
theorem ι_injective : Function.Injective (CliffordAlgebra.ι Q) := by
  intro v w h
  have h' := congrArg (fun y => (cliffordEquiv hQ y).coeff) h
  simp only [cliffordEquiv_ι, ← toVec_apply] at h'
  funext i
  have := congrFun h' (BitVec.twoPow n i)
  rwa [toVec_coeff_gen, toVec_coeff_gen] at this

/-! ## The multiplication table -/

/-- **The multiplication table of the monomial basis** of `CliffordAlgebra Q`:
`monomial a * monomial b = (-1)^{σ(a,b)} Π_{i ∈ a∧b} gᵢ • monomial (a ⊕ b)`,
transported from the spec's `Cl.blade_mul_blade`. -/
theorem monomial_mul_monomial (a b : BitVec n) :
    monomial Q a * monomial Q b = coef g a b • monomial Q (a ^^^ b) := by
  apply (cliffordEquiv hQ).injective
  rw [map_mul, map_smul, cliffordEquiv_monomial, cliffordEquiv_monomial, cliffordEquiv_monomial,
    Cl.blade_mul_blade']

/-- **Products in coordinates**: the monomial coordinates of `x * y` are the
twisted convolution `Σ_a xₐ · y_{a⊕c} · coef g a (a⊕c)` of the coordinates
(`Cl.coeff_mul`). -/
theorem repr_mul (x y : CliffordAlgebra Q) (c : BitVec n) :
    (monomialBasis hQ).repr (x * y) c =
      bsum n fun a => (monomialBasis hQ).repr x a * (monomialBasis hQ).repr y (a ^^^ c) *
        coef g a (a ^^^ c) := by
  simp only [monomialBasis_repr, map_mul]
  exact Cl.coeff_mul _ _ c

/-! ## Reversion and grade involution -/

omit hQ in
theorem _root_.Grassmann.Spec.Cl.reverse_smul (r : R) (x : Cl g) : Cl.reverse (r • x) = r • Cl.reverse x := by
  ext a; exact mul_left_comm _ _ _

omit hQ in
theorem _root_.Grassmann.Spec.Cl.involute_smul (r : R) (x : Cl g) :
    Cl.involute (r • x) = r • Cl.involute x := by
  ext a; exact mul_left_comm _ _ _

omit hQ in
theorem _root_.Grassmann.Spec.Cl.involute_add (x y : Cl g) :
    Cl.involute (x + y) = Cl.involute x + Cl.involute y := by
  ext a; exact mul_add _ _ _

omit hQ in
/-- The spec reversion as a linear map. -/
noncomputable def _root_.Grassmann.Spec.Cl.reverseLin : Cl g →ₗ[R] Cl g where
  toFun := Cl.reverse
  map_add' := Cl.reverse_add
  map_smul' := Cl.reverse_smul

omit hQ in
/-- The spec grade involution as a linear map. -/
noncomputable def _root_.Grassmann.Spec.Cl.involuteLin : Cl g →ₗ[R] Cl g where
  toFun := Cl.involute
  map_add' := Cl.involute_add
  map_smul' := Cl.involute_smul

omit hQ in
theorem reverse_algebraMap (r : R) : Cl.reverse (algebraMap R (Cl g) r) = algebraMap R (Cl g) r := by
  rw [Cl.algebraMap_eq_scalar]
  ext a
  show revSign a * (if a = 0 then r else 0) = if a = 0 then r else 0
  by_cases h : a = 0
  · rw [ite_eq_left h, h]; simp [revSign, grade, Leibniz.parityreverse]
  · rw [ite_eq_right h, mul_zero]

omit hQ in
theorem involute_algebraMap (r : R) :
    Cl.involute (algebraMap R (Cl g) r) = algebraMap R (Cl g) r := by
  rw [Cl.algebraMap_eq_scalar]
  ext a
  show invSign a * (if a = 0 then r else 0) = if a = 0 then r else 0
  by_cases h : a = 0
  · rw [ite_eq_left h, h]; simp [invSign, grade, Leibniz.parityinvolute]
  · rw [ite_eq_right h, mul_zero]

omit hQ in
theorem reverse_toVec (v : Fin n → R) : Cl.reverse (toVec g v) = toVec g v := by
  rw [toVec_apply]
  change Cl.reverseLin _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  change v i • Cl.reverse (Cl.gen i) = _
  rw [Cl.gen, Cl.reverse_blade, Cl.grade_twoPow]
  simp [Leibniz.parityreverse]

omit hQ in
theorem involute_toVec (v : Fin n → R) : Cl.involute (toVec g v) = -toVec g v := by
  rw [toVec_apply]
  change Cl.involuteLin _ = _
  rw [map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  change v i • Cl.involute (Cl.gen i) = _
  rw [Cl.gen, Cl.involute_blade, Cl.grade_twoPow]
  simp [Leibniz.parityinvolute]

/-- **mathlib's reversion is the spec's reversion** (Julia `reverse`):
`~(y)` corresponds to `Cl.reverse`, the sign `(-1)^{k(k-1)/2}` on grade `k`. -/
theorem cliffordEquiv_reverse (y : CliffordAlgebra Q) :
    cliffordEquiv hQ (CliffordAlgebra.reverse y) = Cl.reverse (cliffordEquiv hQ y) := by
  induction y using CliffordAlgebra.induction with
  | algebraMap r => rw [CliffordAlgebra.reverse.commutes, AlgEquiv.commutes, reverse_algebraMap]
  | ι v => rw [CliffordAlgebra.reverse_ι, cliffordEquiv_ι, ← toVec_apply, reverse_toVec]
  | mul a b ha hb => rw [CliffordAlgebra.reverse.map_mul, map_mul, map_mul, hb, ha, Cl.reverse_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, Cl.reverse_add]

/-- **mathlib's grade involution is the spec's** (Julia `involute`): `(-1)^k` on grade `k`. -/
theorem cliffordEquiv_involute (y : CliffordAlgebra Q) :
    cliffordEquiv hQ (CliffordAlgebra.involute y) = Cl.involute (cliffordEquiv hQ y) := by
  induction y using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, AlgEquiv.commutes, involute_algebraMap]
  | ι v => rw [CliffordAlgebra.involute_ι, map_neg, cliffordEquiv_ι, ← toVec_apply, involute_toVec]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, Cl.involute_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, Cl.involute_add]

end Grassmann.Bridge

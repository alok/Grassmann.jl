/-
The specification algebra `Cl g` as a mathlib `R`-algebra.

`Grassmann.Spec.Cl g` is a coefficient function on the `2ⁿ` basis blades with an
explicit geometric product (`Grassmann.Spec.Cl.coeff_mul`), and its ring laws
are theorems of the core-only specification (`Cl.mul_assoc`, `Cl.one_mul`,
`Cl.mul_add`, `Cl.smul_mul`, …). This file packages them as mathlib structure:

* an `AddCommGroup` and an `R`-`Module` transported along the coefficient map
  (which is injective by `Cl.ext`), so `Cl g ≃ₗ[R] (BitVec n → R)`
  (`Cl.equivFun`) and the blades form a basis (`Cl.basis`, `Cl.basis_apply`);
* a `Ring` whose multiplication is the spec's geometric product, and an
  `Algebra R` with `algebraMap r = Cl.scalar r`.

Nothing here reproves a law: every field is a theorem of `Grassmann.Spec`.
The algebra facts used downstream (`Cl.gen_mul_gen_self`, `Cl.gen_mul_gen_anticomm`,
`Cl.blade_mul_blade'`) are the spec's own theorems restated with `algebraMap`.
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.FinEnum
import Grassmann.Spec

namespace Grassmann.Spec.Cl

variable {R : Type*} [CommRing R] {n : ℕ} {g : Fin n → R}

/-! ## Additive structure -/

/-- `ℕ`-multiples, coefficientwise. -/
instance instSMulNat : SMul ℕ (Cl g) := ⟨fun k x => ⟨fun a => k • x.coeff a⟩⟩

/-- `ℤ`-multiples, coefficientwise. -/
instance instSMulInt : SMul ℤ (Cl g) := ⟨fun k x => ⟨fun a => k • x.coeff a⟩⟩

omit [CommRing R] in
/-- A multivector is determined by its coefficients. -/
theorem coeff_injective : Function.Injective (Cl.coeff : Cl g → BitVec n → R) :=
  fun _ _ h => Cl.ext h

/-- The additive group of multivectors: the coefficient functions, pointwise. -/
instance instAddCommGroup : AddCommGroup (Cl g) :=
  coeff_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The coefficient map as an additive homomorphism. -/
def coeffHom : Cl g →+ (BitVec n → R) where
  toFun := Cl.coeff
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The `R`-module of multivectors: coefficientwise scaling (the spec's `SMul R`). -/
instance instModule : Module R (Cl g) :=
  coeff_injective.module R coeffHom fun _ _ => rfl

/-- `Cl g` is the free module `BitVec n → R` of blade coefficients. -/
def equivFun : Cl g ≃ₗ[R] (BitVec n → R) where
  toFun := Cl.coeff
  invFun := Cl.mk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem equivFun_apply (x : Cl g) : equivFun x = x.coeff := rfl

/-- The blade basis of `Cl g`. -/
noncomputable def basis : Module.Basis (BitVec n) R (Cl g) := Module.Basis.ofEquivFun equivFun

/-- The basis vectors are the basis blades `e_a`. -/
@[simp] theorem basis_apply (a : BitVec n) : (basis a : Cl g) = blade a := by
  ext c
  simp only [basis, Module.Basis.coe_ofEquivFun, coeff_blade]
  show Function.update (0 : BitVec n → R) a 1 c = _
  rw [Function.update_apply]
  rfl

/-- The coordinates of a multivector in the blade basis are its coefficients. -/
@[simp] theorem basis_repr_apply (x : Cl g) (a : BitVec n) : basis.repr x a = x.coeff a := by
  simp [basis]

/-! ## Ring and algebra structure -/

/-- The geometric product makes `Cl g` a ring; every law is a spec theorem. -/
instance instRing : Ring (Cl g) where
  __ := instAddCommGroup
  mul := (· * ·)
  one := 1
  mul_assoc := Cl.mul_assoc
  one_mul := Cl.one_mul
  mul_one := Cl.mul_one
  zero_mul := Cl.zero_mul
  mul_zero := Cl.mul_zero
  left_distrib := Cl.mul_add
  right_distrib := Cl.add_mul

/-- Scalars are central and pull out of both factors (`Cl.smul_mul`, `Cl.mul_smul`),
so `Cl g` is an `R`-algebra. -/
instance instAlgebra : Algebra R (Cl g) := Algebra.ofModule Cl.smul_mul Cl.mul_smul

/-- The algebra map is the spec's scalar embedding. -/
theorem algebraMap_eq_scalar (r : R) : algebraMap R (Cl g) r = scalar r := by
  rw [Algebra.algebraMap_eq_smul_one, scalar_eq_smul_one]

/-- `eᵢ² = gᵢ` (`Cl.gen_mul_self`), with `algebraMap`. -/
theorem gen_mul_gen_self (i : Fin n) : (gen i * gen i : Cl g) = algebraMap R (Cl g) (g i) := by
  rw [algebraMap_eq_scalar]
  exact gen_mul_self i

/-- `eᵢ eⱼ = -eⱼ eᵢ` for `i ≠ j` (`Cl.gen_mul_gen_comm`). -/
theorem gen_mul_gen_anticomm {i j : Fin n} (hij : i ≠ j) :
    (gen i * gen j : Cl g) = -(gen j * gen i) :=
  gen_mul_gen_comm hij

/-- The blade table `e_a e_b = coef g a b • e_{a⊕b}` (`Cl.blade_mul_blade`). -/
theorem blade_mul_blade' (a b : BitVec n) :
    (blade a * blade b : Cl g) = coef g a b • blade (a ^^^ b) :=
  blade_mul_blade a b

end Grassmann.Spec.Cl

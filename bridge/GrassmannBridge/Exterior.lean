/-
The spec's exterior product is mathlib's `ExteriorAlgebra`.

mathlib defines `ExteriorAlgebra R M` as the Clifford algebra of the zero
quadratic form, and the spec's exterior product `Cl.wedge` is, by definition,
the twisted convolution with the zero-metric blade coefficient
(`Cl.wedge_eq_mul_zero`). The zero form is diagonal with zero weights, so
`cliffordEquiv` specializes to

  `exteriorEquiv : ExteriorAlgebra R Rⁿ ≃ₐ[R] Cl (0 : Fin n → R)`,

and, since `∧` does not depend on the metric, for **every** metric `g`

  `exteriorLinearEquiv g : ExteriorAlgebra R Rⁿ ≃ₗ[R] Cl g`,
  `exteriorLinearEquiv g (x * y) = Cl.wedge (exteriorLinearEquiv g x) (exteriorLinearEquiv g y)`:

mathlib's exterior product is the spec's `∧` on the multivectors of any
diagonal algebra. Over every commutative ring.
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import GrassmannBridge.Clifford

namespace Grassmann.Bridge

open Grassmann.Spec

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The zero quadratic form is diagonal with zero weights. -/
theorem zero_form_apply (v : Fin n → R) :
    (0 : QuadraticForm R (Fin n → R)) v = ∑ i, (fun _ : Fin n => (0 : R)) i * (v i * v i) := by
  simp

/-- **mathlib's exterior algebra is the spec algebra of the zero metric**:
`ExteriorAlgebra R Rⁿ ≃ₐ[R] Cl 0`, over every commutative ring. -/
noncomputable def exteriorEquiv : ExteriorAlgebra R (Fin n → R) ≃ₐ[R] Cl (fun _ : Fin n => (0 : R)) :=
  cliffordEquiv zero_form_apply

@[simp] theorem exteriorEquiv_ι (v : Fin n → R) :
    exteriorEquiv (ExteriorAlgebra.ι R v) = ∑ i, v i • Cl.gen i :=
  cliffordEquiv_ι _ v

/-- The coefficientwise identification of the multivectors of two metrics
(the blades do not depend on the metric, only the product does). -/
def recast (g g' : Fin n → R) : Cl g ≃ₗ[R] Cl g' where
  toFun x := ⟨x.coeff⟩
  invFun x := ⟨x.coeff⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem recast_coeff (g g' : Fin n → R) (x : Cl g) : (recast g g' x).coeff = x.coeff := rfl

/-- The spec exterior product in any metric is the zero-metric geometric product
of the same coefficients (`Cl.wedge_eq_mul_zero`, as an equation of multivectors). -/
theorem recast_wedge (g : Fin n → R) (x y : Cl g) :
    recast g (fun _ => 0) (Cl.wedge x y) = recast g (fun _ => 0) x * recast g (fun _ => 0) y :=
  Cl.ext (Cl.wedge_eq_mul_zero x y)

/-- mathlib's exterior algebra as the multivectors of any diagonal algebra `Cl g`
(an `R`-linear isomorphism). -/
noncomputable def exteriorLinearEquiv (g : Fin n → R) : ExteriorAlgebra R (Fin n → R) ≃ₗ[R] Cl g :=
  exteriorEquiv.toLinearEquiv.trans (recast g (fun _ => 0)).symm

theorem recast_exteriorLinearEquiv (g : Fin n → R) (x : ExteriorAlgebra R (Fin n → R)) :
    recast g (fun _ => 0) (exteriorLinearEquiv g x) = exteriorEquiv x := rfl

/-- **mathlib's exterior product is the spec's `∧`**, in every diagonal algebra:
`x * y ↦ Cl.wedge x y`. -/
theorem exteriorLinearEquiv_mul (g : Fin n → R) (x y : ExteriorAlgebra R (Fin n → R)) :
    exteriorLinearEquiv g (x * y) = Cl.wedge (exteriorLinearEquiv g x) (exteriorLinearEquiv g y) := by
  apply (recast g (fun _ => 0)).injective
  rw [recast_wedge, recast_exteriorLinearEquiv, recast_exteriorLinearEquiv,
    recast_exteriorLinearEquiv, map_mul]

/-- The unit of the exterior algebra is the unit blade. -/
@[simp] theorem exteriorLinearEquiv_one (g : Fin n → R) :
    exteriorLinearEquiv g (1 : ExteriorAlgebra R (Fin n → R)) = 1 := by
  apply (recast g (fun _ => 0)).injective
  rw [recast_exteriorLinearEquiv, map_one]
  rfl

/-- `ι(v) ↦ Σ vᵢ eᵢ`, in any metric. -/
@[simp] theorem exteriorLinearEquiv_ι (g : Fin n → R) (v : Fin n → R) :
    exteriorLinearEquiv g (ExteriorAlgebra.ι R v) = ∑ i, v i • Cl.gen i := by
  apply (recast g (fun _ => 0)).injective
  rw [recast_exteriorLinearEquiv, exteriorEquiv_ι, map_sum]
  simp only [map_smul]
  rfl

end Grassmann.Bridge

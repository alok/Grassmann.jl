/-
The regressive product: the implementation's `∨` against the spec.

`Grassmann.Spec.Cl.vee` is the De Morgan dual of `∧` under the right complement
(`!(x ∨ y) = !x ∧ !y`), proved associative in general (`Cl.vee_assoc`). Here
kernel evaluation checks that DirectSum's blade rule `terms₂ .vee` (Julia's
`(-1)^{L(L-n)} ⋆⁻¹(⋆a ∧ ⋆b)` with the Euclidean complement) gives exactly the
spec `∨` on every pair of basis blades, coefficient by coefficient. The rule is
metric-independent, so one space per dimension suffices.
-/
import Grassmann.Proofs.Tables

namespace Grassmann.Proofs

open DirectSum DirectSum.Proofs Grassmann.Spec Lean.Grind

variable {n : Nat}

/-- The implementation's regressive product on every pair of basis blades is the
spec term: `e_a ∨ e_b` at its blade `~(a ⊕ b)`. -/
def VeeAgrees (V : TensorBundle) (g : Fin n → Rat) : Prop :=
  ∀ a b : BitVec n, Matches (V.terms₂ .vee (mask a) (mask b)) (~~~(a ^^^ b))
    ((Cl.vee (Cl.blade a) (Cl.blade b) : Cl g).coeff (~~~(a ^^^ b))) = true

/-- A matching regressive table gives the spec `∨` on every pair of blades. -/
theorem implVee_blade (hn : n ≤ 64) {V : TensorBundle} {g : Fin n → Rat} (h : VeeAgrees V g) (a b : BitVec n) :
    ofTerms g (V.terms₂ .vee (mask a) (mask b)) = Cl.vee (Cl.blade a) (Cl.blade b) := by
  rw [ofTerms_of_matches hn (h a b), ← Cl.vee_blade]

theorem R2_vee_table : VeeAgrees ℝ2 (gEuclid 2) := by unfold VeeAgrees; decide +kernel
theorem R3_vee_table : VeeAgrees ℝ3 (gEuclid 3) := by unfold VeeAgrees; decide +kernel
theorem STA_vee_table : VeeAgrees STA gSTA := by unfold VeeAgrees; decide +kernel
theorem PGA3_vee_table : VeeAgrees PGA3 (gPGA 4) := by unfold VeeAgrees; decide +kernel
theorem D123_vee_table : VeeAgrees D!"1,2,-3" gD123 := by unfold VeeAgrees; decide +kernel

end Grassmann.Proofs

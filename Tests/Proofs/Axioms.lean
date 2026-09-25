/-
Axiom audit of the flagship theorems (compile-time).

Each `#guard_msgs` fails the build if a theorem starts depending on anything
beyond Lean's three standard axioms: `sorryAx` (a `sorry`), a custom `axiom`, or
`Lean.ofReduceBool` (`native_decide`/`bv_decide`).
-/
import DirectSum.Proofs
import Grassmann.Spec
import Grassmann.Proofs

/-- info: 'DirectSum.Proofs.reorderParity_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms DirectSum.Proofs.reorderParity_eq_spec

/-- info: 'DirectSum.Proofs.sigma_cocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms DirectSum.Proofs.sigma_cocycle

/-- info: 'DirectSum.Proofs.bladeCoef_cocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms DirectSum.Proofs.bladeCoef_cocycle

/-- info: 'DirectSum.Proofs.signOf_parityjoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms DirectSum.Proofs.signOf_parityjoin

/-- info: 'Grassmann.Spec.Cl.mul_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Spec.Cl.mul_assoc

/-- info: 'Grassmann.Spec.Cl.wedge_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Spec.Cl.wedge_comm

/-- info: 'Grassmann.Spec.Cl.reverse_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Spec.Cl.reverse_mul

/-- info: 'Grassmann.Spec.Cl.hodge_hodge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Spec.Cl.hodge_hodge

/-- info: 'Grassmann.Proofs.STA_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.STA_mul

/-- info: 'Grassmann.Proofs.PGA3_mul_plan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.PGA3_mul_plan

/-- info: 'Grassmann.Proofs.mulSign_eq_coef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.mulSign_eq_coef

/-- info: 'Grassmann.Proofs.implMul_assoc_of_conf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.implMul_assoc_of_conf

/-- info: 'Grassmann.Spec.Cl.mul_self_of_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Spec.Cl.mul_self_of_vector

/-- info: 'Grassmann.Spec.Cl.contract_eq_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Spec.Cl.contract_eq_proj

/-- info: 'Grassmann.Spec.Cl.vee_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Spec.Cl.vee_assoc

/-- info: 'Grassmann.Proofs.implMul_eq_mul_of_signature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.implMul_eq_mul_of_signature

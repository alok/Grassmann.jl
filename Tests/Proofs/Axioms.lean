/-
Axiom audit of the flagship theorems (compile-time).

Each `#guard_msgs` fails the build if a theorem starts depending on anything
beyond Lean's three standard axioms: `sorryAx` (a `sorry`), a custom `axiom`, or
`Lean.ofReduceBool` (`native_decide`/`bv_decide`).
-/
import DirectSum.Proofs
import Grassmann.Spec
import Grassmann.Proofs
import Grassmann.Tactic
import Grassmann.MaskIngress
import Grassmann.Kernel.R3RotorLaws

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

/-- info: 'Grassmann.Proofs.implWedge_eq_wedge_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.implWedge_eq_wedge_of_flat

/-- info: 'DirectSum.Proofs.popcount_eq_bitCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms DirectSum.Proofs.popcount_eq_bitCount

/-- info: 'Grassmann.Proofs.implReverse_eq_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.implReverse_eq_reverse

/-- info: 'DirectSum.Proofs.metricProduct_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms DirectSum.Proofs.metricProduct_eq

/-- info: 'Grassmann.Proofs.implMul_eq_mul_of_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.implMul_eq_mul_of_diag

/-- info: 'DirectSum.Proofs.sumIndices_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms DirectSum.Proofs.sumIndices_eq

/-- info: 'Grassmann.Proofs.implHodge_implHodge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.implHodge_implHodge

/-- info: 'Grassmann.Proofs.CGA3_mul_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.CGA3_mul_assoc

/-- info: 'Grassmann.Proofs.conf_table_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.conf_table_5

/-- info: 'Grassmann.Tactic.eq_of_coords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Tactic.eq_of_coords

/-- info: 'Grassmann.Tactic.coords_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Tactic.coords_of_eq

/-- info: 'Grassmann.Spec.Cl.instRing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Spec.Cl.instRing

/-- info: 'Grassmann.Spec.Cl.isGrade_sandwich_of_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Spec.Cl.isGrade_sandwich_of_even

/-- info: 'Grassmann.Spec.Cl.sandwich_sq_of_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Spec.Cl.sandwich_sq_of_vector

/-- info: 'Grassmann.Proofs.implMul_assoc_of_signature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.implMul_assoc_of_signature

/-- info: 'Grassmann.Proofs.isGrade_implSandwich_of_signature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.isGrade_implSandwich_of_signature

/-- info: 'Grassmann.Proofs.implWedge_comm_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.implWedge_comm_of_flat

/-- info: 'Grassmann.Proofs.Interp.eval₂_eq_twist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.Interp.eval₂_eq_twist

/-- info: 'Grassmann.Proofs.Interp.refBin_eq_twist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.Interp.refBin_eq_twist

/-- info: 'Grassmann.Proofs.Interp.STA_refMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.Interp.STA_refMul

/-- info: 'Grassmann.Proofs.Interp.PGA3_refMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.Interp.PGA3_refMul

/-- info: 'Grassmann.Proofs.Interp.eval₁_eq_unary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.Interp.eval₁_eq_unary

/-- info: 'Grassmann.Proofs.Interp.STA_refHodge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.Interp.STA_refHodge

/-- info: 'Grassmann.Proofs.ProjectiveConformal.poincare_invol_PGA2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.ProjectiveConformal.poincare_invol_PGA2

/-- info: 'Grassmann.Proofs.ProjectiveConformal.poincare_invol_PGA3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.ProjectiveConformal.poincare_invol_PGA3

/--
info: 'Grassmann.Proofs.ProjectiveConformal.pga3_poincare_e0_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Grassmann.Proofs.ProjectiveConformal.pga3_poincare_e0_ne_zero

/-- info: 'Grassmann.Proofs.ProjectiveConformal.pga3_hodge_e0_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.ProjectiveConformal.pga3_hodge_e0_eq_zero

/--
info: 'Grassmann.Proofs.ProjectiveConformal.ganjaCompat_pga3_dualChain_e0_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Grassmann.Proofs.ProjectiveConformal.ganjaCompat_pga3_dualChain_e0_ne_zero

/--
info: 'Grassmann.Proofs.ProjectiveConformal.ganjaCompat_pga3_undual_dual_e0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Grassmann.Proofs.ProjectiveConformal.ganjaCompat_pga3_undual_dual_e0

/-- info: 'Grassmann.Proofs.ProjectiveConformal.pga3_motor_mul_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.ProjectiveConformal.pga3_motor_mul_reverse

/--
info: 'Grassmann.Proofs.ProjectiveConformal.pga3_motor_reverse_norm_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Grassmann.Proofs.ProjectiveConformal.pga3_motor_reverse_norm_inv

/-- info: 'Grassmann.Proofs.ProjectiveConformal.pga3_study_quadric_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.ProjectiveConformal.pga3_study_quadric_iff

/--
info: 'Grassmann.Proofs.ProjectiveConformal.pga3_unit_motor_mul_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Grassmann.Proofs.ProjectiveConformal.pga3_unit_motor_mul_closed

/--
info: 'Grassmann.Proofs.ProjectiveConformal.pga3_impl_motor_mul_reverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Grassmann.Proofs.ProjectiveConformal.pga3_impl_motor_mul_reverse

/-- info: 'Grassmann.Proofs.ProjectiveConformal.cga3_point_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.ProjectiveConformal.cga3_point_mul_self

/-- info: 'Grassmann.Proofs.ProjectiveConformal.cga3_point_distance_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.ProjectiveConformal.cga3_point_distance_sq

/-- info: 'Grassmann.Proofs.ProjectiveConformal.cga2_point_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.ProjectiveConformal.cga2_point_mul_self

/-- info: 'Grassmann.Proofs.ProjectiveConformal.r3_rotor_mul_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.ProjectiveConformal.r3_rotor_mul_reverse

/--
info: 'Grassmann.Proofs.ProjectiveConformal.r3_unit_rotor_preserves_norm_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Grassmann.Proofs.ProjectiveConformal.r3_unit_rotor_preserves_norm_sq

/--
info: 'Grassmann.Proofs.ProjectiveConformal.r3_concrete_rational_rotor_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Grassmann.Proofs.ProjectiveConformal.r3_concrete_rational_rotor_unit

/-- info: 'Grassmann.MaskIngress.single?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.MaskIngress.single?_sound

/-- info: 'Grassmann.Kernel.R3Rotor.action_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Kernel.R3Rotor.action_formula

/-- info: 'Grassmann.Proofs.SpacetimeWedge.sta_timelike_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.sta_timelike_sq

/-- info: 'Grassmann.Proofs.SpacetimeWedge.sta_spacelike_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.sta_spacelike_sq

/-- info: 'Grassmann.Proofs.SpacetimeWedge.sta_generators_anticomm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.sta_generators_anticomm

/--
info: 'Grassmann.Proofs.SpacetimeWedge.sta_minkowski_quadratic_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.sta_minkowski_quadratic_form

/-- info: 'Grassmann.Proofs.SpacetimeWedge.sta_boost_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.sta_boost_unit

/-- info: 'Grassmann.Proofs.SpacetimeWedge.sta_boost_composition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.sta_boost_composition

/-- info: 'Grassmann.Proofs.SpacetimeWedge.sta_boost_sandwich_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.sta_boost_sandwich_formula

/--
info: 'Grassmann.Proofs.SpacetimeWedge.sta_boost_preserves_minkowski' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.sta_boost_preserves_minkowski

/--
info: 'Grassmann.Proofs.SpacetimeWedge.sta_impl_boost_preserves_minkowski' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.sta_impl_boost_preserves_minkowski

/--
info: 'Grassmann.Proofs.SpacetimeWedge.sta_spatial_rot_preserves_minkowski' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.sta_spatial_rot_preserves_minkowski

/-- info: 'Grassmann.Proofs.SpacetimeWedge.sta_concrete_rational_boost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.sta_concrete_rational_boost

/-- info: 'Grassmann.Proofs.SpacetimeWedge.PGA2_vee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.PGA2_vee

/-- info: 'Grassmann.Proofs.SpacetimeWedge.PGA3_vee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.PGA3_vee

/-- info: 'Grassmann.Proofs.SpacetimeWedge.pga2_point_on_line_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.pga2_point_on_line_eq

/-- info: 'Grassmann.Proofs.SpacetimeWedge.pga2_join_antisymm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.pga2_join_antisymm

/-- info: 'Grassmann.Proofs.SpacetimeWedge.pga2_join_incident' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.pga2_join_incident

/-- info: 'Grassmann.Proofs.SpacetimeWedge.pga2_meet_lines_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.pga2_meet_lines_laws

/-- info: 'Grassmann.Proofs.SpacetimeWedge.pga2_midpoint_on_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.pga2_midpoint_on_join

/-- info: 'Grassmann.Proofs.SpacetimeWedge.pga2_impl_wedge_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.pga2_impl_wedge_laws

/-- info: 'Grassmann.Proofs.SpacetimeWedge.pga3_point_on_plane_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.pga3_point_on_plane_eq

/-- info: 'Grassmann.Proofs.SpacetimeWedge.pga3_meet_planes_incident' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.pga3_meet_planes_incident

/--
info: 'Grassmann.Proofs.SpacetimeWedge.pga3_meet_three_planes_incident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.pga3_meet_three_planes_incident

/-- info: 'Grassmann.Proofs.SpacetimeWedge.pga3_join_points_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.pga3_join_points_laws

/--
info: 'Grassmann.Proofs.SpacetimeWedge.pga3_join_three_points_plane_incident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.pga3_join_three_points_plane_incident

/-- info: 'Grassmann.Proofs.SpacetimeWedge.pga3_impl_wedge_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Proofs.SpacetimeWedge.pga3_impl_wedge_laws

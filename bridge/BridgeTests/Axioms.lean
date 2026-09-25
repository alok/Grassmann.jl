/-
Axiom audit of the bridge theorems (compile-time).

Each `#guard_msgs` fails the build if a theorem starts depending on anything
beyond Lean's three standard axioms: `sorryAx` (a `sorry`), a custom `axiom`, or
`Lean.ofReduceBool` (`native_decide`/`bv_decide`). mathlib itself uses only
these three.
-/
import GrassmannBridge

/-- info: 'Grassmann.Bridge.cliffordEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Bridge.cliffordEquiv

/-- info: 'Grassmann.Bridge.toCl_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Bridge.toCl_injective

/-- info: 'Grassmann.Bridge.toCl_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Bridge.toCl_surjective

/-- info: 'Grassmann.Bridge.genAt_mul_monomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Bridge.genAt_mul_monomial

/-- info: 'Grassmann.Bridge.weightedSumSquaresEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Bridge.weightedSumSquaresEquiv

/-- info: 'Grassmann.Bridge.finrank_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Bridge.finrank_eq

/-- info: 'Grassmann.Bridge.ι_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Bridge.ι_injective

/-- info: 'Grassmann.Bridge.monomial_mul_monomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Bridge.monomial_mul_monomial

/-- info: 'Grassmann.Bridge.cliffordEquiv_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Bridge.cliffordEquiv_reverse

/-- info: 'Grassmann.Bridge.cliffordEquiv_involute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Bridge.cliffordEquiv_involute

/-- info: 'Grassmann.Bridge.exteriorEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Bridge.exteriorEquiv

/-- info: 'Grassmann.Bridge.exteriorLinearEquiv_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Grassmann.Bridge.exteriorLinearEquiv_mul

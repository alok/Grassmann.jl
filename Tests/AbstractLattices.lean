import AbstractLattices
import Tests.AbstractLattices.Harness
import Tests.AbstractLattices.Unified

/-!
AbstractLattices tests: the Julia test suite (`AbstractLattices.jl test/runtests.jl`)
and the Bool methods of 0.2.2/0.3.x (port-notes/small-algebra.md §6.1); `Unified` checks at
compile time that one `∧`/`∨` class family serves AbstractTensors, Grassmann, DeMorgan and
Dendriform.
-/

open AbstractLattices Tests.Small

namespace Tests.AbstractLattices

/-! Compile-time checks: `test/runtests.jl` defines `∧ = min`, `∨ = max` on numbers. -/

example : wedge (MinMax.mk 5) (MinMax.mk 10) = MinMax.mk 5 := by decide
example : vee (MinMax.mk 5) (MinMax.mk 10) = MinMax.mk 10 := by decide
example : wedge₁ 3 = vee₁ 3 := rfl
example : wedge true false = false := by decide
example : vee true false = true := by decide
example : wedgeAll true [true, false, true] = false := by decide
example : veeAll false [false, false, true] = true := by decide
-- the derived lattice laws specialise to Bool
example (p : Bool) : wedge p p = p := wedge_self p
example (a b : MinMax Nat) : wedge a b = a ↔ vee a b = b := wedge_eq_left_iff_vee_eq_right a b

/-- Runtime checks (all exhaustive over small domains). -/
def suite : TestM Unit := do
  for p in [false, true] do
    for q in [false, true] do
      checkEq s!"wedge {p} {q}" (wedge p q) (p && q)
      checkEq s!"vee {p} {q}" (vee p q) (p || q)
  for a in [0, 3, 5, 10] do
    for b in [0, 3, 5, 10] do
      checkEq s!"min {a} {b}" (wedge (MinMax.mk a) (MinMax.mk b)).val (min a b)
      checkEq s!"max {a} {b}" (vee (MinMax.mk a) (MinMax.mk b)).val (max a b)
  checkEq "5 ∧ 10" (wedge (MinMax.mk (5 : Int)) (MinMax.mk (10 : Int))).val 5
  checkEq "5 ∨ 10" (vee (MinMax.mk (5 : Int)) (MinMax.mk (10 : Int))).val 10

/-- Suite entry point for the `lake test` driver. -/
def run : IO (Nat × Nat) := runSuite "AbstractLattices" suite

end Tests.AbstractLattices

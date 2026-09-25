/-
Examples for `grind` on the specification algebra (docs/TACTICS.md): abstract
multivector identities in any dimension, for any diagonal metric, over any
commutative ring, proved by

* plain `grind`: `Cl g` is a `Lean.Grind.Ring` (`Grassmann.Spec.Ring`), so
  products are normalized as non-commutative polynomials, and the involutions
  are pushed inward by `grind`'s preprocessor (`Grassmann.Spec.Grind`);
* `grind [grassmann]`: the Clifford-algebra laws (generators, vectors, grades,
  graded commutativity, sandwiches) as E-matching lemmas.

The whole file checks in about half a second.
-/
import Grassmann.Tactic

namespace Tests.Proofs.GrindExamples

open Grassmann.Spec Grassmann.Spec.Cl Lean.Grind

variable {R : Type} [CommRing R] {n : Nat} {g : Fin n → R} {g₃ : Fin 3 → R}

/-! ## Ring normalization of multivector expressions -/

example (x y z w : Cl g) : x * (y * z) * w = x * y * (z * w) := by grind
example (x y : Cl g) : (x + y) * (x - y) = x * x - y * y - x * y + y * x := by grind
example (x : Cl g) : x ^ 2 * x = x * x ^ 2 := by grind
example (x : Cl g) : (2 : Cl g) * x - x = x := by grind
/-- Re-bracketing inside a product needs associativity as a lemma. -/
example (x y z : Cl g) (h : y * z = 0) : x * y * z = 0 := by grind [Cl.mul_assoc]

/-! ## Involutions of products -/

example (x y z : Cl g) : reverse (x * y * z) = reverse z * reverse y * reverse x := by grind
example (x y : Cl g) : reverse (x * reverse y) = y * reverse x := by grind
example (x : Cl g) : reverse (x * reverse x) = x * reverse x := by grind
example (x y : Cl g) (r : R) : reverse (r • x + y) = r • reverse x + reverse y := by grind
example (x y z : Cl g) : involute (x * y * involute z) = involute x * involute y * z := by grind
example (x y : Cl g) : clifford (x * y) = clifford y * clifford x := by grind
example (r x : Cl g) : reverse (r * x * reverse r) = r * reverse x * reverse r := by grind

/-! ## Generators -/

example (i j : Fin n) (h : i ≠ j) : (gen i * gen j : Cl g) + gen j * gen i = 0 := by grind [grassmann]
example : (gen 0 * gen 1 : Cl g₃) = -(gen 1 * gen 0) := by grind [grassmann]
example : (gen 0 * gen 0 : Cl g₃) = scalar (g₃ 0) := by grind [grassmann]
example : reverse (gen 0 * gen 1 : Cl g₃) = -(gen 0 * gen 1) := by grind [grassmann]

/-! ## Vectors: the Clifford relation and graded commutativity -/

example (v : Cl g) (hv : IsGrade 1 v) : v * v = scalar (dot v v) := by grind [grassmann]
example (v : Cl g) (hv : IsGrade 1 v) : reverse v * v = scalar (dot v v) := by grind [grassmann]
/-- The vector hypothesis is derived from the shape of the element. -/
example (a b : R) : (a • gen 0 + b • gen 1 : Cl g₃) * (a • gen 0 + b • gen 1)
    = scalar (dot (a • gen 0 + b • gen 1 : Cl g₃) (a • gen 0 + b • gen 1)) := by grind [grassmann]
example (u v : Cl g) (hu : IsGrade 1 u) (hv : IsGrade 1 v) :
    u * v + v * u = scalar (dot u v + dot u v) := by grind [grassmann]
example (u v : Cl g) (hu : IsGrade 1 u) (hv : IsGrade 1 v) : wedge u v + wedge v u = 0 := by
  grind [grassmann]
example (a b : R) : wedge (a • gen 0 + b • gen 1 : Cl g₃) (a • gen 0 + b • gen 1) = 0 := by
  grind [grassmann]
example (u v : Cl g) (hu : IsGrade 1 u) (hv : IsGrade 1 v) : IsGrade 2 (wedge u v) := by
  grind [grassmann]
/-- A vector and a bivector commute under `∧` (`(-1)^{1·2} = 1`). -/
example (u B : Cl g) (hu : IsGrade 1 u) (hB : IsGrade 2 B) : wedge u B = wedge B u := by
  grind [grassmann]
example (u v w : Cl g) (hu : IsGrade 1 u) (hv : IsGrade 1 v) (hw : IsGrade 1 w) :
    wedge (wedge u v) w = wedge w (wedge u v) := by grind [grassmann]

/-! ## Sandwiches -/

example (r x y : Cl g) (h : reverse r * r = 1) :
    r * x * reverse r * (r * y * reverse r) = r * (x * y) * reverse r := by grind [grassmann]
/-- Sandwiching by a unit element (`R̃ R = R R̃ = 1`) is an isometry on vectors. -/
example (r v : Cl g) (hl : reverse r * r = 1) (hr : r * reverse r = 1) (hv : IsGrade 1 v) :
    r * v * reverse r * (r * v * reverse r) = scalar (dot v v) := by grind [grassmann]
/-- **Grade preservation**: in dimension `≤ 4` an even element sandwiches
vectors to vectors (no normalization needed; `R` without 2-torsion). -/
example [NoNatZeroDivisors R] (r v : Cl g₃) (hr : involute r = r) (hv : IsGrade 1 v) :
    IsGrade 1 (r * v * reverse r) := by grind [grassmann]
example [NoNatZeroDivisors R] (r v : Cl g₃) (hr : involute r = r) (hv : IsGrade 1 v) :
    proj 3 (r * v * reverse r) = 0 := by grind [grassmann]

end Tests.Proofs.GrindExamples

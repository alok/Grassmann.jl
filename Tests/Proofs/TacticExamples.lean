/-
Examples for the `clifford` tactic (docs/TACTICS.md), compiled as part of the
proofs suite. Each is an identity in a concrete space with coefficients in an
arbitrary commutative ring `R`; symbolic scalars are variables of `R`,
symbolic multivectors are variables of `Cl g`.

Timings (elaboration + kernel check, measured with `trace.profiler`) are in
docs/TACTICS.md; every example here takes well under a second except the
fully opaque Jacobi identity (about 0.8 s).
-/
import Grassmann.Tactic

namespace Tests.Proofs.TacticExamples

open Grassmann.Spec Lean.Grind

variable {R : Type} [CommRing R]

/-! ## Euclidean 3-space -/

/-- The Euclidean metric of `ℝ³`, over any commutative ring. -/
abbrev E3 (R : Type) [CommRing R] : Fin 3 → R := fun _ => 1

abbrev v₁ : Cl (E3 R) := Cl.gen 0
abbrev v₂ : Cl (E3 R) := Cl.gen 1
abbrev v₃ : Cl (E3 R) := Cl.gen 2
/-- The pseudoscalar `v₁₂₃`. -/
abbrev I₃ : Cl (E3 R) := Cl.pseudoscalar

/-- The vector `a v₁ + b v₂ + c v₃`. -/
abbrev vec (a b c : R) : Cl (E3 R) := a • v₁ + b • v₂ + c • v₃
/-- The bivector `a v₁₂ + b v₁₃ + c v₂₃`. -/
abbrev biv (a b c : R) : Cl (E3 R) := a • (v₁ * v₂) + b • (v₁ * v₃) + c • (v₂ * v₃)
/-- The commutator product (without the factor `1/2`). -/
abbrev comm (x y : Cl (E3 R)) : Cl (E3 R) := x * y - y * x

/-- The Clifford relation, for a vector in the plane. -/
example (a b : R) : (a • v₁ + b • v₂) * (a • v₁ + b • v₂) = Cl.scalar (a ^ 2 + b ^ 2) := by
  clifford

/-- The Clifford relation, for every vector of `ℝ³`. -/
example (a b c : R) : vec a b c * vec a b c = Cl.scalar (a ^ 2 + b ^ 2 + c ^ 2) := by
  clifford

/-- Distinct generators anticommute; a unit bivector squares to `-1`. -/
example : (v₁ * v₂ : Cl (E3 R)) = -(v₂ * v₁) := by clifford
example : (v₁ * v₂ : Cl (E3 R)) * (v₁ * v₂) = -1 := by clifford

/-- The triple product: `u ∧ v ∧ w = det(u, v, w) I`. -/
example (u₁ u₂ u₃ w₁ w₂ w₃ x₁ x₂ x₃ : R) :
    Cl.wedge (Cl.wedge (vec u₁ u₂ u₃) (vec w₁ w₂ w₃)) (vec x₁ x₂ x₃)
      = (u₁ * (w₂ * x₃ - w₃ * x₂) - u₂ * (w₁ * x₃ - w₃ * x₁) + u₃ * (w₁ * x₂ - w₂ * x₁)) • I₃ := by
  clifford

/-- Lagrange's identity: `(u ∧ v)(u ∧ v)~ = |u|²|v|² - (u · v)²`. -/
example (u₁ u₂ u₃ w₁ w₂ w₃ : R) :
    Cl.wedge (vec u₁ u₂ u₃) (vec w₁ w₂ w₃) * Cl.reverse (Cl.wedge (vec u₁ u₂ u₃) (vec w₁ w₂ w₃))
      = Cl.scalar ((u₁ ^ 2 + u₂ ^ 2 + u₃ ^ 2) * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2)
          - (u₁ * w₁ + u₂ * w₂ + u₃ * w₃) ^ 2) := by
  clifford

/-- The Hodge dual of `u ∧ w` is the cross product `u × w`. -/
example (u₁ u₂ u₃ w₁ w₂ w₃ : R) :
    Cl.hodge (Cl.wedge (vec u₁ u₂ u₃) (vec w₁ w₂ w₃))
      = vec (u₂ * w₃ - u₃ * w₂) (u₃ * w₁ - u₁ * w₃) (u₁ * w₂ - u₂ * w₁) := by
  clifford

/-- The product of two vectors is their inner product plus their wedge. -/
example (a b c x y z : R) :
    vec a b c * vec x y z = Cl.scalar (a * x + b * y + c * z) + Cl.wedge (vec a b c) (vec x y z) := by
  clifford

/-- The Jacobi identity of the commutator product, for bivectors. -/
example (a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ : R) :
    comm (comm (biv a₁ a₂ a₃) (biv b₁ b₂ b₃)) (biv c₁ c₂ c₃)
      + comm (comm (biv b₁ b₂ b₃) (biv c₁ c₂ c₃)) (biv a₁ a₂ a₃)
      + comm (comm (biv c₁ c₂ c₃) (biv a₁ a₂ a₃)) (biv b₁ b₂ b₃) = 0 := by
  clifford

/-- The commutator of two bivectors is a bivector (bivectors form a Lie algebra). -/
example (a₁ a₂ a₃ b₁ b₂ b₃ : R) :
    Cl.proj 2 (comm (biv a₁ a₂ a₃) (biv b₁ b₂ b₃)) = comm (biv a₁ a₂ a₃) (biv b₁ b₂ b₃) := by
  clifford

/-- The Jacobi identity for arbitrary (opaque) multivectors: each of their 8
coordinates is a symbolic atom. -/
example (x y z : Cl (E3 R)) : comm (comm x y) z + comm (comm y z) x + comm (comm z x) y = 0 := by
  clifford

/-! ## Quaternions as the even subalgebra of `ℝ³` -/

abbrev qi : Cl (E3 R) := v₃ * v₂
abbrev qj : Cl (E3 R) := v₁ * v₃
abbrev qk : Cl (E3 R) := v₂ * v₁

/-- Hamilton's relations `i² = j² = k² = ijk = -1`. -/
example : (qi * qi : Cl (E3 R)) = -1 := by clifford
example : (qj * qj : Cl (E3 R)) = -1 := by clifford
example : (qk * qk : Cl (E3 R)) = -1 := by clifford
example : (qi * qj * qk : Cl (E3 R)) = -1 := by clifford
example : (qi * qj : Cl (E3 R)) = qk := by clifford

/-! ## Rotors -/

/-- A rotor `c + s v₁₂` with `c² + s² = 1` is normalized: `R R̃ = 1`. -/
example (c s : R) (h : c ^ 2 + s ^ 2 = 1) :
    (Cl.scalar c + s • (v₁ * v₂)) * Cl.reverse (Cl.scalar c + s • (v₁ * v₂)) = 1 := by
  clifford

/-- The sandwich of a vector by an even element has no trivector part. -/
example (a b c d x y z : R) :
    Cl.proj 3 ((Cl.scalar a + biv b c d) * vec x y z * Cl.reverse (Cl.scalar a + biv b c d)) = 0 := by
  clifford

/-- A unit rotor is an isometry: `(R v R̃)² = v²`. -/
example (a b c d x y z : R) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) :
    ((Cl.scalar a + biv b c d) * vec x y z * Cl.reverse (Cl.scalar a + biv b c d))
      * ((Cl.scalar a + biv b c d) * vec x y z * Cl.reverse (Cl.scalar a + biv b c d))
      = Cl.scalar (x ^ 2 + y ^ 2 + z ^ 2) := by
  clifford

/-- The same with the normalization stated for multivectors: multivector
hypotheses become coordinate hypotheses. -/
example (a b c d x y z : R)
    (h : (Cl.scalar a + biv b c d) * Cl.reverse (Cl.scalar a + biv b c d) = 1) :
    ((Cl.scalar a + biv b c d) * vec x y z * Cl.reverse (Cl.scalar a + biv b c d))
      * ((Cl.scalar a + biv b c d) * vec x y z * Cl.reverse (Cl.scalar a + biv b c d))
      = Cl.scalar (x ^ 2 + y ^ 2 + z ^ 2) := by
  clifford

/-- An opaque multivector pinned down by a hypothesis. -/
example (r : Cl (E3 R)) (a b c d : R) (hr : r = Cl.scalar a + biv b c d)
    (h : r * Cl.reverse r = 1) : Cl.reverse r * r = 1 := by
  clifford

/-! ## Spacetime algebra -/

/-- The spacetime metric in Hestenes' signature `(+, -, -, -)`. -/
abbrev STA (R : Type) [CommRing R] : Fin 4 → R := fun i => if i.1 = 0 then 1 else -1

abbrev γ₀ : Cl (STA R) := Cl.gen 0
abbrev γ₁ : Cl (STA R) := Cl.gen 1
abbrev γ₂ : Cl (STA R) := Cl.gen 2
abbrev γ₃ : Cl (STA R) := Cl.gen 3

example : (γ₀ * γ₀ : Cl (STA R)) = 1 := by clifford
example : (γ₁ * γ₁ : Cl (STA R)) = -1 := by clifford
/-- Reflection of `γ₁` in the time axis. -/
example : (γ₀ * γ₁ * γ₀ : Cl (STA R)) = -γ₁ := by clifford
example : (γ₀ * γ₂ * γ₀ : Cl (STA R)) = -γ₂ := by clifford
/-- The pseudoscalar `γ₀γ₁γ₂γ₃` squares to `-1`. -/
example : (γ₀ * γ₁ * γ₂ * γ₃ : Cl (STA R)) = Cl.pseudoscalar := by clifford
example : (Cl.pseudoscalar * Cl.pseudoscalar : Cl (STA R)) = -1 := by clifford
/-- The Minkowski norm. -/
example (t x y z : R) :
    (t • γ₀ + x • γ₁ + y • γ₂ + z • γ₃) * (t • γ₀ + x • γ₁ + y • γ₂ + z • γ₃)
      = Cl.scalar (t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2) := by
  clifford
/-- A boost generator `γ₁γ₀` squares to `+1`. -/
example : (γ₁ * γ₀ * (γ₁ * γ₀) : Cl (STA R)) = 1 := by clifford

/-! ## Symbolic metrics and other spaces -/

/-- The Clifford relation for an arbitrary diagonal metric `g`. -/
example (g : Fin 3 → R) (a b : R) :
    (a • Cl.gen 0 + b • Cl.gen 1 : Cl g) * (a • Cl.gen 0 + b • Cl.gen 1)
      = Cl.scalar (g 0 * a ^ 2 + g 1 * b ^ 2) := by
  clifford

/-- Projective geometric algebra: the degenerate generator squares to `0`. -/
example : (Cl.gen 0 * Cl.gen 0 : Cl (fun i : Fin 4 => if i.1 = 0 then (0 : R) else 1)) = 0 := by
  clifford

/-- Reversion is an anti-automorphism, checked on opaque multivectors of `ℝ⁵`. -/
example (x y : Cl (fun _ : Fin 5 => (1 : R))) : Cl.reverse (x * y) = Cl.reverse y * Cl.reverse x := by
  clifford

/-- The rational spaces of `Grassmann.Proofs.Tables` work too. -/
example (x : Cl (fun _ : Fin 2 => (1 : Rat))) : x * 1 = x := by clifford

/-! ## Axiom audit -/

/-- A rotor identity with a hypothesis, as a named theorem. -/
theorem rotor_normalized (c s : R) (h : c ^ 2 + s ^ 2 = 1) :
    (Cl.scalar c + s • (v₁ * v₂)) * Cl.reverse (Cl.scalar c + s • (v₁ * v₂)) = 1 := by
  clifford

/-- The Jacobi identity for opaque multivectors, as a named theorem. -/
theorem jacobi (x y z : Cl (E3 R)) : comm (comm x y) z + comm (comm y z) x + comm (comm z x) y = 0 := by
  clifford

/-- info: 'Tests.Proofs.TacticExamples.rotor_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rotor_normalized

/-- info: 'Tests.Proofs.TacticExamples.jacobi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms jacobi

end Tests.Proofs.TacticExamples

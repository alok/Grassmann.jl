/-
Concrete instances of the bridge theorems (compile-time checks).

Each example is a fact about mathlib's `CliffordAlgebra`/`ExteriorAlgebra` of a
concrete diagonal form, obtained from the spec model through the isomorphism.
The characteristic-2 examples are outside the reach of mathlib's
`Invertible 2` results (`CliffordAlgebra.equivExterior`).
-/
import Mathlib.Data.ZMod.Basic
import GrassmannBridge

open Grassmann.Bridge

/-- The Clifford algebra of Euclidean `ℚ³` has dimension `8`. -/
example : Module.finrank ℚ (CliffordAlgebra (QuadraticMap.weightedSumSquares ℚ ![1, 1, 1])) = 8 :=
  finrank_eq (weightedSumSquares_apply' _)

/-- Spacetime algebra `Cl(1,3)` over `ℤ`: free of rank `16`. -/
example : Module.finrank ℤ (CliffordAlgebra (QuadraticMap.weightedSumSquares ℤ ![-1, 1, 1, 1])) = 16 :=
  finrank_eq (weightedSumSquares_apply' _)

/-- Characteristic 2, where `2` is not invertible: still rank `2ⁿ`. -/
example :
    Module.finrank (ZMod 2) (CliffordAlgebra (QuadraticMap.weightedSumSquares (ZMod 2) ![(1 : ZMod 2), 1])) = 4 :=
  finrank_eq (weightedSumSquares_apply' ![(1 : ZMod 2), 1])

/-- Characteristic 2: `ι` is injective. -/
example :
    Function.Injective (CliffordAlgebra.ι (QuadraticMap.weightedSumSquares (ZMod 2) ![(1 : ZMod 2), 0, 1])) :=
  ι_injective (weightedSumSquares_apply' ![(1 : ZMod 2), 0, 1])

/-- A degenerate (projective) metric over `ℤ`: `ι` is injective. -/
example : Function.Injective (CliffordAlgebra.ι (QuadraticMap.weightedSumSquares ℤ ![0, 1, 1, 1])) :=
  ι_injective (weightedSumSquares_apply' _)

/-- The exterior algebra of `ℤ⁴` has rank `16`. -/
example : Module.finrank ℤ (ExteriorAlgebra ℤ (Fin 4 → ℤ)) = 16 :=
  finrank_eq zero_form_apply

/-- The monomial table in mathlib's algebra is the spec's blade coefficient. -/
example (g : Fin 3 → ℤ) (a b : BitVec 3) :
    monomial (QuadraticMap.weightedSumSquares ℤ g) a * monomial _ b =
      Grassmann.Spec.coef g a b • monomial _ (a ^^^ b) :=
  monomial_mul_monomial (weightedSumSquares_apply' g) a b

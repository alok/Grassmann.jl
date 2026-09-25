/-
The headline theorems, transported to the implementation.

The link theorems identify the implementation's operations (DirectSum's blade
rules `terms₂`/`terms₁`, extended (bi)linearly exactly as the reference
kernels do: `implMul`, `implWedge`, `implUnary`) with the specification in
whole families of spaces. Rewriting along them states the laws of
`Grassmann.Spec` for the implementation itself, in every space of the family
at once:

* every plain signature space (`IsSignatureSpace`, dimension `≤ 64`):
  the geometric product is associative and unital
  (`implMul_assoc_of_signature`, `implMul_one_of_signature`), reversion
  reverses it and the grade involution preserves it
  (`implReverse_implMul_of_signature`, `implInvolute_implMul_of_signature`),
  vectors square to their quadratic form (`implMul_self_of_signature`), and in
  dimension `≤ 4` the sandwich of a vector by an even element is a vector
  (`isGrade_implSandwich_of_signature`);
* every `DiagonalForm` space (`IsDiagSpace`: any entries, degenerate
  included): the geometric product is associative
  (`implMul_assoc_of_diag`);
* every flat space (`IsFlatSpace`: any metric, `MetricTensor`s included): the
  exterior product is associative (`implWedge_assoc_of_flat`) and graded
  commutative (`implWedge_comm_of_flat`);
* the conformal spaces `CGA2`, `CGA3`: associativity is in
  `Grassmann.Proofs.Conformal` (`CGA2_mul_assoc`, `CGA3_mul_assoc`).

What remains between these statements and the typed containers
(`Multivector V α * Multivector V α`) is the plan interpreter
`Grassmann.Kernel.Plan.eval₂`: the plans are checked to be the spec tables in
small spaces (`*_mul_plan`) and the interpreter is tested, not proved
(docs/PROOFS.md).
-/
import Grassmann.Proofs.General
import Grassmann.Proofs.Diagonal
import Grassmann.Spec.Sandwich

namespace Grassmann.Proofs

open DirectSum DirectSum.Proofs Grassmann.Spec Lean.Grind

variable {n : Nat}

/-! ## Signature spaces -/

/-- A plain signature space is flat. -/
theorem IsSignatureSpace.isFlat {V : TensorBundle} (hV : IsSignatureSpace V) : IsFlatSpace V :=
  ⟨hV.conformal, hV.tangent⟩

section Signature

variable {V : TensorBundle} (hV : IsSignatureSpace V) (hn : n ≤ 64)
include hV hn

/-- **The implementation's geometric product is associative in every plain
signature space** (dimension `≤ 64`). -/
theorem implMul_assoc_of_signature (x y z : Cl (sigG (R := Rat) n V.sigBits.toNat)) :
    implMul V (implMul V x y) z = implMul V x (implMul V y z) := by
  simp only [implMul_eq_mul_of_signature hV hn, Cl.mul_assoc]

/-- `1` is a two-sided unit of the implementation's product. -/
theorem implMul_one_of_signature (x : Cl (sigG (R := Rat) n V.sigBits.toNat)) :
    implMul V 1 x = x ∧ implMul V x 1 = x := by
  simp only [implMul_eq_mul_of_signature hV hn, Cl.one_mul, Cl.mul_one, and_self]

/-- The implementation's vectors square to their quadratic form
`Σ ±vᵢ²` (the Clifford relation). -/
theorem implMul_self_of_signature {v : Cl (sigG (R := Rat) n V.sigBits.toNat)} (hv : Cl.IsGrade 1 v) :
    implMul V v v = Cl.scalar (Cl.dot v v) := by
  rw [implMul_eq_mul_of_signature hV hn, Cl.mul_self_of_vector hv]

variable (hVn : V.n = n)
include hVn

/-- **The implementation's reversion reverses its product**:
`~(x y) = ~y ~x` in every plain signature space. -/
theorem implReverse_implMul_of_signature (x y : Cl (sigG (R := Rat) n V.sigBits.toNat)) :
    implUnary V .reverse (implMul V x y) = implMul V (implUnary V .reverse y) (implUnary V .reverse x) := by
  simp only [implMul_eq_mul_of_signature hV hn, implReverse_eq_reverse hV.isFlat hVn hn, Cl.reverse_mul]

/-- The implementation's grade involution is an automorphism of its product. -/
theorem implInvolute_implMul_of_signature (x y : Cl (sigG (R := Rat) n V.sigBits.toNat)) :
    implUnary V .involute (implMul V x y)
      = implMul V (implUnary V .involute x) (implUnary V .involute y) := by
  simp only [implMul_eq_mul_of_signature hV hn, implInvolute_eq_involute hV.isFlat hVn hn, Cl.involute_mul]

/-- **Grade preservation, for the implementation**: in a plain signature
space of dimension `≤ 4`, the sandwich `R v R̃` (computed with the
implementation's product and reversion) of a vector by an even element is a
vector. -/
theorem isGrade_implSandwich_of_signature (h4 : n ≤ 4) {r v : Cl (sigG (R := Rat) n V.sigBits.toNat)}
    (hr : implUnary V .involute r = r) (hv : Cl.IsGrade 1 v) :
    Cl.IsGrade 1 (implMul V (implMul V r v) (implUnary V .reverse r)) := by
  rw [implInvolute_eq_involute hV.isFlat hVn hn] at hr
  simp only [implMul_eq_mul_of_signature hV hn, implReverse_eq_reverse hV.isFlat hVn hn]
  exact Cl.isGrade_sandwich_of_even h4 hr hv

end Signature

/-! ## Diagonal spaces -/

/-- **The implementation's geometric product is associative in every
`DiagonalForm` space** (any entries: zeros, negatives, fractions). -/
theorem implMul_assoc_of_diag {V : TensorBundle} {d : Array Rat} (hV : IsDiagSpace V d)
    (x y z : Cl (diagMetric d)) : implMul V (implMul V x y) z = implMul V x (implMul V y z) := by
  simp only [implMul_eq_mul_of_diag hV, Cl.mul_assoc]

/-! ## The exterior product in flat spaces -/

section Flat

variable {V : TensorBundle} (hV : IsFlatSpace V) (hn : n ≤ 64) {g : Fin n → Rat}
include hV hn

/-- **The implementation's exterior product is associative** in every flat
space (any metric). -/
theorem implWedge_assoc_of_flat (x y z : Cl g) :
    implWedge V (implWedge V x y) z = implWedge V x (implWedge V y z) := by
  simp only [implWedge_eq_wedge_of_flat hV hn, Cl.wedge_assoc]

/-- **The implementation's exterior product is graded commutative**:
`x ∧ y = (-1)^{pq} y ∧ x` for a `p`-vector `x` and a `q`-vector `y`, in every
flat space. -/
theorem implWedge_comm_of_flat {p q : Nat} {x y : Cl g} (hx : Cl.IsGrade p x) (hy : Cl.IsGrade q y) :
    implWedge V x y = (-1 : Rat) ^ (p * q) • implWedge V y x := by
  simp only [implWedge_eq_wedge_of_flat hV hn, Cl.wedge_comm hx hy]

end Flat

/-! ## Instances -/

/-- `ℝ⁷`: the implementation's product is associative. -/
theorem R7_mul_assoc (x y z : Cl (sigG (R := Rat) 7 ℝ7.sigBits.toNat)) :
    implMul ℝ7 (implMul ℝ7 x y) z = implMul ℝ7 x (implMul ℝ7 y z) :=
  implMul_assoc_of_signature ⟨Or.inr rfl, rfl, rfl⟩ (by decide) x y z

end Grassmann.Proofs

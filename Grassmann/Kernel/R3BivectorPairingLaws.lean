/- Optional R3 grade-two/grade-two raw scalar contraction proofs, concrete provider frozen.
Julia real-domain dispatch: Grassmann src/products.jl:1165; existing TA no-conj policy stays. -/
import Grassmann.Kernel.R3BivectorContractionLaws

namespace Grassmann.Kernel.R3BivectorPairing
open DirectSum StaticVectors

private theorem get_set {α : Type} [Packed α] {n : Nat} (v : Values α n)
    (i j : Fin n) (x : α) :
    (v.set i x).get j = if i.val = j.val then x else v.get j :=
  Packed.get_set v.data _ x j.val _

private theorem plan_ext {p q : Plan} (ia : p.ia = q.ia) (ib : p.ib = q.ib)
    (code : p.code = q.code) (coef : p.coef = q.coef)
    (rows : p.rowStart = q.rowStart) (nested : p.nested = q.nested) : p = q := by
  cases p; cases q; simp_all

/-- Ordered scalar payload in bivector input basis [e12,e13,e23], reusing the scalar evaluator. -/
@[specialize] def formula {α : Type} [Coeff α] (x y : Values α 3) : Values α 1 :=
  R3Contraction.formula x y

/-- Actual emitted grade-two/grade-two storage, for every operations-only coefficient input. -/
theorem generated {α : Type} [Coeff α] (x y : Values α 3) :
    Gen.ℝ3.k_bin_contraction_c2_c2_c0 x y = formula x y := by
  apply Values.ext
  intro ⟨i, hi⟩
  change i < 1 at hi
  have h : i = 0 := by omega
  subst i
  simp [Gen.ℝ3.k_bin_contraction_c2_c2_c0, formula, R3Contraction.formula,
    R3Contraction.coordinate, get_set]

/-- Actual concrete bin dispatch with no supplied basis or formula certificate. -/
theorem bin {α : Type} [Coeff α] (x y : Values α 3) :
    @Kernels.bin ℝ3 Gen.ℝ3.instKernels α _ .contraction (.chain 2) (.chain 2) (.chain 0)
      x y = formula x y := generated x y

/-- Actual bivector input and scalar-grade output layouts. -/
theorem layouts : (Layout.chain 2).blades 3 = #[3,5,6] ∧
    (Layout.chain 0).blades 3 = #[0] := by decide +kernel

/-- Actual bivector/bivector expression-form reference key. -/
def loopKey : Loops.JKey :=
  { V := ℝ3, op := .contraction, a := .dense (.chain 2), b := .dense (.chain 2),
    lc := .chain 0, outerFirst := true }

/-- The actual computed scalar row; agreement with vector scalar storage is derived. -/
theorem loop_plan : Loops.plan loopKey =
    { ia := #[0,1,2], ib := #[0,1,2], code := ⟨#[0,0,0]⟩,
      coef := #[1,1,1], rowStart := #[0,3], nested := 0 } := by
  apply plan_ext <;> decide +kernel

/-- Reuse the first-term scalar evaluator only after deriving equality of the actual plans. -/
theorem loop_formula {α : Type} [Coeff α] (x y : Values α 3) :
    Loops.run true loopKey x.data y.data = formula x y := by
  change Loops.eval (k := 1) true (Loops.plan loopKey) x.data y.data = R3Contraction.formula x y
  have plans : Loops.plan loopKey = Loops.plan R3Contraction.loopKey :=
    loop_plan.trans R3Contraction.loop_plan.symm
  rw [plans]
  exact R3Contraction.loop_formula x y

/-- Actual frozen fast routing preserves a raw scalar-grade Chain, including coefficient zero. -/
theorem fast_formula {α : Type} [Coeff α] (a b : Chain ℝ3 2 α) :
    @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 2 a) (.chain 2 b) =
      .chain 0 ⟨formula a.v b.v⟩ :=
  congrArg (fun v : Values α 1 ↦ (TA.chain 0 ⟨v⟩ : TA ℝ3 α)) (generated a.v b.v)

/-- Actual frozen reference routing and stored scalar payload. -/
theorem reference_formula {α : Type} [Coeff α] (a b : Chain ℝ3 2 α) :
    @TA.contraction ℝ3 α _ Gen.ℝ3.instKernels (.chain 2 a) (.chain 2 b) =
      .chain 0 ⟨formula a.v b.v⟩ :=
  congrArg (fun v : Values α 1 ↦ (TA.chain 0 ⟨v⟩ : TA ℝ3 α)) (loop_formula a.v b.v)

/-- Universal raw equality for arbitrary bivector inputs and every Coeff. -/
theorem contractionF_eq_contraction {α : Type} [Coeff α] (a b : Chain ℝ3 2 α) :
    @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 2 a) (.chain 2 b) =
      @TA.contraction ℝ3 α _ Gen.ℝ3.instKernels (.chain 2 a) (.chain 2 b) :=
  (fast_formula a b).trans (reference_formula a b).symm

/-- Existing typed contraction selects this same complete generated scalar payload. -/
theorem typed_formula {α : Type} [Coeff α] (a b : Chain ℝ3 2 α) :
    (a ⋅ b : Chain ℝ3 0 α) = ⟨formula a.v b.v⟩ :=
  congrArg (fun v : Values α 1 ↦ (⟨v⟩ : Chain ℝ3 0 α)) (generated a.v b.v)

/-- Existing typed scalar Chain agrees with the frozen raw dynamic contraction. -/
theorem typed_eq_fast {α : Type} [Coeff α] (a b : Chain ℝ3 2 α) :
    (TA.chain 0 (a ⋅ b : Chain ℝ3 0 α) : TA ℝ3 α) =
      @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 2 a) (.chain 2 b) := by
  rw [typed_formula, fast_formula]

/-- Plain bivector pairing on the actual frozen contractionF/coeff0 path. -/
@[specialize] def pairingCoefficient {α : Type} [Coeff α] (a b : Chain ℝ3 2 α) : α :=
  (@TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 2 a) (.chain 2 b)).coeff 0

/-- Executable pairing retains the same ordered scalar polynomial without algebraic laws. -/
theorem pairingCoefficient_formula {α : Type} [Coeff α] (a b : Chain ℝ3 2 α) :
    pairingCoefficient a b = R3Contraction.coordinate a.v b.v := by
  unfold pairingCoefficient
  rw [fast_formula, R3Contraction.coeff_scalar]
  simp [formula, R3Contraction.formula]

/-- Actual bivector pairing agrees with its frozen reference contraction coefficient. -/
theorem pairingCoefficient_eq_reference {α : Type} [Coeff α] (a b : Chain ℝ3 2 α) :
    pairingCoefficient a b =
      (@TA.contraction ℝ3 α _ Gen.ℝ3.instKernels (.chain 2 a) (.chain 2 b)).coeff 0 :=
  congrArg (fun out : TA ℝ3 α ↦ out.coeff 0) (contractionF_eq_contraction a b)

/-- Pairing symmetry assumes only commutation of this actual multiplication operation. -/
theorem pairingCoefficient_symm {α : Type} [Coeff α]
    (comm : ∀ p q : α, p*q = q*p) (a b : Chain ℝ3 2 α) :
    pairingCoefficient a b = pairingCoefficient b a := by
  rw [pairingCoefficient_formula, pairingCoefficient_formula]
  exact R3Contraction.coordinate_symm comm a.v b.v

/-- Genuine default Rat multiplication commutation discharges arbitrary-input symmetry. -/
theorem rational_symm (a b : Chain ℝ3 2 Rat) : pairingCoefficient a b = pairingCoefficient b a :=
  pairingCoefficient_symm Rat.mul_comm a b

/-- Genuine default unbounded Int multiplication gives the same symmetry without division. -/
theorem integer_symm (a b : Chain ℝ3 2 Int) : pairingCoefficient a b = pairingCoefficient b a :=
  pairingCoefficient_symm Int.mul_comm a b

end Grassmann.Kernel.R3BivectorPairing

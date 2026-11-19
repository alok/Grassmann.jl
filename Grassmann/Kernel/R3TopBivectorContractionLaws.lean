/- Optional R3 grade-three/grade-two stored vector contraction proofs.
Julia real-domain dispatch: Grassmann src/products.jl:1165; TA's no-conj policy is retained. -/
import Grassmann.Kernel.R3TopContractionLaws

namespace Grassmann.Kernel.R3TopBivectorContraction
open DirectSum StaticVectors

private theorem get_set {α : Type} [Packed α] {n : Nat} (v : Values α n)
    (i j : Fin n) (x : α) :
    (v.set i x).get j = if i.val = j.val then x else v.get j :=
  Packed.get_set v.data _ x j.val _

private theorem plan_ext {p q : Plan} (ia : p.ia = q.ia) (ib : p.ib = q.ib)
    (code : p.code = q.code) (coef : p.coef = q.coef)
    (rows : p.rowStart = q.rowStart) (nested : p.nested = q.nested) : p = q := by
  cases p; cases q; simp_all

/-- Ordered vector coordinates in [e1,e2,e3], reusing the existing scalar operations. -/
@[specialize] def formula {α : Type} [Coeff α] (x : Values α 1) (y : Values α 3) :
    Values α 3 := R3TopContraction.formula x y

/-- Actual emitted top/bivector writes refine for arbitrary packed inputs and every Coeff. -/
theorem generated {α : Type} [Coeff α] (x : Values α 1) (y : Values α 3) :
    Gen.ℝ3.k_bin_contraction_c3_c2_c1 x y = formula x y := by
  apply Values.ext
  intro ⟨i, hi⟩
  change i < 3 at hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases with h | h | h <;> subst i <;>
    simp [Gen.ℝ3.k_bin_contraction_c3_c2_c1, formula, R3TopContraction.formula, get_set]
  all_goals
    intro h
    change (2 : Nat) = _ at h
    omega

/-- Actual generated bin dispatch with no basis or formula witness premise. -/
theorem bin {α : Type} [Coeff α] (x : Values α 1) (y : Values α 3) :
    @Kernels.bin ℝ3 Gen.ℝ3.instKernels α _ .contraction (.chain 3) (.chain 2) (.chain 1)
      x y = formula x y := generated x y

/-- Actual pseudoscalar/bivector input order and vector output layout. -/
theorem layouts : (Layout.chain 3).blades 3 = #[7] ∧
    (Layout.chain 2).blades 3 = #[3,5,6] ∧ (Layout.chain 1).blades 3 = #[1,2,4] :=
  by decide +kernel

/-- Actual first-operand-outermost expression-loop key for this grade pair. -/
def loopKey : Loops.JKey :=
  { V := ℝ3, op := .contraction, a := .dense (.chain 3), b := .dense (.chain 2),
    lc := .chain 1, outerFirst := true }

/-- This grade pair's computed plan, with one signed first term per output. -/
theorem loop_plan : Loops.plan loopKey =
    { ia := #[0,0,0], ib := #[2,1,0], code := ⟨#[0,1,0]⟩,
      coef := #[1,-1,1], rowStart := #[0,1,2,3], nested := 0 } := by
  apply plan_ext <;> decide +kernel

/-- Shared first-term evaluation follows derived equality of the actual computed plans. -/
theorem loop_formula {α : Type} [Coeff α] (x : Values α 1) (y : Values α 3) :
    Loops.run true loopKey x.data y.data = formula x y := by
  change Loops.eval (k := 3) true (Loops.plan loopKey) x.data y.data =
    R3TopContraction.formula x y
  rw [loop_plan.trans R3TopContraction.loop_plan.symm]
  exact R3TopContraction.loop_formula x y

/-- Actual top-grade fast fallback compares the routes under the same arbitrary provider. -/
theorem raw_fallback {α : Type} [Coeff α] (kernels : Kernels ℝ3)
    (a : Chain ℝ3 3 α) (b : Chain ℝ3 2 α) :
    @TA.contractionF ℝ3 α _ kernels Gen.ℝ3.instDynKernels (.chain 3 a) (.chain 2 b) =
      @TA.contraction ℝ3 α _ kernels (.chain 3 a) (.chain 2 b) := by
  simp only [TA.contractionF, TA.prodF, TA.contraction,
    show decide (3 < 3) = false from rfl, Bool.and_false, Bool.false_and,
    Bool.false_eq_true, ite_false, ite_self]

/-- Actual frozen reference route retains all three stored vector slots, including zero. -/
theorem reference_formula {α : Type} [Coeff α] (a : Chain ℝ3 3 α) (b : Chain ℝ3 2 α) :
    @TA.contraction ℝ3 α _ Gen.ℝ3.instKernels (.chain 3 a) (.chain 2 b) =
      .chain 1 ⟨formula a.v b.v⟩ := by
  change TA.chain 1 ⟨Loops.run true loopKey a.v.data b.v.data⟩ = _
  exact congrArg (fun v : Values α 3 ↦ (TA.chain 1 ⟨v⟩ : TA ℝ3 α)) (loop_formula a.v b.v)

/-- Actual frozen fast fallback has the complete stored vector payload. -/
theorem fast_formula {α : Type} [Coeff α] (a : Chain ℝ3 3 α) (b : Chain ℝ3 2 α) :
    @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 3 a) (.chain 2 b) =
      .chain 1 ⟨formula a.v b.v⟩ :=
  (raw_fallback Gen.ℝ3.instKernels a b).trans (reference_formula a b)

/-- Universal raw fast/reference equality for arbitrary top/bivector inputs and every Coeff. -/
theorem contractionF_eq_contraction {α : Type} [Coeff α]
    (a : Chain ℝ3 3 α) (b : Chain ℝ3 2 α) :
    @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 3 a) (.chain 2 b) =
      @TA.contraction ℝ3 α _ Gen.ℝ3.instKernels (.chain 3 a) (.chain 2 b) :=
  raw_fallback Gen.ℝ3.instKernels a b

/-- Existing concrete typed contraction uses the actual emitted kernel and stored vector. -/
theorem typed_formula {α : Type} [Coeff α] (a : Chain ℝ3 3 α) (b : Chain ℝ3 2 α) :
    (a ⋅ b : Chain ℝ3 1 α) = ⟨formula a.v b.v⟩ :=
  congrArg (fun v : Values α 3 ↦ (⟨v⟩ : Chain ℝ3 1 α)) (generated a.v b.v)

/-- Existing concrete typed contraction agrees with raw dynamic storage without scalar laws. -/
theorem typed_eq_fast {α : Type} [Coeff α] (a : Chain ℝ3 3 α) (b : Chain ℝ3 2 α) :
    (TA.chain 1 (a ⋅ b : Chain ℝ3 1 α) : TA ℝ3 α) =
      @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 3 a) (.chain 2 b) := by
  rw [typed_formula, fast_formula]

/-- Reversing the grades returns symbolic Zero, not a stored scalar Chain. -/
theorem reverse_zero {α : Type} [Coeff α] (a : Chain ℝ3 3 α) (b : Chain ℝ3 2 α) :
    @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 2 b) (.chain 3 a) =
      .zero := by
  simp only [TA.contractionF, TA.prodF,
    show decide (3 < 3) = false from rfl, Bool.and_false,
    Bool.false_eq_true, ite_false, ite_self]
  rfl

/-- Reuse the zero-first scalar payload, without identifying it with the first-term result. -/
@[specialize] def staticFormula {α : Type} [Coeff α] (x : Values α 1) (y : Values α 3) :
    Values α 3 := R3TopContraction.staticFormula x y

/-- Actual strict replacing reference-provider key for top/bivector inputs. -/
def staticKey : PlanKey :=
  { V := ℝ3, op := .bin .contraction, la := .chain 3, lb := .chain 2, lc := .chain 1 }

/-- Actual strict reference plan, derived independently for this input/output layout. -/
theorem static_plan : Grassmann.Kernel.plan staticKey = .ok
    { ia := #[0,0,0], ib := #[2,1,0], code := ⟨#[0,1,0]⟩,
      coef := #[1,-1,1], rowStart := #[0,1,2,3], nested := 0 } := by
  have ia : (Grassmann.Kernel.plan staticKey).toOption.map (·.ia) = some #[0,0,0] :=
    by decide +kernel
  have ib : (Grassmann.Kernel.plan staticKey).toOption.map (·.ib) = some #[2,1,0] :=
    by decide +kernel
  have code : (Grassmann.Kernel.plan staticKey).toOption.map (·.code) = some ⟨#[0,1,0]⟩ :=
    by decide +kernel
  have coef : (Grassmann.Kernel.plan staticKey).toOption.map (·.coef) = some #[1,-1,1] :=
    by decide +kernel
  have rows : (Grassmann.Kernel.plan staticKey).toOption.map (·.rowStart) = some #[0,1,2,3] :=
    by decide +kernel
  have nested : (Grassmann.Kernel.plan staticKey).toOption.map (·.nested) = some 0 :=
    by decide +kernel
  generalize hp : Grassmann.Kernel.plan staticKey = p at *
  cases p with
  | error e => cases ia
  | ok p =>
    apply congrArg (fun p : Plan ↦ (Except.ok p : Except String Plan))
    exact plan_ext (Option.some.inj ia) (Option.some.inj ib) (Option.some.inj code)
      (Option.some.inj coef) (Option.some.inj rows) (Option.some.inj nested)

/-- Actual zero-first evaluation is reused only after equality of the computed static plans. -/
theorem static_bin_formula {α : Type} [Coeff α] (x : Values α 1) (y : Values α 3) :
    @Kernels.bin ℝ3 (Kernels.reference ℝ3) α _ .contraction
      (.chain 3) (.chain 2) (.chain 1) x y = staticFormula x y := by
  change (match Grassmann.Kernel.plan staticKey with
    | .ok p => p.eval₂ x y
    | .error e => panic! e) = R3TopContraction.staticFormula x y
  rw [static_plan.trans R3TopContraction.static_plan.symm]
  exact R3TopContraction.static_bin_formula x y

/-- Two sufficient actual zero identities identify the replacing/generated providers. -/
theorem reference_bin_eq_generated {α : Type} [Coeff α]
    (zeroAdd : ∀ p : α, AbstractTensors.Coeff.zero + p = p)
    (zeroSub : ∀ p : α, AbstractTensors.Coeff.zero - p = -p)
    (x : Values α 1) (y : Values α 3) :
    @Kernels.bin ℝ3 (Kernels.reference ℝ3) α _ .contraction
      (.chain 3) (.chain 2) (.chain 1) x y =
      @Kernels.bin ℝ3 Gen.ℝ3.instKernels α _ .contraction
        (.chain 3) (.chain 2) (.chain 1) x y := by
  rw [static_bin_formula, bin]
  exact R3TopContraction.staticFormula_eq_formula zeroAdd zeroSub x y

/-- Genuine default Rat scalar identities identify these actual provider outputs. -/
theorem rational_reference_bin_eq_generated (x : Values Rat 1) (y : Values Rat 3) :
    @Kernels.bin ℝ3 (Kernels.reference ℝ3) Rat _ .contraction
      (.chain 3) (.chain 2) (.chain 1) x y =
      @Kernels.bin ℝ3 Gen.ℝ3.instKernels Rat _ .contraction
        (.chain 3) (.chain 2) (.chain 1) x y :=
  reference_bin_eq_generated LawfulCoeff.zero_add
    (fun p ↦ by rw [LawfulCoeff.sub_eq_add_neg, LawfulCoeff.zero_add]) x y

/-- Genuine default unbounded Int scalar identities give the same provider bridge. -/
theorem integer_reference_bin_eq_generated (x : Values Int 1) (y : Values Int 3) :
    @Kernels.bin ℝ3 (Kernels.reference ℝ3) Int _ .contraction
      (.chain 3) (.chain 2) (.chain 1) x y =
      @Kernels.bin ℝ3 Gen.ℝ3.instKernels Int _ .contraction
        (.chain 3) (.chain 2) (.chain 1) x y :=
  reference_bin_eq_generated LawfulCoeff.zero_add
    (fun p ↦ by rw [LawfulCoeff.sub_eq_add_neg, LawfulCoeff.zero_add]) x y

end Grassmann.Kernel.R3TopBivectorContraction

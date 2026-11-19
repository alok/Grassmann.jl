/- Optional R3 grade-three/grade-one stored bivector contraction proofs.
Julia real-domain dispatch: Grassmann src/products.jl:1165; TA's no-conj policy is retained. -/
import Grassmann.Kernel.R3BivectorPairingLaws

namespace Grassmann.Kernel.R3TopContraction
open DirectSum StaticVectors

private theorem get_set {α : Type} [Packed α] {n : Nat} (v : Values α n)
    (i j : Fin n) (x : α) :
    (v.set i x).get j = if i.val = j.val then x else v.get j :=
  Packed.get_set v.data _ x j.val _

private theorem plan_ext {p q : Plan} (ia : p.ia = q.ia) (ib : p.ib = q.ib)
    (code : p.code = q.code) (coef : p.coef = q.coef)
    (rows : p.rowStart = q.rowStart) (nested : p.nested = q.nested) : p = q := by
  cases p; cases q; simp_all

/-- Ordered bivector coordinates in [e12,e13,e23], retaining actual multiplication and Neg. -/
@[specialize] def formula {α : Type} [Coeff α] (x : Values α 1) (y : Values α 3) :
    Values α 3 :=
  Values.ofFn fun i ↦ match i.val with
    | 0 => x.get 0 * y.get 2
    | 1 => -(x.get 0 * y.get 1)
    | _ => x.get 0 * y.get 0

/-- Actual emitted top-grade kernel writes all three slots without scalar algebra laws. -/
theorem generated {α : Type} [Coeff α] (x : Values α 1) (y : Values α 3) :
    Gen.ℝ3.k_bin_contraction_c3_c1_c2 x y = formula x y := by
  apply Values.ext
  intro ⟨i, hi⟩
  change i < 3 at hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases with h | h | h <;> subst i <;>
    simp [Gen.ℝ3.k_bin_contraction_c3_c1_c2, formula, get_set]
  all_goals
    intro h
    change (2 : Nat) = _ at h
    omega

/-- Actual concrete generated bin dispatch, separate from the dynamic top-grade fallback. -/
theorem bin {α : Type} [Coeff α] (x : Values α 1) (y : Values α 3) :
    @Kernels.bin ℝ3 Gen.ℝ3.instKernels α _ .contraction (.chain 3) (.chain 1) (.chain 2)
      x y = formula x y := generated x y

/-- Actual pseudoscalar/vector input and bivector output layouts. -/
theorem layouts : (Layout.chain 3).blades 3 = #[7] ∧
    (Layout.chain 1).blades 3 = #[1,2,4] ∧ (Layout.chain 2).blades 3 = #[3,5,6] :=
  by decide +kernel

/-- Actual first-operand-outermost expression-loop key for this top-grade pair. -/
def loopKey : Loops.JKey :=
  { V := ℝ3, op := .contraction, a := .dense (.chain 3), b := .dense (.chain 1),
    lc := .chain 2, outerFirst := true }

/-- Computed three-entry plan: one signed term per output, without initial scalar zero. -/
theorem loop_plan : Loops.plan loopKey =
    { ia := #[0,0,0], ib := #[2,1,0], code := ⟨#[0,1,0]⟩,
      coef := #[1,-1,1], rowStart := #[0,1,2,3], nested := 0 } := by
  apply plan_ext <;> decide +kernel

/-- Actual first-term reference evaluator and its complete stored output. -/
theorem loop_formula {α : Type} [Coeff α] (x : Values α 1) (y : Values α 3) :
    Loops.run true loopKey x.data y.data = formula x y := by
  change Loops.eval (k := 3) true (Loops.plan loopKey) x.data y.data = formula x y
  rw [loop_plan]
  dsimp [Loops.eval, Plan.Aligned, ByteArray.size]
  repeat (rw [Loops.fill]; dsimp)
  dsimp [Loops.row, Loops.first, Plan.acc]
  repeat (rw [Plan.row₂]; dsimp [Plan.acc])
  simp [Plan.rd, x.size_eq, y.size_eq, ByteArray.getElem_eq_getElem_data]
  apply Values.ext
  intro ⟨i, hi⟩
  change i < 3 at hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases with h | h | h <;> subst i <;>
    simp only [formula, Values.get_ofFn] <;> (simp only [get_set]; dsimp; simp [Values.get])

/-- Top-grade fast routing falls back for this exact pair, under any ambient Kernels. -/
theorem raw_fallback {α : Type} [Coeff α] (kernels : Kernels ℝ3)
    (a : Chain ℝ3 3 α) (b : Chain ℝ3 1 α) :
    @TA.contractionF ℝ3 α _ kernels Gen.ℝ3.instDynKernels (.chain 3 a) (.chain 1 b) =
      @TA.contraction ℝ3 α _ kernels (.chain 3 a) (.chain 1 b) := by
  simp only [TA.contractionF, TA.prodF, TA.contraction,
    show decide (3 < 3) = false from rfl, Bool.and_false, Bool.false_and,
    Bool.false_eq_true, ite_false, ite_self]

/-- Actual frozen dynamic reference route retains the stored bivector, including zero. -/
theorem reference_formula {α : Type} [Coeff α] (a : Chain ℝ3 3 α) (b : Chain ℝ3 1 α) :
    @TA.contraction ℝ3 α _ Gen.ℝ3.instKernels (.chain 3 a) (.chain 1 b) =
      .chain 2 ⟨formula a.v b.v⟩ := by
  change TA.chain 2 ⟨Loops.run true loopKey a.v.data b.v.data⟩ = _
  exact congrArg (fun v : Values α 3 ↦ (TA.chain 2 ⟨v⟩ : TA ℝ3 α)) (loop_formula a.v b.v)

/-- Actual frozen fast fallback has the same complete stored bivector payload. -/
theorem fast_formula {α : Type} [Coeff α] (a : Chain ℝ3 3 α) (b : Chain ℝ3 1 α) :
    @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 3 a) (.chain 1 b) =
      .chain 2 ⟨formula a.v b.v⟩ :=
  (raw_fallback Gen.ℝ3.instKernels a b).trans (reference_formula a b)

/-- Universal raw fast/reference equality for arbitrary inputs and every Coeff. -/
theorem contractionF_eq_contraction {α : Type} [Coeff α]
    (a : Chain ℝ3 3 α) (b : Chain ℝ3 1 α) :
    @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 3 a) (.chain 1 b) =
      @TA.contraction ℝ3 α _ Gen.ℝ3.instKernels (.chain 3 a) (.chain 1 b) :=
  raw_fallback Gen.ℝ3.instKernels a b

/-- Existing typed contraction uses the actual emitted first-term kernel for this pair. -/
theorem typed_formula {α : Type} [Coeff α] (a : Chain ℝ3 3 α) (b : Chain ℝ3 1 α) :
    (a ⋅ b : Chain ℝ3 2 α) = ⟨formula a.v b.v⟩ :=
  congrArg (fun v : Values α 3 ↦ (⟨v⟩ : Chain ℝ3 2 α)) (generated a.v b.v)

/-- Existing concrete typed contraction agrees with actual raw dynamic storage for all Coeff. -/
theorem typed_eq_fast {α : Type} [Coeff α] (a : Chain ℝ3 3 α) (b : Chain ℝ3 1 α) :
    (TA.chain 2 (a ⋅ b : Chain ℝ3 2 α) : TA ℝ3 α) =
      @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 3 a) (.chain 1 b) := by
  rw [typed_formula, fast_formula]

/-- The reversed dynamic grade pair is symbolic Zero, not a stored scalar Chain. -/
theorem reverse_zero {α : Type} [Coeff α] (a : Chain ℝ3 3 α) (b : Chain ℝ3 1 α) :
    @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 1 b) (.chain 3 a) =
      .zero := by
  simp only [TA.contractionF, TA.prodF,
    show decide (3 < 3) = false from rfl, Bool.and_false,
    Bool.false_eq_true, ite_false, ite_self]
  rfl

/-- The separately replacing reference provider retains zero-first Add/Sub in every slot. -/
@[specialize] def staticFormula {α : Type} [Coeff α] (x : Values α 1) (y : Values α 3) :
    Values α 3 :=
  Values.ofFn fun i ↦ match i.val with
    | 0 => AbstractTensors.Coeff.zero + x.get 0 * y.get 2
    | 1 => AbstractTensors.Coeff.zero - x.get 0 * y.get 1
    | _ => AbstractTensors.Coeff.zero + x.get 0 * y.get 0

/-- Equality with zero-first storage needs exactly these actual operation identities. -/
theorem staticFormula_eq_formula {α : Type} [Coeff α]
    (zeroAdd : ∀ p : α, AbstractTensors.Coeff.zero + p = p)
    (zeroSub : ∀ p : α, AbstractTensors.Coeff.zero - p = -p)
    (x : Values α 1) (y : Values α 3) : staticFormula x y = formula x y := by
  apply Values.ext
  intro i
  simp only [staticFormula, formula, Values.get_ofFn]
  split <;> simp only [zeroAdd, zeroSub]

/-- Genuine default Rat scalar identities justify the separate zero-first normalization. -/
theorem rational_staticFormula_eq_formula (x : Values Rat 1) (y : Values Rat 3) :
    staticFormula x y = formula x y :=
  staticFormula_eq_formula LawfulCoeff.zero_add
    (fun p ↦ by rw [LawfulCoeff.sub_eq_add_neg, LawfulCoeff.zero_add]) x y

/-- Genuine default unbounded Int identities justify the same separate normalization. -/
theorem integer_staticFormula_eq_formula (x : Values Int 1) (y : Values Int 3) :
    staticFormula x y = formula x y :=
  staticFormula_eq_formula LawfulCoeff.zero_add
    (fun p ↦ by rw [LawfulCoeff.sub_eq_add_neg, LawfulCoeff.zero_add]) x y

/-- Actual strict static reference key; this route accumulates each row from scalar zero. -/
def staticKey : PlanKey :=
  { V := ℝ3, op := .bin .contraction, la := .chain 3, lb := .chain 1, lc := .chain 2 }

/-- Computed actual strict reference plan, with one signed term in each output row. -/
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

/-- The actual reference provider computes zero-first Add/Sub, without algebra laws. -/
theorem static_bin_formula {α : Type} [Coeff α] (x : Values α 1) (y : Values α 3) :
    @Kernels.bin ℝ3 (Kernels.reference ℝ3) α _ .contraction
      (.chain 3) (.chain 1) (.chain 2) x y = staticFormula x y := by
  change refBin ℝ3 .contraction (.chain 3) (.chain 1) (.chain 2) x y = staticFormula x y
  unfold refBin
  change (match Grassmann.Kernel.plan staticKey with
    | .ok p => p.eval₂ x y
    | .error e => panic! e) = staticFormula x y
  rw [static_plan]
  dsimp only [Plan.eval₂]
  rw [dite_eq_left (by decide +kernel)]
  repeat (rw [Plan.fill₂]; dsimp)
  repeat (rw [Plan.row₂]; dsimp [Plan.acc])
  simp [Plan.rd, x.size_eq, y.size_eq, ByteArray.getElem_eq_getElem_data]
  apply Values.ext
  intro ⟨i, hi⟩
  change i < 3 at hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases with h | h | h <;> subst i <;>
    simp only [staticFormula, Values.get_ofFn] <;> (simp only [get_set]; dsimp; simp [Values.get])

/-- Equality of the actual reference/generated providers uses exactly the two zero laws. -/
theorem reference_bin_eq_generated {α : Type} [Coeff α]
    (zeroAdd : ∀ p : α, AbstractTensors.Coeff.zero + p = p)
    (zeroSub : ∀ p : α, AbstractTensors.Coeff.zero - p = -p)
    (x : Values α 1) (y : Values α 3) :
    @Kernels.bin ℝ3 (Kernels.reference ℝ3) α _ .contraction
      (.chain 3) (.chain 1) (.chain 2) x y =
      @Kernels.bin ℝ3 Gen.ℝ3.instKernels α _ .contraction
        (.chain 3) (.chain 1) (.chain 2) x y := by
  rw [static_bin_formula, bin]
  exact staticFormula_eq_formula zeroAdd zeroSub x y

/-- Genuine default Rat zero identities identify the two actual providers. -/
theorem rational_reference_bin_eq_generated (x : Values Rat 1) (y : Values Rat 3) :
    @Kernels.bin ℝ3 (Kernels.reference ℝ3) Rat _ .contraction
      (.chain 3) (.chain 1) (.chain 2) x y =
      @Kernels.bin ℝ3 Gen.ℝ3.instKernels Rat _ .contraction
        (.chain 3) (.chain 1) (.chain 2) x y :=
  reference_bin_eq_generated LawfulCoeff.zero_add
    (fun p ↦ by rw [LawfulCoeff.sub_eq_add_neg, LawfulCoeff.zero_add]) x y

/-- Genuine default unbounded Int zero identities identify the two actual providers. -/
theorem integer_reference_bin_eq_generated (x : Values Int 1) (y : Values Int 3) :
    @Kernels.bin ℝ3 (Kernels.reference ℝ3) Int _ .contraction
      (.chain 3) (.chain 1) (.chain 2) x y =
      @Kernels.bin ℝ3 Gen.ℝ3.instKernels Int _ .contraction
        (.chain 3) (.chain 1) (.chain 2) x y :=
  reference_bin_eq_generated LawfulCoeff.zero_add
    (fun p ↦ by rw [LawfulCoeff.sub_eq_add_neg, LawfulCoeff.zero_add]) x y

end Grassmann.Kernel.R3TopContraction

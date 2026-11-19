/- Optional raw top-grade proofs for the concrete generated Euclidean R3 provider. -/
import Grassmann.Kernel.R3WedgeLaws

namespace Grassmann.Kernel.R3TopWedge
open DirectSum StaticVectors AbstractTensors

private theorem get_set {α : Type} [Packed α] {n : Nat} (v : Values α n)
    (i j : Fin n) (x : α) :
    (v.set i x).get j = if i.val = j.val then x else v.get j :=
  Packed.get_set v.data _ x j.val _

private theorem plan_ext {p q : Plan} (ia : p.ia = q.ia) (ib : p.ib = q.ib)
    (code : p.code = q.code) (coef : p.coef = q.coef)
    (rows : p.rowStart = q.rowStart) (nested : p.nested = q.nested) : p = q := by
  cases p; cases q; simp_all

/-- Actual ordered top coordinate for grade2/grade1 or grade1/grade2 inputs.
The two input conventions differ; operand order and left grouping are retained. -/
@[specialize] def coordinate {α : Type} [Coeff α] (x y : Values α 3) : α :=
  (x.get ⟨0, by decide⟩ * y.get ⟨2, by decide⟩ -
    x.get ⟨1, by decide⟩ * y.get ⟨1, by decide⟩) +
    x.get ⟨2, by decide⟩ * y.get ⟨0, by decide⟩

/-- One stored top-grade slot; no symbolic zero normalization. -/
def formula {α : Type} [Coeff α] (x y : Values α 3) : Values α 1 :=
  Values.ofFn fun _ => coordinate x y

/-- Actual emitted grade2/grade1 storage refines for every operations-only input. -/
theorem generated21 {α : Type} [Coeff α] (x y : Values α 3) :
    Gen.ℝ3.k_bin_wedge_c2_c1_c3 x y = formula x y := by
  apply Values.ext
  intro ⟨i, hi⟩
  change i < 1 at hi
  have h : i = 0 := by omega
  subst i
  simp [Gen.ℝ3.k_bin_wedge_c2_c1_c3, formula, coordinate, get_set]

/-- Actual emitted grade1/grade2 storage, without equating the two operand orders. -/
theorem generated12 {α : Type} [Coeff α] (x y : Values α 3) :
    Gen.ℝ3.k_bin_wedge_c1_c2_c3 x y = formula x y := by
  apply Values.ext
  intro ⟨i, hi⟩
  change i < 1 at hi
  have h : i = 0 := by omega
  subst i
  simp [Gen.ℝ3.k_bin_wedge_c1_c2_c3, formula, coordinate, get_set]

/-- Concrete generated grade2/grade1 bin dispatch. -/
theorem bin21 {α : Type} [Coeff α] (x y : Values α 3) :
    @Kernels.bin ℝ3 Gen.ℝ3.instKernels α _ .wedge (.chain 2) (.chain 1) (.chain 3) x y =
      formula x y := generated21 x y

/-- Concrete generated grade1/grade2 bin dispatch. -/
theorem bin12 {α : Type} [Coeff α] (x y : Values α 3) :
    @Kernels.bin ℝ3 Gen.ℝ3.instKernels α _ .wedge (.chain 1) (.chain 2) (.chain 3) x y =
      formula x y := generated12 x y

/-- Actual input and top output layouts. -/
theorem layouts : (Layout.chain 1).blades 3 = #[1,2,4] ∧
    (Layout.chain 2).blades 3 = #[3,5,6] ∧ (Layout.chain 3).blades 3 = #[7] :=
  by decide +kernel

/-- Actual first-operand-outer key; true selects grade1/grade2, false grade2/grade1. -/
def loopKey (reverse : Bool) : Loops.JKey :=
  { V := ℝ3, op := .wedge, a := .dense (.chain (if reverse then 1 else 2)),
    b := .dense (.chain (if reverse then 2 else 1)), lc := .chain 3, outerFirst := true }

/-- Both actual computed three-entry plans, without a supplied plan witness. -/
theorem loop_plan (reverse : Bool) : Loops.plan (loopKey reverse) =
    { ia := #[0,1,2], ib := #[2,1,0], code := ⟨#[0,1,0]⟩,
      coef := #[1,-1,1], rowStart := #[0,3], nested := 0 } := by
  cases reverse <;> apply plan_ext <;> decide +kernel

/-- Actual single first-term reference row retains (first-second)+third grouping. -/
theorem loop_formula {α : Type} [Coeff α] (reverse : Bool) (x y : Values α 3) :
    Loops.eval (k := 1) true (Loops.plan (loopKey reverse)) x.data y.data = formula x y := by
  rw [loop_plan]
  dsimp [Loops.eval, Plan.Aligned, ByteArray.size]
  repeat (rw [Loops.fill]; dsimp)
  dsimp [Loops.row, Loops.first, Plan.acc]
  repeat (rw [Plan.row₂]; dsimp [Plan.acc])
  simp [Plan.rd, x.size_eq, y.size_eq, ByteArray.getElem_eq_getElem_data]
  apply Values.ext
  intro ⟨i, hi⟩
  change i < 1 at hi
  have h : i = 0 := by omega
  subst i
  simp only [formula, Values.get_ofFn]
  simp only [coordinate, get_set]; dsimp; simp [Values.get]

/-- Actual fast grade2/grade1 routing with generated provider and true selector frozen. -/
theorem fast21 {α : Type} [Coeff α] (a : Chain ℝ3 2 α) (b : Chain ℝ3 1 α) :
    @TA.wedgeF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 2 a) (.chain 1 b) =
      .chain 3 ⟨formula a.v b.v⟩ :=
  congrArg (fun v : Values α 1 => (TA.chain 3 ⟨v⟩ : TA ℝ3 α)) (generated21 a.v b.v)

/-- Actual fast grade1/grade2 routing, proved independently of coefficient commutation. -/
theorem fast12 {α : Type} [Coeff α] (a : Chain ℝ3 1 α) (b : Chain ℝ3 2 α) :
    @TA.wedgeF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 1 a) (.chain 2 b) =
      .chain 3 ⟨formula a.v b.v⟩ :=
  congrArg (fun v : Values α 1 => (TA.chain 3 ⟨v⟩ : TA ℝ3 α)) (generated12 a.v b.v)

/-- Actual reference grade2/grade1 routing and stored top-grade shape. -/
theorem reference21 {α : Type} [Coeff α] (a : Chain ℝ3 2 α) (b : Chain ℝ3 1 α) :
    @TA.wedge ℝ3 α _ Gen.ℝ3.instKernels (.chain 2 a) (.chain 1 b) =
      .chain 3 ⟨formula a.v b.v⟩ :=
  congrArg (fun v : Values α 1 => (TA.chain 3 ⟨v⟩ : TA ℝ3 α)) (loop_formula false a.v b.v)

/-- Actual reference grade1/grade2 routing and stored top-grade shape. -/
theorem reference12 {α : Type} [Coeff α] (a : Chain ℝ3 1 α) (b : Chain ℝ3 2 α) :
    @TA.wedge ℝ3 α _ Gen.ℝ3.instKernels (.chain 1 a) (.chain 2 b) =
      .chain 3 ⟨formula a.v b.v⟩ :=
  congrArg (fun v : Values α 1 => (TA.chain 3 ⟨v⟩ : TA ℝ3 α)) (loop_formula true a.v b.v)

/-- Universal RAW grade2/grade1 fast/reference equality, including stored zeros. -/
theorem wedgeF_eq_wedge21 {α : Type} [Coeff α] (a : Chain ℝ3 2 α) (b : Chain ℝ3 1 α) :
    @TA.wedgeF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 2 a) (.chain 1 b) =
      @TA.wedge ℝ3 α _ Gen.ℝ3.instKernels (.chain 2 a) (.chain 1 b) :=
  (fast21 a b).trans (reference21 a b).symm

/-- Universal RAW grade1/grade2 equality; no relation between the operand orders is assumed. -/
theorem wedgeF_eq_wedge12 {α : Type} [Coeff α] (a : Chain ℝ3 1 α) (b : Chain ℝ3 2 α) :
    @TA.wedgeF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 1 a) (.chain 2 b) =
      @TA.wedge ℝ3 α _ Gen.ℝ3.instKernels (.chain 1 a) (.chain 2 b) :=
  (fast12 a b).trans (reference12 a b).symm

/-- Actual coeff7 reads the only top-grade slot, with no algebraic law. -/
theorem coeff_top {α : Type} [Coeff α] (v : Values α 1) :
    (TA.chain 3 ⟨v⟩ : TA ℝ3 α).coeff 7 = v.get ⟨0, by decide⟩ := rfl

end Grassmann.Kernel.R3TopWedge

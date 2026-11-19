/- Optional plain R3 Chain contraction refinements, with concrete generated provider frozen.
Julia dispatch: Grassmann src/products.jl:1165; TA's existing no-conj policy is preserved. -/
import Grassmann.Kernel.R3ChainLaws

namespace Grassmann.Kernel.R3Contraction
open DirectSum StaticVectors AbstractTensors

private theorem get_set {α : Type} [Packed α] {n : Nat} (v : Values α n)
    (i j : Fin n) (x : α) :
    (v.set i x).get j = if i.val = j.val then x else v.get j :=
  Packed.get_set v.data _ x j.val _

private theorem plan_ext {p q : Plan} (ia : p.ia = q.ia) (ib : p.ib = q.ib)
    (code : p.code = q.code) (coef : p.coef = q.coef)
    (rows : p.rowStart = q.rowStart) (nested : p.nested = q.nested) : p = q := by
  cases p; cases q; simp_all

/-- Actual plain ordered coordinate; no conjugation, reassociation or scalar law. -/
@[specialize] def coordinate {α : Type} [Coeff α] (x y : Values α 3) : α :=
  (x.get ⟨0, by decide⟩ * y.get ⟨0, by decide⟩ +
    x.get ⟨1, by decide⟩ * y.get ⟨1, by decide⟩) +
    x.get ⟨2, by decide⟩ * y.get ⟨2, by decide⟩

/-- Complete stored scalar-grade payload, including coefficient zero. -/
def formula {α : Type} [Coeff α] (x y : Values α 3) : Values α 1 :=
  Values.ofFn fun _ ↦ coordinate x y

/-- Actual emitted storage, for every operations-only coefficient input. -/
theorem generated {α : Type} [Coeff α] (x y : Values α 3) :
    Gen.ℝ3.k_bin_contraction_c1_c1_c0 x y = formula x y := by
  apply Values.ext
  intro ⟨i, hi⟩
  change i < 1 at hi
  have h : i = 0 := by omega
  subst i
  simp [Gen.ℝ3.k_bin_contraction_c1_c1_c0, formula, coordinate, get_set]

/-- Concrete generated contraction bin dispatch. -/
theorem bin {α : Type} [Coeff α] (x y : Values α 3) :
    @Kernels.bin ℝ3 Gen.ℝ3.instKernels α _ .contraction (.chain 1) (.chain 1) (.chain 0)
      x y = formula x y := generated x y

/-- Actual vector and scalar-grade basis order. -/
theorem layouts : (Layout.chain 1).blades 3 = #[1,2,4] ∧
    (Layout.chain 0).blades 3 = #[0] := by decide +kernel

/-- Actual first-operand-outer expression-form contraction key. -/
def loopKey : Loops.JKey :=
  { V := ℝ3, op := .contraction, a := .dense (.chain 1), b := .dense (.chain 1),
    lc := .chain 0, outerFirst := true }

/-- Actual computed plan, with no supplied plan or basis-result premise. -/
theorem loop_plan : Loops.plan loopKey =
    { ia := #[0,1,2], ib := #[0,1,2], code := ⟨#[0,0,0]⟩,
      coef := #[1,1,1], rowStart := #[0,3], nested := 0 } := by
  apply plan_ext <;> decide +kernel

/-- Actual first-term loop retains (first+second)+third without an initial zero. -/
theorem loop_formula {α : Type} [Coeff α] (x y : Values α 3) :
    Loops.eval (k := 1) true (Loops.plan loopKey) x.data y.data = formula x y := by
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

/-- Actual frozen fast routing preserves a raw stored scalar-grade Chain. -/
theorem fast_formula {α : Type} [Coeff α] (a b : Chain ℝ3 1 α) :
    @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 1 a) (.chain 1 b) =
      .chain 0 ⟨formula a.v b.v⟩ :=
  congrArg (fun v : Values α 1 ↦ (TA.chain 0 ⟨v⟩ : TA ℝ3 α)) (generated a.v b.v)

/-- Actual reference routing reduces Loops.run to the computed one-slot first-term loop. -/
theorem reference_formula {α : Type} [Coeff α] (a b : Chain ℝ3 1 α) :
    @TA.contraction ℝ3 α _ Gen.ℝ3.instKernels (.chain 1 a) (.chain 1 b) =
      .chain 0 ⟨formula a.v b.v⟩ :=
  congrArg (fun v : Values α 1 ↦ (TA.chain 0 ⟨v⟩ : TA ℝ3 α)) (loop_formula a.v b.v)

/-- Universal RAW fast/reference equality for the frozen generated R3 vector fragment. -/
theorem contractionF_eq_contraction {α : Type} [Coeff α] (a b : Chain ℝ3 1 α) :
    @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 1 a) (.chain 1 b) =
      @TA.contraction ℝ3 α _ Gen.ℝ3.instKernels (.chain 1 a) (.chain 1 b) :=
  (fast_formula a b).trans (reference_formula a b).symm

/-- Actual coeff0 reads the only scalar-grade slot; raw Chain shape is retained. -/
theorem coeff_scalar {α : Type} [Coeff α] (v : Values α 1) :
    (TA.chain 0 ⟨v⟩ : TA ℝ3 α).coeff 0 = v.get ⟨0, by decide⟩ := rfl

/-- Plain ordered pairing on the actual frozen contractionF/coeff0 path, not Hermitian. -/
@[specialize] def pairingCoefficient {α : Type} [Coeff α] (a b : Chain ℝ3 1 α) : α :=
  (@TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 1 a) (.chain 1 b)).coeff 0

/-- Universal executable pairing refinement, with the original grouping and multiplication. -/
theorem pairingCoefficient_formula {α : Type} [Coeff α] (a b : Chain ℝ3 1 α) :
    pairingCoefficient a b = coordinate a.v b.v := by
  unfold pairingCoefficient
  rw [fast_formula, coeff_scalar]
  simp [formula]

/-- Actual executable scalar pairing agrees with the frozen reference computation. -/
theorem pairingCoefficient_eq_reference {α : Type} [Coeff α] (a b : Chain ℝ3 1 α) :
    pairingCoefficient a b =
      (@TA.contraction ℝ3 α _ Gen.ℝ3.instKernels (.chain 1 a) (.chain 1 b)).coeff 0 :=
  congrArg (fun out : TA ℝ3 α ↦ out.coeff 0) (contractionF_eq_contraction a b)

/-- The plain contraction coefficient is the scalar coordinate of the actual geometric product.
This relates two executable paths without assuming any coefficient algebra laws. -/
theorem pairingCoefficient_eq_mulF_scalar {α : Type} [Coeff α] (a b : Chain ℝ3 1 α) :
    pairingCoefficient a b =
      (@TA.mulF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 1 a) (.chain 1 b)).coeff 0 := by
  rw [pairingCoefficient_formula, R3Chain.mulF_formula]
  change coordinate a.v b.v = (R3Chain.formula a.v b.v).get ⟨0, by decide⟩
  simp [R3Chain.formula, coordinate]

/-- Coordinate symmetry requires only actual multiplication commutation, not additive laws. -/
theorem coordinate_symm {α : Type} [Coeff α]
    (comm : ∀ x y : α, x*y = y*x) (x y : Values α 3) :
    coordinate x y = coordinate y x := by
  unfold coordinate
  rw [comm (x.get ⟨0, by decide⟩) (y.get ⟨0, by decide⟩),
    comm (x.get ⟨1, by decide⟩) (y.get ⟨1, by decide⟩),
    comm (x.get ⟨2, by decide⟩) (y.get ⟨2, by decide⟩)]

/-- Symmetry needs only commutation of the actual multiplication operation.
The summand order and addition grouping are identical, so no additive laws are needed. -/
theorem pairingCoefficient_symm {α : Type} [Coeff α]
    (comm : ∀ x y : α, x*y = y*x) (a b : Chain ℝ3 1 α) :
    pairingCoefficient a b = pairingCoefficient b a := by
  rw [pairingCoefficient_formula, pairingCoefficient_formula]
  exact coordinate_symm comm a.v b.v

/-- Genuine default exact Rat multiplication gives arbitrary-input pairing symmetry. -/
theorem rational_symm (a b : Chain ℝ3 1 Rat) : pairingCoefficient a b = pairingCoefficient b a :=
  pairingCoefficient_symm Rat.mul_comm a b

/-- Genuine default unbounded Int multiplication gives the same law without division. -/
theorem integer_symm (a b : Chain ℝ3 1 Int) : pairingCoefficient a b = pairingCoefficient b a :=
  pairingCoefficient_symm Int.mul_comm a b

end Grassmann.Kernel.R3Contraction

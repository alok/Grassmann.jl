/- Optional raw R3 grade-two/grade-one contraction proofs for the frozen generated provider.
Julia real-domain dispatch: Grassmann src/products.jl:1165. TA's no-conj policy is retained. -/
import Grassmann.Kernel.R3ContractionLaws

namespace Grassmann.Kernel.R3BivectorContraction
open DirectSum StaticVectors

private theorem get_set {α : Type} [Packed α] {n : Nat} (v : Values α n)
    (i j : Fin n) (x : α) :
    (v.set i x).get j = if i.val = j.val then x else v.get j :=
  Packed.get_set v.data _ x j.val _

private theorem plan_ext {p q : Plan} (ia : p.ia = q.ia) (ib : p.ib = q.ib)
    (code : p.code = q.code) (coef : p.coef = q.coef)
    (rows : p.rowStart = q.rowStart) (nested : p.nested = q.nested) : p = q := by
  cases p; cases q; simp_all

/-- Actual ordered output coordinates in [e1,e2,e3]; unary Neg and binary Sub stay distinct. -/
@[specialize] def formula {α : Type} [Coeff α] (x y : Values α 3) : Values α 3 :=
  Values.ofFn fun i ↦ match i.val with
    | 0 => -(x.get ⟨0, by decide⟩ * y.get ⟨1, by decide⟩) -
        x.get ⟨1, by decide⟩ * y.get ⟨2, by decide⟩
    | 1 => x.get ⟨0, by decide⟩ * y.get ⟨0, by decide⟩ -
        x.get ⟨2, by decide⟩ * y.get ⟨2, by decide⟩
    | _ => x.get ⟨1, by decide⟩ * y.get ⟨0, by decide⟩ +
        x.get ⟨2, by decide⟩ * y.get ⟨1, by decide⟩

/-- All generated writes refine for arbitrary packed inputs and operations-only coefficients. -/
theorem generated {α : Type} [Coeff α] (x y : Values α 3) :
    Gen.ℝ3.k_bin_contraction_c2_c1_c1 x y = formula x y := by
  apply Values.ext
  intro ⟨i, hi⟩
  change i < 3 at hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases with h | h | h <;> subst i <;>
    simp [Gen.ℝ3.k_bin_contraction_c2_c1_c1, formula, get_set]
  all_goals
    intro h
    change (2 : Nat) = _ at h
    omega

/-- Actual concrete bin dispatch, with no formula witness or scalar laws. -/
theorem bin {α : Type} [Coeff α] (x y : Values α 3) :
    @Kernels.bin ℝ3 Gen.ℝ3.instKernels α _ .contraction (.chain 2) (.chain 1) (.chain 1)
      x y = formula x y := generated x y

/-- Actual bivector/vector input order and vector output layout. -/
theorem layouts : (Layout.chain 2).blades 3 = #[3,5,6] ∧
    (Layout.chain 1).blades 3 = #[1,2,4] := by decide +kernel

/-- Actual expression-form reference key, first operand outermost. -/
def loopKey : Loops.JKey :=
  { V := ℝ3, op := .contraction, a := .dense (.chain 2), b := .dense (.chain 1),
    lc := .chain 1, outerFirst := true }

/-- Computed six-entry plan; the first output starts with a negative term. -/
theorem loop_plan : Loops.plan loopKey =
    { ia := #[0,1,0,2,1,2], ib := #[1,2,0,2,0,1],
      code := ⟨#[1,1,0,1,0,0]⟩, coef := #[-1,-1,1,-1,1,1],
      rowStart := #[0,2,4,6], nested := 0 } := by
  apply plan_ext <;> decide +kernel

/-- Actual first-term evaluator preserves Neg/Sub/Add, operand order and every stored output. -/
theorem loop_formula {α : Type} [Coeff α] (x y : Values α 3) :
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

/-- Actual frozen fast route retains a complete stored grade-one Chain, including zeros. -/
theorem fast_formula {α : Type} [Coeff α] (a : Chain ℝ3 2 α) (b : Chain ℝ3 1 α) :
    @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 2 a) (.chain 1 b) =
      .chain 1 ⟨formula a.v b.v⟩ :=
  congrArg (fun v : Values α 3 ↦ (TA.chain 1 ⟨v⟩ : TA ℝ3 α)) (generated a.v b.v)

/-- Actual frozen reference route uses the computed first-term expression loop. -/
theorem reference_formula {α : Type} [Coeff α] (a : Chain ℝ3 2 α) (b : Chain ℝ3 1 α) :
    @TA.contraction ℝ3 α _ Gen.ℝ3.instKernels (.chain 2 a) (.chain 1 b) =
      .chain 1 ⟨formula a.v b.v⟩ :=
  congrArg (fun v : Values α 3 ↦ (TA.chain 1 ⟨v⟩ : TA ℝ3 α)) (loop_formula a.v b.v)

/-- Universal raw equality for this actual grade pair, without algebra laws or witness premises. -/
theorem contractionF_eq_contraction {α : Type} [Coeff α]
    (a : Chain ℝ3 2 α) (b : Chain ℝ3 1 α) :
    @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 2 a) (.chain 1 b) =
      @TA.contraction ℝ3 α _ Gen.ℝ3.instKernels (.chain 2 a) (.chain 1 b) :=
  (fast_formula a b).trans (reference_formula a b).symm

/-- The existing public typed contraction selects the same frozen generated output. -/
theorem typed_formula {α : Type} [Coeff α] (a : Chain ℝ3 2 α) (b : Chain ℝ3 1 α) :
    (a ⋅ b : Chain ℝ3 1 α) = ⟨formula a.v b.v⟩ :=
  congrArg (fun v : Values α 3 ↦ (⟨v⟩ : Chain ℝ3 1 α)) (generated a.v b.v)

/-- Actual typed contraction agrees with the raw dynamic stored Chain for all coefficients. -/
theorem typed_eq_fast {α : Type} [Coeff α] (a : Chain ℝ3 2 α) (b : Chain ℝ3 1 α) :
    (TA.chain 1 (a ⋅ b : Chain ℝ3 1 α) : TA ℝ3 α) =
      @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 2 a) (.chain 1 b) := by
  rw [typed_formula, fast_formula]

/-- Combining the first coordinate's two negatives requires these actual scalar operation laws. -/
theorem first_neg_sum {α : Type} [Coeff α]
    (sub : ∀ p q : α, p-q = p + -q) (negAdd : ∀ p q : α, -(p+q) = -p + -q)
    (x y : Values α 3) :
    (formula x y).get ⟨0, by decide⟩ =
      -(x.get ⟨0, by decide⟩ * y.get ⟨1, by decide⟩ +
        x.get ⟨1, by decide⟩ * y.get ⟨2, by decide⟩) := by
  simp only [formula, Values.get_ofFn]
  rw [sub, negAdd]

/-- Genuine default Rat subtraction/negation laws justify this separate normalization. -/
theorem rational_first_neg_sum (x y : Values Rat 3) :
    (formula x y).get ⟨0, by decide⟩ = -(x.get 0*y.get 1 + x.get 1*y.get 2) :=
  first_neg_sum LawfulCoeff.sub_eq_add_neg LawfulCoeff.neg_add x y

/-- Genuine default unbounded Int subtraction/negation laws give the same normalization. -/
theorem integer_first_neg_sum (x y : Values Int 3) :
    (formula x y).get ⟨0, by decide⟩ = -(x.get 0*y.get 1 + x.get 1*y.get 2) :=
  first_neg_sum LawfulCoeff.sub_eq_add_neg LawfulCoeff.neg_add x y

end Grassmann.Kernel.R3BivectorContraction

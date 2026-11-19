/- Optional proofs for the concrete generated ℝ3 grade1 Chain product.
Importing this module deliberately imports Generated.R3; Dynamic does not re-export it. -/
import Grassmann.Dynamic
import Grassmann.Kernel.Generated.R3

namespace Grassmann.Kernel.R3Chain

open DirectSum StaticVectors

private theorem get_set {α : Type} [Packed α] {n : Nat} (v : Values α n)
    (i j : Fin n) (x : α) :
    (v.set i x).get j = if i.val = j.val then x else v.get j :=
  Packed.get_set v.data _ x j.val _

private theorem plan_ext {p q : Plan} (ia : p.ia = q.ia) (ib : p.ib = q.ib)
    (code : p.code = q.code) (coef : p.coef = q.coef)
    (rows : p.rowStart = q.rowStart) (nested : p.nested = q.nested) : p = q := by
  cases p; cases q; simp_all

/-- The actual emitted ordered polynomial in even basis [scalar,e12,e13,e23].
This uses only executable Coeff operations, retaining grouping and operand order. -/
def formula {α : Type} [Coeff α] (x y : Values α 3) : Values α 4 :=
  Values.ofFn fun i => match i.val with
    | 0 => (x.get ⟨0, by decide⟩ * y.get ⟨0, by decide⟩ +
        x.get ⟨1, by decide⟩ * y.get ⟨1, by decide⟩) +
        x.get ⟨2, by decide⟩ * y.get ⟨2, by decide⟩
    | 1 => x.get ⟨0, by decide⟩ * y.get ⟨1, by decide⟩ -
        x.get ⟨1, by decide⟩ * y.get ⟨0, by decide⟩
    | 2 => x.get ⟨0, by decide⟩ * y.get ⟨2, by decide⟩ -
        x.get ⟨2, by decide⟩ * y.get ⟨0, by decide⟩
    | _ => x.get ⟨1, by decide⟩ * y.get ⟨2, by decide⟩ -
        x.get ⟨2, by decide⟩ * y.get ⟨1, by decide⟩

/-- Generated storage writes refine to the ordered polynomial for every packed input.
No algebraic law or ambient Kernels instance is assumed. -/
theorem generated_formula {α : Type} [Coeff α] (x y : Values α 3) :
    Gen.ℝ3.k_bin_mul_c1_c1_e x y = formula x y := by
  apply Values.ext
  intro i
  rcases i with ⟨i, hi⟩
  change i < 4 at hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with h | h | h | h <;> subst i <;>
    simp [Gen.ℝ3.k_bin_mul_c1_c1_e, formula, get_set]
  all_goals
    intro h
    change (3 : Nat) = _ at h
    omega

/-- The frozen provider's actual bin dispatch selects the checked emitted definition. -/
theorem generated_bin {α : Type} [Coeff α] (x y : Values α 3) :
    @Kernels.bin ℝ3 Gen.ℝ3.instKernels α _ .mul (.chain 1) (.chain 1) .even x y =
      formula x y := by
  change Gen.ℝ3.k_bin_mul_c1_c1_e x y = formula x y
  exact generated_formula x y

/-- Every well-typed grade1 Chain is covered through its sole arbitrary Values field.
Both the concrete provider and existing true fast selector are frozen explicitly. -/
theorem mulF_formula {α : Type} [Coeff α] (a b : Chain ℝ3 1 α) :
    @TA.mulF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 1 a) (.chain 1 b) =
      .spinor ⟨formula a.v b.v⟩ := by
  change (TA.spinor ⟨Gen.ℝ3.k_bin_mul_c1_c1_e a.v b.v⟩ : TA ℝ3 α) = _
  exact congrArg (fun v : Values α 4 => (TA.spinor ⟨v⟩ : TA ℝ3 α))
    (generated_formula (show Values α 3 from a.v) (show Values α 3 from b.v))

/-- Actual storage order, independent of any coefficient or provider law. -/
theorem layouts : (Layout.chain 1).blades 3 = #[1,2,4] ∧
    Layout.even.blades 3 = #[0,3,5,6] := by decide +kernel

/-- The actual Julia expression-loop key for this bounded grade pair. -/
def loopKey : Loops.JKey :=
  { V := ℝ3, op := .mul, a := .dense (.chain 1), b := .dense (.chain 1),
    lc := .even, outerFirst := true }

/-- Closed row data is checked against the actual executable plan builder. -/
theorem loop_plan : Loops.plan loopKey =
    { ia := #[0,1,2,0,1,0,2,1,2], ib := #[0,1,2,1,0,2,0,2,1],
      code := ⟨#[0,0,0,0,1,0,1,0,1]⟩, coef := #[1,1,1,1,-1,1,-1,1,-1],
      rowStart := #[0,3,5,7,9], nested := 0 } := by
  apply plan_ext <;> decide +kernel

/-- Actual first-term Julia loop equals the emitted ordered polynomial for all inputs.
The nine plan entries and packed reads/writes are refined, with no scalar laws. -/
theorem loop_formula {α : Type} [Coeff α] (x y : Values α 3) :
    Loops.run true loopKey x.data y.data = formula x y := by
  change Loops.eval (k := 4) true (Loops.plan loopKey) x.data y.data = formula x y
  rw [loop_plan]
  dsimp [Loops.eval, Plan.Aligned, ByteArray.size]
  repeat (rw [Loops.fill]; dsimp)
  dsimp [Loops.row, Loops.first, Plan.acc]
  repeat (rw [Plan.row₂]; dsimp [Plan.acc])
  simp [Plan.rd, x.size_eq, y.size_eq, ByteArray.getElem_eq_getElem_data]
  apply Values.ext
  intro i
  rcases i with ⟨i, hi⟩
  change i < 4 at hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with h | h | h | h <;> subst i <;>
    simp only [formula, Values.get_ofFn] <;>
    (simp only [get_set]; simp [Values.get]; try omega)

/-- Actual dynamic reference dispatch produces the same raw Spinor for every grade1 Chain.
The provider is explicit; this is Julia's expression loop, not static zero accumulation. -/
theorem mul_formula {α : Type} [Coeff α] (a b : Chain ℝ3 1 α) :
    @TA.mul ℝ3 α _ Gen.ℝ3.instKernels (.chain 1 a) (.chain 1 b) =
      .spinor ⟨formula a.v b.v⟩ := by
  change (TA.spinor ⟨Loops.run true loopKey a.v.data b.v.data⟩ : TA ℝ3 α) = _
  exact congrArg (fun v : Values α 4 => (TA.spinor ⟨v⟩ : TA ℝ3 α))
    (loop_formula (show Values α 3 from a.v) (show Values α 3 from b.v))

/-- Raw generated/reference refinement for every well-typed ℝ3 grade1 Chain and Coeff.
Concrete provider and actual fast selector prevent ambient replacement from changing scope. -/
theorem mulF_eq_mul {α : Type} [Coeff α] (a b : Chain ℝ3 1 α) :
    @TA.mulF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 1 a) (.chain 1 b) =
      @TA.mul ℝ3 α _ Gen.ℝ3.instKernels (.chain 1 a) (.chain 1 b) := by
  exact (mulF_formula a b).trans (mul_formula a b).symm

end Grassmann.Kernel.R3Chain

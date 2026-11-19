/- Optional proofs for the concrete generated ℝ3 grade1 exterior product.
Importing this module deliberately imports Generated.R3; Dynamic does not re-export it. -/
import Grassmann.Dynamic
import Grassmann.Kernel.Generated.R3

namespace Grassmann.Kernel.R3Wedge

open DirectSum StaticVectors AbstractTensors

private theorem get_set {α : Type} [Packed α] {n : Nat} (v : Values α n)
    (i j : Fin n) (x : α) :
    (v.set i x).get j = if i.val = j.val then x else v.get j :=
  Packed.get_set v.data _ x j.val _

private theorem plan_ext {p q : Plan} (ia : p.ia = q.ia) (ib : p.ib = q.ib)
    (code : p.code = q.code) (coef : p.coef = q.coef)
    (rows : p.rowStart = q.rowStart) (nested : p.nested = q.nested) : p = q := by
  cases p; cases q; simp_all

/-- Actual emitted ordered exterior coordinates in grade2 basis [e12,e13,e23].
Only executable Coeff operations are used; Sub and operand order are preserved. -/
def formula {α : Type} [Coeff α] (x y : Values α 3) : Values α 3 :=
  Values.ofFn fun i => match i.val with
    | 0 => x.get ⟨0, by decide⟩ * y.get ⟨1, by decide⟩ -
        x.get ⟨1, by decide⟩ * y.get ⟨0, by decide⟩
    | 1 => x.get ⟨0, by decide⟩ * y.get ⟨2, by decide⟩ -
        x.get ⟨2, by decide⟩ * y.get ⟨0, by decide⟩
    | _ => x.get ⟨1, by decide⟩ * y.get ⟨2, by decide⟩ -
        x.get ⟨2, by decide⟩ * y.get ⟨1, by decide⟩

/-- Actual generated storage writes equal the ordered formula for all packed inputs. -/
theorem generated_formula {α : Type} [Coeff α] (x y : Values α 3) :
    Gen.ℝ3.k_bin_wedge_c1_c1_c2 x y = formula x y := by
  apply Values.ext
  intro i
  rcases i with ⟨i, hi⟩
  change i < 3 at hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases with h | h | h <;> subst i <;>
    simp [Gen.ℝ3.k_bin_wedge_c1_c1_c2, formula, get_set]
  all_goals
    intro h
    change (2 : Nat) = _ at h
    omega

/-- The concrete provider's actual wedge bin selects the checked emitted definition. -/
theorem generated_bin {α : Type} [Coeff α] (x y : Values α 3) :
    @Kernels.bin ℝ3 Gen.ℝ3.instKernels α _ .wedge (.chain 1) (.chain 1) (.chain 2) x y =
      formula x y := by
  change Gen.ℝ3.k_bin_wedge_c1_c1_c2 x y = formula x y
  exact generated_formula x y

/-- Actual fast routing returns a stored grade2 Chain for every arbitrary grade1 pair.
Concrete provider and existing true fast selector are frozen explicitly. -/
theorem wedgeF_formula {α : Type} [Coeff α] (a b : Chain ℝ3 1 α) :
    @TA.wedgeF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 1 a) (.chain 1 b) =
      .chain 2 ⟨formula a.v b.v⟩ := by
  change (TA.chain 2 ⟨Gen.ℝ3.k_bin_wedge_c1_c1_c2 a.v b.v⟩ : TA ℝ3 α) = _
  exact congrArg (fun v : Values α 3 => (TA.chain 2 ⟨v⟩ : TA ℝ3 α))
    (generated_formula (show Values α 3 from a.v) (show Values α 3 from b.v))

/-- Actual packed input/output basis order, checked independently of scalar laws. -/
theorem layouts : (Layout.chain 1).blades 3 = #[1,2,4] ∧
    (Layout.chain 2).blades 3 = #[3,5,6] := by decide +kernel

/-- Actual Julia expression-loop key with first-operand outer nesting. -/
def loopKey : Loops.JKey :=
  { V := ℝ3, op := .wedge, a := .dense (.chain 1), b := .dense (.chain 1),
    lc := .chain 2, outerFirst := true }

/-- Six plan entries are checked against the actual executable builder, without a witness premise. -/
theorem loop_plan : Loops.plan loopKey =
    { ia := #[0,1,0,2,1,2], ib := #[1,0,2,0,2,1],
      code := ⟨#[0,1,0,1,0,1]⟩, coef := #[1,-1,1,-1,1,-1],
      rowStart := #[0,2,4,6], nested := 0 } := by
  apply plan_ext <;> decide +kernel

/-- Actual first-term reference rows equal the formula for arbitrary packed inputs. -/
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
  intro i
  rcases i with ⟨i, hi⟩
  change i < 3 at hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases with h | h | h <;> subst i <;>
    simp only [formula, Values.get_ofFn] <;>
    (simp only [get_set]; dsimp; simp [Values.get])

/-- Actual reference dispatch returns the same stored grade2 Chain, including zeros. -/
theorem wedge_formula {α : Type} [Coeff α] (a b : Chain ℝ3 1 α) :
    @TA.wedge ℝ3 α _ Gen.ℝ3.instKernels (.chain 1 a) (.chain 1 b) =
      .chain 2 ⟨formula a.v b.v⟩ := by
  change (TA.chain 2 ⟨Loops.run true loopKey a.v.data b.v.data⟩ : TA ℝ3 α) = _
  exact congrArg (fun v : Values α 3 => (TA.chain 2 ⟨v⟩ : TA ℝ3 α))
    (loop_formula (show Values α 3 from a.v) (show Values α 3 from b.v))

/-- Universal raw fast/reference wedge refinement with the concrete provider/selector frozen. -/
theorem wedgeF_eq_wedge {α : Type} [Coeff α] (a b : Chain ℝ3 1 α) :
    @TA.wedgeF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 1 a) (.chain 1 b) =
      @TA.wedge ℝ3 α _ Gen.ℝ3.instKernels (.chain 1 a) (.chain 1 b) :=
  (wedgeF_formula a b).trans (wedge_formula a b).symm

/-- Multiplication commutation and subtraction cancellation suffice for self-zero coordinates
for actual Coeff operations. Neither fact is assumed for operations-only coefficients. -/
theorem formula_self {α : Type} [Coeff α]
    (comm : ∀ x y : α, x*y = y*x) (cancel : ∀ x : α, x-x = Coeff.zero)
    (x : Values α 3) : formula x x = zeroValues 3 := by
  apply Values.ext
  intro i
  rcases i with ⟨i, hi⟩
  change i < 3 at hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases with h | h | h <;> subst i <;>
    simp [formula, zeroValues, comm, cancel]

/-- Actual generated self-wedge is a stored zero Chain under the two explicit scalar laws. -/
theorem wedgeF_self {α : Type} [Coeff α]
    (comm : ∀ x y : α, x*y = y*x) (cancel : ∀ x : α, x-x = Coeff.zero)
    (a : Chain ℝ3 1 α) :
    @TA.wedgeF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 1 a) (.chain 1 a) =
      .chain 2 ⟨zeroValues 3⟩ := by
  rw [wedgeF_formula]
  exact congrArg (fun v : Values α 3 => (TA.chain 2 ⟨v⟩ : TA ℝ3 α))
    (formula_self comm cancel (show Values α 3 from a.v))

end Grassmann.Kernel.R3Wedge

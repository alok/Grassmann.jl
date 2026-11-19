/- Optional R3 top-grade contraction: raw Single0 and typed Chain0 observer bridges.
Julia real-domain dispatch: Grassmann src/products.jl:1165; no-conj policy is retained. -/
import Grassmann.Kernel.R3TopBivectorContractionLaws

namespace Grassmann.Kernel.R3TopPairing
open DirectSum StaticVectors

private theorem get_set {α : Type} [Packed α] {n : Nat} (v : Values α n)
    (i j : Fin n) (x : α) :
    (v.set i x).get j = if i.val = j.val then x else v.get j :=
  Packed.get_set v.data _ x j.val _

private theorem plan_ext {p q : Plan} (ia : p.ia = q.ia) (ib : p.ib = q.ib)
    (code : p.code = q.code) (coef : p.coef = q.coef)
    (rows : p.rowStart = q.rowStart) (nested : p.nested = q.nested) : p = q := by
  cases p; cases q; simp_all

/-- The actual ordered top-grade scalar product, without conjugation or scalar laws. -/
@[specialize] def coordinate {α : Type} [Coeff α] (x y : Values α 1) : α :=
  x.get ⟨0, by decide⟩ * y.get ⟨0, by decide⟩

/-- Complete typed scalar storage retains its only slot, including coefficient zero. -/
def formula {α : Type} [Coeff α] (x y : Values α 1) : Values α 1 :=
  Values.ofFn fun _ ↦ coordinate x y

/-- Actual emitted top/top scalar writes, for arbitrary inputs and every Coeff. -/
theorem generated {α : Type} [Coeff α] (x y : Values α 1) :
    Gen.ℝ3.k_bin_contraction_c3_c3_c0 x y = formula x y := by
  apply Values.ext
  intro ⟨i, hi⟩
  change i < 1 at hi
  have h : i = 0 := by omega
  subst i
  simp [Gen.ℝ3.k_bin_contraction_c3_c3_c0, formula, coordinate, get_set]

/-- Concrete generated bin dispatch, with no supplied formula or blade witness. -/
theorem bin {α : Type} [Coeff α] (x y : Values α 1) :
    @Kernels.bin ℝ3 Gen.ℝ3.instKernels α _ .contraction (.chain 3) (.chain 3) (.chain 0)
      x y = formula x y := generated x y

/-- Actual top input and typed scalar output bases. -/
theorem layouts : (Layout.chain 3).blades 3 = #[7] ∧
    (Layout.chain 0).blades 3 = #[0] := by decide +kernel

/-- Actual top-blade contraction is the positive scalar blade before coefficient scaling. -/
theorem blade_result : ℝ3.apply₂ .contraction 7 7 = .ok (.blade 0) := by
  have h : (ℝ3.apply₂ .contraction 7 7).toOption.map
      (fun r ↦ match r with | .blade b => some b | _ => none) = some (some 0) :=
    by decide +kernel
  generalize hr : ℝ3.apply₂ .contraction 7 7 = r at *
  cases r with
  | error e => cases h
  | ok r =>
    cases r with
    | blade b =>
      have hb : b = 0 := Option.some.inj (Option.some.inj h)
      subst b
      rfl
    | zero => cases h
    | single c b => cases h
    | sum ts => cases h
    | nested z r => cases h

/-- Actual top-grade fallback compares both raw routes under the same arbitrary provider. -/
theorem raw_fallback {α : Type} [Coeff α] (kernels : Kernels ℝ3)
    (a b : Chain ℝ3 3 α) :
    @TA.contractionF ℝ3 α _ kernels Gen.ℝ3.instDynKernels (.chain 3 a) (.chain 3 b) =
      @TA.contraction ℝ3 α _ kernels (.chain 3 a) (.chain 3 b) := by
  simp only [TA.contractionF, TA.prodF, TA.contraction,
    show decide (3 < 3) = false from rfl, Bool.and_false, Bool.false_and,
    Bool.false_eq_true, ite_false, ite_self]

/-- Actual top-right redirect restores scalar operand order and returns raw Single0. -/
theorem reference_formula {α : Type} [Coeff α] (a b : Chain ℝ3 3 α) :
    @TA.contraction ℝ3 α _ Gen.ℝ3.instKernels (.chain 3 a) (.chain 3 b) =
      .single 0 (coordinate a.v b.v) := by
  change TA.termProd .contraction 7 (getD a.v 0) false 7 (getD b.v 0) false = _
  simp only [TA.termProd, TA.POp.bin, blade_result]
  rfl

/-- Actual fast fallback keeps the raw Single0 constructor even at zero or unit. -/
theorem fast_formula {α : Type} [Coeff α] (a b : Chain ℝ3 3 α) :
    @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 3 a) (.chain 3 b) =
      .single 0 (coordinate a.v b.v) :=
  (raw_fallback Gen.ℝ3.instKernels a b).trans (reference_formula a b)

/-- Universal raw fast/reference equality for the frozen top/top contraction. -/
theorem contractionF_eq_contraction {α : Type} [Coeff α] (a b : Chain ℝ3 3 α) :
    @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 3 a) (.chain 3 b) =
      @TA.contraction ℝ3 α _ Gen.ℝ3.instKernels (.chain 3 a) (.chain 3 b) :=
  raw_fallback Gen.ℝ3.instKernels a b

/-- Existing concrete typed contraction stores Chain0, without raw normalization. -/
theorem typed_formula {α : Type} [Coeff α] (a b : Chain ℝ3 3 α) :
    (a ⋅ b : Chain ℝ3 0 α) = ⟨formula a.v b.v⟩ :=
  congrArg (fun v : Values α 1 ↦ (⟨v⟩ : Chain ℝ3 0 α)) (generated a.v b.v)

/-- Every blade coefficient agrees between stored scalar Chain0 and raw Single0. -/
theorem scalar_coeff {α : Type} [Coeff α] (v : Values α 1) (β : UInt64) :
    (TA.chain 0 ⟨v⟩ : TA ℝ3 α).coeff β =
      (TA.single 0 (v.get ⟨0, by decide⟩) : TA ℝ3 α).coeff β := by
  change (Chain.coeff (⟨v⟩ : Chain ℝ3 0 α) β) = _
  rw [TA.Chain_coeff_zero_grade (V := ℝ3) (layoutInv_le8 3 (by decide))]
  simp [TA.coeff, getD, show Leibniz.binomial 3 0 = 1 from rfl]
  split <;> rfl

/-- Existing typed scalar and actual raw contraction agree at every UInt64 mask. -/
theorem typed_coeff_eq_fast {α : Type} [Coeff α] (a b : Chain ℝ3 3 α) (β : UInt64) :
    (TA.chain 0 (a ⋅ b : Chain ℝ3 0 α) : TA ℝ3 α).coeff β =
      (@TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels
        (.chain 3 a) (.chain 3 b)).coeff β := by
  rw [typed_formula, fast_formula, scalar_coeff]
  simp [formula]

/-- Complete dense observers agree without scalar algebra laws or constructor equality. -/
theorem typed_dense_eq_fast {α : Type} [Coeff α] (a b : Chain ℝ3 3 α) :
    (TA.chain 0 (a ⋅ b : Chain ℝ3 0 α) : TA ℝ3 α).toDense =
      (@TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels
        (.chain 3 a) (.chain 3 b)).toDense := by
  rw [fast_formula]
  apply TA.toDense_ext
  intro i
  have h := typed_coeff_eq_fast a b (TA.fullBlade 3 i.val)
  rw [fast_formula] at h
  simp only [TA.dget_chain, TA.dget_single]
  exact h

/-- The actual typed toMultivector conversion agrees with complete raw dense storage. -/
theorem typed_toMultivector_eq_fast {α : Type} [Coeff α] (a b : Chain ℝ3 3 α) :
    (a ⋅ b : Chain ℝ3 0 α).toMultivector =
      (@TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels
        (.chain 3 a) (.chain 3 b)).toDense := by
  rw [← typed_dense_eq_fast]
  apply TA.Multivector_ext
  intro i
  change (TA.multi (toMultivector (a ⋅ b : Chain ℝ3 0 α))).dget i =
    (TA.chain 0 (a ⋅ b : Chain ℝ3 0 α)).dget i
  simp only [TA.dget_toMultivector_chain, TA.dget_chain]

/-- Raw Single0 and typed Chain0 remain distinct for every input, including zero and unit. -/
theorem typed_raw_ne_fast {α : Type} [Coeff α] (a b : Chain ℝ3 3 α) :
    (TA.chain 0 (a ⋅ b : Chain ℝ3 0 α) : TA ℝ3 α) ≠
      @TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 3 a) (.chain 3 b) := by
  rw [fast_formula]
  simp

/-- Plain executable top-grade pairing uses the scalar coefficient of actual raw dispatch. -/
@[specialize] def pairingCoefficient {α : Type} [Coeff α] (a b : Chain ℝ3 3 α) : α :=
  (@TA.contractionF ℝ3 α _ Gen.ℝ3.instKernels Gen.ℝ3.instDynKernels (.chain 3 a) (.chain 3 b)).coeff 0

/-- Exact pairing is the ordered scalar product, with no Hermitian or field law. -/
theorem pairingCoefficient_formula {α : Type} [Coeff α] (a b : Chain ℝ3 3 α) :
    pairingCoefficient a b = coordinate a.v b.v := by
  unfold pairingCoefficient
  rw [fast_formula]
  simp [TA.coeff]

/-- Pairing symmetry needs only commutation of the actual multiplication operation. -/
theorem pairingCoefficient_symm {α : Type} [Coeff α]
    (comm : ∀ p q : α, p*q = q*p) (a b : Chain ℝ3 3 α) :
    pairingCoefficient a b = pairingCoefficient b a := by
  rw [pairingCoefficient_formula, pairingCoefficient_formula]
  exact comm _ _

/-- Genuine default rational multiplication discharges arbitrary-input symmetry. -/
theorem rational_symm (a b : Chain ℝ3 3 Rat) : pairingCoefficient a b = pairingCoefficient b a :=
  pairingCoefficient_symm Rat.mul_comm a b

/-- Genuine default unbounded integer multiplication gives the same symmetry. -/
theorem integer_symm (a b : Chain ℝ3 3 Int) : pairingCoefficient a b = pairingCoefficient b a :=
  pairingCoefficient_symm Int.mul_comm a b

/-- Actual strict reference-provider key for the top/top typed scalar grade pair. -/
def staticKey : PlanKey :=
  { V := ℝ3, op := .bin .contraction, la := .chain 3, lb := .chain 3, lc := .chain 0 }

/-- This grade pair's actual successful strict plan has one positive scalar term. -/
theorem static_plan : Grassmann.Kernel.plan staticKey = .ok
    { ia := #[0], ib := #[0], code := ⟨#[0]⟩,
      coef := #[1], rowStart := #[0,1], nested := 0 } := by
  have ia : (Grassmann.Kernel.plan staticKey).toOption.map (·.ia) = some #[0] :=
    by decide +kernel
  have ib : (Grassmann.Kernel.plan staticKey).toOption.map (·.ib) = some #[0] :=
    by decide +kernel
  have code : (Grassmann.Kernel.plan staticKey).toOption.map (·.code) = some ⟨#[0]⟩ :=
    by decide +kernel
  have coef : (Grassmann.Kernel.plan staticKey).toOption.map (·.coef) = some #[1] :=
    by decide +kernel
  have rows : (Grassmann.Kernel.plan staticKey).toOption.map (·.rowStart) = some #[0,1] :=
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

/-- Actual replacing reference storage starts its sole positive row from scalar zero. -/
theorem static_bin_formula {α : Type} [Coeff α] (x y : Values α 1) :
    @Kernels.bin ℝ3 (Kernels.reference ℝ3) α _ .contraction
      (.chain 3) (.chain 3) (.chain 0) x y =
      Values.ofFn (fun _ ↦ AbstractTensors.Coeff.zero + coordinate x y) := by
  change (match Grassmann.Kernel.plan staticKey with
    | .ok p => p.eval₂ x y
    | .error e => panic! e) = _
  rw [static_plan]
  change Plan.eval₂ (k := 1)
    { ia := #[0], ib := #[0], code := ⟨#[0]⟩,
      coef := #[1], rowStart := #[0,1], nested := 0 } x y = _
  dsimp only [Plan.eval₂]
  rw [dite_eq_left (by decide +kernel)]
  rw [Plan.fill₂]
  dsimp
  rw [Plan.fill₂]
  dsimp
  rw [Plan.row₂]
  dsimp [Plan.acc]
  rw [Plan.row₂]
  dsimp [Plan.acc]
  simp [Plan.rd, x.size_eq, y.size_eq, ByteArray.getElem_eq_getElem_data]
  apply Values.ext
  intro ⟨i, hi⟩
  change i < 1 at hi
  have h : i = 0 := by omega
  subst i
  simp only [get_set]
  simp [coordinate, Values.get, Values.ofFn]

/-- Only a sufficient zero-add identity is needed to identify these actual typed providers. -/
theorem reference_bin_eq_generated {α : Type} [Coeff α]
    (zeroAdd : ∀ p : α, AbstractTensors.Coeff.zero + p = p) (x y : Values α 1) :
    @Kernels.bin ℝ3 (Kernels.reference ℝ3) α _ .contraction
      (.chain 3) (.chain 3) (.chain 0) x y =
      @Kernels.bin ℝ3 Gen.ℝ3.instKernels α _ .contraction
        (.chain 3) (.chain 3) (.chain 0) x y := by
  rw [static_bin_formula, bin]
  simp only [zeroAdd, formula]
  rfl

/-- Genuine default rational zero-add law identifies the actual providers. -/
theorem rational_reference_bin_eq_generated (x y : Values Rat 1) :
    @Kernels.bin ℝ3 (Kernels.reference ℝ3) Rat _ .contraction
      (.chain 3) (.chain 3) (.chain 0) x y =
      @Kernels.bin ℝ3 Gen.ℝ3.instKernels Rat _ .contraction
        (.chain 3) (.chain 3) (.chain 0) x y :=
  reference_bin_eq_generated LawfulCoeff.zero_add x y

/-- Genuine default unbounded integer zero-add law gives the same provider bridge. -/
theorem integer_reference_bin_eq_generated (x y : Values Int 1) :
    @Kernels.bin ℝ3 (Kernels.reference ℝ3) Int _ .contraction
      (.chain 3) (.chain 3) (.chain 0) x y =
      @Kernels.bin ℝ3 Gen.ℝ3.instKernels Int _ .contraction
        (.chain 3) (.chain 3) (.chain 0) x y :=
  reference_bin_eq_generated LawfulCoeff.zero_add x y

end Grassmann.Kernel.R3TopPairing

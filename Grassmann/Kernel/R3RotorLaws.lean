/- Checked finite R3 decoding and one exact rational Euclidean rotor.
Attribution: independent Lean port of Michael Reed/chakravala's Grassmann ecosystem. -/
import Grassmann.Kernel.R3TopPairingLaws

namespace Grassmann.Kernel.R3Rotor
open DirectSum StaticVectors

@[instance_reducible] private def wfDecidable {α : Type} [Coeff α]
    (x : TA ℝ3 α) : Decidable x.WF := by
  cases x <;> dsimp [TA.WF] <;> infer_instance

attribute [local instance] wfDecidable

/-- Checked linear coefficient storage; rejects non-linear kinds and invalid stored blades.
This guard checks representation well-formedness, not numeric finiteness of Float coefficients. -/
def decode {α : Type} [Coeff α] (x : TA ℝ3 α) : Option (Multivector ℝ3 α) :=
  if x.WF then some x.toDense else none

/-- Explicit checked dense normalization, without changing raw public operator results. -/
def normalize {α : Type} [Coeff α] (x : TA ℝ3 α) : Option (TA ℝ3 α) :=
  (decode x).map TA.multi

/-- Every admitted representation decodes to its existing complete dense observation. -/
theorem decode_of_wf {α : Type} [Coeff α] (x : TA ℝ3 α) (h : x.WF) :
    decode x = some x.toDense := by simp [decode, h]

/-- Rejected representations cannot be silently promoted to finite geometry. -/
theorem decode_of_not_wf {α : Type} [Coeff α] (x : TA ℝ3 α) (h : ¬ x.WF) :
    decode x = none := by simp [decode, h]

/-- Checked normalization preserves complete decoding for every Coeff, with no scalar laws. -/
theorem decode_normalize {α : Type} [Coeff α] (x : TA ℝ3 α) :
    (normalize x).bind decode = decode x := by
  by_cases h : x.WF
  · simp only [normalize, decode_of_wf x h, Option.map_some, Option.bind_some]
    exact decode_of_wf (.multi x.toDense) trivial
  · simp [normalize, decode_of_not_wf x h]

/-- Stored canonical scalar Chain0, including the actual operation-only coefficient zero. -/
def scalarChain {α : Type} [Coeff α] (q : α) : Chain ℝ3 0 α :=
  ⟨Values.ofFn fun _ => q⟩

/-- Canonical Chain0 and raw Single0 have the same every-mask coefficient denotation.
Coefficient copying requires no zero-add, commutation or ring law. -/
theorem scalar_coeff {α : Type} [Coeff α] (q : α) (mask : UInt64) :
    (TA.chain 0 (scalarChain q) : TA ℝ3 α).coeff mask =
      (TA.single 0 q : TA ℝ3 α).coeff mask := by
  have h := R3TopPairing.scalar_coeff (scalarChain q).v mask
  have read : (scalarChain q).v.get (⟨0, by decide⟩ : Fin 1) = q := by
    simp [scalarChain, Values.get, Values.ofFn]
  exact h.trans (congrArg (fun v : α => (TA.single 0 v : TA ℝ3 α).coeff mask) read)

/-- Complete checked scalar decoding agrees while preserving distinct raw constructors. -/
theorem decode_scalar {α : Type} [Coeff α] (q : α) :
    decode (TA.chain 0 (scalarChain q) : TA ℝ3 α) = decode (.single 0 q) := by
  simp only [decode, TA.WF, TA.valid_zero, ite_eq_left]
  apply congrArg some
  apply TA.toDense_ext
  intro i
  simp only [TA.dget_chain, TA.dget_single]
  exact scalar_coeff q (TA.fullBlade 3 i.val)

/-- Even at zero/unit, scalar storage representations remain structurally distinct. -/
theorem scalar_raw_ne {α : Type} [Coeff α] (q : α) :
    (TA.chain 0 (scalarChain q) : TA ℝ3 α) ≠ .single 0 q := by
  intro h
  cases h

/-- Actual Euclidean R3 layouts; dense storage is grade-major rather than numeric-mask order. -/
theorem layouts : (Layout.chain 1).blades 3 = #[1,2,4] ∧
    Layout.even.blades 3 = #[0,3,5,6] ∧ Layout.odd.blades 3 = #[1,2,4,7] ∧
    Layout.full.blades 3 = #[0,1,2,4,3,5,6,7] := by decide +kernel

/-- The fixed exact rotor 3/5 + (4/5)e12, using positive Euclidean basis squares. -/
def rotor : Spinor ℝ3 Rat := spinor![3/5, 4/5, 0, 0]

/-- Rational Euclidean vector coordinates in the existing typed Chain1 representation. -/
def point (x y z : Rat) : Chain ℝ3 1 Rat :=
  Chain.ofList [x,y,z] (by change 3 = _; decide +kernel)

/-- Independent rational matrix for r*v*reverse(r), with the chosen bivector orientation. -/
def coordinates (x y z : Rat) : Chain ℝ3 1 Rat :=
  point ((-7*x+24*y)/25) ((-24*x-7*y)/25) z

/-- Existing concrete generated projected action; freezes SandwichKernels as well as Kernels. -/
def action (x y z : Rat) : Chain ℝ3 1 Rat := rotor >>> point x y z

/-- The opposite sandwich convention reverse(r)*v*r. -/
def inverseAction (x y z : Rat) : Chain ℝ3 1 Rat := point x y z ⊘ rotor

/-- Complete two-product sandwich retains all four odd slots before grade projection. -/
def fullAction (x y z : Rat) : CoSpinor ℝ3 Rat := rotor * point x y z * rotor.reverse

/-- Actual reversion and Clifford conjugation agree for this even exact rotor. -/
theorem rotor_reverse : rotor.reverse = (spinor![3/5,-(4/5),0,0] : Spinor ℝ3 Rat) ∧
    rotor.clifford = rotor.reverse := by decide +kernel

/-- Both actual typed products certify this rotor's unit normalization. -/
theorem rotor_unit : (rotor * rotor.reverse : Spinor ℝ3 Rat) = Spinor.one ∧
    (rotor.reverse * rotor : Spinor ℝ3 Rat) = Spinor.one := by decide +kernel

private theorem get_set {n : Nat} (v : Values Rat n)
    (i j : Fin n) (x : Rat) :
    (v.set i x).get j = if i.val = j.val then x else v.get j :=
  Packed.get_set v.data _ x j.val _

/-- Actual generated fused writes equal the independent coordinate matrix for every Rat point. -/
theorem action_formula (x y z : Rat) : action x y z = coordinates x y z := by
  change (⟨Gen.ℝ3.k_tsandwich_e_c1 rotor.v (point x y z).v⟩ : Chain ℝ3 1 Rat) = _
  apply congrArg (fun v : Values Rat 3 => (⟨v⟩ : Chain ℝ3 1 Rat))
  apply Values.ext
  intro ⟨i,hi⟩
  change i < 3 at hi
  have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases h with h | h | h <;> subst i <;>
    simp [Gen.ℝ3.k_tsandwich_e_c1, rotor, point, Half.ofList, Chain.ofList,
      get_set, halfDim, Layout.size, Leibniz.binomial] <;> grind

/-- Reversing the sandwich orientation reverses the spatial rotation sign. -/
theorem inverseAction_formula (x y z : Rat) :
    inverseAction x y z = point ((-7*x-24*y)/25) ((24*x-7*y)/25) z := by
  change (⟨Gen.ℝ3.k_sandwich_e_c1 rotor.v (point x y z).v⟩ : Chain ℝ3 1 Rat) = _
  apply congrArg (fun v : Values Rat 3 => (⟨v⟩ : Chain ℝ3 1 Rat))
  apply Values.ext
  intro ⟨i,hi⟩
  change i < 3 at hi
  have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases h with h | h | h <;> subst i <;>
    simp [Gen.ℝ3.k_sandwich_e_c1, rotor, point, Half.ofList, Chain.ofList,
      get_set, halfDim, Layout.size, Leibniz.binomial] <;> grind

/-- The actual complete product agrees with the matrix and has zero trivector coefficient. -/
theorem fullAction_formula (x y z : Rat) :
    fullAction x y z =
      (Half.ofList [(-7*x+24*y)/25,(-24*x-7*y)/25,z,0] (by rfl) : CoSpinor ℝ3 Rat) := by
  unfold fullAction
  rw [rotor_reverse.1]
  change (⟨Gen.ℝ3.k_bin_mul_o_e_o
    (Gen.ℝ3.k_bin_mul_e_c1_o rotor.v (point x y z).v)
      (spinor![3/5,-(4/5),0,0] : Spinor ℝ3 Rat).v⟩ : CoSpinor ℝ3 Rat) = _
  apply congrArg (fun v : Values Rat 4 => (⟨v⟩ : CoSpinor ℝ3 Rat))
  apply Values.ext
  intro ⟨i,hi⟩
  change i < 4 at hi
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h with h | h | h | h <;> subst i <;>
    simp [Gen.ℝ3.k_bin_mul_o_e_o, Gen.ℝ3.k_bin_mul_e_c1_o,
      rotor, point, Half.ofList, Chain.ofList,
      get_set, halfDim, Layout.size, Leibniz.binomial] <;> grind

/-- The independent exact matrix preserves squared Euclidean length for arbitrary Rat points. -/
theorem coordinates_norm (x y z : Rat) :
    ((-7*x+24*y)/25)^2 + ((-24*x-7*y)/25)^2 + z^2 = x^2+y^2+z^2 := by grind

end Grassmann.Kernel.R3Rotor

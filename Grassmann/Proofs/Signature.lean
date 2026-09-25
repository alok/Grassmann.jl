/-
Signature spaces in every dimension: the implementation's geometric product is
the spec, proved without enumeration.

A *plain signature space* has a `Signature` (Julia `S"…"`, `ℝ^n`) or `Int`
(Julia `n`, `V"n"`) metric, no conformal pair and no tangent variables. For every
such space and every width `n ≤ 64`:

* `terms_mul`: DirectSum's blade rule `terms₂ .mul a b` is the single term
  `±e_{a⊕b}` with the sign `parityjoin V.sigBits a b`, for **all** `UInt64`
  masks. The metric factor `metricProduct` is a product of `±1`s, so its
  absolute value is `1` whatever its loop visits;
* `table_mul`: hence the blade table agrees with the spec coefficient of the
  signature metric (`DirectSum.Proofs.signOf_parityjoin`);
* `implMul_eq_mul_of_signature`: **the implementation's geometric product is
  the spec product `Cl.mul` on all multivectors**, in every dimension up to 64.

`Grassmann.Proofs.Tables` checks the same for small spaces by evaluation; this
file covers `ℝ⁵ … ℝ⁶⁴`, `S!"-+++…"`, `S!"++--"` and every other plain
signature space at once.
-/
import Grassmann.Proofs.Link

namespace Grassmann.Proofs

open DirectSum DirectSum.Proofs Grassmann.Spec Lean.Grind

/-- A plain signature space: `Signature` or `Int` metric, no conformal null
pair, no tangent variables. -/
structure IsSignatureSpace (V : TensorBundle) : Prop where
  /-- The metric is a signature mask or Euclidean. -/
  metric : (∃ s, V.metric = .signature s) ∨ V.metric = .euclid
  /-- No conformal null pair. -/
  conformal : V.hasconformal = false
  /-- No tangent variables. -/
  tangent : V.diffvars = 0

private theorem blade_terms (d : UInt64) : (BladeResult.blade d).bladeTerms = #[{ bits := d, coef := 1 }] := by
  have : ((1 : Rat) != 0) = true := by decide +kernel
  simp [BladeResult.bladeTerms, BladeResult.terms, this]

private theorem single_terms (c : Rat) (d : UInt64) (hc : c ≠ 0) :
    (BladeResult.single c d).bladeTerms = #[{ bits := d, coef := c }] := by
  simp [BladeResult.bladeTerms, BladeResult.terms, hc]

namespace IsSignatureSpace

variable {V : TensorBundle} (hV : IsSignatureSpace V)
include hV

theorem isdiag : V.isdiag = true := by
  unfold TensorBundle.isdiag
  rcases hV.metric with ⟨s, h⟩ | h <;> rw [h]
  simp [hV.conformal]

theorem istangent : V.istangent = false := by
  unfold TensorBundle.istangent; simp [hV.tangent]

theorem diffmask : V.diffmask = 0 := by
  unfold TensorBundle.diffmask TensorBundle.diffmaskV TensorBundle.diffmaskW
  rw [hV.tangent]
  have h0 : Bits.lowMask 0 = 0 := by decide
  have hs : ∀ k, Bits.shl 0 k = 0 := fun k => by unfold Bits.shl; split <;> simp
  rw [h0, hs]; split <;> simp [hs]

theorem symmetricmask (a b : UInt64) : V.symmetricmask a b = (a, b, 0, 0) := by
  unfold TensorBundle.symmetricmask
  rw [hV.diffmask]
  simp

theorem parity (a b : UInt64) : V.parity a b = parityjoin V.sigBits a b := by
  unfold TensorBundle.parity
  rw [hV.diffmask]
  simp

theorem metricAt (i : Nat) : V.metricAt i = 1 ∨ V.metricAt i = -1 := by
  unfold TensorBundle.metricAt
  rcases hV.metric with ⟨s, h⟩ | h <;> rw [h]
  · simp only; split <;> simp
  · simp

/-- In a signature space the metric factor of any mask is `±1` (a product of
`±1`s), whatever the loop visits. -/
theorem metricProduct (b : UInt64) : V.metricProduct b = 1 ∨ V.metricProduct b = -1 := by
  unfold TensorBundle.metricProduct
  have key : ∀ fuel (x : UInt64) (acc : Rat), (acc = 1 ∨ acc = -1) →
      TensorBundle.metricProduct.go V x acc fuel = 1 ∨ TensorBundle.metricProduct.go V x acc fuel = -1 := by
    intro fuel
    induction fuel with
    | zero => intro x acc h; exact h
    | succ fuel ih =>
      intro x acc h
      unfold TensorBundle.metricProduct.go
      split
      · exact h
      · apply ih
        rcases h with h | h <;> rcases hV.metricAt (Bits.ctz x + 1) with h' | h' <;> rw [h, h'] <;> grind
  exact key 64 b 1 (Or.inl rfl)

theorem parityinner (a b : UInt64) :
    V.parityinner a b = if parityjoin V.sigBits a b then -1 else 1 := by
  unfold TensorBundle.parityinner
  rw [hV.symmetricmask]
  simp only
  rw [hV.parity]
  have h1 : ¬ (1 : Rat) < 0 := by decide +kernel
  have h2 : (-1 : Rat) < 0 := by decide +kernel
  have h3 : -(-1 : Rat) = 1 := by decide +kernel
  rcases hV.metricProduct (a &&& b) with h | h <;> rw [h]
  · rw [ite_eq_right h1]
  · rw [ite_eq_left h2, h3]

/-- **DirectSum's geometric product of two blades in a plain signature space**:
`e_a e_b = (-1)^{parityjoin} e_{a⊕b}`, for all 64-bit masks. -/
theorem terms_mul (a b : UInt64) :
    V.terms₂ .mul a b = .ok #[{ bits := a ^^^ b, coef := signOf (parityjoin V.sigBits a b) }] := by
  have hd := hV.isdiag
  have ht := hV.istangent
  show Except.ok (V.mul a b).bladeTerms = _
  congr 1
  unfold TensorBundle.mul TensorBundle.mulDiag
  rw [hd, ht, hV.symmetricmask]
  simp only [ite_true, Bool.false_and, Bool.false_eq_true, ite_false, UInt64.or_zero]
  unfold TensorBundle.nestTangent
  rw [hV.tangent]
  simp only [beq_self_eq_true, Bool.true_or, ite_true]
  rw [hV.parity, hV.parityinner]
  have h1 : decide ((1 : Rat) < 0) = false := by decide +kernel
  have h2 : decide ((-1 : Rat) < 0) = true := by decide +kernel
  have hn1 : (-1 : Rat) ≠ 0 := by decide +kernel
  have hp1 : (1 : Rat) ≠ 0 := by decide +kernel
  by_cases hab : (a &&& b == 0) = true
  · rw [ite_eq_left hab, ite_eq_left hab]
    cases parityjoin V.sigBits a b
    · simp only [Bool.false_eq_true, ite_false, h1]
      show (BladeResult.blade (a ^^^ b)).bladeTerms = _
      rw [blade_terms]; rfl
    · simp only [ite_true, h2]
      show (BladeResult.single (-1) (a ^^^ b)).bladeTerms = _
      rw [single_terms _ _ hn1]; rfl
  · rw [ite_eq_right hab, ite_eq_right hab]
    cases parityjoin V.sigBits a b
    · simp only [Bool.false_eq_true, ite_false]
      rw [single_terms _ _ hp1]; rfl
    · simp only [ite_true]
      rw [single_terms _ _ hn1]; rfl

/-- The blade table of a plain signature space agrees with the spec coefficient
of its signature metric, in every width `n ≤ 64`. -/
theorem table_mul {n : Nat} (hn : n ≤ 64) : TableAgrees V .mul (coef (sigG (R := Rat) n V.sigBits.toNat)) := by
  intro a b
  rw [hV.terms_mul, ← mulSign_eq_coef hn V a b]
  have hmask : mask (a ^^^ b) = mask a ^^^ mask b := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_xor, toNat_mask hn, toNat_mask hn, toNat_mask hn, BitVec.toNat_xor]
  have hne : (signOf (V.mulSign (mask a) (mask b)) : Rat) ≠ 0 := by
    cases V.mulSign (mask a) (mask b) <;> decide
  simp only [Matches, single, hne, ite_false, hmask]
  simp [TensorBundle.mulSign]

end IsSignatureSpace

/-- **The implementation's geometric product is the spec product in every plain
signature space of dimension `≤ 64`**, on all multivectors (over `ℚ`, the
coefficient field of DirectSum's term lists). -/
theorem implMul_eq_mul_of_signature {V : TensorBundle} (hV : IsSignatureSpace V) {n : Nat} (hn : n ≤ 64)
    (x y : Cl (sigG (R := Rat) n V.sigBits.toNat)) : implMul V x y = x * y :=
  implMul_eq_mul hn (hV.table_mul hn) x y

/-- `ℝⁿ` (Julia `V"n"`, the `Int` space) is a plain signature space. -/
theorem isSignatureSpace_euclidean (n : Nat) : IsSignatureSpace (TensorBundle.euclidean n) :=
  ⟨Or.inr rfl, rfl, rfl⟩

/-- Julia `Signature` spaces `TensorBundle.sig n neg` (`ℝ^n`, `S!"-+++"`, …) are
plain signature spaces. -/
theorem isSignatureSpace_sig (n : Nat) (neg : UInt64) : IsSignatureSpace (TensorBundle.sig n neg) :=
  ⟨Or.inl ⟨_, rfl⟩, rfl, rfl⟩

/-- `ℝ⁷`: the implementation's product is the spec product (no enumeration of
the `2¹⁴` blade pairs). -/
theorem R7_mul (x y : Cl (sigG (R := Rat) 7 ℝ7.sigBits.toNat)) : implMul ℝ7 x y = x * y :=
  implMul_eq_mul_of_signature ⟨Or.inr rfl, rfl, rfl⟩ (by decide) x y

/-- A split signature `S!"++-+--"`: the implementation's product is the spec
product. -/
theorem S33_mul (x y : Cl (sigG (R := Rat) 6 S!"++-+--".sigBits.toNat)) : implMul S!"++-+--" x y = x * y :=
  implMul_eq_mul_of_signature ⟨Or.inl ⟨_, rfl⟩, rfl, rfl⟩ (by decide) x y

end Grassmann.Proofs

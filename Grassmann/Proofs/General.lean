/-
Every dimension at once: the implementation's geometric product (signature
spaces) and exterior product (every non-conformal, non-tangent space) are the
spec, proved without enumeration.

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

The exterior product needs even less: its blade rule is metric-independent, so
for **every** space without a conformal pair or tangent variables
(`IsFlatSpace`: signatures, `DiagonalForm`s including degenerate ones, and
`MetricTensor`s) and every width `n ≤ 64`, `terms_wedge` and
`implWedge_eq_wedge_of_flat` identify it with the spec exterior product.

`Grassmann.Proofs.Tables` checks the same for small spaces by evaluation; this
file covers `ℝ⁵ … ℝ⁶⁴`, `S!"-+++…"`, `S!"++--"`, `D!"0,1,1,1,1"` and every other
such space at once.
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

/-! ## The exterior product in every flat space -/

/-- A flat space: no conformal null pair and no tangent variables (any metric). -/
structure IsFlatSpace (V : TensorBundle) : Prop where
  /-- No conformal null pair. -/
  conformal : V.hasconformal = false
  /-- No tangent variables. -/
  tangent : V.diffvars = 0

namespace IsFlatSpace

variable {V : TensorBundle} (hV : IsFlatSpace V)
include hV

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

theorem diffcheck (a b : UInt64) : V.diffcheck a b = false := by
  unfold TensorBundle.diffcheck
  simp [hV.conformal, hV.tangent]

omit hV in
private theorem and_not_zero' (x : UInt64) : x &&& ~~~0 = x := by
  apply UInt64.toBitVec_inj.mp
  simp

theorem parity_of_disjoint {a b : UInt64} (h : a &&& b = 0) : V.parity a b = Bits.reorderParity a b := by
  show parityjoin V.sigBits (a &&& ~~~V.diffmask) (b &&& ~~~V.diffmask) = _
  rw [hV.diffmask, and_not_zero', and_not_zero']
  unfold parityjoin
  rw [h, UInt64.zero_and]
  have : Bits.parity 0 = false := by decide
  rw [this]; simp

/-- **DirectSum's exterior product of two blades in a flat space**: `0` on
overlapping blades, `(-1)^{σ(a,b)} e_{a∪b}` on disjoint ones, for all 64-bit
masks and every metric. -/
theorem terms_wedge (a b : UInt64) :
    V.terms₂ .wedge a b
      = .ok (if a &&& b = 0 then #[{ bits := a ^^^ b, coef := signOf (Bits.reorderParity a b) }] else #[]) := by
  show Except.ok (V.wedge a b).bladeTerms = _
  congr 1
  unfold TensorBundle.wedge
  rw [hV.symmetricmask, hV.diffcheck]
  simp only [Bool.or_false, UInt64.or_zero]
  by_cases hab : a &&& b = 0
  · rw [ite_eq_left hab]
    have hne : (a &&& b != 0) = false := by simp [hab]
    rw [hne]
    simp only [Bool.false_eq_true, ite_false]
    unfold TensorBundle.nestTangent
    rw [hV.tangent]
    simp only [beq_self_eq_true, Bool.true_or, ite_true]
    rw [hV.parity_of_disjoint hab]
    have hn1 : (-1 : Rat) ≠ 0 := by decide +kernel
    cases Bits.reorderParity a b
    · show (BladeResult.blade (a ^^^ b)).bladeTerms = _
      rw [blade_terms]; rfl
    · show (BladeResult.single (-1) (a ^^^ b)).bladeTerms = _
      rw [single_terms _ _ hn1]; rfl
  · rw [ite_eq_right hab]
    have hne : (a &&& b != 0) = true := by simp [hab]
    rw [hne]
    simp [BladeResult.bladeTerms, BladeResult.terms]

/-- The exterior-product table of a flat space agrees with the spec in every
width `n ≤ 64`. -/
theorem table_wedge {n : Nat} (hn : n ≤ 64) : TableAgrees V .wedge (wcoef (R := Rat) (n := n)) := by
  intro a b
  rw [hV.terms_wedge]
  have hmask : mask (a ^^^ b) = mask a ^^^ mask b := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_xor, toNat_mask hn, toNat_mask hn, toNat_mask hn, BitVec.toNat_xor]
  have hand : (mask a &&& mask b = 0) ↔ (a &&& b = 0) := by
    rw [← UInt64.toNat_inj, UInt64.toNat_and, toNat_mask hn, toNat_mask hn, ← BitVec.toNat_and]
    exact toNat_eq_zero_iff _
  have hsign : Bits.reorderParity (mask a) (mask b) = sign a b := by
    rw [reorderParity_eq_sigma, toNat_mask hn, toNat_mask hn, sign, sigma_of_lt hn a.isLt]
  unfold wcoef
  by_cases hab : a &&& b = 0
  · have hne : (signOf (sign a b) : Rat) ≠ 0 := by cases sign a b <;> decide
    rw [ite_eq_left (hand.mpr hab), ite_eq_left hab]
    simp only [Matches, single, hne, ite_false, hmask, hsign]
    simp
  · rw [ite_eq_right (fun e => hab (hand.mp e)), ite_eq_right hab]
    simp [Matches, single]

end IsFlatSpace

/-- **The implementation's exterior product is the spec exterior product in
every flat space** (any metric, no conformal pair, no tangent variables) of
dimension `≤ 64`, on all multivectors. -/
theorem implWedge_eq_wedge_of_flat {V : TensorBundle} (hV : IsFlatSpace V) {n : Nat} (hn : n ≤ 64)
    {g : Fin n → Rat} (x y : Cl g) : implWedge V x y = Cl.wedge x y :=
  implWedge_eq_wedge hn (hV.table_wedge hn) x y

/-- `PGA4 = D!"0,1,1,1,1"`: the implementation's exterior product is the spec
exterior product. -/
theorem PGA4_wedge {g : Fin 5 → Rat} (x y : Cl g) : implWedge D!"0,1,1,1,1" x y = Cl.wedge x y :=
  implWedge_eq_wedge_of_flat ⟨rfl, rfl⟩ (by decide) x y

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

/-
The right complement and the Hodge star, in every dimension.

For every *plain* space (no null generators `∞`/`∅`, no tangent variables, not
dyadic) of dimension `n ≤ 64`, DirectSum's blade rules for `!` and `⋆`
(`TensorBundle.complementright`, `complementrighthodge`: `Bits.sumIndices`,
Julia's closed form `parityrightRaw`, the metric loop and Leibniz `complement`)
are the spec's, for every blade:

* `terms_complementright`: `!e_a = (-1)^{σ(a, ā)} e_ā`;
* `terms_hodge`: `⋆e_a = (-1)^{σ(a, ā)} Π_{i∈a} gᵢ e_ā`, for any diagonal
  metric the space reads (`V.metricAt`);
* `implCompl_eq_compl`, `implHodge_eq_hodge`: their linear extensions are the
  spec `Cl.compl`, `Cl.hodge` on all multivectors, so the spec theorems
  `Cl.compl_compl` and `Cl.hodge_hodge` (the double complements) hold for the
  implementation.
-/
import Grassmann.Proofs.Diagonal
import DirectSum.Proofs.Complement

namespace Grassmann.Proofs

open DirectSum DirectSum.Proofs Grassmann.Spec Lean.Grind

/-- A plain space: no null generators, no tangent variables, not dyadic. -/
structure IsPlainSpace (V : TensorBundle) : Prop where
  /-- No `∞`. -/
  noInf : V.hasinf = false
  /-- No `∅`. -/
  noOrigin : V.hasorigin = false
  /-- No tangent variables. -/
  tangent : V.diffvars = 0
  /-- Not the dyadic `V ⊕ V'`. -/
  notDyadic : V.isdyadic = false

private theorem single_terms'' (c : Rat) (x : UInt64) :
    (BladeResult.single c x).bladeTerms = if c = 0 then #[] else #[{ bits := x, coef := c }] := by
  by_cases hc : c = 0
  · subst hc; rw [ite_eq_left rfl]; simp [BladeResult.bladeTerms, BladeResult.terms]
  · rw [ite_eq_right hc]; simp [BladeResult.bladeTerms, BladeResult.terms, hc]

namespace IsPlainSpace

variable {V : TensorBundle} (hV : IsPlainSpace V)
include hV

theorem conformal : V.hasconformal = false := by
  unfold TensorBundle.hasconformal; rw [hV.noInf]; rfl

theorem nulls : V.nulls = 0 := by unfold TensorBundle.nulls; rw [hV.noInf, hV.noOrigin]; rfl

theorem flat : IsFlatSpace V := ⟨hV.conformal, hV.tangent⟩

theorem nullFactor (b : UInt64) : V.nullFactor b = 1 := by
  unfold TensorBundle.nullFactor; rw [hV.conformal]; rfl

variable {n : Nat} (hVn : V.n = n) (hn : n ≤ 64)
include hVn hn

theorem lowMask_and (a : BitVec n) : mask a &&& Bits.lowMask (V.n - V.diffvars) = mask a := by
  rw [hV.tangent, Nat.sub_zero, hVn]
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, toNat_mask hn]
  unfold Bits.lowMask Bits.fullMask
  by_cases h : n ≥ 64
  · have : n = 64 := by omega
    subst this; rw [ite_eq_left h]
    rw [show (0xFFFFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 64 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt a.isLt]
  · rw [ite_eq_right h]
    have hn' : n < 64 := by omega
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_shl_one hn']; exact Nat.one_le_two_pow),
      toNat_shl_one hn', UInt64.toNat_one, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt a.isLt]

/-- The implementation's complement sign of a blade is `σ(a, ā)`. -/
theorem parityright (a : BitVec n) : V.parityright (mask a) = sign a (~~~a) := by
  unfold TensorBundle.parityright
  rw [hV.lowMask_and hVn hn, sumIndices_eq, toNat_mask hn,
    show fsum 64 (fun k => if a.toNat.testBit k then k + 1 else 0) = indexSum n a.toNat from
      indexSum_of_lt a.isLt hn, popcount_eq_bitCount,
    toNat_mask hn, bitCount_of_lt hn a.isLt, parityrightRaw_eq_sigma, sign, toNat_not_eq]

/-- The implementation's complement of a blade is the complementary blade. -/
theorem complement (a : BitVec n) : Leibniz.complement V.n (mask a) V.diffvars 0 = mask (~~~a) := by
  rw [hV.tangent, hVn]
  apply UInt64.toNat_inj.mp
  rw [complement_eq hn, toNat_mask hn, toNat_mask hn, Nat.mod_eq_of_lt a.isLt, toNat_not_eq]

/-- **DirectSum's right complement of a blade in a plain space**:
`!e_a = (-1)^{σ(a, ā)} e_ā`. -/
theorem terms_complementright (a : BitVec n) :
    V.terms₁ .complementright (mask a) = .ok #[{ bits := mask (~~~a), coef := signOf (sign a (~~~a)) }] := by
  show (do let r ← V.complementright (mask a); pure r.bladeTerms) = _
  unfold TensorBundle.complementright
  rw [hV.notDyadic, hV.nullFactor, hV.parityright hVn hn, hV.complement hVn hn]
  simp only [Bool.false_eq_true, ite_false]
  have hne : (signOf (sign a (~~~a)) : Rat) ≠ 0 := by cases sign a (~~~a) <;> decide +kernel
  show Except.ok (BladeResult.single _ _).bladeTerms = _
  rw [single_terms'', show ((if sign a (~~~a) = true then (-1 : Rat) else 1) * 1) = signOf (sign a (~~~a)) by
    simp [signOf], ite_eq_right hne]

/-- The reference kernels' container-level complement is the same. -/
theorem termsC_complementright (a : BitVec n) :
    Grassmann.Kernel.unTermsC V .complementright (mask a)
      = .ok #[{ bits := mask (~~~a), coef := signOf (sign a (~~~a)) }] := by
  show Grassmann.Kernel.ofTerms <$> V.complementrightChain (mask a) = _
  unfold TensorBundle.complementrightChain
  rw [hV.notDyadic, hV.parityright hVn hn, hV.complement hVn hn]
  simp only [Bool.false_eq_true, ite_false]
  have hne : (signOf (sign a (~~~a)) : Rat) ≠ 0 := by cases sign a (~~~a) <;> decide +kernel
  show Except.ok (Grassmann.Kernel.ofTerms #[(mask (~~~a), if sign a (~~~a) = true then -1 else 1)]) = _
  rw [show (if sign a (~~~a) = true then (-1 : Rat) else 1) = signOf (sign a (~~~a)) by simp [signOf]]
  unfold Grassmann.Kernel.ofTerms
  simp [hne]

/-- **DirectSum's Hodge star of a blade in a plain diagonal space**:
`⋆e_a = (-1)^{σ(a, ā)} Π_{i∈a} gᵢ e_ā` for the metric `g` the space reads. -/
theorem terms_hodge (hdiag : V.isdiag = true) {g : Fin n → Rat}
    (hg : ∀ i (h : i < n), V.metricAt (i + 1) = g ⟨i, h⟩) (a : BitVec n) :
    V.terms₁ .complementrighthodge (mask a)
      = .ok (if hodgeCoef g a = 0 then #[] else #[{ bits := mask (~~~a), coef := hodgeCoef g a }]) := by
  show (do let r ← V.complementrighthodge (mask a); pure r.bladeTerms) = _
  unfold TensorBundle.complementrighthodge TensorBundle.parityrighthodge
  rw [hdiag, hV.conformal, hV.notDyadic, hV.nulls, hV.lowMask_and hVn hn]
  simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
  rw [show Leibniz.complement V.n (mask a) V.diffvars 0 = mask (~~~a) from hV.complement hVn hn a]
  have hpr : Leibniz.parityrightRaw (Bits.sumIndices (mask a)) (Bits.popcount (mask a)) = sign a (~~~a) := by
    have := hV.parityright hVn hn a
    unfold TensorBundle.parityright at this
    rwa [hV.lowMask_and hVn hn] at this
  rw [hpr]
  have hm : V.metricProduct (mask a) = mf g a := by
    rw [metricProduct_eq, toNat_mask hn, metricFactor_of_lt _ hn a.isLt, mf]
    apply metricFactor_congr_metric
    intro i hi
    rw [hg i hi]; simp [extendMetric, hi]
  rw [hm]
  show Except.ok (BladeResult.single _ _).bladeTerms = _
  rw [single_terms'']
  have e : (if (sign a (~~~a) != false) = true then -mf g a else mf g a) = hodgeCoef g a := by
    unfold hodgeCoef; cases sign a (~~~a) <;> simp [signOf] <;> grind
  rw [e]

/-- The reference kernels' container-level Hodge star is the same. -/
theorem termsC_hodge (hdiag : V.isdiag = true) {g : Fin n → Rat}
    (hg : ∀ i (h : i < n), V.metricAt (i + 1) = g ⟨i, h⟩) (a : BitVec n) :
    Grassmann.Kernel.unTermsC V .complementrighthodge (mask a)
      = .ok (if hodgeCoef g a = 0 then #[] else #[{ bits := mask (~~~a), coef := hodgeCoef g a }]) := by
  show Grassmann.Kernel.ofTerms <$> V.complementrighthodgeChain (mask a) = _
  have hb := hV.terms_hodge hVn hn hdiag hg a
  unfold TensorBundle.terms₁ TensorBundle.apply₁ TensorBundle.complementrighthodge at hb
  unfold TensorBundle.complementrighthodgeChain
  rw [hV.notDyadic, hdiag]
  rw [hdiag, hV.conformal, hV.notDyadic, hV.nulls] at hb
  simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false] at hb
  simp only [Bool.false_eq_true, ite_false, ite_true]
  show Except.ok (Grassmann.Kernel.ofTerms #[(Leibniz.complement V.n (mask a) V.diffvars 0,
    V.parityrighthodge (mask a))]) = _
  have hb' : (BladeResult.single (V.parityrighthodge (mask a)) (Leibniz.complement V.n (mask a) V.diffvars 0)).bladeTerms
      = if hodgeCoef g a = 0 then #[] else #[{ bits := mask (~~~a), coef := hodgeCoef g a }] := by
    have h2 : (Except.ok (BladeResult.single (V.parityrighthodge (mask a))
        (Leibniz.complement V.n (mask a) V.diffvars 0)).bladeTerms : Except String (Array BladeTerm))
        = Except.ok (if hodgeCoef g a = 0 then #[] else #[{ bits := mask (~~~a), coef := hodgeCoef g a }]) := hb
    injection h2
  rw [← hb']
  unfold Grassmann.Kernel.ofTerms
  simp [BladeResult.bladeTerms, BladeResult.terms]

end IsPlainSpace

/-- The linear extension of a blade rule `e_a ↦ k(a) e_ā` (a complement). -/
theorem lin_compl {n : Nat} {g : Fin n → Rat} {T : BitVec n → Cl g} {k : BitVec n → Rat}
    (hT : ∀ a, T a = k a • Cl.blade (~~~a)) (x : Cl g) : lin T x = ⟨fun c => k (~~~c) * x.coeff (~~~c)⟩ := by
  ext c
  show (bsum n fun a => x.coeff a * (T a).coeff c) = k (~~~c) * x.coeff (~~~c)
  have : ∀ a, x.coeff a * (T a).coeff c = if a = ~~~c then k (~~~c) * x.coeff (~~~c) else 0 := by
    intro a
    rw [hT]
    show x.coeff a * (k a * (if c = ~~~a then 1 else 0)) = _
    by_cases h : a = ~~~c
    · subst h; rw [BitVec.not_not, ite_eq_left rfl, ite_eq_left rfl]; grind
    · have h' : ¬ c = ~~~a := fun e => h (by rw [e, BitVec.not_not])
      rw [ite_eq_right h', ite_eq_right h]; grind
  rw [bsum_congr this, bsum_ite_eq]

/-- **The implementation's right complement is the spec `!` in every plain space**
of dimension `≤ 64`, on all multivectors. -/
theorem implCompl_eq_compl {V : TensorBundle} (hV : IsPlainSpace V) {n : Nat} (hVn : V.n = n) (hn : n ≤ 64)
    {g : Fin n → Rat} (x : Cl g) : implUnary V .complementright x = Cl.compl x := by
  unfold implUnary
  rw [lin_compl (k := fun a => signOf (sign a (~~~a))) fun a => ofTerms_of_matches hn (by
    rw [hV.terms_complementright hVn hn a]
    have hne : (signOf (sign a (~~~a)) : Rat) ≠ 0 := by cases sign a (~~~a) <;> decide +kernel
    simp [Matches, single, hne])]
  ext c
  show signOf (sign (~~~c) (~~~(~~~c))) * x.coeff (~~~c) = signOf (sign (~~~c) c) * x.coeff (~~~c)
  rw [BitVec.not_not]

/-- **The implementation's Hodge star is the spec `⋆` in every plain diagonal
space** of dimension `≤ 64` (for the metric `g` it reads), on all multivectors.
With `Cl.hodge_hodge`, the implementation satisfies `⋆⋆x = (-1)^{k(n-k)} det(g) x`. -/
theorem implHodge_eq_hodge {V : TensorBundle} (hV : IsPlainSpace V) {n : Nat} (hVn : V.n = n) (hn : n ≤ 64)
    (hdiag : V.isdiag = true) {g : Fin n → Rat} (hg : ∀ i (h : i < n), V.metricAt (i + 1) = g ⟨i, h⟩)
    (x : Cl g) : implUnary V .complementrighthodge x = Cl.hodge x := by
  unfold implUnary
  rw [lin_compl (k := hodgeCoef g) fun a => ofTerms_of_matches hn (by
    rw [hV.terms_hodge hVn hn hdiag hg a]
    simp only [Matches, single]
    split <;> simp)]
  ext c
  show hodgeCoef g (~~~c) * x.coeff (~~~c) = signOf (sign (~~~c) c) * mf g (~~~c) * x.coeff (~~~c)
  unfold hodgeCoef; rw [BitVec.not_not]

/-- **The implementation's double Hodge star**: `⋆⋆x = (-1)^{k(n-k)} det(g) x` for
a `k`-vector, in every plain diagonal space of dimension `≤ 64`. -/
theorem implHodge_implHodge {V : TensorBundle} (hV : IsPlainSpace V) {n : Nat} (hVn : V.n = n) (hn : n ≤ 64)
    (hdiag : V.isdiag = true) {g : Fin n → Rat} (hg : ∀ i (h : i < n), V.metricAt (i + 1) = g ⟨i, h⟩)
    {k : Nat} {x : Cl g} (hx : Cl.IsGrade k x) :
    implUnary V .complementrighthodge (implUnary V .complementrighthodge x)
      = ((-1 : Rat) ^ (k * (n - k)) * Cl.det g) • x := by
  rw [implHodge_eq_hodge hV hVn hn hdiag hg, implHodge_eq_hodge hV hVn hn hdiag hg, Cl.hodge_hodge hx]

/-- **The implementation's double right complement**: `!!x = (-1)^{k(n-k)} x` for a
`k`-vector, in every plain space of dimension `≤ 64`. -/
theorem implCompl_implCompl {V : TensorBundle} (hV : IsPlainSpace V) {n : Nat} (hVn : V.n = n) (hn : n ≤ 64)
    {g : Fin n → Rat} {k : Nat} {x : Cl g} (hx : Cl.IsGrade k x) :
    implUnary V .complementright (implUnary V .complementright x) = (-1 : Rat) ^ (k * (n - k)) • x := by
  rw [implCompl_eq_compl hV hVn hn, implCompl_eq_compl hV hVn hn, Cl.compl_compl hx]

/-- `ℝ⁷`: the implementation's Hodge star is the spec `⋆`. -/
theorem R7_hodge (x : Cl (gEuclid 7)) : implUnary ℝ7 .complementrighthodge x = Cl.hodge x :=
  implHodge_eq_hodge (V := ℝ7) (n := 7) ⟨rfl, rfl, rfl, rfl⟩ rfl (by decide) rfl (fun _ _ => rfl) x

/-- `PGA4 = D!"0,1,1,1,1"`: the implementation's Hodge star is the spec `⋆`
(degenerate: `⋆` of a blade containing `e₁` vanishes). -/
theorem PGA4_hodge (x : Cl (diagMetric #[0, 1, 1, 1, 1])) :
    implUnary D!"0,1,1,1,1" .complementrighthodge x = Cl.hodge x :=
  implHodge_eq_hodge (V := D!"0,1,1,1,1") (n := 5) ⟨rfl, rfl, rfl, rfl⟩ rfl (by decide) rfl
    (fun i h => by
      rw [IsDiagSpace.metricAt (V := D!"0,1,1,1,1") (d := #[0, 1, 1, 1, 1]) ⟨rfl, rfl, rfl, rfl, by decide⟩ i]
      simp [diagMetric, show i < 5 from h]) x

end Grassmann.Proofs

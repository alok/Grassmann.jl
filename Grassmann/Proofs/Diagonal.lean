/-
Diagonal metrics in every dimension: the implementation's geometric product of
every `DiagonalForm` space is the spec, proved without enumeration.

A `DiagonalForm` space (Julia `D"…"`, including the degenerate projective
algebras `D"0,1,1,…"`) multiplies shared generators by
`±|Π_{i ∈ a∧b} dᵢ|`, the sign coming from the reordering parity and from the
mask of negative diagonal entries (`TensorBundle.sigBits`, built by a fold). With
the metric-factor loop proved (`DirectSum.Proofs.metricProduct_eq`), this file
shows that sign-and-absolute-value split is exactly `(-1)^σ Π dᵢ`:

* `sigBits_testBit`: the fold marks exactly the negative entries;
* `metricFactor_sign_abs`: `Π dᵢ = (-1)^{#negative} · Π |dᵢ|`;
* `IsDiagSpace.terms_mul`, `IsDiagSpace.table_mul`: the blade table agrees with
  the spec coefficient of the diagonal metric, for every pair of blades;
* `implMul_eq_mul_of_diag`: **the implementation's geometric product is the
  spec product on all multivectors of every non-dual, non-conformal,
  non-tangent `DiagonalForm` space with at most 64 generators** (`PGA4_mul`,
  `PGA6_mul` instantiate it).
-/
import Grassmann.Proofs.General
import DirectSum.Proofs.LowestBit

namespace Grassmann.Proofs

open DirectSum DirectSum.Proofs Grassmann.Spec Lean.Grind

/-! ## Signs and absolute values in `ℚ` -/

/-- The absolute value as the implementation computes it (`TensorBundle.parityinner`). -/
def rabs (x : Rat) : Rat := if x < 0 then -x else x

theorem rabs_nonneg (x : Rat) : 0 ≤ rabs x := by
  unfold rabs
  by_cases h : x < 0
  · rw [ite_eq_left h]; have := Rat.neg_lt_neg h; rw [Rat.neg_zero] at this; exact Rat.le_of_lt this
  · rw [ite_eq_right h]; exact Rat.not_lt.mp h

theorem sign_mul_rabs (x : Rat) : x = signOf (decide (x < 0)) * rabs x := by
  unfold rabs
  by_cases h : x < 0
  · rw [ite_eq_left h]; simp [h, signOf]; grind
  · rw [ite_eq_right h]; simp [h, signOf]

theorem rabs_signOf_mul {A : Rat} (hA : 0 ≤ A) (p : Bool) : rabs (signOf p * A) = A := by
  cases p
  · have e : signOf false * A = A := by simp [signOf]
    rw [e]; unfold rabs; rw [ite_eq_right (Rat.not_lt.mpr hA)]
  · have e : signOf true * A = -A := by simp [signOf]; grind
    rw [e]; unfold rabs
    by_cases h : -A < 0
    · rw [ite_eq_left h, Rat.neg_neg]
    · rw [ite_eq_right h]
      have : 0 ≤ -A := Rat.not_lt.mp h
      have := Rat.nonneg_antisymm hA this
      rw [this]; decide +kernel

/-- Every metric factor is its sign times the metric factor of the absolute values. -/
theorem metricFactor_sign_abs (h : Nat → Rat) (S : Nat) {n : Nat} (hS : ∀ i < n, S.testBit i = decide (h i < 0))
    (m : Nat) :
    metricFactor h n m = signOf (bitParity n (m &&& S)) * metricFactor (fun i => rabs (h i)) n m := by
  induction n with
  | zero => simp [metricFactor]
  | succ n ih =>
    rw [metricFactor_succ, metricFactor_succ, bitParity_succ, Nat.testBit_and, signOf_xor,
      ih (fun i hi => hS i (by omega)), hS n (by omega)]
    cases m.testBit n
    · simp
    · simp only [ite_true, Bool.true_and]
      have := sign_mul_rabs (h n)
      grind

theorem metricFactor_abs_nonneg (h : Nat → Rat) (n m : Nat) : 0 ≤ metricFactor (fun i => rabs (h i)) n m := by
  induction n with
  | zero => show (0 : Rat) ≤ 1; decide +kernel
  | succ n ih =>
    rw [metricFactor_succ]
    apply Rat.mul_nonneg ih
    split
    · exact rabs_nonneg _
    · decide +kernel

/-! ## The negative-sign mask of a diagonal -/

private theorem toNat_shl_one {k : Nat} (hk : k < 64) : (Bits.shl 1 k).toNat = 2 ^ k := by
  unfold Bits.shl
  rw [ite_eq_right (by omega), UInt64.toNat_shiftLeft, UInt64.toNat_one, Nat.toUInt64_eq, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (show k < 2 ^ 64 from Nat.lt_trans hk (by decide)), Nat.mod_eq_of_lt hk,
    Nat.one_shiftLeft, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)]

/-- The fold of `TensorBundle.sigBits` over a diagonal marks exactly its negative
entries (at their positions, below 64). -/
theorem sigFold_testBit (f : UInt64 → Rat × Nat → UInt64)
    (hf : ∀ acc x i, f acc (x, i) = if x < 0 then acc ||| Bits.shl 1 i else acc)
    (l : List Rat) (k : Nat) (acc : UInt64) (hk : k + l.length ≤ 64) (j : Nat) :
    ((l.zipIdx k).foldl f acc).toNat.testBit j
      = (acc.toNat.testBit j || (decide (k ≤ j) && decide (j < k + l.length) && decide (l[j - k]?.getD 1 < 0))) := by
  induction l generalizing k acc with
  | nil => simp; omega
  | cons x l ih =>
    simp only [List.zipIdx_cons, List.foldl_cons, List.length_cons] at hk ⊢
    rw [ih (k + 1) _ (by omega), hf]
    have hacc : (if x < 0 then acc ||| Bits.shl 1 k else acc).toNat.testBit j
        = (acc.toNat.testBit j || (decide (x < 0) && decide (j = k))) := by
      by_cases hx : x < 0
      · rw [ite_eq_left hx, UInt64.toNat_or, Nat.testBit_or, toNat_shl_one (by omega), Nat.testBit_two_pow]
        simp [hx, eq_comm]
      · rw [ite_eq_right hx]; simp [hx]
    rw [hacc]
    rcases Nat.lt_trichotomy j k with h | h | h
    · have h1 : decide (j = k) = false := by simp; omega
      have h2 : decide (k + 1 ≤ j) = false := by simp; omega
      have h3 : decide (k ≤ j) = false := by simp; omega
      rw [h1, h2, h3]; simp
    · subst h
      have h2 : decide (j + 1 ≤ j) = false := by simp
      rw [h2]; simp
    · have h1 : decide (j = k) = false := by simp; omega
      have h2 : decide (k + 1 ≤ j) = true := by simp; omega
      have h3 : decide (k ≤ j) = true := by simp; omega
      have h4 : j - k = (j - (k + 1)) + 1 := by omega
      rw [h1, h2, h3, h4, List.getElem?_cons_succ]
      have h5 : decide (j < k + 1 + l.length) = decide (j < k + (l.length + 1)) := by
        congr 1; apply propext; omega
      rw [h5]; simp

/-- The spec metric of a diagonal `d`: generator `i+1` squares to `d[i]`. -/
def diagMetric (d : Array Rat) : Fin d.size → Rat := fun i => d[i]

/-- The coefficient the implementation computes for `e_a e_b` in a diagonal
space: `(-1)^{σ(a,b)} Π_{i ∈ a∧b} dᵢ`. -/
def diagCoef (d : Array Rat) (a b : UInt64) : Rat :=
  signOf (Bits.reorderParity a b) * metricFactor (fun i => d[i]?.getD 1) 64 (a &&& b).toNat

/-- A diagonal space (Julia `DiagonalForm`, not dual, no conformal pair, no
tangent variables) with at most 64 generators. -/
structure IsDiagSpace (V : TensorBundle) (d : Array Rat) : Prop where
  /-- The metric is the diagonal `d`. -/
  metric : V.metric = .diagonal d
  /-- Not a dual space (its diagonal would be negated). -/
  notDual : V.isdual = false
  /-- No conformal null pair. -/
  conformal : V.hasconformal = false
  /-- No tangent variables. -/
  tangent : V.diffvars = 0
  /-- At most 64 generators. -/
  size : d.size ≤ 64

private theorem blade_terms' (x : UInt64) : (BladeResult.blade x).bladeTerms = #[{ bits := x, coef := 1 }] := by
  have : ((1 : Rat) != 0) = true := by decide +kernel
  simp [BladeResult.bladeTerms, BladeResult.terms, this]

private theorem single_terms' (c : Rat) (x : UInt64) :
    (BladeResult.single c x).bladeTerms = if c = 0 then #[] else #[{ bits := x, coef := c }] := by
  by_cases hc : c = 0
  · subst hc; rw [ite_eq_left rfl]; simp [BladeResult.bladeTerms, BladeResult.terms]
  · rw [ite_eq_right hc]; simp [BladeResult.bladeTerms, BladeResult.terms, hc]

namespace IsDiagSpace

variable {V : TensorBundle} {d : Array Rat} (hV : IsDiagSpace V d)
include hV

theorem flat : IsFlatSpace V := ⟨hV.conformal, hV.tangent⟩

theorem isdiag : V.isdiag = true := by unfold TensorBundle.isdiag; rw [hV.metric]

theorem istangent : V.istangent = false := by unfold TensorBundle.istangent; simp [hV.tangent]

theorem metricAt (i : Nat) : V.metricAt (i + 1) = d[i]?.getD 1 := by
  unfold TensorBundle.metricAt; rw [hV.metric]; simp [hV.notDual]

theorem sigBits_testBit (j : Nat) : V.sigBits.toNat.testBit j = decide (d[j]?.getD 1 < 0) := by
  have hdv : V.diagValues = d := by unfold TensorBundle.diagValues; rw [hV.metric]; simp [hV.notDual]
  unfold TensorBundle.sigBits
  rw [hV.metric]
  simp only
  rw [hdv, ← Array.foldl_toList, Array.toList_zipIdx,
    sigFold_testBit _ (fun _ _ _ => rfl) d.toList 0 0 (by simpa using hV.size) j]
  simp only [UInt64.toNat_zero, Nat.zero_testBit, Bool.false_or, Nat.zero_le, decide_true, Bool.true_and,
    Nat.zero_add, Nat.sub_zero, Array.length_toList]
  by_cases hj : j < d.size
  · simp [hj]
  · simp [hj]; decide +kernel

/-- In a diagonal space the implementation's metric factor is the metric factor
of the diagonal. -/
theorem metricProduct (m : UInt64) :
    V.metricProduct m = metricFactor (fun i => d[i]?.getD 1) 64 m.toNat := by
  rw [metricProduct_eq]
  exact metricFactor_congr_metric (fun i _ => hV.metricAt i) _

/-- The implementation's shared-generator coefficient in a diagonal space is the
spec coefficient `(-1)^σ Π_{a∧b} dᵢ`. -/
theorem parityinner (a b : UInt64) :
    V.parityinner a b = signOf (Bits.reorderParity a b) * metricFactor (fun i => d[i]?.getD 1) 64 (a &&& b).toNat := by
  have hsplit := metricFactor_sign_abs (fun i => d[i]?.getD 1) V.sigBits.toNat (n := 64)
    (fun i _ => hV.sigBits_testBit i) (a &&& b).toNat
  have hA := metricFactor_abs_nonneg (fun i => d[i]?.getD 1) 64 (a &&& b).toNat
  have hg : (if V.metricProduct (a &&& b) < 0 then -V.metricProduct (a &&& b) else V.metricProduct (a &&& b))
      = metricFactor (fun i => rabs (d[i]?.getD 1)) 64 (a &&& b).toNat := by
    show rabs (V.metricProduct (a &&& b)) = _
    rw [hV.metricProduct, hsplit, rabs_signOf_mul hA]
  have hp : V.parity a b = (Bits.reorderParity a b ^^ bitParity 64 ((a &&& b).toNat &&& V.sigBits.toNat)) := by
    unfold TensorBundle.parity
    rw [hV.flat.diffmask]
    have hnz : ∀ x : UInt64, x &&& ~~~0 = x := fun x => by apply UInt64.toBitVec_inj.mp; simp
    simp only [hnz]
    unfold parityjoin
    rw [parity_eq_bitParity, UInt64.toNat_and]
  unfold TensorBundle.parityinner
  rw [hV.flat.symmetricmask]
  simp only
  rw [hg, hp, hsplit]
  cases Bits.reorderParity a b <;> cases bitParity 64 ((a &&& b).toNat &&& V.sigBits.toNat) <;>
    simp [signOf] <;> grind

/-- **DirectSum's geometric product of two blades in a diagonal space**: the
single term `(-1)^σ Π_{a∧b} dᵢ · e_{a⊕b}` (nothing when a degenerate factor
vanishes), for all 64-bit masks. -/
theorem terms_mul (a b : UInt64) :
    V.terms₂ .mul a b = .ok (if diagCoef d a b = 0 then #[] else #[{ bits := a ^^^ b, coef := diagCoef d a b }]) := by
  unfold diagCoef
  show Except.ok (V.mul a b).bladeTerms = _
  congr 1
  unfold TensorBundle.mul TensorBundle.mulDiag
  rw [hV.isdiag, hV.istangent, hV.flat.symmetricmask]
  simp only [ite_true, Bool.false_and, Bool.false_eq_true, ite_false, UInt64.or_zero]
  unfold TensorBundle.nestTangent
  rw [hV.tangent]
  simp only [beq_self_eq_true, Bool.true_or, ite_true]
  have h1 : decide ((1 : Rat) < 0) = false := by decide +kernel
  have h2 : decide ((-1 : Rat) < 0) = true := by decide +kernel
  by_cases hab : (a &&& b == 0) = true
  · have hab' : a &&& b = 0 := by simpa using hab
    rw [ite_eq_left hab, ite_eq_left hab, hV.flat.parity_of_disjoint hab', hab', UInt64.toNat_zero,
      metricFactor_zero_mask]
    have hne : ∀ p : Bool, (signOf p : Rat) * 1 ≠ 0 := fun p => by cases p <;> decide +kernel
    rw [ite_eq_right (hne _)]
    cases Bits.reorderParity a b
    · simp only [Bool.false_eq_true, ite_false, h1]
      show (BladeResult.blade (a ^^^ b)).bladeTerms = _
      rw [blade_terms']; simp [signOf]
    · simp only [ite_true, h2]
      show (BladeResult.single (-1) (a ^^^ b)).bladeTerms = _
      have hn1 : (-1 : Rat) ≠ 0 := by decide +kernel
      rw [single_terms', ite_eq_right hn1]; simp [signOf]
  · rw [ite_eq_right hab, ite_eq_right hab, hV.parityinner, single_terms']

/-- The blade table of a diagonal space agrees with the spec coefficient of its
diagonal. -/
theorem table_mul : TableAgrees V .mul (coef (diagMetric d)) := by
  have hn := hV.size
  intro a b
  rw [hV.terms_mul]
  have hmask : mask (a ^^^ b) = mask a ^^^ mask b := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_xor, toNat_mask hn, toNat_mask hn, toNat_mask hn, BitVec.toNat_xor]
  have hc : diagCoef d (mask a) (mask b) = coef (diagMetric d) a b := by
    rw [diagCoef, coef, bladeCoef, reorderParity_eq_sigma, toNat_mask hn, toNat_mask hn, sigma_of_lt hn a.isLt,
      UInt64.toNat_and, toNat_mask hn, toNat_mask hn,
      metricFactor_of_lt _ hn (Nat.lt_of_le_of_lt Nat.and_le_left a.isLt)]
    congr 1
    apply metricFactor_congr_metric
    intro i hi
    simp [extendMetric, hi, diagMetric]
  rw [hc]
  simp only [Matches, single, hmask]
  split <;> simp

end IsDiagSpace

/-- **The implementation's geometric product is the spec product in every
diagonal space** (Julia `DiagonalForm`: any entries, including zeros and
negatives; not dual, no conformal pair, no tangent variables) with at most 64
generators, on all multivectors. -/
theorem implMul_eq_mul_of_diag {V : TensorBundle} {d : Array Rat} (hV : IsDiagSpace V d)
    (x y : Cl (diagMetric d)) : implMul V x y = x * y :=
  implMul_eq_mul hV.size hV.table_mul x y

/-- `PGA4 = D!"0,1,1,1,1"` (the projective model of 4-space, degenerate): the
implementation's geometric product is the spec product. -/
theorem PGA4_mul (x y : Cl (diagMetric #[0, 1, 1, 1, 1])) : implMul D!"0,1,1,1,1" x y = x * y :=
  implMul_eq_mul_of_diag (V := D!"0,1,1,1,1") ⟨rfl, rfl, rfl, rfl, by decide⟩ x y

/-- A general diagonal form `D!"1,2,-3,1/2,0,5"` in six dimensions. -/
theorem D6_mul (x y : Cl (diagMetric #[1, 2, -3, 1/2, 0, 5])) : implMul D!"1,2,-3,1/2,0,5" x y = x * y :=
  implMul_eq_mul_of_diag (V := D!"1,2,-3,1/2,0,5") ⟨rfl, rfl, rfl, rfl, by decide⟩ x y

end Grassmann.Proofs

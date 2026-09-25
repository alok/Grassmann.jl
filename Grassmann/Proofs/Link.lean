/-
The bridge between the implementation's blade rules and the specification.

The implementation describes every product by its action on basis blades:
`TensorBundle.terms₂ op a b` (DirectSum's exact `Rat` term lists), which the
reference kernels extend bilinearly (DESIGN.md §5.1; `Grassmann.Kernel.build`
turns them into multiply-accumulate plans). The specification `Grassmann.Spec`
describes the same products as twisted convolutions. This file provides the
glue:

* `ofTerms`: read an implementation term list as a spec multivector;
* `Matches`: an implementation result is the single spec term `x · e_c`;
* `bilin`, `bilin_eq_twist`: the bilinear extension of a blade rule that
  matches `k(a,b) · e_{a⊕b}` *is* the twisted convolution `twist k`, so a blade
  table that agrees with the spec on every pair gives agreement on **all**
  multivectors (`implMul_eq_mul`, `implWedge_eq_wedge`);
* `mulSign_eq_coef`: for every space and every width `n ≤ 64`, the
  allocation-free signature-product sign `TensorBundle.mulSign` is the spec
  blade coefficient, proved in general (no enumeration).

The per-space enumerations live in `Grassmann.Proofs.Tables`.
-/
import Grassmann.Spec
import Grassmann.Kernel.Reference

namespace Grassmann.Proofs

open DirectSum DirectSum.Proofs Grassmann.Spec Lean.Grind

variable {n : Nat}

/-! ## Reading implementation results -/

/-- The `UInt64` mask of an `n`-bit blade (bit `k` ⇔ generator `k+1`, as in
`DirectSum.Bits`). -/
def mask (a : BitVec n) : UInt64 := a.toNat.toUInt64

/-- A blade's `UInt64` mask has the same bits. -/
theorem toNat_mask (hn : n ≤ 64) (a : BitVec n) : (mask a).toNat = a.toNat := by
  unfold mask
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.isLt
    (Nat.pow_le_pow_right (by decide) hn))]

/-- Distinct blades have distinct masks. -/
theorem mask_inj (hn : n ≤ 64) {a b : BitVec n} (h : mask a = mask b) : a = b := by
  apply BitVec.eq_of_toNat_eq
  rw [← toNat_mask hn a, ← toNat_mask hn b, h]

/-- The implementation's representation of the spec term `x · e_c`: a single
`BladeTerm`, or nothing when `x = 0` (zero coefficients are dropped, so a
degenerate product such as `e₀e₀ = 0` in projective space is an empty list). -/
def single (c : BitVec n) (x : Rat) : Array BladeTerm :=
  if x = 0 then #[] else #[{ bits := mask c, coef := x }]

/-- An implementation result is the spec term `x · e_c` (and not an error). -/
def Matches (r : Except String (Array BladeTerm)) (c : BitVec n) (x : Rat) : Bool :=
  match r with
  | .ok ts => ts == single c x
  | .error _ => false

/-- An implementation term list read as a spec multivector: the coefficient of
`e_c` is the sum of the coefficients of the terms on blade `c` (errors read as
`0`; `Matches` rules them out). -/
def ofTerms (g : Fin n → Rat) (r : Except String (Array BladeTerm)) : Cl g :=
  ⟨fun c => match r with
    | .ok ts => ts.foldl (fun acc t => if t.bits = mask c then acc + t.coef else acc) 0
    | .error _ => 0⟩

/-- A matching result reads as the spec term. -/
theorem ofTerms_of_matches (hn : n ≤ 64) {g : Fin n → Rat} {r : Except String (Array BladeTerm)}
    {c : BitVec n} {x : Rat} (h : Matches r c x = true) : ofTerms g r = x • Cl.blade c := by
  cases r with
  | error e => simp [Matches] at h
  | ok ts =>
    simp only [Matches, beq_iff_eq] at h
    subst h
    ext d
    show (single c x).foldl (fun acc t => if t.bits = mask d then acc + t.coef else acc) 0
      = x * (if d = c then 1 else 0)
    unfold single
    by_cases hx : x = 0
    · subst hx; simp
    · rw [ite_eq_right hx]
      simp only [List.foldl_toArray', List.foldl_cons, List.foldl_nil]
      by_cases hd : d = c
      · subst hd; simp; grind
      · have : ¬ mask c = mask d := fun e => hd (mask_inj hn e).symm
        simp [this, hd]

/-! ## The reference kernels read these blade rules -/

/-- The reference kernels' blade rule for `*` (`Grassmann.Kernel.binTermsC`, from
which `Grassmann.Kernel.build` makes the plans) is DirectSum's `terms₂ .mul`. -/
theorem binTermsC_mul (V : TensorBundle) (a b : UInt64) :
    Grassmann.Kernel.binTermsC V .mul a b = V.terms₂ .mul a b := rfl

/-- The reference kernels' blade rule for `∧` is `terms₂ .wedge`. -/
theorem binTermsC_wedge (V : TensorBundle) (a b : UInt64) :
    Grassmann.Kernel.binTermsC V .wedge a b = V.terms₂ .wedge a b := rfl

/-- The reference kernels' blade rule for `∨` is `terms₂ .vee`. -/
theorem binTermsC_vee (V : TensorBundle) (a b : UInt64) :
    Grassmann.Kernel.binTermsC V .vee a b = V.terms₂ .vee a b := rfl

/-- The reference kernels' blade rule for `⋅` is `terms₂ .contraction`. -/
theorem binTermsC_contraction (V : TensorBundle) (a b : UInt64) :
    Grassmann.Kernel.binTermsC V .contraction a b = V.terms₂ .contraction a b := rfl

/-! ## Bilinear extension -/

/-- The bilinear extension of a blade-level rule `T` (what the reference kernels
compute from the blade rules). -/
def bilin {g : Fin n → Rat} (T : BitVec n → BitVec n → Cl g) (x y : Cl g) : Cl g :=
  ⟨fun c => bsum n fun a => bsum n fun b => x.coeff a * y.coeff b * (T a b).coeff c⟩

/-- **The bilinear extension of a blade rule `e_a ⋆ e_b = k(a,b) e_{a⊕b}` is the
twisted convolution with `k`.** -/
theorem bilin_eq_twist {g : Fin n → Rat} {T : BitVec n → BitVec n → Cl g} {k : BitVec n → BitVec n → Rat}
    (hT : ∀ a b, T a b = k a b • Cl.blade (a ^^^ b)) (x y : Cl g) :
    (bilin T x y).coeff = twist k x.coeff y.coeff := by
  funext c
  show (bsum n fun a => bsum n fun b => x.coeff a * y.coeff b * (T a b).coeff c) = _
  unfold twist
  refine bsum_congr fun a => ?_
  have hterm : ∀ b, x.coeff a * y.coeff b * (T a b).coeff c
      = if b = a ^^^ c then x.coeff a * y.coeff (a ^^^ c) * k a (a ^^^ c) else 0 := by
    intro b
    rw [hT]
    show x.coeff a * y.coeff b * (k a b * (if c = a ^^^ b then 1 else 0)) = _
    by_cases hb : b = a ^^^ c
    · subst hb; rw [xor_xor_cancel_left, ite_eq_left rfl, ite_eq_left rfl]; grind
    · have : ¬ c = a ^^^ b := fun e => hb (by rw [e, xor_xor_cancel_left])
      rw [ite_eq_right this, ite_eq_right hb]; grind
  rw [bsum_congr hterm, bsum_ite_eq]

/-! ## The implementation's products on spec multivectors -/

/-- The implementation's geometric product (bilinear extension of
`TensorBundle.terms₂ .mul`), on spec multivectors. -/
def implMul (V : TensorBundle) {g : Fin n → Rat} (x y : Cl g) : Cl g :=
  bilin (fun a b => ofTerms g (V.terms₂ .mul (mask a) (mask b))) x y

/-- The implementation's exterior product (bilinear extension of
`TensorBundle.terms₂ .wedge`). -/
def implWedge (V : TensorBundle) {g : Fin n → Rat} (x y : Cl g) : Cl g :=
  bilin (fun a b => ofTerms g (V.terms₂ .wedge (mask a) (mask b))) x y

/-- The implementation's contraction `⋅` (bilinear extension of
`TensorBundle.terms₂ .contraction`). -/
def implContract (V : TensorBundle) {g : Fin n → Rat} (x y : Cl g) : Cl g :=
  bilin (fun a b => ofTerms g (V.terms₂ .contraction (mask a) (mask b))) x y

/-- The implementation's blade table for `op` agrees with the twisting function
`k` on every pair of `n`-bit blades. -/
def TableAgrees (V : TensorBundle) (op : BinOp) (k : BitVec n → BitVec n → Rat) : Prop :=
  ∀ a b : BitVec n, Matches (V.terms₂ op (mask a) (mask b)) (a ^^^ b) (k a b) = true

/-- **A geometric-product table that agrees with the spec on basis blades gives
the spec product on all multivectors.** -/
theorem implMul_eq_mul (hn : n ≤ 64) {V : TensorBundle} {g : Fin n → Rat} (h : TableAgrees V .mul (coef g))
    (x y : Cl g) : implMul V x y = x * y := by
  ext c
  exact congrFun (bilin_eq_twist (fun a b => ofTerms_of_matches hn (h a b)) x y) c

/-- An exterior-product table that agrees with the spec on basis blades gives
the spec exterior product on all multivectors. -/
theorem implWedge_eq_wedge (hn : n ≤ 64) {V : TensorBundle} {g : Fin n → Rat} (h : TableAgrees V .wedge (wcoef (n := n)))
    (x y : Cl g) : implWedge V x y = Cl.wedge x y := by
  ext c
  exact congrFun (bilin_eq_twist (fun a b => ofTerms_of_matches hn (h a b)) x y) c

/-- A contraction table that agrees with the spec on basis blades gives the spec
contraction on all multivectors. -/
theorem implContract_eq_contract (hn : n ≤ 64) {V : TensorBundle} {g : Fin n → Rat}
    (h : TableAgrees V .contraction (ccoef g)) (x y : Cl g) : implContract V x y = Cl.contract x y := by
  ext c
  exact congrFun (bilin_eq_twist (fun a b => ofTerms_of_matches hn (h a b)) x y) c

/-! ## Signature spaces, in general -/

/-- The diagonal metric of a signature mask on `n` generators: `-1` where the
bit is set. -/
def sigG {R : Type _} [CommRing R] (n s : Nat) : Fin n → R := fun i => signOf (s.testBit i)

/-- **The signature-space product sign is the spec coefficient, for every width
`n ≤ 64` and every pair of blades**: `(-1)^{mulSign a b} = coef (sigG s) a b`
with `s = V.sigBits`. (`TensorBundle.mulSign` is the allocation-free sign used
by the signature-space kernels.) -/
theorem mulSign_eq_coef {R : Type _} [CommRing R] (hn : n ≤ 64) (V : TensorBundle) (a b : BitVec n) :
    (signOf (V.mulSign (mask a) (mask b)) : R) = coef (sigG n V.sigBits.toNat) a b := by
  unfold TensorBundle.mulSign
  rw [signOf_parityjoin, toNat_mask hn, toNat_mask hn, coef]
  unfold bladeCoef
  rw [sigma_of_lt hn a.isLt, metricFactor_of_lt _ hn (Nat.lt_of_le_of_lt Nat.and_le_left a.isLt)]
  congr 1
  apply metricFactor_congr_metric
  intro i hi
  simp [extendMetric, hi, sigG, sigMetric]

end Grassmann.Proofs

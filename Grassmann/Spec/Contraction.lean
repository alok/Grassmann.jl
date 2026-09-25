/-
The contraction and the regressive product in the specification model.

* `contract` is Julia's `contraction(x, y)` (`x ⋅ y`, `x ⨽ y`): the left
  contraction of `~y` onto `x`, blade by blade
  `e_a ⋅ e_b = ⟨~e_b e_a⟩ = (-1)^{rev b} e_b e_a` when `b ⊆ a`, else `0`
  (`v₁₂ ⋅ v₂ = -v₁`, `v₁₂ ⋅ v₁₂ = 1`). Theorems: `contract_eq_proj`
  (**`x ⋅ y = ⟨~y x⟩_{p-q}`** for a `p`-vector `x` and a `q`-vector `y`,
  `q ≤ p`) and `contract_of_vector` (on vectors it is the inner product).
* `vee` is Julia's regressive product `x ∨ y`, the De Morgan dual of `∧` under
  the right complement: `!(x ∨ y) = !x ∧ !y` (`compl_vee`). Theorems: `!` is a
  bijection (`complInv`), and `vee_assoc`: the regressive product is
  associative, by transport from `wedge_assoc`.
-/
import Grassmann.Spec.Vector
import Grassmann.Spec.Hodge

namespace Grassmann.Spec

open Lean.Grind DirectSum.Proofs

universe u

variable {R : Type u} [CommRing R] {n : Nat}

/-! ## Sub-blades -/

/-- `b ⊆ a` exactly when the common part of `a` and `b` has the grade of `b`. -/
theorem subset_iff_grade (a b : BitVec n) : b &&& a = b ↔ grade (a &&& b) = grade b := by
  unfold grade
  rw [BitVec.toNat_and, bitCount_and_eq_iff]
  constructor
  · intro h i _ hb
    have := congrArg (fun x : BitVec n => x.toNat.testBit i) h
    simp only [BitVec.toNat_and, Nat.testBit_and, hb] at this
    simpa using this
  · intro h
    apply BitVec.eq_of_toNat_eq
    apply Nat.eq_of_testBit_eq
    intro i
    rw [BitVec.toNat_and, Nat.testBit_and]
    by_cases hi : i < n
    · cases hb : b.toNat.testBit i
      · rfl
      · rw [h i hi hb]; rfl
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))]
      rfl

/-- The grade of the symmetric difference of `b ⊆ a` is `|a| - |b|`. -/
theorem grade_xor_of_subset {a b : BitVec n} (h : b &&& a = b) : grade (a ^^^ b) = grade a - grade b := by
  have k := bitCount_xor_add n a.toNat b.toNat
  have e := (subset_iff_grade a b).mp h
  unfold grade at e ⊢
  rw [BitVec.toNat_xor]; rw [BitVec.toNat_and] at e; omega

/-! ## The contraction -/

/-- The contraction coefficient: `e_a ⋅ e_b = ccoef g a b · e_{a⊕b}`, the
coefficient of `⟨~e_b e_a⟩` when `b ⊆ a`, else `0`. -/
def ccoef (g : Fin n → R) (a b : BitVec n) : R := if b &&& a = b then revSign b * coef g b a else 0

namespace Cl

variable {g : Fin n → R}

/-- **The contraction** `x ⋅ y` (Julia `contraction`): the left contraction of
`~y` onto `x`. -/
def contract (x y : Cl g) : Cl g := ⟨twist (ccoef g) x.coeff y.coeff⟩

/-- Blades contract by `ccoef`. -/
theorem blade_contract_blade (a b : BitVec n) :
    contract (blade a) (blade b : Cl g) = ccoef g a b • blade (a ^^^ b) := by
  ext c
  exact congrFun (twist_delta_delta (ccoef g) a b) c

/-- The contraction is left distributive. -/
theorem contract_add (x y z : Cl g) : contract x (y + z) = contract x y + contract x z := by
  ext c
  exact congrFun (twist_add_right (ccoef g) x.coeff y.coeff z.coeff) c

/-- The contraction is right distributive. -/
theorem add_contract (x y z : Cl g) : contract (x + y) z = contract x z + contract y z := by
  ext c
  exact congrFun (twist_add_left (ccoef g) x.coeff y.coeff z.coeff) c

/-- **The contraction of a `p`-vector by a `q`-vector is `⟨~y x⟩_{p-q}`.** -/
theorem contract_eq_proj {p q : Nat} {x y : Cl g} (hx : IsGrade p x) (hy : IsGrade q y) (hqp : q ≤ p) :
    contract x y = proj (p - q) (reverse y * x) := by
  ext c
  show twist (ccoef g) x.coeff y.coeff c
    = if grade c = p - q then twist (coef g) (fun b => revSign b * y.coeff b) x.coeff c else 0
  rw [twist_eq_sum_right]
  by_cases hc : grade c = p - q
  · rw [ite_eq_left hc]
    unfold twist
    refine bsum_congr fun b => ?_
    by_cases hxa : x.coeff (b ^^^ c) = 0
    · rw [hxa]; grind
    by_cases hyb : y.coeff b = 0
    · rw [hyb]; grind
    have ga : grade (b ^^^ c) = p := Classical.byContradiction fun h => hxa (hx _ h)
    have gb : grade b = q := Classical.byContradiction fun h => hyb (hy _ h)
    -- `c = (b ⊕ c) ⊕ b` has grade `p - q`, so `b ⊆ b ⊕ c`
    have hsub : b &&& (b ^^^ c) = b := by
      rw [subset_iff_grade]
      have k := bitCount_xor_add n (b ^^^ c).toNat b.toNat
      have hcc : (b ^^^ c) ^^^ b = c := by rw [BitVec.xor_comm, xor_xor_cancel_left]
      have e1 : grade c = bitCount n ((b ^^^ c).toNat ^^^ b.toNat) := by
        unfold grade; rw [← BitVec.toNat_xor, hcc]
      have kb : bitCount n ((b ^^^ c).toNat &&& b.toNat) ≤ bitCount n b.toNat := by
        rw [bitCount_and_comm]; exact bitCount_and_le_left n _ _
      unfold grade at ga gb e1 hc ⊢
      rw [BitVec.toNat_and]
      omega
    unfold ccoef
    rw [ite_eq_left hsub]
    grind
  · rw [ite_eq_right hc, bsum_congr (f' := fun _ => (0 : R)) ?_, bsum_const_zero]
    intro b
    by_cases hxa : x.coeff (b ^^^ c) = 0
    · rw [hxa]; grind
    by_cases hyb : y.coeff b = 0
    · rw [hyb]; grind
    have ga : grade (b ^^^ c) = p := Classical.byContradiction fun h => hxa (hx _ h)
    have gb : grade b = q := Classical.byContradiction fun h => hyb (hy _ h)
    unfold ccoef
    by_cases hsub : b &&& (b ^^^ c) = b
    · have := grade_xor_of_subset hsub
      rw [BitVec.xor_comm, xor_xor_cancel_left] at this
      omega
    · rw [ite_eq_right hsub]; grind

/-- On vectors the contraction is the inner product: `u ⋅ v = B(u, v)`. -/
theorem contract_of_vector {u v : Cl g} (hu : IsGrade 1 u) (hv : IsGrade 1 v) :
    contract u v = scalar (dot u v) := by
  rw [contract_eq_proj hu hv (Nat.le_refl 1), Nat.sub_self]
  ext c
  show (if grade c = 0 then (reverse v * u).coeff c else 0) = if c = 0 then dot u v else 0
  by_cases hc : c = 0
  · subst hc
    have h0 : grade (0 : BitVec n) = 0 := (grade_eq_zero_iff _).mpr rfl
    rw [ite_eq_left h0, ite_eq_left rfl, coeff_mul]
    unfold dot
    refine bsum_congr fun a => ?_
    show revSign a * v.coeff a * u.coeff (a ^^^ 0) * coef g a (a ^^^ 0) = u.coeff a * v.coeff a * coef g a a
    rw [xor_zero']
    by_cases hva : v.coeff a = 0
    · rw [hva]; grind
    have ga : grade a = 1 := Classical.byContradiction fun h => hva (hv a h)
    have hr : (revSign a : R) = 1 := by rw [revSign, ga]; rfl
    rw [hr]; grind
  · rw [ite_eq_right (fun h => hc ((grade_eq_zero_iff c).mp h)), ite_eq_right hc]

/-! ## The regressive product -/

/-- The inverse of the right complement (Julia `complementleft` on Euclidean
blades): `e_b ↦ (-1)^{σ(b̄, b)} e_b̄`. -/
def complInv (x : Cl g) : Cl g := ⟨fun c => signOf (sign c (~~~c)) * x.coeff (~~~c)⟩

private theorem signOf_mul_self_mul (s : Bool) (r : R) : signOf s * (signOf s * r) = r := by
  have := signOf_mul_self (R := R) s
  grind

theorem compl_complInv (x : Cl g) : compl (complInv x) = x := by
  ext c
  show signOf (sign (~~~c) c) * (signOf (sign (~~~c) (~~~(~~~c))) * x.coeff (~~~(~~~c))) = x.coeff c
  rw [BitVec.not_not]; exact signOf_mul_self_mul _ _

theorem complInv_compl (x : Cl g) : complInv (compl x) = x := by
  ext c
  show signOf (sign c (~~~c)) * (signOf (sign (~~~(~~~c)) (~~~c)) * x.coeff (~~~(~~~c))) = x.coeff c
  rw [BitVec.not_not]; exact signOf_mul_self_mul _ _

/-- **The regressive product** `x ∨ y` (Julia `∨`), the De Morgan dual of `∧`. -/
def vee (x y : Cl g) : Cl g := complInv (wedge (compl x) (compl y))

/-- De Morgan: `!(x ∨ y) = !x ∧ !y`. -/
theorem compl_vee (x y : Cl g) : compl (vee x y) = wedge (compl x) (compl y) := compl_complInv _

theorem not_xor_not (a b : BitVec n) : ~~~a ^^^ ~~~b = a ^^^ b := by
  rw [not_eq_xor_allOnes, not_eq_xor_allOnes]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_xor]
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_xor]
  cases a.toNat.testBit i <;> cases b.toNat.testBit i <;> cases (BitVec.allOnes n).toNat.testBit i <;> rfl

/-- The regressive product of two blades is a multiple of the complement of
their symmetric difference: `e_a ∨ e_b ∈ R · e_{~(a⊕b)}`. -/
theorem vee_blade (a b : BitVec n) :
    vee (blade a) (blade b : Cl g) = (vee (blade a) (blade b : Cl g)).coeff (~~~(a ^^^ b)) • blade (~~~(a ^^^ b)) := by
  have hw : wedge (compl (blade a)) (compl (blade b) : Cl g)
      = ((signOf (sign a (~~~a)) : R) * signOf (sign b (~~~b)) * wcoef (~~~a) (~~~b)) • blade (a ^^^ b) := by
    rw [compl_blade, compl_blade, smul_wedge, wedge_smul, blade_wedge_blade, not_xor_not]
    ext c; simp only [coeff_smul]; grind
  ext c
  show signOf (sign c (~~~c)) * (wedge (compl (blade a)) (compl (blade b))).coeff (~~~c)
    = (signOf (sign (~~~(a ^^^ b)) (~~~(~~~(a ^^^ b))))
        * (wedge (compl (blade a)) (compl (blade b))).coeff (~~~(~~~(a ^^^ b))))
      * (if c = ~~~(a ^^^ b) then 1 else 0)
  rw [hw]
  simp only [coeff_smul, coeff_blade, BitVec.not_not]
  by_cases hc : c = ~~~(a ^^^ b)
  · subst hc; simp only [BitVec.not_not, ite_true]; grind
  · have : ¬ ~~~c = a ^^^ b := fun e => hc (by rw [← e, BitVec.not_not])
    rw [ite_eq_right this, ite_eq_right hc]; grind

/-- **The regressive product is associative.** -/
theorem vee_assoc (x y z : Cl g) : vee (vee x y) z = vee x (vee y z) := by
  unfold vee
  rw [compl_complInv, compl_complInv, wedge_assoc]

end Cl

end Grassmann.Spec

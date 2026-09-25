/-
Complements and the Hodge star in the specification model.

With `ā = ~~~a` the complementary blade (all `n` generators not in `a`):

* `compl` is the Euclidean right complement (Julia `complementright`, `!x`):
  `!e_a = (-1)^{σ(a, ā)} e_ā`, the unique signed blade with `e_a ∧ !e_a = I`
  (`blade_wedge_compl`);
* `hodge` is the metric (Hodge) complement (Julia `complementrighthodge`, `⋆x`):
  `⋆e_a = (-1)^{σ(a, ā)} Π_{i ∈ a} gᵢ e_ā`, and `hodge_eq_reverse_mul` proves it
  is `~x · I`, the definition Julia uses for general metrics.

The double-complement theorems: for a `k`-vector `x`,
`!!x = (-1)^{k(n-k)} x` (`compl_compl`) and `⋆⋆x = (-1)^{k(n-k)} det(g) x`
(`hodge_hodge`), both from the swap identity of `σ` (and the metric factor of a
blade and its complement multiplying to the determinant).
-/
import Grassmann.Spec.Involution

namespace Grassmann.Spec

open Lean.Grind DirectSum.Proofs

universe u

variable {R : Type u} [CommRing R] {n : Nat}

/-! ## Complementary blades -/

theorem not_eq_xor_allOnes (c : BitVec n) : ~~~c = c ^^^ BitVec.allOnes n := BitVec.xor_allOnes.symm

/-- A blade and its complement make up the pseudoscalar. -/
theorem not_xor_self (c : BitVec n) : ~~~c ^^^ c = BitVec.allOnes n := by
  rw [not_eq_xor_allOnes, BitVec.xor_comm c, BitVec.xor_assoc, xor_self', xor_zero']

/-- The complement mask is the xor with `2ⁿ - 1`. -/
theorem toNat_not_eq (c : BitVec n) : (~~~c).toNat = c.toNat ^^^ (2 ^ n - 1) := by
  rw [not_eq_xor_allOnes, BitVec.toNat_xor, BitVec.toNat_allOnes]

/-- The complementary blade has the complementary grade. -/
theorem grade_not (c : BitVec n) : grade (~~~c) = n - grade c := by
  have := bitCount_xor_allOnes n c.toNat
  unfold grade; rw [toNat_not_eq]; omega

/-- A blade and its complement are disjoint. -/
theorem and_not_self' (c : BitVec n) : c &&& ~~~c = 0 := BitVec.and_not_self c

/-- The sign of swapping a blade and its complement: `(-1)^{k(n-k)}`. -/
theorem sign_compl_swap (c : BitVec n) :
    (sign c (~~~c) ^^ sign (~~~c) c) = ((grade c % 2 == 1) && ((n - grade c) % 2 == 1)) := by
  unfold sign
  rw [sigma_swap, ← BitVec.toNat_and, and_not_self']
  have hp : bitParity n (BitVec.toNat (0 : BitVec n)) = false := by simp [bitParity]
  rw [hp, Bool.xor_false]
  show ((grade c % 2 == 1) && (grade (~~~c) % 2 == 1)) = _
  rw [grade_not]

namespace Cl

variable {g : Fin n → R}

/-! ## The complements -/

/-- The Euclidean right complement `!x` (Julia `complementright`):
`!e_a = (-1)^{σ(a, ā)} e_ā`. -/
def compl (x : Cl g) : Cl g := ⟨fun c => signOf (sign (~~~c) c) * x.coeff (~~~c)⟩

/-- The Hodge complement `⋆x` (Julia `complementrighthodge`):
`⋆e_a = (-1)^{σ(a, ā)} Π_{i∈a} gᵢ e_ā`. -/
def hodge (x : Cl g) : Cl g := ⟨fun c => signOf (sign (~~~c) c) * mf g (~~~c) * x.coeff (~~~c)⟩

/-- The determinant `Π_{i<n} gᵢ` of the metric (the square of the pseudoscalar
up to the reversion sign). -/
def det (g : Fin n → R) : R := mf g (BitVec.allOnes n)

private theorem not_eq_iff (a c : BitVec n) : ~~~c = a ↔ c = ~~~a := by
  constructor
  · rintro rfl; exact BitVec.not_not.symm
  · rintro rfl; exact BitVec.not_not

/-- The right complement of a basis blade. -/
theorem compl_blade (a : BitVec n) : compl (blade a : Cl g) = (signOf (sign a (~~~a)) : R) • blade (~~~a) := by
  ext c
  show signOf (sign (~~~c) c) * (if ~~~c = a then 1 else 0)
    = signOf (sign a (~~~a)) * (if c = ~~~a then 1 else 0)
  by_cases h : c = ~~~a
  · subst h; rw [BitVec.not_not, ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right (fun e => h ((not_eq_iff a c).mp e)), ite_eq_right h, Semiring.mul_zero,
      Semiring.mul_zero]

/-- The Hodge complement of a basis blade. -/
theorem hodge_blade (a : BitVec n) :
    hodge (blade a : Cl g) = (signOf (sign a (~~~a)) * mf g a : R) • blade (~~~a) := by
  ext c
  show signOf (sign (~~~c) c) * mf g (~~~c) * (if ~~~c = a then 1 else 0)
    = signOf (sign a (~~~a)) * mf g a * (if c = ~~~a then 1 else 0)
  by_cases h : c = ~~~a
  · subst h; rw [BitVec.not_not, ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right (fun e => h ((not_eq_iff a c).mp e)), ite_eq_right h, Semiring.mul_zero,
      Semiring.mul_zero]

/-- **The defining property of the right complement**: `e_a ∧ !e_a = I`. -/
theorem blade_wedge_compl (a : BitVec n) : wedge (blade a) (compl (blade a)) = (pseudoscalar : Cl g) := by
  rw [compl_blade, wedge_smul, blade_wedge_blade, BitVec.xor_comm, not_xor_self]
  have hw : (wcoef a (~~~a) : R) = signOf (sign a (~~~a)) := by
    unfold wcoef; rw [ite_eq_left (and_not_self' a)]
  rw [hw]
  ext c
  show signOf (sign a (~~~a)) * (signOf (sign a (~~~a)) * (if c = BitVec.allOnes n then 1 else 0))
    = (if c = BitVec.allOnes n then (1 : R) else 0)
  have := signOf_mul_self (R := R) (sign a (~~~a))
  grind

/-- **The double right complement**: `!!x = (-1)^{k(n-k)} x` for a `k`-vector `x`. -/
theorem compl_compl {k : Nat} {x : Cl g} (hx : IsGrade k x) :
    compl (compl x) = (-1 : R) ^ (k * (n - k)) • x := by
  ext c
  show signOf (sign (~~~c) c) * (signOf (sign (~~~(~~~c)) (~~~c)) * x.coeff (~~~(~~~c)))
    = (-1 : R) ^ (k * (n - k)) * x.coeff c
  rw [BitVec.not_not]
  by_cases hxc : x.coeff c = 0
  · rw [hxc]; grind
  have gc : grade c = k := Classical.byContradiction fun h => hxc (hx c h)
  have hs := congrArg (signOf (R := R)) (sign_compl_swap c)
  rw [signOf_xor, gc] at hs
  rw [neg_one_pow, odd_mul, ← hs]
  grind

/-- **The Hodge star is `~x · I`** (reverse, then multiply by the pseudoscalar
on the right): Julia's definition for general metrics agrees with the
diagonal formula. -/
theorem hodge_eq_reverse_mul (x : Cl g) : hodge x = reverse x * pseudoscalar := by
  ext c
  show signOf (sign (~~~c) c) * mf g (~~~c) * x.coeff (~~~c)
    = bsum n fun a => revSign a * x.coeff a * (if a ^^^ c = BitVec.allOnes n then 1 else 0) * coef g a (a ^^^ c)
  have hterm : ∀ a : BitVec n, revSign a * x.coeff a * (if a ^^^ c = BitVec.allOnes n then (1 : R) else 0)
      * coef g a (a ^^^ c) = if a = ~~~c then revSign a * x.coeff a * coef g a (a ^^^ c) else 0 := by
    intro a
    have hiff : a ^^^ c = BitVec.allOnes n ↔ a = ~~~c := by
      constructor
      · intro h
        rw [← not_xor_self c] at h
        have : a ^^^ c ^^^ c = ~~~c ^^^ c ^^^ c := congrArg (· ^^^ c) h
        rwa [xor_xor_cancel_right, xor_xor_cancel_right] at this
      · rintro rfl; exact not_xor_self c
    by_cases h : a = ~~~c
    · rw [ite_eq_left (hiff.mpr h), ite_eq_left h, Semiring.mul_one]
    · rw [ite_eq_right (fun e => h (hiff.mp e)), ite_eq_right h, Semiring.mul_zero, Semiring.zero_mul]
  rw [bsum_congr hterm, bsum_ite_eq, not_xor_self, revSign_eq, coef_eq]
  have hand : ~~~c &&& BitVec.allOnes n = ~~~c := by
    rw [← BitVec.xor_allOnes (x := c)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
  rw [hand]
  have hsplit : sign (~~~c) (BitVec.allOnes n) = (sign (~~~c) (~~~c) ^^ sign (~~~c) c) := by
    rw [← not_xor_self c]; unfold sign; rw [BitVec.toNat_xor, sigma_xor_right]
  rw [hsplit, signOf_xor]
  have := signOf_mul_self (R := R) (sign (~~~c) (~~~c))
  grind

/-- The metric factors of a blade and of its complement multiply to the
determinant. -/
theorem mf_mul_mf_not (c : BitVec n) : mf g c * mf g (~~~c) = det g := by
  unfold det
  unfold mf
  rw [toNat_not_eq, BitVec.toNat_allOnes]
  exact metricFactor_mul_compl _ _ _

/-- **The double Hodge star**: `⋆⋆x = (-1)^{k(n-k)} det(g) x` for a `k`-vector `x`. -/
theorem hodge_hodge {k : Nat} {x : Cl g} (hx : IsGrade k x) :
    hodge (hodge x) = ((-1 : R) ^ (k * (n - k)) * det g) • x := by
  ext c
  show signOf (sign (~~~c) c) * mf g (~~~c)
      * (signOf (sign (~~~(~~~c)) (~~~c)) * mf g (~~~(~~~c)) * x.coeff (~~~(~~~c)))
    = (-1 : R) ^ (k * (n - k)) * det g * x.coeff c
  rw [BitVec.not_not]
  by_cases hxc : x.coeff c = 0
  · rw [hxc]; grind
  have gc : grade c = k := Classical.byContradiction fun h => hxc (hx c h)
  have hs := congrArg (signOf (R := R)) (sign_compl_swap c)
  rw [signOf_xor, gc] at hs
  rw [neg_one_pow, odd_mul, ← hs, ← mf_mul_mf_not c]
  grind

end Cl

end Grassmann.Spec

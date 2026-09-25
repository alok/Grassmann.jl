/-
The exterior product and grades in the specification model.

The exterior product is the twisted convolution with the cocycle

  `w(a, b) = (-1)^{σ(a,b)}` if `a ∧ b = 0`, else `0`   (`wcoef`),

which is the blade coefficient of the **zero** metric (`wcoef_eq_coef_zero`):
the exterior algebra is the Clifford algebra of the zero form, so
associativity (`wedge_assoc`) comes for free from `twist_assoc`. Grades:
`IsGrade k x` (`x` is a `k`-vector) and the projection `proj k`. The main
theorems: the wedge of a `p`-vector and a `q`-vector is a `(p+q)`-vector
(`isGrade_wedge`), and **graded commutativity**
`x ∧ y = (-1)^{pq} y ∧ x` (`wedge_comm`), from the swap identity of `σ`.
-/
import Grassmann.Spec.Clifford

namespace Grassmann.Spec

open Lean.Grind DirectSum.Proofs

universe u

variable {R : Type u} [CommRing R] {n : Nat}

/-! ## Blade level -/

/-- The exterior-product coefficient: `e_a ∧ e_b = wcoef a b · e_{a⊕b}`, the
reordering sign on disjoint blades and `0` on overlapping ones. -/
def wcoef (a b : BitVec n) : R := if a &&& b = 0 then signOf (sign a b) else 0

theorem toNat_eq_zero_iff (a : BitVec n) : a.toNat = 0 ↔ a = 0 := by
  constructor
  · intro h; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
  · rintro rfl; rfl

/-- A blade has grade `0` exactly when it is the empty blade. -/
theorem grade_eq_zero_iff (a : BitVec n) : grade a = 0 ↔ a = 0 := by
  rw [grade, bitCount_eq_zero_iff a.isLt, toNat_eq_zero_iff]

/-- The grade of a disjoint union is the sum of the grades. -/
theorem grade_xor_of_disjoint {a b : BitVec n} (h : a &&& b = 0) : grade (a ^^^ b) = grade a + grade b := by
  have key := bitCount_xor_add n a.toNat b.toNat
  have h0 : bitCount n (a.toNat &&& b.toNat) = 0 := by
    rw [← BitVec.toNat_and, h]; exact bitCount_zero_mask n
  unfold grade; rw [BitVec.toNat_xor]; omega

/-- **The exterior algebra is the Clifford algebra of the zero metric.** -/
theorem wcoef_eq_coef_zero (a b : BitVec n) : (wcoef a b : R) = coef (fun _ : Fin n => (0 : R)) a b := by
  have hm : metricFactor (extendMetric (fun _ : Fin n => (0 : R))) n (a.toNat &&& b.toNat)
      = metricFactor (fun _ => (0 : R)) n (a.toNat &&& b.toNat) :=
    metricFactor_congr_metric (fun i hi => by simp [extendMetric, hi]) _
  unfold wcoef coef bladeCoef
  rw [hm, metricFactor_zero_metric, ← BitVec.toNat_and]
  have : bitCount n (a &&& b).toNat = 0 ↔ a &&& b = 0 := grade_eq_zero_iff _
  by_cases h : a &&& b = 0
  · rw [ite_eq_left h, ite_eq_left (this.mpr h), Semiring.mul_one]; rfl
  · rw [ite_eq_right h, ite_eq_right (fun e => h (this.mp e)), Semiring.mul_zero]

/-- The exterior coefficients form a 2-cocycle. -/
theorem wcoef_cocycle : IsCocycle (wcoef : BitVec n → BitVec n → R) := by
  intro a b c
  simp only [wcoef_eq_coef_zero]
  exact coef_cocycle _ a b c

theorem wcoef_zero_left (b : BitVec n) : (wcoef 0 b : R) = 1 := by
  rw [wcoef_eq_coef_zero, coef_zero_left]

theorem wcoef_zero_right (a : BitVec n) : (wcoef a 0 : R) = 1 := by
  rw [wcoef_eq_coef_zero, coef_zero_right]

/-- Swapping two blades in an exterior product: the sign `(-1)^{|a||b|}`. -/
theorem wcoef_swap (a b : BitVec n) :
    (wcoef a b : R) = signOf ((grade a % 2 == 1) && (grade b % 2 == 1)) * wcoef b a := by
  unfold wcoef
  rw [BitVec.and_comm b a]
  by_cases h : a &&& b = 0
  · rw [ite_eq_left h, ite_eq_left h, ← signOf_xor]
    have hs := sigma_swap n a.toNat b.toNat
    rw [← BitVec.toNat_and, h] at hs
    have hp : bitParity n (BitVec.toNat (0 : BitVec n)) = false := by simp [bitParity]
    rw [hp, Bool.xor_false] at hs
    unfold sign; congr 1
    revert hs
    cases sigma n a.toNat b.toNat <;> cases sigma n b.toNat a.toNat <;> simp [bitParity, grade] <;> omega
  · rw [ite_eq_right h, ite_eq_right h, Semiring.mul_zero]

namespace Cl

variable {g : Fin n → R}

/-! ## The exterior product -/

/-- **The exterior (wedge) product**, `x ∧ y`, as an explicit finite sum. -/
def wedge (x y : Cl g) : Cl g := ⟨twist wcoef x.coeff y.coeff⟩

theorem coeff_wedge (x y : Cl g) (c : BitVec n) :
    (wedge x y).coeff c = bsum n fun a => x.coeff a * y.coeff (a ^^^ c) * wcoef a (a ^^^ c) := rfl

/-- The exterior product is the geometric product of the zero metric (on the
same coefficient functions). -/
theorem wedge_eq_mul_zero (x y : Cl g) :
    (wedge x y).coeff = ((⟨x.coeff⟩ : Cl (fun _ : Fin n => (0 : R))) * ⟨y.coeff⟩).coeff := by
  show twist wcoef x.coeff y.coeff = twist (coef _) x.coeff y.coeff
  congr 1
  funext a b
  exact wcoef_eq_coef_zero a b

/-- **Associativity of the exterior product.** -/
theorem wedge_assoc (x y z : Cl g) : wedge (wedge x y) z = wedge x (wedge y z) := by
  ext c
  exact congrFun (twist_assoc wcoef_cocycle x.coeff y.coeff z.coeff) c

/-- `1` is a left unit of `∧`. -/
theorem one_wedge (x : Cl g) : wedge 1 x = x := by
  ext c
  exact congrFun (twist_delta_zero_left wcoef_zero_left x.coeff) c

/-- `1` is a right unit of `∧`. -/
theorem wedge_one (x : Cl g) : wedge x 1 = x := by
  ext c
  exact congrFun (twist_delta_zero_right wcoef_zero_right x.coeff) c

/-- `∧` is left distributive. -/
theorem wedge_add (x y z : Cl g) : wedge x (y + z) = wedge x y + wedge x z := by
  ext c
  exact congrFun (twist_add_right wcoef x.coeff y.coeff z.coeff) c

/-- `∧` is right distributive. -/
theorem add_wedge (x y z : Cl g) : wedge (x + y) z = wedge x z + wedge y z := by
  ext c
  exact congrFun (twist_add_left wcoef x.coeff y.coeff z.coeff) c

/-- Scalars pull out of the left factor of `∧`. -/
theorem smul_wedge (r : R) (x y : Cl g) : wedge (r • x) y = r • wedge x y := by
  ext c
  exact congrFun (twist_smul_left wcoef r x.coeff y.coeff) c

/-- Scalars pull out of the right factor of `∧`. -/
theorem wedge_smul (r : R) (x y : Cl g) : wedge x (r • y) = r • wedge x y := by
  ext c
  exact congrFun (twist_smul_right wcoef r x.coeff y.coeff) c

/-- Blades wedge by the sign table: `e_a ∧ e_b = ±e_{a∪b}` or `0`. -/
theorem blade_wedge_blade (a b : BitVec n) :
    (wedge (blade a) (blade b) : Cl g) = (wcoef a b : R) • blade (a ^^^ b) := by
  ext c
  exact congrFun (twist_delta_delta wcoef a b) c

/-! ## Grades -/

/-- `x` is homogeneous of grade `k` (a `k`-vector). -/
def IsGrade (k : Nat) (x : Cl g) : Prop := ∀ a, grade a ≠ k → x.coeff a = 0

/-- The grade-`k` part `⟨x⟩ₖ`. -/
def proj (k : Nat) (x : Cl g) : Cl g := ⟨fun a => if grade a = k then x.coeff a else 0⟩

theorem isGrade_proj (k : Nat) (x : Cl g) : IsGrade k (proj k x) := by
  intro a h
  show (if grade a = k then x.coeff a else 0) = 0
  rw [ite_eq_right h]

theorem proj_eq_self {k : Nat} {x : Cl g} (h : IsGrade k x) : proj k x = x := by
  ext a
  show (if grade a = k then x.coeff a else 0) = x.coeff a
  by_cases hk : grade a = k
  · rw [ite_eq_left hk]
  · rw [ite_eq_right hk, h a hk]

theorem proj_proj_of_ne {j k : Nat} (h : j ≠ k) (x : Cl g) : proj j (proj k x) = 0 := by
  ext a
  show (if grade a = j then (if grade a = k then x.coeff a else 0) else 0) = 0
  by_cases hj : grade a = j
  · rw [ite_eq_left hj, ite_eq_right (by omega)]
  · rw [ite_eq_right hj]

theorem proj_add (k : Nat) (x y : Cl g) : proj k (x + y) = proj k x + proj k y := by
  ext a
  show (if grade a = k then x.coeff a + y.coeff a else 0)
    = (if grade a = k then x.coeff a else 0) + (if grade a = k then y.coeff a else 0)
  by_cases hk : grade a = k
  · rw [ite_eq_left hk, ite_eq_left hk, ite_eq_left hk]
  · rw [ite_eq_right hk, ite_eq_right hk, ite_eq_right hk, Semiring.add_zero]

theorem proj_smul (k : Nat) (r : R) (x : Cl g) : proj k (r • x) = r • proj k x := by
  ext a
  show (if grade a = k then r * x.coeff a else 0) = r * (if grade a = k then x.coeff a else 0)
  by_cases hk : grade a = k
  · rw [ite_eq_left hk, ite_eq_left hk]
  · rw [ite_eq_right hk, ite_eq_right hk, Semiring.mul_zero]

/-- A basis blade is homogeneous of its grade. -/
theorem isGrade_blade (a : BitVec n) : IsGrade (grade a) (blade a : Cl g) := by
  intro c h
  show (if c = a then (1 : R) else 0) = 0
  exact ite_eq_right fun e => h (by rw [e])

theorem grade_twoPow (i : Fin n) : grade (BitVec.twoPow n i) = 1 := by
  rw [grade, BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) i.2),
    bitCount_two_pow i.2]

/-- A generator is a vector. -/
theorem isGrade_gen (i : Fin n) : IsGrade 1 (gen i : Cl g) := by
  have := isGrade_blade (g := g) (BitVec.twoPow n i)
  rwa [grade_twoPow] at this

/-- **The exterior product of a `p`-vector and a `q`-vector is a
`(p+q)`-vector.** -/
theorem isGrade_wedge {p q : Nat} {x y : Cl g} (hx : IsGrade p x) (hy : IsGrade q y) :
    IsGrade (p + q) (wedge x y) := by
  intro c hc
  rw [coeff_wedge, bsum_congr (f' := fun _ => (0 : R)) ?_, bsum_const_zero]
  intro a
  by_cases hxa : x.coeff a = 0
  · rw [hxa]; grind
  by_cases hyb : y.coeff (a ^^^ c) = 0
  · rw [hyb]; grind
  have ga : grade a = p := Classical.byContradiction fun h => hxa (hx a h)
  have gb : grade (a ^^^ c) = q := Classical.byContradiction fun h => hyb (hy _ h)
  unfold wcoef
  by_cases hd : a &&& (a ^^^ c) = 0
  · have := grade_xor_of_disjoint hd
    rw [xor_xor_cancel_left] at this
    omega
  · rw [ite_eq_right hd, Semiring.mul_zero]

/-- **Graded commutativity of the exterior product**: for a `p`-vector `x` and
a `q`-vector `y`, `x ∧ y = (-1)^{pq} y ∧ x`. -/
theorem wedge_comm {p q : Nat} {x y : Cl g} (hx : IsGrade p x) (hy : IsGrade q y) :
    wedge x y = (-1 : R) ^ (p * q) • wedge y x := by
  ext c
  show twist wcoef x.coeff y.coeff c = (-1 : R) ^ (p * q) * twist wcoef y.coeff x.coeff c
  rw [twist_eq_sum_right wcoef y.coeff x.coeff c, mul_bsum]
  unfold twist
  refine bsum_congr fun a => ?_
  by_cases hxa : x.coeff a = 0
  · rw [hxa]; grind
  by_cases hyb : y.coeff (a ^^^ c) = 0
  · rw [hyb]; grind
  have ga : grade a = p := Classical.byContradiction fun h => hxa (hx a h)
  have gb : grade (a ^^^ c) = q := Classical.byContradiction fun h => hyb (hy _ h)
  rw [wcoef_swap a (a ^^^ c), ga, gb, neg_one_pow, odd_mul]
  grind

/-- Vectors anticommute under `∧`: `u ∧ v = -(v ∧ u)`. -/
theorem wedge_comm_vec {x y : Cl g} (hx : IsGrade 1 x) (hy : IsGrade 1 y) : wedge x y = -wedge y x := by
  rw [wedge_comm hx hy, neg_eq_smul]
  congr 1
  rw [Nat.one_mul, Semiring.pow_one]

end Cl

end Grassmann.Spec

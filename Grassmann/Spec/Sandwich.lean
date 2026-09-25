/-
Sandwiches `R x R̃` and the small laws that make the specification usable by
`grind`.

* Involutions of `0`, `1`, scalars, generators, negations, differences and
  scalar multiples (`reverse_gen : ~eᵢ = eᵢ`, `involute_gen : êᵢ = -eᵢ`, …);
  the involutions of a homogeneous element (`reverse_of_isGrade`,
  `involute_of_isGrade`) and of a grade projection (`proj_reverse`,
  `proj_involute`).
* Grades are closed under sums, negations, differences and scalar multiples;
  scalars have grade `0`, generators grade `1`.
* Sandwiches: `~(R x R̃) = R x̃ R̃` (`reverse_sandwich`); when `R̃ R = 1`,
  sandwiching is multiplicative (`sandwich_mul`); with `R R̃ = 1` as well it
  is an isometry on vectors, `(R v R̃)² = v²` (`sandwich_sq_of_vector`).
* **Grade preservation** (`proj_sandwich_of_even`): for an even `R` and a
  vector `v`, `R v R̃` has no part of grade `k ≢ 1 (mod 4)`, over any
  commutative ring without 2-torsion. It is self-reverse (so the grades
  `≡ 2, 3 (mod 4)` vanish) and odd (so the even grades vanish). Hence in
  dimension `≤ 4` the sandwich of a vector by an even element is a vector
  (`isGrade_sandwich_of_even`); no normalization `R R̃ = 1` is needed.
-/
import Grassmann.Spec.Contraction

namespace Grassmann.Spec.Cl

open Lean.Grind DirectSum.Proofs

universe u

variable {R : Type u} [CommRing R] {n : Nat} {g : Fin n → R}

/-! ## Involutions of the basic operations -/

theorem reverse_neg (x : Cl g) : reverse (-x) = -reverse x := by
  ext a; show revSign a * -x.coeff a = -(revSign a * x.coeff a); grind

theorem reverse_sub (x y : Cl g) : reverse (x - y) = reverse x - reverse y := by
  ext a; show revSign a * (x.coeff a - y.coeff a) = revSign a * x.coeff a - revSign a * y.coeff a; grind

theorem reverse_smul (r : R) (x : Cl g) : reverse (r • x) = r • reverse x := by
  ext a; show revSign a * (r * x.coeff a) = r * (revSign a * x.coeff a); grind

theorem reverse_zero : reverse (0 : Cl g) = 0 := by
  ext a; show revSign a * 0 = 0; grind

theorem involute_add (x y : Cl g) : involute (x + y) = involute x + involute y := by
  ext a; show invSign a * (x.coeff a + y.coeff a) = invSign a * x.coeff a + invSign a * y.coeff a; grind

theorem involute_neg (x : Cl g) : involute (-x) = -involute x := by
  ext a; show invSign a * -x.coeff a = -(invSign a * x.coeff a); grind

theorem involute_sub (x y : Cl g) : involute (x - y) = involute x - involute y := by
  ext a; show invSign a * (x.coeff a - y.coeff a) = invSign a * x.coeff a - invSign a * y.coeff a; grind

theorem involute_smul (r : R) (x : Cl g) : involute (r • x) = r • involute x := by
  ext a; show invSign a * (r * x.coeff a) = r * (invSign a * x.coeff a); grind

theorem involute_zero : involute (0 : Cl g) = 0 := by
  ext a; show invSign a * 0 = 0; grind

/-- The grade-`k` part of the reverse: `⟨x̃⟩ₖ = (-1)^{k(k-1)/2} ⟨x⟩ₖ`. -/
theorem proj_reverse (k : Nat) (x : Cl g) :
    proj k (reverse x) = (signOf (Leibniz.parityreverse k) : R) • proj k x := by
  ext a
  show (if grade a = k then revSign a * x.coeff a else 0)
    = signOf (Leibniz.parityreverse k) * (if grade a = k then x.coeff a else 0)
  by_cases h : grade a = k
  · rw [ite_eq_left h, ite_eq_left h, revSign, h]
  · rw [ite_eq_right h, ite_eq_right h]; grind

/-- The grade-`k` part of the involute: `⟨x̂⟩ₖ = (-1)^k ⟨x⟩ₖ`. -/
theorem proj_involute (k : Nat) (x : Cl g) :
    proj k (involute x) = (signOf (Leibniz.parityinvolute k) : R) • proj k x := by
  ext a
  show (if grade a = k then invSign a * x.coeff a else 0)
    = signOf (Leibniz.parityinvolute k) * (if grade a = k then x.coeff a else 0)
  by_cases h : grade a = k
  · rw [ite_eq_left h, ite_eq_left h, invSign, h]
  · rw [ite_eq_right h, ite_eq_right h]; grind

/-- A `k`-vector is reversed by the sign `(-1)^{k(k-1)/2}`. -/
theorem reverse_of_isGrade {k : Nat} {x : Cl g} (hx : IsGrade k x) :
    reverse x = (signOf (Leibniz.parityreverse k) : R) • x := by
  ext a
  show revSign a * x.coeff a = signOf (Leibniz.parityreverse k) * x.coeff a
  by_cases h : grade a = k
  · rw [revSign, h]
  · rw [hx a h]; grind

/-- A `k`-vector is involuted by the sign `(-1)^k`. -/
theorem involute_of_isGrade {k : Nat} {x : Cl g} (hx : IsGrade k x) :
    involute x = (signOf (Leibniz.parityinvolute k) : R) • x := by
  ext a
  show invSign a * x.coeff a = signOf (Leibniz.parityinvolute k) * x.coeff a
  by_cases h : grade a = k
  · rw [invSign, h]
  · rw [hx a h]; grind

private theorem one_smul' (x : Cl g) : (1 : R) • x = x := by
  ext a; show 1 * x.coeff a = x.coeff a; grind

private theorem neg_one_smul' (x : Cl g) : (-1 : R) • x = -x := by
  ext a; show -1 * x.coeff a = -x.coeff a; grind

/-- Vectors are self-reverse. -/
theorem reverse_of_vector {v : Cl g} (hv : IsGrade 1 v) : reverse v = v := by
  rw [reverse_of_isGrade hv]; exact one_smul' v

/-- Vectors are odd. -/
theorem involute_of_vector {v : Cl g} (hv : IsGrade 1 v) : involute v = -v := by
  rw [involute_of_isGrade hv]; exact neg_one_smul' v

/-- Scalars are fixed by reversion. -/
theorem reverse_scalar (r : R) : reverse (scalar r : Cl g) = scalar r := by
  ext a
  show revSign a * (if a = 0 then r else 0) = if a = 0 then r else 0
  by_cases h : a = 0
  · subst h; rw [ite_eq_left rfl]; show signOf (Leibniz.parityreverse (grade (0 : BitVec n))) * r = r
    rw [(grade_eq_zero_iff _).mpr rfl]; show 1 * r = r; grind
  · rw [ite_eq_right h]; grind

/-- Scalars are fixed by the grade involution. -/
theorem involute_scalar (r : R) : involute (scalar r : Cl g) = scalar r := by
  ext a
  show invSign a * (if a = 0 then r else 0) = if a = 0 then r else 0
  by_cases h : a = 0
  · subst h; rw [ite_eq_left rfl]; show signOf (Leibniz.parityinvolute (grade (0 : BitVec n))) * r = r
    rw [(grade_eq_zero_iff _).mpr rfl]; show 1 * r = r; grind
  · rw [ite_eq_right h]; grind

theorem reverse_one : reverse (1 : Cl g) = 1 := by
  have := reverse_scalar (g := g) 1
  rwa [scalar_eq_smul_one, one_smul'] at this

theorem involute_one : involute (1 : Cl g) = 1 := by
  have := involute_scalar (g := g) 1
  rwa [scalar_eq_smul_one, one_smul'] at this

/-- Generators are self-reverse. -/
theorem reverse_gen (i : Fin n) : reverse (gen i : Cl g) = gen i := reverse_of_vector (isGrade_gen i)

/-- Generators are odd. -/
theorem involute_gen (i : Fin n) : involute (gen i : Cl g) = -gen i := involute_of_vector (isGrade_gen i)

/-- Clifford conjugation is the involute of the reverse. -/
theorem clifford_eq (x : Cl g) : clifford x = involute (reverse x) := rfl

/-! ## Grades are closed under the linear operations -/

theorem IsGrade.zero (k : Nat) : IsGrade k (0 : Cl g) := fun _ _ => rfl

theorem IsGrade.add {k : Nat} {x y : Cl g} (hx : IsGrade k x) (hy : IsGrade k y) : IsGrade k (x + y) := by
  intro a h; show x.coeff a + y.coeff a = 0; rw [hx a h, hy a h]; grind

theorem IsGrade.neg {k : Nat} {x : Cl g} (hx : IsGrade k x) : IsGrade k (-x) := by
  intro a h; show -x.coeff a = 0; rw [hx a h]; grind

theorem IsGrade.sub {k : Nat} {x y : Cl g} (hx : IsGrade k x) (hy : IsGrade k y) : IsGrade k (x - y) := by
  intro a h; show x.coeff a - y.coeff a = 0; rw [hx a h, hy a h]; grind

theorem IsGrade.smul {k : Nat} (r : R) {x : Cl g} (hx : IsGrade k x) : IsGrade k (r • x) := by
  intro a h; show r * x.coeff a = 0; rw [hx a h]; grind

/-- Scalars have grade `0`. -/
theorem isGrade_scalar (r : R) : IsGrade 0 (scalar r : Cl g) := by
  intro a h
  show (if a = 0 then r else 0) = 0
  exact ite_eq_right fun e => h ((grade_eq_zero_iff a).mpr e)

/-- A multivector is the sum of its grade projections below `k`, … — here only
what the sandwich theorem needs: the coefficient of blade `a` is that of its
grade part. -/
theorem coeff_proj_grade (x : Cl g) (a : BitVec n) : (proj (grade a) x).coeff a = x.coeff a := by
  show (if grade a = grade a then x.coeff a else 0) = x.coeff a
  rw [ite_eq_left rfl]

/-! ## Graded commutativity, sign by sign -/

/-- `x ∧ y = y ∧ x` for a `p`-vector and a `q`-vector with `pq` even. -/
theorem wedge_comm_of_even {p q : Nat} {x y : Cl g} (hx : IsGrade p x) (hy : IsGrade q y)
    (h : p * q % 2 = 0) : wedge x y = wedge y x := by
  rw [wedge_comm hx hy, neg_one_pow]
  have : (p * q % 2 == 1) = false := by simp [h]
  rw [this, signOf_false]; exact one_smul' _

/-- `x ∧ y = -(y ∧ x)` for a `p`-vector and a `q`-vector with `pq` odd. -/
theorem wedge_comm_of_odd {p q : Nat} {x y : Cl g} (hx : IsGrade p x) (hy : IsGrade q y)
    (h : p * q % 2 = 1) : wedge x y = -wedge y x := by
  rw [wedge_comm hx hy, neg_one_pow]
  have : (p * q % 2 == 1) = true := by simp [h]
  rw [this, signOf_true]; exact neg_one_smul' _

/-! ## Sandwiches -/

/-- `~(R x R̃) = R x̃ R̃`. -/
theorem reverse_sandwich (r x : Cl g) : reverse (r * x * reverse r) = r * reverse x * reverse r := by
  rw [reverse_mul, reverse_mul, reverse_reverse, mul_assoc]

/-- The involute of a sandwich. -/
theorem involute_sandwich (r x : Cl g) :
    involute (r * x * reverse r) = involute r * involute x * reverse (involute r) := by
  rw [involute_mul, involute_mul, ← reverse_involute]

/-- With `R̃ R = 1`, sandwiching is multiplicative. -/
theorem sandwich_mul {r : Cl g} (h : reverse r * r = 1) (x y : Cl g) :
    r * x * reverse r * (r * y * reverse r) = r * (x * y) * reverse r := by
  rw [mul_assoc (r * x), ← mul_assoc (reverse r), ← mul_assoc (reverse r), h, one_mul, mul_assoc r x,
    mul_assoc r (x * y), mul_assoc x]

/-- With `R R̃ = 1`, scalars are fixed. -/
theorem sandwich_scalar {r : Cl g} (h : r * reverse r = 1) (c : R) : r * scalar c * reverse r = scalar c := by
  rw [mul_scalar, smul_mul, h, scalar_eq_smul_one]

/-- **Sandwiching by a unit element is an isometry on vectors**: if
`R̃ R = R R̃ = 1` then `(R v R̃)² = v² = B(v, v)`. -/
theorem sandwich_sq_of_vector {r v : Cl g} (hl : reverse r * r = 1) (hr : r * reverse r = 1)
    (hv : IsGrade 1 v) : r * v * reverse r * (r * v * reverse r) = scalar (dot v v) := by
  rw [sandwich_mul hl, mul_self_of_vector hv, sandwich_scalar hr]

private theorem eq_zero_of_eq_neg [NoNatZeroDivisors R] {c : R} (h : c = -c) : c = 0 := by
  grind

private theorem eq_zero_of_smul_eq {k : Nat} {s : Bool} {x : Cl g} [NoNatZeroDivisors R] (hs : s = true)
    (h : proj k x = (signOf s : R) • proj k x) : proj k x = 0 := by
  ext a
  have := congrArg (·.coeff a) h
  simp only [hs, signOf_true, coeff_smul] at this
  rw [coeff_zero]
  exact eq_zero_of_eq_neg (by grind)

/-- A self-reverse element has no part of grade `≡ 2, 3 (mod 4)`. -/
theorem proj_eq_zero_of_reverse_eq [NoNatZeroDivisors R] {x : Cl g} (hx : reverse x = x) {k : Nat}
    (hk : Leibniz.parityreverse k = true) : proj k x = 0 := by
  apply eq_zero_of_smul_eq hk
  conv => lhs; rw [← hx]
  exact proj_reverse k x

/-- An odd element (`x̂ = -x`) has no part of even grade. -/
theorem proj_eq_zero_of_involute_eq_neg [NoNatZeroDivisors R] {x : Cl g} (hx : involute x = -x)
    {k : Nat} (hk : Leibniz.parityinvolute k = false) : proj k x = 0 := by
  have h := proj_involute k x
  rw [hx, hk] at h
  ext a
  have := congrArg (·.coeff a) h
  simp only [signOf_false, coeff_smul] at this
  show (if grade a = k then x.coeff a else 0) = 0
  have e : (proj k (-x)).coeff a = -(proj k x).coeff a := by
    show (if grade a = k then -x.coeff a else 0) = -(if grade a = k then x.coeff a else 0)
    split <;> grind
  rw [e] at this
  exact eq_zero_of_eq_neg (by
    show (proj k x).coeff a = -(proj k x).coeff a
    grind)

/-- **Grade preservation**: the sandwich `R v R̃` of a vector by an even
element (`R̂ = R`) has no part of grade `k ≢ 1 (mod 4)` (over any commutative
ring without 2-torsion; `R R̃ = 1` is not needed). -/
theorem proj_sandwich_of_even [NoNatZeroDivisors R] {r v : Cl g} (hr : involute r = r)
    (hv : IsGrade 1 v) {k : Nat} (hk : k % 4 ≠ 1) : proj k (r * v * reverse r) = 0 := by
  by_cases h2 : k % 4 ≥ 2
  · apply proj_eq_zero_of_reverse_eq _ (by simp [Leibniz.parityreverse, h2])
    rw [reverse_sandwich, reverse_of_vector hv]
  · apply proj_eq_zero_of_involute_eq_neg _ (by simp [Leibniz.parityinvolute]; omega)
    rw [involute_sandwich, hr, involute_of_vector hv, mul_neg, neg_mul]

/-- In dimension `≤ 4`, **the sandwich of a vector by an even element is a
vector**. -/
theorem isGrade_sandwich_of_even [NoNatZeroDivisors R] (hn : n ≤ 4) {r v : Cl g} (hr : involute r = r)
    (hv : IsGrade 1 v) : IsGrade 1 (r * v * reverse r) := by
  intro a ha
  have hle : grade a ≤ n := by
    have := bitCount_le n a.toNat
    unfold grade; omega
  have hk : grade a % 4 ≠ 1 := by omega
  rw [← coeff_proj_grade, proj_sandwich_of_even hr hv hk]
  rfl

end Grassmann.Spec.Cl

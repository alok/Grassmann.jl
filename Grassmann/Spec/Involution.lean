/-
Reversion, grade involution and Clifford conjugation in the specification model.

`reverse` negates the blades of grade `≡ 2, 3 (mod 4)` (Julia `~`,
`Leibniz.parityreverse`), `involute` the odd grades (`Leibniz.parityinvolute`).
The main theorems, for every diagonal metric:

* `reverse_mul`: `~(x y) = ~y ~x` (reversion is an **anti**-automorphism), and
  likewise `reverse_wedge` for `∧`;
* `involute_mul`, `involute_wedge`: the grade involution is an automorphism;
* `clifford_mul`: Clifford conjugation is an anti-automorphism;
* all three are involutions.

The proofs go through two generic statements about twisted convolutions
(`twist_anti`, `twist_hom`): a diagonal sign `s` reverses (resp. preserves) the
product when `s(a⊕b) k(a,b) = s(a) s(b) k(b,a)` (resp. `… k(a,b)`). For the
reversion sign `(-1)^{σ(a,a)}` the first identity is the bilinearity of `σ`:
`σ(a⊕b, a⊕b) = σ(a,a) + σ(a,b) + σ(b,a) + σ(b,b)`.
-/
import Grassmann.Spec.Exterior

namespace Grassmann.Spec

open Lean.Grind DirectSum.Proofs

universe u

variable {R : Type u} [CommRing R] {n : Nat}

/-! ## Diagonal signs and twisted convolutions -/

/-- A diagonal sign `s` that satisfies `s(a⊕b) k(a,b) = s(a) s(b) k(b,a)` turns
the twisted product around: `s·(x ⋆ y) = (s·y) ⋆ (s·x)`. -/
theorem twist_anti {k : BitVec n → BitVec n → R} (s : BitVec n → R)
    (hk : ∀ a b, s (a ^^^ b) * k a b = s a * s b * k b a) (x y : BitVec n → R) :
    (fun c => s c * twist k x y c) = twist k (fun b => s b * y b) (fun a => s a * x a) := by
  funext c
  rw [twist_eq_sum_right, twist, mul_bsum]
  refine bsum_congr fun a => ?_
  obtain ⟨b, rfl⟩ : ∃ b, c = a ^^^ b := ⟨a ^^^ c, (xor_xor_cancel_left a c).symm⟩
  rw [xor_xor_cancel_left]
  have := hk a b
  grind

/-- A diagonal sign `s` with `s(a⊕b) k(a,b) = s(a) s(b) k(a,b)` is multiplicative:
`s·(x ⋆ y) = (s·x) ⋆ (s·y)`. -/
theorem twist_hom {k : BitVec n → BitVec n → R} (s : BitVec n → R)
    (hk : ∀ a b, s (a ^^^ b) * k a b = s a * s b * k a b) (x y : BitVec n → R) :
    (fun c => s c * twist k x y c) = twist k (fun a => s a * x a) (fun b => s b * y b) := by
  funext c
  rw [twist, twist, mul_bsum]
  refine bsum_congr fun a => ?_
  obtain ⟨b, rfl⟩ : ∃ b, c = a ^^^ b := ⟨a ^^^ c, (xor_xor_cancel_left a c).symm⟩
  rw [xor_xor_cancel_left]
  have := hk a b
  grind

/-! ## The reversion and involution signs -/

/-- The reversion sign of a blade, `(-1)^{k(k-1)/2}` for grade `k` (Julia
`parityreverse`). -/
def revSign (a : BitVec n) : R := signOf (Leibniz.parityreverse (grade a))

/-- The grade-involution sign of a blade, `(-1)^k` (Julia `parityinvolute`). -/
def invSign (a : BitVec n) : R := signOf (Leibniz.parityinvolute (grade a))

/-- The reversion sign is `(-1)^{σ(a,a)}`. -/
theorem revSign_eq (a : BitVec n) : (revSign a : R) = signOf (sign a a) := by
  rw [revSign, sign, sigma_self]; rfl

/-- The involution sign is `(-1)^{|a|}`. -/
theorem invSign_eq (a : BitVec n) : (invSign a : R) = signOf (bitParity n a.toNat) := rfl

/-- The reversion identity of the blade signs: `σ(a⊕b, a⊕b) + σ(a,b) ≡ σ(a,a) + σ(b,b) + σ(b,a)`. -/
theorem sign_rev (a b : BitVec n) :
    (sign (a ^^^ b) (a ^^^ b) ^^ sign a b) = ((sign a a ^^ sign b b) ^^ sign b a) := by
  unfold sign
  rw [BitVec.toNat_xor, sigma_xor_left, sigma_xor_right, sigma_xor_right]
  cases sigma n a.toNat a.toNat <;> cases sigma n a.toNat b.toNat <;> cases sigma n b.toNat a.toNat <;>
    cases sigma n b.toNat b.toNat <;> rfl

/-- A twisting function of the form `(-1)^{σ(a,b)} m(a,b)` with `m` symmetric is
reversed by the reversion sign. -/
theorem revSign_twist {k m : BitVec n → BitVec n → R} (hm : ∀ a b, m a b = m b a)
    (hk : ∀ a b, k a b = signOf (sign a b) * m a b) (a b : BitVec n) :
    revSign (a ^^^ b) * k a b = revSign a * revSign b * k b a := by
  rw [revSign_eq, revSign_eq, revSign_eq, hk, hk, hm b a]
  have h := congrArg (signOf (R := R)) (sign_rev a b)
  rw [signOf_xor, signOf_xor, signOf_xor] at h
  grind

/-- Every twisting function is preserved by the grade-involution sign (the grade
parity is additive). -/
theorem invSign_twist (k : BitVec n → BitVec n → R) (a b : BitVec n) :
    invSign (a ^^^ b) * k a b = invSign a * invSign b * k a b := by
  rw [invSign_eq, invSign_eq, invSign_eq, BitVec.toNat_xor, bitParity_xor, signOf_xor]

/-- The geometric-product coefficients are reversed by the reversion sign. -/
theorem coef_revSign (g : Fin n → R) (a b : BitVec n) :
    revSign (a ^^^ b) * coef g a b = revSign a * revSign b * coef g b a :=
  revSign_twist (m := fun a b => mf g (a &&& b)) (fun a b => by rw [BitVec.and_comm]) (coef_eq g) a b

/-- The exterior-product coefficients are reversed by the reversion sign. -/
theorem wcoef_revSign (a b : BitVec n) :
    revSign (a ^^^ b) * (wcoef a b : R) = revSign a * revSign b * wcoef b a :=
  revSign_twist (m := fun a b => if a &&& b = 0 then 1 else 0) (fun a b => by rw [BitVec.and_comm])
    (fun a b => by
      unfold wcoef
      by_cases h : a &&& b = 0
      · rw [ite_eq_left h, ite_eq_left h, Semiring.mul_one]
      · rw [ite_eq_right h, ite_eq_right h, Semiring.mul_zero]) a b

namespace Cl

variable {g : Fin n → R}

/-! ## The involutions -/

/-- **Reversion** `~x` (Julia `reverse`): `~e_a = (-1)^{k(k-1)/2} e_a` for grade `k`. -/
def reverse (x : Cl g) : Cl g := ⟨fun a => revSign a * x.coeff a⟩

/-- **Grade involution** `x̂` (Julia `involute`): `ê_a = (-1)^k e_a` for grade `k`. -/
def involute (x : Cl g) : Cl g := ⟨fun a => invSign a * x.coeff a⟩

/-- **Clifford conjugation** `x̄ = ~x̂` (Julia `clifford`). -/
def clifford (x : Cl g) : Cl g := involute (reverse x)

/-- **Reversion is an anti-automorphism of the geometric product**: `~(x y) = ~y ~x`. -/
theorem reverse_mul (x y : Cl g) : reverse (x * y) = reverse y * reverse x := by
  ext c
  exact congrFun (twist_anti revSign (coef_revSign g) x.coeff y.coeff) c

/-- Reversion is an anti-automorphism of the exterior product. -/
theorem reverse_wedge (x y : Cl g) : reverse (wedge x y) = wedge (reverse y) (reverse x) := by
  ext c
  exact congrFun (twist_anti revSign wcoef_revSign x.coeff y.coeff) c

/-- **The grade involution is an automorphism** of the geometric product. -/
theorem involute_mul (x y : Cl g) : involute (x * y) = involute x * involute y := by
  ext c
  exact congrFun (twist_hom invSign (invSign_twist (coef g)) x.coeff y.coeff) c

/-- The grade involution is an automorphism of the exterior product. -/
theorem involute_wedge (x y : Cl g) : involute (wedge x y) = wedge (involute x) (involute y) := by
  ext c
  exact congrFun (twist_hom invSign (invSign_twist wcoef) x.coeff y.coeff) c

private theorem signOf_mul_self_mul (s : Bool) (r : R) : signOf s * (signOf s * r) = r := by
  have := signOf_mul_self (R := R) s
  grind

/-- Reversion is an involution. -/
theorem reverse_reverse (x : Cl g) : reverse (reverse x) = x := by
  ext a; exact signOf_mul_self_mul _ _

/-- The grade involution is an involution. -/
theorem involute_involute (x : Cl g) : involute (involute x) = x := by
  ext a; exact signOf_mul_self_mul _ _

/-- Reversion and the grade involution commute. -/
theorem reverse_involute (x : Cl g) : reverse (involute x) = involute (reverse x) := by
  ext a
  show revSign a * (invSign a * x.coeff a) = invSign a * (revSign a * x.coeff a)
  grind

/-- Clifford conjugation is an anti-automorphism of the geometric product. -/
theorem clifford_mul (x y : Cl g) : clifford (x * y) = clifford y * clifford x := by
  rw [clifford, reverse_mul, involute_mul]; rfl

/-- Clifford conjugation is an involution. -/
theorem clifford_clifford (x : Cl g) : clifford (clifford x) = x := by
  rw [clifford, clifford, ← reverse_involute, involute_involute, reverse_reverse]

/-- Reversion is additive. -/
theorem reverse_add (x y : Cl g) : reverse (x + y) = reverse x + reverse y := by
  ext a; show revSign a * (x.coeff a + y.coeff a) = revSign a * x.coeff a + revSign a * y.coeff a
  grind

/-- Reversing a basis blade gives Julia's `parityreverse` sign. -/
theorem reverse_blade (a : BitVec n) :
    reverse (blade a : Cl g) = (signOf (Leibniz.parityreverse (grade a)) : R) • blade a := by
  ext c
  show revSign c * (if c = a then 1 else 0) = signOf (Leibniz.parityreverse (grade a)) * (if c = a then 1 else 0)
  by_cases h : c = a
  · subst h; rfl
  · rw [ite_eq_right h, Semiring.mul_zero, Semiring.mul_zero]

/-- The grade involution of a basis blade gives Julia's `parityinvolute` sign. -/
theorem involute_blade (a : BitVec n) :
    involute (blade a : Cl g) = (signOf (Leibniz.parityinvolute (grade a)) : R) • blade a := by
  ext c
  show invSign c * (if c = a then 1 else 0) = signOf (Leibniz.parityinvolute (grade a)) * (if c = a then 1 else 0)
  by_cases h : c = a
  · subst h; rfl
  · rw [ite_eq_right h, Semiring.mul_zero, Semiring.mul_zero]

/-- `e_a ~e_a` is the metric factor of the blade: the squared norm
`Π_{i ∈ a} gᵢ` of a basis blade. -/
theorem blade_mul_reverse (a : BitVec n) : (blade a * reverse (blade a) : Cl g) = scalar (mf g a) := by
  rw [reverse_blade, mul_smul, blade_mul_blade, xor_self', coef_eq, BitVec.and_self]
  have hs : (signOf (Leibniz.parityreverse (grade a)) : R) = signOf (sign a a) := revSign_eq a
  rw [hs, scalar_eq_smul_one]
  ext c
  show signOf (sign a a) * (signOf (sign a a) * mf g a * (if c = 0 then 1 else 0))
    = mf g a * (if c = 0 then 1 else 0)
  have := signOf_mul_self (R := R) (sign a a)
  grind

end Cl

end Grassmann.Spec

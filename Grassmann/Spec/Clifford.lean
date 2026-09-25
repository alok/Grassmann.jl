/-
The specification model: the Clifford algebra `Cl(g)` of a diagonal metric.

`Cl g` is the geometric algebra of the quadratic form `q(x) = Σᵢ gᵢ xᵢ²` on `Rⁿ`
over a commutative ring `R` (`Lean.Grind.CommRing`: `Int`, `Rat`, …), with any
diagonal `g : Fin n → R` (positive, negative or zero entries: Euclidean,
Lorentzian and degenerate/projective algebras alike). An element is a
coefficient function on the `2ⁿ` basis blades, blade `e_A` being the `n`-bit
mask `a` of `A`. The geometric product is the explicit finite sum

  `(x y)(c) = Σ_a x(a) · y(a ⊕ c) · (-1)^{σ(a, a⊕c)} · Π_{i ∈ a ∧ (a⊕c)} gᵢ`

with `σ` the inversion-count sign (`DirectSum.Proofs.sigma`) and the metric
factor over the shared generators (`DirectSum.Proofs.bladeCoef`). Nothing in the
definition mentions associativity; it is a theorem (`mul_assoc`), from the
cocycle identities of `DirectSum.Proofs` through `Grassmann.Spec.twist_assoc`.

This file: the type, its module structure, the product and its ring laws, basis
blades and generators (`gen_mul_self`: `eᵢ² = gᵢ`; `gen_mul_gen_comm`:
`eᵢ eⱼ = -eⱼ eᵢ`). The exterior product, grades, involutions and complements
follow in `Grassmann.Spec.{Exterior, Involution, Hodge}`.
-/
import Grassmann.Spec.Twisted
import DirectSum.Proofs

namespace Grassmann.Spec

open Lean.Grind DirectSum.Proofs

universe u

variable {R : Type u} [CommRing R] {n : Nat}

/-! ## Blade-level data -/

/-- The metric on all generator indices: `g i` below `n`, `1` from `n` on (the
bit-level functions of `DirectSum.Proofs` take metrics on `Nat`). -/
def extendMetric (g : Fin n → R) (i : Nat) : R := if h : i < n then g ⟨i, h⟩ else 1

/-- The reordering sign `σ(a, b)` of two `n`-bit blades. -/
def sign (a b : BitVec n) : Bool := sigma n a.toNat b.toNat

/-- The grade (number of generators) of a blade. -/
def grade (a : BitVec n) : Nat := bitCount n a.toNat

/-- The blade-product coefficient of the diagonal metric `g`:
`e_a e_b = coef g a b · e_{a ⊕ b}`. -/
def coef (g : Fin n → R) (a b : BitVec n) : R := bladeCoef (extendMetric g) n a.toNat b.toNat

/-- The metric factor `Π_{i ∈ a} gᵢ` of a blade (`e_a ẽ_a = mf g a`). -/
def mf (g : Fin n → R) (a : BitVec n) : R := metricFactor (extendMetric g) n a.toNat

theorem coef_eq (g : Fin n → R) (a b : BitVec n) :
    coef g a b = signOf (sign a b) * mf g (a &&& b) := by
  simp [coef, bladeCoef, sign, mf, BitVec.toNat_and]

/-- The blade coefficients of a diagonal metric form a 2-cocycle. -/
theorem coef_cocycle (g : Fin n → R) : IsCocycle (coef g) := by
  intro a b c
  simp only [coef, BitVec.toNat_xor]
  exact bladeCoef_cocycle _ _ _ _ _

theorem coef_zero_left (g : Fin n → R) (b : BitVec n) : coef g 0 b = 1 := by
  simp [coef, bladeCoef_zero_left]

theorem coef_zero_right (g : Fin n → R) (a : BitVec n) : coef g a 0 = 1 := by
  simp [coef, bladeCoef_zero_right]

/-! ## The algebra -/

/-- A multivector of the Clifford algebra `Cl(g)` of the diagonal metric
`g : Fin n → R`: one coefficient per basis blade. -/
@[ext] structure Cl {R : Type u} {n : Nat} (g : Fin n → R) : Type u where
  /-- The coefficient of the basis blade with mask `a`. -/
  coeff : BitVec n → R

namespace Cl

variable {g : Fin n → R}

instance : Zero (Cl g) := ⟨⟨fun _ => 0⟩⟩
instance : Add (Cl g) := ⟨fun x y => ⟨fun a => x.coeff a + y.coeff a⟩⟩
instance : Neg (Cl g) := ⟨fun x => ⟨fun a => -x.coeff a⟩⟩
instance : Sub (Cl g) := ⟨fun x y => ⟨fun a => x.coeff a - y.coeff a⟩⟩
instance : SMul R (Cl g) := ⟨fun r x => ⟨fun a => r * x.coeff a⟩⟩

/-- The basis blade `e_a`. -/
def blade (a : BitVec n) : Cl g := ⟨delta a⟩

/-- The scalar `r` (the multiple `r e_∅` of the unit blade). -/
def scalar (r : R) : Cl g := ⟨fun a => if a = 0 then r else 0⟩

/-- The generator `eᵢ₊₁` (0-based index `i`). -/
def gen (i : Fin n) : Cl g := blade (BitVec.twoPow n i)

/-- The pseudoscalar `e₁ e₂ ⋯ eₙ`. -/
def pseudoscalar : Cl g := blade (BitVec.allOnes n)

instance : One (Cl g) := ⟨blade 0⟩

/-- **The geometric product**, as an explicit finite sum over blade pairs. -/
instance : Mul (Cl g) := ⟨fun x y => ⟨twist (coef g) x.coeff y.coeff⟩⟩

@[simp] theorem coeff_zero (a : BitVec n) : (0 : Cl g).coeff a = 0 := rfl
@[simp] theorem coeff_add (x y : Cl g) (a : BitVec n) : (x + y).coeff a = x.coeff a + y.coeff a := rfl
@[simp] theorem coeff_neg (x : Cl g) (a : BitVec n) : (-x).coeff a = -x.coeff a := rfl
@[simp] theorem coeff_sub (x y : Cl g) (a : BitVec n) : (x - y).coeff a = x.coeff a - y.coeff a := rfl
@[simp] theorem coeff_smul (r : R) (x : Cl g) (a : BitVec n) : (r • x).coeff a = r * x.coeff a := rfl
@[simp] theorem coeff_blade (a c : BitVec n) : (blade a : Cl g).coeff c = if c = a then 1 else 0 := rfl
@[simp] theorem coeff_scalar (r : R) (c : BitVec n) :
    (scalar r : Cl g).coeff c = if c = 0 then r else 0 := rfl
@[simp] theorem coeff_one (c : BitVec n) : (1 : Cl g).coeff c = if c = 0 then 1 else 0 := rfl

/-- The coefficients of a geometric product. -/
theorem coeff_mul (x y : Cl g) (c : BitVec n) :
    (x * y).coeff c = bsum n fun a => x.coeff a * y.coeff (a ^^^ c) * coef g a (a ^^^ c) := rfl

/-! ### Ring laws -/

/-- **Associativity of the geometric product**, for every diagonal metric over
every commutative ring, in every dimension. -/
theorem mul_assoc (x y z : Cl g) : x * y * z = x * (y * z) := by
  ext c
  exact congrFun (twist_assoc (coef_cocycle g) x.coeff y.coeff z.coeff) c

/-- `1` is a left unit. -/
theorem one_mul (x : Cl g) : 1 * x = x := by
  ext c
  exact congrFun (twist_delta_zero_left (coef_zero_left g) x.coeff) c

/-- `1` is a right unit. -/
theorem mul_one (x : Cl g) : x * 1 = x := by
  ext c
  exact congrFun (twist_delta_zero_right (coef_zero_right g) x.coeff) c

/-- Left distributivity. -/
theorem mul_add (x y z : Cl g) : x * (y + z) = x * y + x * z := by
  ext c
  exact congrFun (twist_add_right (coef g) x.coeff y.coeff z.coeff) c

/-- Right distributivity. -/
theorem add_mul (x y z : Cl g) : (x + y) * z = x * z + y * z := by
  ext c
  exact congrFun (twist_add_left (coef g) x.coeff y.coeff z.coeff) c

/-- Scalars pull out of the left factor. -/
theorem smul_mul (r : R) (x y : Cl g) : (r • x) * y = r • (x * y) := by
  ext c
  exact congrFun (twist_smul_left (coef g) r x.coeff y.coeff) c

/-- Scalars pull out of the right factor. -/
theorem mul_smul (r : R) (x y : Cl g) : x * (r • y) = r • (x * y) := by
  ext c
  exact congrFun (twist_smul_right (coef g) r x.coeff y.coeff) c

/-- `-x = (-1) • x`. -/
theorem neg_eq_smul (x : Cl g) : -x = (-1 : R) • x := by
  ext a
  show -x.coeff a = -1 * x.coeff a
  grind

/-- Negation pulls out of the left factor. -/
theorem neg_mul (x y : Cl g) : -x * y = -(x * y) := by
  rw [neg_eq_smul, smul_mul, ← neg_eq_smul]

/-- Negation pulls out of the right factor. -/
theorem mul_neg (x y : Cl g) : x * -y = -(x * y) := by
  rw [neg_eq_smul, mul_smul, ← neg_eq_smul]

/-- `0` is absorbing on the left. -/
theorem zero_mul (x : Cl g) : 0 * x = 0 := by
  ext c
  rw [coeff_mul, coeff_zero]
  rw [bsum_congr (f' := fun _ => (0 : R)) fun a => by
    show (0 : R) * x.coeff (a ^^^ c) * coef g a (a ^^^ c) = 0; grind, bsum_const_zero]

/-- `0` is absorbing on the right. -/
theorem mul_zero (x : Cl g) : x * 0 = 0 := by
  ext c
  rw [coeff_mul, coeff_zero]
  rw [bsum_congr (f' := fun _ => (0 : R)) fun a => by
    show x.coeff a * (0 : R) * coef g a (a ^^^ c) = 0; grind, bsum_const_zero]

/-- A scalar is that multiple of `1`. -/
theorem scalar_eq_smul_one (r : R) : (scalar r : Cl g) = r • (1 : Cl g) := by
  ext a
  show (if a = 0 then r else 0) = r * (if a = 0 then 1 else 0)
  by_cases h : a = 0
  · rw [ite_eq_left h, ite_eq_left h, Semiring.mul_one]
  · rw [ite_eq_right h, ite_eq_right h, Semiring.mul_zero]

/-- A scalar multiplies like a scalar: `r x = r • x`. -/
theorem scalar_mul (r : R) (x : Cl g) : scalar r * x = r • x := by
  rw [scalar_eq_smul_one, smul_mul, one_mul]

/-- `x r = r • x`: scalars are central. -/
theorem mul_scalar (r : R) (x : Cl g) : x * scalar r = r • x := by
  rw [scalar_eq_smul_one, mul_smul, mul_one]

/-! ### Basis blades -/

/-- **Blades multiply by the sign-and-metric table**:
`e_a e_b = (-1)^{σ(a,b)} Π_{i ∈ a∧b} gᵢ · e_{a⊕b}`. This is the table every
kernel of the implementation encodes (`Grassmann.Proofs`). -/
theorem blade_mul_blade (a b : BitVec n) : (blade a * blade b : Cl g) = coef g a b • blade (a ^^^ b) := by
  ext c
  exact congrFun (twist_delta_delta (coef g) a b) c

/-- The coefficient of `e_a e_b` at its (unique) blade `a ⊕ b`. -/
theorem blade_mul_blade_coeff (a b : BitVec n) :
    (blade a * blade b : Cl g).coeff (a ^^^ b) = coef g a b := by
  rw [blade_mul_blade]; simp [Semiring.mul_one]

private theorem toNat_twoPow {i : Nat} (hi : i < n) : (BitVec.twoPow n i).toNat = 2 ^ i := by
  rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hi)]

theorem sign_gen_gen (i : Fin n) : sign (BitVec.twoPow n i) (BitVec.twoPow n i) = false := by
  rw [sign, toNat_twoPow i.2, sigma_self, bitCount_two_pow i.2]; rfl

/-- **The Clifford relation of a generator**: `eᵢ² = gᵢ`. -/
theorem gen_mul_self (i : Fin n) : (gen i * gen i : Cl g) = scalar (g i) := by
  unfold gen
  rw [blade_mul_blade, xor_self', coef_eq, sign_gen_gen, BitVec.and_self, mf, toNat_twoPow i.2,
    metricFactor_two_pow _ i.2]
  have hg : extendMetric g i.1 = g i := by simp [extendMetric, i.2]
  rw [hg, signOf_false, Semiring.one_mul, scalar_eq_smul_one]
  rfl

/-- **Distinct generators anticommute**: `eᵢ eⱼ = -eⱼ eᵢ` for `i ≠ j`. -/
theorem gen_mul_gen_comm {i j : Fin n} (hij : i ≠ j) : (gen i * gen j : Cl g) = -(gen j * gen i) := by
  unfold gen
  rw [blade_mul_blade, blade_mul_blade, BitVec.xor_comm (BitVec.twoPow n j)]
  have hne : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
  have hdis : ∀ k l : Fin n, k.1 ≠ l.1 → (BitVec.twoPow n k &&& BitVec.twoPow n l) = 0 := by
    intro k l hkl
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, toNat_twoPow k.2, toNat_twoPow l.2]
    apply Nat.eq_of_testBit_eq; intro m
    simp [Nat.testBit_two_pow]; omega
  have hswap := sigma_swap n (2 ^ i.1) (2 ^ j.1)
  have hand : (2 ^ i.1 &&& 2 ^ j.1 : Nat) = 0 := by
    apply Nat.eq_of_testBit_eq; intro m; simp [Nat.testBit_two_pow]; omega
  rw [bitParity, bitParity, bitParity, bitCount_two_pow i.2, bitCount_two_pow j.2, hand,
    bitCount_zero_mask] at hswap
  rw [coef_eq, coef_eq, hdis i j hne, hdis j i (Ne.symm hne), sign, sign, toNat_twoPow i.2,
    toNat_twoPow j.2]
  have hs : sigma n (2 ^ i.1) (2 ^ j.1) = !sigma n (2 ^ j.1) (2 ^ i.1) := by
    revert hswap; cases sigma n (2 ^ i.1) (2 ^ j.1) <;> cases sigma n (2 ^ j.1) (2 ^ i.1) <;> decide
  rw [hs, signOf_not]
  ext c
  simp only [coeff_smul, coeff_neg]
  grind

end Cl

end Grassmann.Spec

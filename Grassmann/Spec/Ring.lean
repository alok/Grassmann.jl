/-
`Cl g` is a ring: `Lean.Grind.Ring (Cl g)`.

With this instance `grind` normalizes multivector expressions as polynomials
in non-commuting variables (its non-commutative ring normalizer): it
reassociates products, distributes, collects integer multiples and powers,
e.g. `x * (y * z) * w = x * y * (z * w)` or
`(x + y) * (x + y) = x * x + x * y + y * x + y * y` by plain `grind`. The
Clifford-algebra facts themselves (generators anticommute, vectors square to
scalars, reversion reverses products, …) come from the `grassmann` lemma set
(`Grassmann.Spec.Grind`).

Numerals: `0`, `1` and every `k` are `Cl.instOfNat` (`Grassmann.Spec.Clifford`),
which is also the ring's `ofNat`, so the goal's numerals and `grind`'s agree;
`k ≥ 2` is the scalar `k`. Integer casts and integer/natural multiples are the
matching scalars; they are not global instances (as for every
`Lean.Grind.Ring`), so they do not clash with the `R`-module action `r • x`.
-/
import Grassmann.Spec.Clifford

namespace Grassmann.Spec.Cl

open Lean.Grind

universe u

variable {R : Type u} [CommRing R] {n : Nat} {g : Fin n → R}

/-- Integer casts: `k ↦ k`, `-(k+1) ↦ -(k+1)`. -/
@[reducible] def intCastCl : Int → Cl g
  | .ofNat k => ofNatCl k
  | .negSucc k => -ofNatCl (k + 1)

/-- Powers by repeated multiplication on the right. -/
def npowCl (x : Cl g) : Nat → Cl g
  | 0 => 1
  | k + 1 => npowCl x k * x

/-- Addition is commutative. -/
theorem add_comm (x y : Cl g) : x + y = y + x := by
  ext a; simp only [coeff_add]; grind

/-- Addition is associative. -/
theorem add_assoc (x y z : Cl g) : x + y + z = x + (y + z) := by
  ext a; simp only [coeff_add]; grind

/-- `0` is an additive unit. -/
theorem add_zero (x : Cl g) : x + 0 = x := by
  ext a; simp only [coeff_add, coeff_zero]; grind

/-- `-x` is an additive inverse. -/
theorem neg_add_cancel (x : Cl g) : -x + x = 0 := by
  ext a; simp only [coeff_add, coeff_neg, coeff_zero]; grind

/-- Subtraction is addition of the negative. -/
theorem sub_eq_add_neg (x y : Cl g) : x - y = x + -y := by
  ext a; simp only [coeff_add, coeff_neg, coeff_sub]; grind

private theorem ofNatCl_succ (k : Nat) : (ofNatCl (k + 1) : Cl g) = ofNatCl k + 1 := by
  match k with
  | 0 => show (1 : Cl g) = 0 + 1; rw [add_comm, add_zero]
  | 1 =>
    ext a
    show (if a = 0 then (OfNat.ofNat 2 : R) else 0) = (if a = 0 then 1 else 0) + (if a = 0 then 1 else 0)
    split <;> grind
  | k + 2 =>
    ext a
    show (if a = 0 then (OfNat.ofNat (k + 3) : R) else 0)
      = (if a = 0 then (OfNat.ofNat (k + 2) : R) else 0) + (if a = 0 then 1 else 0)
    split
    · rw [Semiring.ofNat_succ]
    · grind

private theorem intCastCl_neg (i : Int) : (intCastCl (-i) : Cl g) = -intCastCl i := by
  match i with
  | .ofNat 0 => ext a; show (0 : R) = -0; grind
  | .ofNat (k + 1) => rfl
  | .negSucc k =>
    ext a
    show (ofNatCl (k + 1) : Cl g).coeff a = -(-(ofNatCl (k + 1) : Cl g).coeff a)
    grind

/-- **The Clifford algebra is a ring** (non-commutative), for `grind`. -/
instance instRing : Lean.Grind.Ring (Cl g) where
  natCast := ⟨ofNatCl⟩
  ofNat := instOfNat
  nsmul := ⟨fun k x => ofNatCl k * x⟩
  npow := ⟨npowCl⟩
  intCast := ⟨intCastCl⟩
  zsmul := ⟨fun i x => intCastCl i * x⟩
  add_zero := add_zero
  add_comm := add_comm
  add_assoc := add_assoc
  mul_assoc := mul_assoc
  mul_one := mul_one
  one_mul := one_mul
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ := ofNatCl_succ
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg := sub_eq_add_neg
  neg_zsmul i x := by
    show intCastCl (-i) * x = -(intCastCl i * x)
    rw [intCastCl_neg, neg_mul]
  intCast_neg := intCastCl_neg

/-- Powers are iterated products. -/
theorem pow_succ (x : Cl g) (k : Nat) : x ^ (k + 1) = x ^ k * x := rfl

/-- The numeral `k + 2` is the scalar `k + 2`. -/
theorem ofNat_eq_scalar (k : Nat) :
    (OfNat.ofNat (k + 2) : Cl g) = scalar (OfNat.ofNat (k + 2)) := rfl

end Grassmann.Spec.Cl

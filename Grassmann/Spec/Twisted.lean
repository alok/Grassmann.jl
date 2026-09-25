/-
Twisted group algebras of `(ℤ/2)ⁿ`: the algebraic skeleton of the geometric product.

A multivector is a coefficient function on the `2ⁿ` basis blades, and blades
multiply by `e_a e_b = k(a, b) e_{a ⊕ b}` for a *twisting* function `k`. The
bilinear extension is the twisted convolution

  `(x ⋆ y)(c) = Σ_a x(a) · y(a ⊕ c) · k(a, a ⊕ c)`   (`twist`).

`twist_assoc` is the general fact behind every associativity statement of the
specification: **the convolution is associative as soon as `k` is a 2-cocycle**,
`k(a,b)·k(a⊕b,c) = k(b,c)·k(a,b⊕c)`. The Clifford algebra of a diagonal metric
(`DirectSum.Proofs.bladeCoef_cocycle`) and the exterior algebra (the zero metric)
are the two instances used here. The proof is four lines of algebra: expand,
swap the sums, re-index by xor, and apply the cocycle identity term by term.
-/
import Grassmann.Spec.Sum

namespace Grassmann.Spec

open Lean.Grind

universe u

variable {R : Type u} [CommRing R] {n : Nat}

/-- The 2-cocycle identity of a twisting function `k : (ℤ/2)ⁿ × (ℤ/2)ⁿ → R`. -/
def IsCocycle (k : BitVec n → BitVec n → R) : Prop :=
  ∀ a b c, k a b * k (a ^^^ b) c = k b c * k a (b ^^^ c)

/-- The twisted convolution `(x ⋆ y)(c) = Σ_a x(a) y(a ⊕ c) k(a, a ⊕ c)`: the
bilinear extension of `e_a ⋆ e_b = k(a,b) e_{a⊕b}`. -/
def twist (k : BitVec n → BitVec n → R) (x y : BitVec n → R) : BitVec n → R :=
  fun c => bsum n fun a => x a * y (a ^^^ c) * k a (a ^^^ c)

/-- The coefficient function of the basis blade `e_a`. -/
def delta (a : BitVec n) : BitVec n → R := fun c => if c = a then 1 else 0

/-- `0 ^^^ x = x`, stated with the numeral `0` (`BitVec.zero_xor` uses `0#n`). -/
theorem zero_xor' (x : BitVec n) : (0 : BitVec n) ^^^ x = x := BitVec.zero_xor

/-- `x ^^^ 0 = x`, stated with the numeral `0`. -/
theorem xor_zero' (x : BitVec n) : x ^^^ (0 : BitVec n) = x := BitVec.xor_zero

/-- `x ^^^ x = 0`, stated with the numeral `0`. -/
theorem xor_self' (x : BitVec n) : x ^^^ x = (0 : BitVec n) := BitVec.xor_self

/-- `a ^^^ c = 0` exactly when `a = c`. -/
theorem xor_eq_zero_iff (a c : BitVec n) : a ^^^ c = 0 ↔ a = c := by
  constructor
  · intro h
    have : a ^^^ c ^^^ c = 0 ^^^ c := congrArg (· ^^^ c) h
    rwa [BitVec.xor_assoc, xor_self', xor_zero', zero_xor'] at this
  · rintro rfl; exact xor_self' a

theorem xor_xor_cancel_left (a x : BitVec n) : a ^^^ (a ^^^ x) = x := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem xor_xor_cancel_right (a x : BitVec n) : x ^^^ a ^^^ a = x := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The convolution summed the other way: over the right factor's blade. -/
theorem twist_eq_sum_right (k : BitVec n → BitVec n → R) (x y : BitVec n → R) (c : BitVec n) :
    twist k x y c = bsum n fun b => x (b ^^^ c) * y b * k (b ^^^ c) b := by
  unfold twist
  rw [← bsum_xor c]
  refine bsum_congr fun a => ?_
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- **Associativity of twisted convolution for any 2-cocycle.** -/
theorem twist_assoc {k : BitVec n → BitVec n → R} (hk : IsCocycle k) (x y z : BitVec n → R) :
    twist k (twist k x y) z = twist k x (twist k y z) := by
  funext c
  simp only [twist, bsum_mul, mul_bsum]
  rw [bsum_comm]
  refine bsum_congr fun a => ?_
  rw [← bsum_xor a]
  refine bsum_congr fun b => ?_
  obtain ⟨d, rfl⟩ : ∃ d, c = a ^^^ (b ^^^ d) := ⟨b ^^^ (a ^^^ c), by
    rw [xor_xor_cancel_left, xor_xor_cancel_left]⟩
  have h₁ : a ^^^ (b ^^^ a) = b := by rw [BitVec.xor_comm b, xor_xor_cancel_left]
  have h₂ : b ^^^ a ^^^ (a ^^^ (b ^^^ d)) = d := by
    rw [BitVec.xor_assoc, xor_xor_cancel_left, xor_xor_cancel_left]
  have h₃ : b ^^^ (a ^^^ (a ^^^ (b ^^^ d))) = d := by rw [xor_xor_cancel_left, xor_xor_cancel_left]
  have h₄ : a ^^^ (a ^^^ (b ^^^ d)) = b ^^^ d := xor_xor_cancel_left _ _
  rw [h₁, h₂, h₃, h₄, BitVec.xor_comm b a]
  have := hk a b d
  grind

/-- Blades multiply by the twisting function: `e_a ⋆ e_b = k(a,b) e_{a⊕b}`. -/
theorem twist_delta_delta (k : BitVec n → BitVec n → R) (a b : BitVec n) :
    twist k (delta a) (delta b) = fun c => k a b * delta (a ^^^ b) c := by
  funext c
  unfold twist delta
  have : ∀ x : BitVec n, (if x = a then (1 : R) else 0) * (if x ^^^ c = b then 1 else 0) * k x (x ^^^ c)
      = if x = a then (if a ^^^ c = b then 1 else 0) * k a (a ^^^ c) else 0 := by
    intro x
    by_cases h : x = a
    · subst h; simp [Semiring.one_mul]
    · simp [h, Semiring.zero_mul]
  rw [bsum_congr this, bsum_ite_eq]
  by_cases h : a ^^^ c = b
  · have hc : c = a ^^^ b := by rw [← h, xor_xor_cancel_left]
    subst hc
    simp [xor_xor_cancel_left, Semiring.one_mul, Semiring.mul_one]
  · have hc : ¬ c = a ^^^ b := fun e => h (by rw [e, xor_xor_cancel_left])
    simp [h, hc, Semiring.zero_mul, Semiring.mul_zero]

/-- A left unit: `e_0 ⋆ y = y` when `k(0, b) = 1`. -/
theorem twist_delta_zero_left {k : BitVec n → BitVec n → R} (hk : ∀ b, k 0 b = 1) (y : BitVec n → R) :
    twist k (delta 0) y = y := by
  funext c
  unfold twist delta
  have : ∀ a : BitVec n, (if a = 0 then (1 : R) else 0) * y (a ^^^ c) * k a (a ^^^ c)
      = if a = 0 then y c else 0 := by
    intro a
    by_cases h : a = 0
    · subst h; rw [ite_eq_left rfl, ite_eq_left rfl, zero_xor', hk, Semiring.one_mul, Semiring.mul_one]
    · rw [ite_eq_right h, ite_eq_right h, Semiring.zero_mul, Semiring.zero_mul]
  rw [bsum_congr this, bsum_ite_eq]

/-- A right unit: `x ⋆ e_0 = x` when `k(a, 0) = 1`. -/
theorem twist_delta_zero_right {k : BitVec n → BitVec n → R} (hk : ∀ a, k a 0 = 1) (x : BitVec n → R) :
    twist k x (delta 0) = x := by
  funext c
  unfold twist delta
  have : ∀ a : BitVec n, x a * (if a ^^^ c = 0 then (1 : R) else 0) * k a (a ^^^ c)
      = if a = c then x c else 0 := by
    intro a
    by_cases h : a = c
    · subst h; rw [xor_self', ite_eq_left rfl, ite_eq_left rfl, hk, Semiring.mul_one, Semiring.mul_one]
    · have h' : ¬ a ^^^ c = 0 := fun e => h ((xor_eq_zero_iff a c).mp e)
      rw [ite_eq_right h, ite_eq_right h', Semiring.mul_zero, Semiring.zero_mul]
  rw [bsum_congr this, bsum_ite_eq]

/-- The convolution is additive in the left factor. -/
theorem twist_add_left (k : BitVec n → BitVec n → R) (x x' y : BitVec n → R) :
    twist k (fun a => x a + x' a) y = fun c => twist k x y c + twist k x' y c := by
  funext c
  unfold twist
  rw [← bsum_add]
  exact bsum_congr fun a => by grind

/-- The convolution is additive in the right factor. -/
theorem twist_add_right (k : BitVec n → BitVec n → R) (x y y' : BitVec n → R) :
    twist k x (fun a => y a + y' a) = fun c => twist k x y c + twist k x y' c := by
  funext c
  unfold twist
  rw [← bsum_add]
  exact bsum_congr fun a => by grind

/-- Scalars pull out of the left factor. -/
theorem twist_smul_left (k : BitVec n → BitVec n → R) (r : R) (x y : BitVec n → R) :
    twist k (fun a => r * x a) y = fun c => r * twist k x y c := by
  funext c
  unfold twist
  rw [mul_bsum]
  exact bsum_congr fun a => by grind

/-- Scalars pull out of the right factor. -/
theorem twist_smul_right (k : BitVec n → BitVec n → R) (r : R) (x y : BitVec n → R) :
    twist k x (fun a => r * y a) = fun c => r * twist k x y c := by
  funext c
  unfold twist
  rw [mul_bsum]
  exact bsum_congr fun a => by grind

end Grassmann.Spec

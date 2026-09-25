/-
Finite sums over the `2ⁿ` basis blades.

`bsum n f = Σ_{a : BitVec n} f a`, by recursion on the top generator
(`BitVec.cons`). This is all the summation theory the specification needs:
linearity, Fubini (`bsum_comm`), the Kronecker delta (`bsum_ite_eq`) and,
crucially, invariance under translation by xor (`bsum_xor`): the blades form
the group `(ℤ/2)ⁿ` and the geometric product is a twisted convolution over it.
-/

namespace Grassmann.Spec

open Lean.Grind

universe u

variable {R : Type u} [CommRing R]

/-- `bsum n f = Σ_{a : BitVec n} f a`, summing the top bit first. -/
def bsum : (n : Nat) → (BitVec n → R) → R
  | 0, f => f 0#0
  | n + 1, f => bsum n (fun x => f (BitVec.cons false x)) + bsum n (fun x => f (BitVec.cons true x))

@[simp] theorem bsum_zero_dim (f : BitVec 0 → R) : bsum 0 f = f 0#0 := rfl

theorem bsum_succ (n : Nat) (f : BitVec (n + 1) → R) :
    bsum (n + 1) f = bsum n (fun x => f (BitVec.cons false x)) + bsum n (fun x => f (BitVec.cons true x)) :=
  rfl

/-- Pointwise equal summands have equal sums. -/
theorem bsum_congr {n : Nat} {f f' : BitVec n → R} (h : ∀ a, f a = f' a) : bsum n f = bsum n f' := by
  rw [funext h]

/-- The sum of zeros. -/
@[simp] theorem bsum_const_zero (n : Nat) : bsum n (fun _ => (0 : R)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bsum_succ, ih, Semiring.add_zero]

/-- Sums are additive. -/
theorem bsum_add (n : Nat) (f f' : BitVec n → R) :
    bsum n (fun a => f a + f' a) = bsum n f + bsum n f' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bsum_succ, bsum_succ, bsum_succ, ih, ih]
    grind

/-- Sums commute with negation. -/
theorem bsum_neg (n : Nat) (f : BitVec n → R) : bsum n (fun a => -f a) = -bsum n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bsum_succ, bsum_succ, ih, ih]
    grind

/-- Sums commute with subtraction. -/
theorem bsum_sub (n : Nat) (f f' : BitVec n → R) :
    bsum n (fun a => f a - f' a) = bsum n f - bsum n f' := by
  have : ∀ a, f a - f' a = f a + -f' a := fun a => Ring.sub_eq_add_neg _ _
  rw [bsum_congr this, bsum_add, bsum_neg, Ring.sub_eq_add_neg]

/-- Left multiplication distributes over sums. -/
theorem mul_bsum (n : Nat) (r : R) (f : BitVec n → R) : r * bsum n f = bsum n (fun a => r * f a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bsum_succ, bsum_succ, ← ih, ← ih, Semiring.left_distrib]

/-- Right multiplication distributes over sums. -/
theorem bsum_mul (n : Nat) (f : BitVec n → R) (r : R) : bsum n f * r = bsum n (fun a => f a * r) := by
  rw [CommSemiring.mul_comm, mul_bsum]
  exact bsum_congr fun a => CommSemiring.mul_comm _ _

/-- **Fubini**: the order of a double sum does not matter. -/
theorem bsum_comm (n m : Nat) (f : BitVec n → BitVec m → R) :
    bsum n (fun a => bsum m (fun b => f a b)) = bsum m (fun b => bsum n (fun a => f a b)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bsum_succ, ih, ih, ← bsum_add]
    rfl

private theorem cons_eq_cons {n : Nat} {b b' : Bool} {x x' : BitVec n} :
    BitVec.cons b x = BitVec.cons b' x' ↔ b = b' ∧ x = x' := by
  constructor
  · intro h
    have h₁ := congrArg BitVec.msb h
    have h₂ := congrArg (BitVec.setWidth n) h
    simp only [BitVec.msb_cons, BitVec.setWidth_cons] at h₁ h₂
    exact ⟨h₁, h₂⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- **The Kronecker delta**: summing `f` against `[a = a₀]` picks out `f a₀`. -/
theorem bsum_ite_eq {n : Nat} (a₀ : BitVec n) (f : BitVec n → R) :
    bsum n (fun a => if a = a₀ then f a else 0) = f a₀ := by
  induction n with
  | zero =>
    have : a₀ = 0#0 := BitVec.eq_of_toNat_eq (by have := a₀.isLt; simp at this; simp [this])
    subst this; simp
  | succ n ih =>
    obtain ⟨b, x₀, rfl⟩ : ∃ b x₀, a₀ = BitVec.cons b x₀ :=
      ⟨a₀.msb, a₀.setWidth n, (BitVec.cons_msb_setWidth a₀).symm⟩
    rw [bsum_succ]
    simp only [cons_eq_cons]
    cases b
    · simp only [true_and, Bool.true_eq_false, false_and, ite_false]
      rw [ih x₀ (fun x => f (BitVec.cons false x)), bsum_const_zero, Semiring.add_zero]
    · simp only [true_and, Bool.false_eq_true, false_and, ite_false]
      rw [ih x₀ (fun x => f (BitVec.cons true x)), bsum_const_zero, Semiring.add_comm, Semiring.add_zero]

/-- The Kronecker delta, with the equation the other way round. -/
theorem bsum_ite_eq' {n : Nat} (a₀ : BitVec n) (f : BitVec n → R) :
    bsum n (fun a => if a₀ = a then f a else 0) = f a₀ := by
  rw [← bsum_ite_eq a₀ f]
  refine bsum_congr fun a => ?_
  by_cases h : a = a₀
  · subst h; simp
  · have h' : ¬ a₀ = a := fun e => h e.symm
    simp [h, h']

/-- **Translation invariance**: re-indexing a sum by `a ↦ a ^^^ t` (a bijection of
`BitVec n`, the group law of `(ℤ/2)ⁿ`) does not change it. -/
theorem bsum_xor {n : Nat} (t : BitVec n) (f : BitVec n → R) :
    bsum n (fun a => f (a ^^^ t)) = bsum n f := by
  induction n with
  | zero =>
    have : t = 0#0 := BitVec.eq_of_toNat_eq (by have := t.isLt; simp at this; simp [this])
    subst this; simp
  | succ n ih =>
    obtain ⟨b, t₀, rfl⟩ : ∃ b t₀, t = BitVec.cons b t₀ :=
      ⟨t.msb, t.setWidth n, (BitVec.cons_msb_setWidth t).symm⟩
    rw [bsum_succ, bsum_succ]
    simp only [BitVec.cons_xor_cons]
    rw [ih t₀ (fun y => f (BitVec.cons (false ^^ b) y)), ih t₀ (fun y => f (BitVec.cons (true ^^ b) y))]
    cases b
    · rfl
    · exact Semiring.add_comm _ _

end Grassmann.Spec

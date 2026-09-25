/-
Vectors: the Clifford relation and the split of the vector product.

For vectors (`IsGrade 1`) `u`, `v` of `Cl(g)`, with the bilinear form
`B(u, v) = Σᵢ gᵢ uᵢ vᵢ` (`dot`):

* `mul_self_of_vector`: **`v² = B(v, v)`**, the defining relation of the
  Clifford algebra of the quadratic form `q(v) = Σ gᵢ vᵢ²`;
* `mul_eq_dot_add_wedge`: `u v = B(u, v) + u ∧ v`;
* `mul_add_mul_swap`: `u v + v u = 2 B(u, v)`;
* `wedge_self_of_vector`: `v ∧ v = 0`.

These hold over **every** commutative ring, including characteristic 2, where
"`x = -x` hence `x = 0`" is not available: the off-diagonal terms of `v²` cancel
in pairs (`bsum_eq_zero_of_antisymm`: a sum whose summand changes sign under a
fixed-point-free xor translation vanishes).
-/
import Grassmann.Spec.Exterior

namespace Grassmann.Spec

open Lean.Grind DirectSum.Proofs

universe u

variable {R : Type u} [CommRing R] {n : Nat}

private theorem cons_eq_cons' {b b' : Bool} {x x' : BitVec n} :
    BitVec.cons b x = BitVec.cons b' x' ↔ b = b' ∧ x = x' := by
  constructor
  · intro h
    have h₁ := congrArg BitVec.msb h
    have h₂ := congrArg (BitVec.setWidth n) h
    simp only [BitVec.msb_cons, BitVec.setWidth_cons] at h₁ h₂
    exact ⟨h₁, h₂⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- **Pairing**: if translating by a nonzero `t` negates the summand, the sum
vanishes (in any commutative ring: the terms cancel in pairs `{a, a ⊕ t}`). -/
theorem bsum_eq_zero_of_antisymm {t : BitVec n} (ht : t ≠ 0) (f : BitVec n → R)
    (hf : ∀ a, f (a ^^^ t) = -f a) : bsum n f = 0 := by
  induction n with
  | zero => exact absurd (BitVec.eq_of_toNat_eq (by have := t.isLt; simp at this; simp [this])) ht
  | succ n ih =>
    obtain ⟨b, t₀, rfl⟩ : ∃ b t₀, t = BitVec.cons b t₀ :=
      ⟨t.msb, t.setWidth n, (BitVec.cons_msb_setWidth t).symm⟩
    rw [bsum_succ]
    cases b
    · -- the translation stays inside each half
      have ht₀ : t₀ ≠ 0 := fun e => ht (by
        subst e; exact BitVec.eq_of_toNat_eq (by simp))
      have h₀ := ih ht₀ (fun x => f (BitVec.cons false x)) fun x => by
        have := hf (BitVec.cons false x); rwa [BitVec.cons_xor_cons] at this
      have h₁ := ih ht₀ (fun x => f (BitVec.cons true x)) fun x => by
        have := hf (BitVec.cons true x); rwa [BitVec.cons_xor_cons] at this
      rw [h₀, h₁, Semiring.add_zero]
    · -- the translation swaps the halves
      have : bsum n (fun x => f (BitVec.cons true x)) = -bsum n (fun x => f (BitVec.cons false x)) := by
        rw [← bsum_xor t₀ (fun x => f (BitVec.cons true x)), ← bsum_neg]
        refine bsum_congr fun x => ?_
        have := hf (BitVec.cons false x)
        rw [BitVec.cons_xor_cons] at this
        simpa using this
      rw [this]; grind

namespace Cl

variable {g : Fin n → R}

/-- The symmetric bilinear form of the metric on vectors, `B(u, v) = Σ gᵢ uᵢ vᵢ`
(on general multivectors: the scalar part of `u ~v`, summed blade by blade). -/
def dot (u v : Cl g) : R := bsum n fun a => u.coeff a * v.coeff a * coef g a a

/-- A vector (grade-1) blade `e_i`: its coefficient with itself is `gᵢ`, and
distinct vector blades anticommute. -/
theorem coef_vec_vec {a b : BitVec n} (ha : grade a = 1) (hb : grade b = 1) (hab : a ≠ b) :
    (coef g a b : R) = -coef g b a ∧ a &&& b = 0 := by
  have hdis : a &&& b = 0 := by
    have k := bitCount_xor_add n a.toNat b.toNat
    have ka : bitCount n (a.toNat &&& b.toNat) ≤ bitCount n a.toNat := bitCount_and_le_left n _ _
    have kb : bitCount n (a.toNat &&& b.toNat) ≤ bitCount n b.toNat := by
      rw [bitCount_and_comm]; exact bitCount_and_le_left n _ _
    unfold grade at ha hb
    -- if they shared a generator, both would be that generator
    have hx : bitCount n (a.toNat ^^^ b.toNat) ≠ 0 := by
      intro h0
      rw [bitCount_eq_zero_iff (Nat.xor_lt_two_pow a.isLt b.isLt)] at h0
      exact hab (BitVec.eq_of_toNat_eq (Nat.eq_of_testBit_eq fun i => by
        have := congrArg (·.testBit i) h0; simpa [Nat.testBit_xor] using this))
    have : bitCount n (a.toNat &&& b.toNat) = 0 := by omega
    rw [bitCount_eq_zero_iff (Nat.lt_of_le_of_lt Nat.and_le_left a.isLt), ← BitVec.toNat_and] at this
    exact (toNat_eq_zero_iff _).mp this
  refine ⟨?_, hdis⟩
  have hs := sigma_swap n a.toNat b.toNat
  rw [← BitVec.toNat_and, hdis] at hs
  have hp : bitParity n (BitVec.toNat (0 : BitVec n)) = false := by simp [bitParity]
  simp only [bitParity] at hs hp
  unfold grade at ha hb
  rw [ha, hb, hp] at hs
  rw [coef_eq, coef_eq, hdis, BitVec.and_comm, hdis]
  have e : sign a b = !sign b a := by
    unfold sign; revert hs
    cases sigma n a.toNat b.toNat <;> cases sigma n b.toNat a.toNat <;> decide
  rw [e, signOf_not]
  grind

/-- **The Clifford relation**: a vector squares to its quadratic form,
`v² = B(v, v) = Σ gᵢ vᵢ²`, over every commutative ring. -/
theorem mul_self_of_vector {v : Cl g} (hv : IsGrade 1 v) : v * v = scalar (dot v v) := by
  ext c
  rw [coeff_mul, coeff_scalar]
  by_cases hc : c = 0
  · subst hc
    rw [ite_eq_left rfl]
    unfold dot
    exact bsum_congr fun a => by rw [xor_zero']
  · rw [ite_eq_right hc]
    apply bsum_eq_zero_of_antisymm hc
    intro a
    rw [xor_xor_cancel_right]
    -- the pair `{a, a ⊕ c}`: both vector blades, or a vanishing term
    by_cases ha : v.coeff a = 0
    · rw [ha]; grind
    by_cases hb : v.coeff (a ^^^ c) = 0
    · rw [hb]; grind
    have ga : grade a = 1 := Classical.byContradiction fun h => ha (hv a h)
    have gb : grade (a ^^^ c) = 1 := Classical.byContradiction fun h => hb (hv _ h)
    have hne : a ^^^ c ≠ a := by
      intro e
      have : a ^^^ c ^^^ a = a ^^^ a := congrArg (· ^^^ a) e
      rw [BitVec.xor_comm a c, BitVec.xor_assoc, xor_self', xor_zero'] at this
      exact hc this
    have := (coef_vec_vec (g := g) gb ga hne).1
    grind

/-- The geometric product of two vectors is their inner product plus their
exterior product: `u v = B(u, v) + u ∧ v`. -/
theorem mul_eq_dot_add_wedge {u v : Cl g} (hu : IsGrade 1 u) (hv : IsGrade 1 v) :
    u * v = scalar (dot u v) + wedge u v := by
  ext c
  rw [coeff_add, coeff_mul, coeff_wedge, coeff_scalar]
  by_cases hc : c = 0
  · subst hc
    rw [ite_eq_left rfl]
    have hw : (bsum n fun a => u.coeff a * v.coeff (a ^^^ 0) * wcoef a (a ^^^ 0)) = (0 : R) := by
      rw [bsum_congr (f' := fun _ => (0 : R)) ?_, bsum_const_zero]
      intro a
      rw [xor_zero']
      by_cases ha : u.coeff a = 0
      · rw [ha]; grind
      have ga : grade a = 1 := Classical.byContradiction fun h => ha (hu a h)
      have : a &&& a ≠ 0 := by
        rw [BitVec.and_self]; intro e; rw [e] at ga; simp [grade] at ga
      unfold wcoef; rw [ite_eq_right this]; grind
    rw [hw, Semiring.add_zero]
    unfold dot
    exact bsum_congr fun a => by rw [xor_zero']
  · rw [ite_eq_right hc]
    have : ∀ r : R, (0 : R) + r = r := fun r => by grind
    rw [this]
    refine bsum_congr fun a => ?_
    by_cases ha : u.coeff a = 0
    · rw [ha]; grind
    by_cases hb : v.coeff (a ^^^ c) = 0
    · rw [hb]; grind
    have ga : grade a = 1 := Classical.byContradiction fun h => ha (hu a h)
    have gb : grade (a ^^^ c) = 1 := Classical.byContradiction fun h => hb (hv _ h)
    have hne : a ≠ a ^^^ c := by
      intro e
      have : a ^^^ a = a ^^^ (a ^^^ c) := congrArg (a ^^^ ·) e
      rw [xor_self', xor_xor_cancel_left] at this
      exact hc this.symm
    have hdis := (coef_vec_vec (g := g) ga gb hne).2
    rw [wcoef_eq_coef_zero, coef_eq, coef_eq, hdis]
    simp [mf]

/-- Vectors anticommute up to their inner product: `u v + v u = 2 B(u, v)`. -/
theorem mul_add_mul_swap {u v : Cl g} (hu : IsGrade 1 u) (hv : IsGrade 1 v) :
    u * v + v * u = scalar (dot u v + dot u v) := by
  rw [mul_eq_dot_add_wedge hu hv, mul_eq_dot_add_wedge hv hu, wedge_comm_vec hv hu]
  have hd : dot v u = dot u v := by
    unfold dot; exact bsum_congr fun a => by grind
  rw [hd]
  ext c
  simp only [coeff_add, coeff_neg, coeff_scalar]
  by_cases hc : c = 0
  · rw [ite_eq_left hc]; grind
  · rw [ite_eq_right hc]; grind

/-- A vector wedged with itself vanishes, over every commutative ring. -/
theorem wedge_self_of_vector {v : Cl g} (hv : IsGrade 1 v) : wedge v v = 0 := by
  have h1 := mul_eq_dot_add_wedge hv hv
  rw [mul_self_of_vector hv] at h1
  ext c
  have := congrArg (·.coeff c) h1
  simp only [coeff_add] at this
  rw [coeff_zero]
  grind

end Cl

end Grassmann.Spec

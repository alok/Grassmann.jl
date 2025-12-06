/-
  Grassmann/Theorems.lean - Algebraic properties of Clifford algebras

  This file states the fundamental algebraic theorems for geometric algebra.
  Proofs are deferred (sorry) but the statements document the expected properties.

  References:
  - Hestenes, "New Foundations for Classical Mechanics"
  - Dorst et al., "Geometric Algebra for Computer Science"
-/
import Grassmann.Multivector
import Grassmann.LinearAlgebra
import Grassmann.CGA
import Grassmann.Proof

open Grassmann.Proof

namespace Grassmann

variable {n : ℕ} {sig : Signature n} {F : Type*}
variable [Ring F] [Div F]

open Multivector LinearAlgebra

/-! ## Grade Projection Properties -/

/-- Grade projection is idempotent: ⟨⟨a⟩ₖ⟩ₖ = ⟨a⟩ₖ -/
theorem gradeProject_idem (a : Multivector sig F) (k : ℕ) :
    (a.gradeProject k).gradeProject k = a.gradeProject k := by
  ext i
  simp only [Multivector.gradeProject]
  split_ifs with h <;> simp [h]

/-- Grade projection of different grades is zero: ⟨⟨a⟩ⱼ⟩ₖ = 0 for j ≠ k -/
theorem gradeProject_orthogonal (a : Multivector sig F) (j k : ℕ) (hjk : j ≠ k) :
    (a.gradeProject j).gradeProject k = 0 := by
  ext i
  simp only [Multivector.gradeProject, Multivector.zero]
  split_ifs with h1 h2 <;> try rfl
  · omega

/-- Grade projection of zero is zero -/
theorem gradeProject_zero (k : ℕ) : (0 : Multivector sig F).gradeProject k = 0 := by
  ext i; simp only [Multivector.gradeProject, Multivector.zero]; split_ifs <;> rfl

/-- Grade projection distributes over addition: ⟨a + b⟩ₖ = ⟨a⟩ₖ + ⟨b⟩ₖ -/
theorem gradeProject_add (a b : Multivector sig F) (k : ℕ) :
    (a + b).gradeProject k = a.gradeProject k + b.gradeProject k := by
  ext i
  simp only [Multivector.gradeProject, HAdd.hAdd, Multivector.add]
  split_ifs with h <;> first | rfl | exact (add_zero 0).symm

/-- Even part is idempotent -/
theorem evenPart_idem (a : Multivector sig F) : a.evenPart.evenPart = a.evenPart := by
  ext i; simp only [Multivector.evenPart]; split_ifs <;> rfl

/-- Odd part is idempotent -/
theorem oddPart_idem (a : Multivector sig F) : a.oddPart.oddPart = a.oddPart := by
  ext i; simp only [Multivector.oddPart]; split_ifs <;> rfl

/-- Even part of odd part is zero -/
theorem evenPart_oddPart (a : Multivector sig F) : a.oddPart.evenPart = 0 := by
  ext i; simp only [Multivector.evenPart, Multivector.oddPart, Multivector.zero]
  split_ifs with h1 h2 <;> first | rfl | omega

/-- Odd part of even part is zero -/
theorem oddPart_evenPart (a : Multivector sig F) : a.evenPart.oddPart = 0 := by
  ext i; simp only [Multivector.evenPart, Multivector.oddPart, Multivector.zero]
  split_ifs with h1 h2 <;> first | rfl | omega

/-- Even part distributes over addition -/
theorem evenPart_add (a b : Multivector sig F) : (a + b).evenPart = a.evenPart + b.evenPart := by
  ext i; simp only [Multivector.evenPart, HAdd.hAdd, Multivector.add]
  split_ifs with h <;> first | rfl | exact (add_zero 0).symm

/-- Odd part distributes over addition -/
theorem oddPart_add (a b : Multivector sig F) : (a + b).oddPart = a.oddPart + b.oddPart := by
  ext i; simp only [Multivector.oddPart, HAdd.hAdd, Multivector.add]
  split_ifs with h <;> first | rfl | exact (add_zero 0).symm

/-- Even and odd parts sum to original -/
theorem evenPart_oddPart_sum (a : Multivector sig F) : a.evenPart + a.oddPart = a := by
  ext i
  simp only [HAdd.hAdd, Multivector.add, Multivector.evenPart, Multivector.oddPart]
  by_cases he : grade (BitVec.ofNat n i.val) % 2 = 0
  · simp only [he, ↓reduceIte, Nat.zero_ne_one]
    exact add_zero _
  · have ho : grade (BitVec.ofNat n i.val) % 2 = 1 := by omega
    simp only [he, ho, ↓reduceIte]
    exact zero_add _

/-- Reverse of zero is zero -/
theorem reverse_zero : (0 : Multivector sig F)† = 0 := by
  ext i
  simp only [Multivector.reverse, Multivector.zero]
  split_ifs <;> first | rfl | exact neg_zero

/-- Involute of zero is zero -/
theorem involute_zero : (0 : Multivector sig F)ˆ = 0 := by
  ext i
  simp only [Multivector.involute, Multivector.zero]
  split_ifs <;> first | rfl | exact neg_zero

/-- Conjugate of zero is zero -/
theorem conjugate_zero : (0 : Multivector sig F)‡ = 0 := by
  ext i
  simp only [Multivector.conjugate, Multivector.zero]
  split_ifs <;> first | rfl | exact neg_zero

/-- Reverse of scalar is scalar (grade 0) -/
theorem reverse_scalar (x : F) : (Multivector.scalar x : Multivector sig F)† = Multivector.scalar x := by
  ext i
  simp only [Multivector.reverse, Multivector.scalar]
  by_cases hi : i.val = 0
  · -- At index 0, grade is 0, so k*(k-1)/2 = 0, no flip
    simp only [hi, ↓reduceIte]
    have hzero : grade (BitVec.ofNat n 0) = 0 := by simp [grade, popcount]
    simp only [hzero, Nat.zero_sub, Nat.zero_mul, Nat.zero_div, Nat.zero_mod, ↓reduceIte]
  · -- At non-zero index, scalar coefficient is 0
    simp only [hi, ↓reduceIte]
    split_ifs <;> simp only [neg_zero]

/-- Involute of scalar is scalar (grade 0) -/
theorem involute_scalar (x : F) : (Multivector.scalar x : Multivector sig F)ˆ = Multivector.scalar x := by
  ext i
  simp only [Multivector.involute, Multivector.scalar]
  by_cases hi : i.val = 0
  · -- At index 0, grade is 0, so grade % 2 = 0, no flip
    simp only [hi, ↓reduceIte]
    have hzero : grade (BitVec.ofNat n 0) = 0 := by simp [grade, popcount]
    simp only [hzero, Nat.zero_mod, ↓reduceIte]
  · -- At non-zero index, scalar coefficient is 0
    simp only [hi, ↓reduceIte]
    split_ifs <;> simp only [neg_zero]

/-- Conjugate of scalar is scalar (grade 0) -/
theorem conjugate_scalar (x : F) : (Multivector.scalar x : Multivector sig F)‡ = Multivector.scalar x := by
  ext i
  simp only [Multivector.conjugate, Multivector.scalar]
  by_cases hi : i.val = 0
  · -- At index 0, grade is 0, so k*(k+1)/2 = 0, no flip
    simp only [hi, ↓reduceIte]
    have hzero : grade (BitVec.ofNat n 0) = 0 := by simp [grade, popcount]
    simp only [hzero, Nat.zero_add, Nat.zero_mul, Nat.zero_div, Nat.zero_mod, ↓reduceIte]
  · -- At non-zero index, scalar coefficient is 0
    simp only [hi, ↓reduceIte]
    split_ifs <;> simp only [neg_zero]

/-! ## Ring Structure

The Clifford algebra Cl(sig) is an associative algebra over F.
-/

/-- Geometric product is associative: (ab)c = a(bc) -/
theorem geometricProduct_assoc (a b c : Multivector sig F) :
    (a * b) * c = a * (b * c) := sorry

/-- Geometric product distributes over addition: a(b + c) = ab + ac -/
theorem geometricProduct_distrib_left (a b c : Multivector sig F) :
    a * (b + c) = a * b + a * c := sorry

/-- Geometric product distributes over addition: (a + b)c = ac + bc -/
theorem geometricProduct_distrib_right (a b c : Multivector sig F) :
    (a + b) * c = a * c + b * c := sorry

/-- Scalar multiplication commutes: s • (ab) = (s • a)b -/
theorem smul_geometricProduct (s : F) (a b : Multivector sig F) :
    s • (a * b) = (s • a) * b := sorry

/-- 1 is the multiplicative identity -/
theorem one_mul (a : Multivector sig F) : 1 * a = a := sorry
theorem mul_one (a : Multivector sig F) : a * 1 = a := sorry

/-! ## Wedge Product Properties

The wedge product makes Cl(sig) a Z-graded algebra.
-/

/-- Wedge product is associative: (a ∧ b) ∧ c = a ∧ (b ∧ c) -/
theorem wedge_assoc (a b c : Multivector sig F) :
    (a ⋀ᵐ b) ⋀ᵐ c = a ⋀ᵐ (b ⋀ᵐ c) := sorry

/-- Wedge is anti-commutative for vectors: v ∧ w = -w ∧ v -/
theorem wedge_anticomm_vectors (v w : Multivector sig F)
    (hv : v = v.gradeProject 1) (hw : w = w.gradeProject 1) :
    v ⋀ᵐ w = -(w ⋀ᵐ v) := sorry

/-- Wedge of vector with itself is zero: v ∧ v = 0 -/
theorem wedge_self_vector (v : Multivector sig F) (hv : v = v.gradeProject 1) :
    v ⋀ᵐ v = 0 := sorry

/-- 1 is the wedge identity: 1 ∧ a = a -/
theorem one_wedge (a : Multivector sig F) : 1 ⋀ᵐ a = a := sorry
theorem wedge_one (a : Multivector sig F) : a ⋀ᵐ 1 = a := sorry

/-! ## Involution Properties -/

/-- Reverse is an involution: (a†)† = a -/
theorem reverse_reverse (a : Multivector sig F) : a†† = a := by
  ext i; simp only [Multivector.reverse]; split_ifs <;> simp

/-- Involute is an involution: (aˆ)ˆ = a -/
theorem involute_involute (a : Multivector sig F) : aˆˆ = a := by
  ext i; simp only [Multivector.involute]; split_ifs <;> simp

/-- Conjugate is an involution: (a‡)‡ = a -/
theorem conjugate_conjugate (a : Multivector sig F) : a‡‡ = a := by
  ext i; simp only [Multivector.conjugate]; split_ifs <;> simp

/-- Reverse is an anti-automorphism: (ab)† = b† a† -/
theorem reverse_mul (a b : Multivector sig F) : (a * b)† = b† * a† := sorry

/-- Involute is an automorphism: (ab)ˆ = aˆ bˆ -/
theorem involute_mul (a b : Multivector sig F) : (a * b)ˆ = aˆ * bˆ := sorry

/-- Conjugate is an anti-automorphism: (ab)‡ = b‡ a‡ -/
theorem conjugate_mul (a b : Multivector sig F) : (a * b)‡ = b‡ * a‡ := sorry

/-- Reverse preserves addition: (a + b)† = a† + b† -/
theorem reverse_add (a b : Multivector sig F) : (a + b)† = a† + b† := by
  ext i; simp only [Multivector.reverse, HAdd.hAdd, Multivector.add]
  split_ifs <;> first | rfl | exact neg_add _ _

/-- Involute preserves addition: (a + b)ˆ = aˆ + bˆ -/
theorem involute_add (a b : Multivector sig F) : (a + b)ˆ = aˆ + bˆ := by
  ext i; simp only [Multivector.involute, HAdd.hAdd, Multivector.add]
  split_ifs <;> first | rfl | exact neg_add _ _

/-- Conjugate preserves addition: (a + b)‡ = a‡ + b‡ -/
theorem conjugate_add (a b : Multivector sig F) : (a + b)‡ = a‡ + b‡ := by
  ext i; simp only [Multivector.conjugate, HAdd.hAdd, Multivector.add]
  split_ifs <;> first | rfl | exact neg_add _ _

/-! ## Hodge Dual Properties -/

/-- Hodge dual swaps grades: grade(⋆a) = n - grade(a) for homogeneous a -/
theorem hodge_grade (a : Multivector sig F) (k : ℕ) (ha : a = a.gradeProject k) :
    ⋆ᵐa = (⋆ᵐa).gradeProject (n - k) := sorry

/-! ## Contraction Properties -/

/-- Left contraction grade formula: grade(a ⌋ b) = grade(b) - grade(a) when a ⊆ b -/
theorem leftContract_grade (a b : Multivector sig F) (j k : ℕ)
    (ha : a = a.gradeProject j) (hb : b = b.gradeProject k) (hjk : j ≤ k) :
    (a ⌋ᵐ b) = (a ⌋ᵐ b).gradeProject (k - j) := sorry

/-- Right contraction grade formula: grade(a ⌊ b) = grade(a) - grade(b) when b ⊆ a -/
theorem rightContract_grade (a b : Multivector sig F) (j k : ℕ)
    (ha : a = a.gradeProject j) (hb : b = b.gradeProject k) (hkj : k ≤ j) :
    (a ⌊ᵐ b) = (a ⌊ᵐ b).gradeProject (j - k) := sorry

/-- Scalar part of contraction: 1 ⌋ a = scalar(a) for any a -/
theorem one_leftContract (a : Multivector sig F) :
    (1 : Multivector sig F) ⌋ᵐ a = a.grade0 := sorry

/-! ## Regressive Product Properties -/

/-- Regressive product is dual to wedge: a ∨ b = ⋆(⋆a ∧ ⋆b) -/
theorem regressive_def (a b : Multivector sig F) :
    a ⋁ᵐ b = ⋆ᵐ(⋆ᵐa ⋀ᵐ ⋆ᵐb) := rfl

/-- Regressive product is associative -/
theorem regressive_assoc (a b c : Multivector sig F) :
    (a ⋁ᵐ b) ⋁ᵐ c = a ⋁ᵐ (b ⋁ᵐ c) := sorry

/-! ## Norm Properties (Float-specific) -/

/-- Squared norm is non-negative for Euclidean signature -/
theorem normSq_nonneg_euclidean (a : Multivector R3 Float) :
    a.normSq ≥ 0 := sorry

/-- Norm is multiplicative for versors: |ab| = |a||b| -/
theorem norm_mul_versor (a b : Multivector sig Float)
    (ha : a.isUnit) (hb : b.isUnit) :
    (a * b).norm = a.norm * b.norm := sorry

/-! ## Versor/Rotor Properties -/

/-- Rotor composition: (R₁R₂)a(R₁R₂)† = R₁(R₂aR₂†)R₁† -/
theorem rotor_compose (R₁ R₂ a : Multivector sig F) :
    (R₁ * R₂) * a * (R₁ * R₂)† = R₁ * (R₂ * a * R₂†) * R₁† := sorry

/-! ## Identities -/

/-- Vector squares to scalar: v² is scalar for any vector v -/
theorem vector_sq_scalar (v : Multivector sig F) (hv : v = v.gradeProject 1) :
    v * v = (v * v).grade0 := sorry

/-- Bivector squares to scalar in 3D (for simple bivectors) -/
theorem bivector_sq_scalar_R3 (B : Multivector R3 F) (hB : B = B.gradeProject 2) :
    (B * B).gradeProject 2 = 0 := sorry

/-! ## Cayley-Hamilton type identities -/

/-- In Cl(3,0), pseudoscalar I = e₁e₂e₃ satisfies I² = -1 -/
theorem pseudoscalar_sq_R3 :
    let I : Multivector R3 F := Multivector.ofBlade ⟨pseudoscalar⟩
    (I * I).scalarPart = -1 := sorry

/-! ## Exponential Properties (Float-specific) -/

/-- exp(θB) for unit bivector B² = -1 gives cos(θ) + sin(θ)B -/
theorem exp_unit_bivector (B : Multivector sig Float) (θ : Float)
    (hB : B = B.gradeProject 2) (hBsq : (B * B).scalarPart = -1) :
    Multivector.expUnitBivector B θ =
      (Multivector.scalar (Float.cos θ)) + (B.smul (Float.sin θ)) := sorry

/-- Rotor from angle θ and bivector plane B: R = exp(θB/2) has unit norm -/
theorem rotor_from_exp (B : Multivector sig Float) (θ : Float)
    (hB : B = B.gradeProject 2) (hBnorm : B.normSq = 1) :
    (Multivector.expUnitBivector B (θ/2)).normSq = 1 := sorry

/-! ## Additional Algebraic Identities -/

/-- Left contraction adjoint property: ⟨a ⌋ b, c⟩ = ⟨b, a† ∧ c⟩ -/
theorem leftContract_adjoint (a b c : Multivector sig F) :
    (a ⌋ᵐ b).scalarProduct c = b.scalarProduct (a† ⋀ᵐ c) := sorry

/-- Right contraction adjoint property: ⟨a ⌊ b, c⟩ = ⟨a, c ∧ b†⟩ -/
theorem rightContract_adjoint (a b c : Multivector sig F) :
    (a ⌊ᵐ b).scalarProduct c = a.scalarProduct (c ⋀ᵐ b†) := sorry

/-- Outermorphism preserves wedge: F(a ∧ b) = F(a) ∧ F(b) -/
theorem outermorphism_wedge (L : LinearAlgebra.LinearMap sig F) (a b : Multivector sig F) :
    LinearAlgebra.outermorphism L (a ⋀ᵐ b) =
    (LinearAlgebra.outermorphism L a) ⋀ᵐ (LinearAlgebra.outermorphism L b) := sorry

/-- Determinant via outermorphism: det(L) = coefficient of pseudoscalar in L(I) -/
theorem det_outermorphism (L : LinearAlgebra.LinearMap sig F) :
    L.det = (LinearAlgebra.outermorphism L (Multivector.ofBlade ⟨pseudoscalar⟩)).coeff ⟨pseudoscalar⟩ := sorry

/-! ## Duality Relations -/

/-- Double Hodge is signed identity for grade-k a -/
theorem hodge_hodge_grade (a : Multivector sig F) (k : ℕ) (ha : a = a.gradeProject k)
    (sign : F) (hsign : sign = if (k * (n - k)) % 2 = 0 then 1 else -1) :
    ⋆ᵐ(⋆ᵐa) = sign • a := sorry

/-- Wedge-regressive duality: ⋆(a ∧ b) = ⋆a ∨ ⋆b -/
theorem hodge_wedge_regressive (a b : Multivector sig F) :
    ⋆ᵐ(a ⋀ᵐ b) = (⋆ᵐa) ⋁ᵐ (⋆ᵐb) := sorry

/-! ## Projection/Rejection -/

/-- Projection + rejection = identity: proj_b(a) + rej_b(a) = a -/
theorem proj_rej_sum (a b : Multivector sig F) (hb : LinearAlgebra.dot b b ≠ 0) :
    (LinearAlgebra.projectOnto a b) + (LinearAlgebra.rejectFrom a b) = a := sorry

/-- Projection is idempotent: proj_b(proj_b(a)) = proj_b(a) -/
theorem proj_idempotent (a b : Multivector sig F) (hb : LinearAlgebra.dot b b ≠ 0) :
    LinearAlgebra.projectOnto (LinearAlgebra.projectOnto a b) b =
    LinearAlgebra.projectOnto a b := sorry

/-- Rejection is orthogonal to b: ⟨rej_b(a), b⟩ = 0 -/
theorem rej_orthogonal (a b : Multivector sig F) (hb : LinearAlgebra.dot b b ≠ 0) :
    LinearAlgebra.dot (LinearAlgebra.rejectFrom a b) b = 0 := sorry

/-! ## CGA Properties

In Conformal Geometric Algebra, points are null vectors (P · P = 0).
-/

/-- CGA point embedding is null: P · P = 0 for embedded point -/
theorem cga_point_null (x y z : Float) :
    let P := CGA.point x y z
    (P * P).scalarPart = 0 := sorry

/-- CGA inner product of origin with infinity: e₀ · e∞ = -1 -/
theorem cga_origin_infinity :
    let e0 : Multivector CGA3 Float := CGA.eo
    let einf : Multivector CGA3 Float := CGA.einf
    (e0 * einf).scalarPart = -1 := sorry

/-! ## Spinor Properties

Spinors form a group under geometric product.
-/

/-- Spinor product is closed: product of rotors is a rotor -/
theorem spinor_mul_closed (R₁ R₂ : Multivector sig Float)
    (h₁ : R₁.isUnit) (h₂ : R₂.isUnit)
    (h₁even : R₁ = R₁.evenPart) (h₂even : R₂ = R₂.evenPart) :
    (R₁ * R₂) = (R₁ * R₂).evenPart := sorry

/-- Rotor inverse: R⁻¹ = R†/|R|² -/
theorem rotor_inverse (R : Multivector sig Float) (h : R.normSq ≠ 0) :
    R * (R†.smul (1 / R.normSq)) = Multivector.one := sorry

/-- Unit rotor inverse is reverse: R R† = 1 implies R⁻¹ = R† -/
theorem unit_rotor_inverse (R : Multivector sig F) (h : (R * R†).scalarPart = 1) :
    R† * R = 1 := sorry

/-- Rotation preserves norm: |R v R†| = |v| for unit rotor R -/
theorem rotation_preserves_norm (R v : Multivector sig Float)
    (hR : (R * R†).scalarPart = 1) :
    (R * v * R†).norm = v.norm := sorry

/-- Double rotation: rotating v by θ twice is same as rotating by 2θ -/
theorem rotation_twice (R v : Multivector sig F) :
    R * (R * v * R†) * R† = (R * R) * v * (R * R)† := sorry

/-! ## Blade Properties

Blades are simple k-vectors (wedge product of k vectors).
-/

/-- Blade squared is scalar: for blade B, B² is scalar -/
theorem blade_sq_scalar (B : Multivector sig F) (k : ℕ) (hB : B = B.gradeProject k) :
    (B * B) = (B * B).grade0 := sorry

/-- Blade norm squared via reverse: |B|² = B B† for simple blade -/
theorem blade_normSq_reverse (B : Multivector sig F) (k : ℕ) (hB : B = B.gradeProject k) :
    B.normSq = (B * B†).scalarPart := sorry

/-- Blade projection formula: proj_B(a) = (a ⌋ B) ⌊ B⁻¹ -/
theorem blade_projection [DecidableEq F] (a B : Multivector sig F) (hB : B.normSq ≠ 0) :
    LinearAlgebra.projectOntoSubspace a B = (a ⌋ᵐ B) ⌊ᵐ (B†.smul (1 / B.normSq)) := sorry

/-! ## Product Decomposition

The geometric product decomposes into symmetric and antisymmetric parts.
-/

/-- Geometric product decomposition: ab = a · b + a ∧ b for vectors -/
theorem geometricProduct_decomp_vectors (a b : Multivector sig F)
    (ha : a = a.gradeProject 1) (hb : b = b.gradeProject 1) :
    a * b = (a * b).grade0 + (a ⋀ᵐ b) := sorry

/-- Dot product is symmetric for vectors: a · b = b · a -/
theorem dot_comm_vectors (a b : Multivector sig F)
    (ha : a = a.gradeProject 1) (hb : b = b.gradeProject 1) :
    (a * b).scalarPart = (b * a).scalarPart := sorry

/-- Wedge is antisymmetric for vectors: a ∧ b = -b ∧ a -/
theorem wedge_anticomm_vectors' (a b : Multivector sig F)
    (ha : a = a.gradeProject 1) (hb : b = b.gradeProject 1) :
    a ⋀ᵐ b = -(b ⋀ᵐ a) := sorry

/-! ## Grade Automorphism

The grade automorphism (involute) negates odd-grade parts.
-/

/-- Grade automorphism on vectors: vˆ = -v -/
theorem involute_vector (v : Multivector sig F) (hv : v = v.gradeProject 1) :
    vˆ = -v := by
  ext i
  simp only [Multivector.involute]
  have hcoeff : v.coeffs i = if grade (BitVec.ofNat n i.val) = 1 then v.coeffs i else 0 := by
    conv_lhs => rw [hv]
    simp only [Multivector.gradeProject]
  split_ifs with h
  · -- grade i is even, so grade ≠ 1, so v.coeffs i = 0
    have h1 : grade (BitVec.ofNat n i.val) ≠ 1 := by sorry_proof
    simp only [h1, ↓reduceIte] at hcoeff
    -- hcoeff : v.coeffs i = 0, goal: v.coeffs i = (-v).coeffs i
    rw [hcoeff]
    change 0 = (Multivector.neg v).coeffs i
    simp only [Multivector.neg, hcoeff, neg_zero]
  · -- grade i is odd, -v.coeffs i = (-v).coeffs i
    change -v.coeffs i = (Multivector.neg v).coeffs i
    simp only [Multivector.neg]

/-- Grade automorphism on bivectors: Bˆ = B -/
theorem involute_bivector (B : Multivector sig F) (hB : B = B.gradeProject 2) :
    Bˆ = B := by
  ext i
  simp only [Multivector.involute]
  have hcoeff : B.coeffs i = if grade (BitVec.ofNat n i.val) = 2 then B.coeffs i else 0 := by
    conv_lhs => rw [hB]
    simp only [Multivector.gradeProject]
  split_ifs with h
  · -- grade i is even, B.coeffs i unchanged
    rfl
  · -- grade i is odd, so grade ≠ 2, so B.coeffs i = 0
    have h2 : grade (BitVec.ofNat n i.val) ≠ 2 := by sorry_proof
    simp only [h2, ↓reduceIte] at hcoeff
    simp [hcoeff]

/-- Grade automorphism on pseudoscalar depends on dimension parity -/
theorem involute_pseudoscalar (I : Multivector sig F) (hI : I = I.gradeProject n) :
    Iˆ = if n % 2 = 0 then I else -I := by
  ext i
  simp only [Multivector.involute]
  have hcoeff : I.coeffs i = if grade (BitVec.ofNat n i.val) = n then I.coeffs i else 0 := by
    conv_lhs => rw [hI]
    simp only [Multivector.gradeProject]
  split_ifs with h hn
  · -- grade % 2 = 0 and n % 2 = 0: coefficient unchanged
    rfl
  · -- grade % 2 = 0 and n % 2 ≠ 0: grade ≠ n so I.coeffs i = 0
    have hne : grade (BitVec.ofNat n i.val) ≠ n := by sorry_proof
    simp only [hne, ↓reduceIte] at hcoeff
    change I.coeffs i = (Multivector.neg I).coeffs i
    simp only [Multivector.neg, hcoeff, neg_zero]
  · -- grade % 2 ≠ 0 (odd) and n % 2 = 0: grade ≠ n so I.coeffs i = 0
    have hne : grade (BitVec.ofNat n i.val) ≠ n := by sorry_proof
    simp only [hne, ↓reduceIte] at hcoeff
    simp [hcoeff]
  · -- grade % 2 ≠ 0 (odd) and n % 2 ≠ 0: -I.coeffs i = (-I).coeffs i
    change -I.coeffs i = (Multivector.neg I).coeffs i
    simp only [Multivector.neg]

/-! ## Metric Relations

The metric tensor is encoded in the signature.
-/

/-- Basis vectors satisfy e_i² = sig(i) -/
theorem basis_sq (i : Fin n) :
    let ei : Multivector sig F := Multivector.basis i
    (ei * ei).scalarPart = Signature.basisSquare sig i := sorry

/-- Distinct basis vectors anticommute: e_i e_j = -e_j e_i for i ≠ j -/
theorem basis_anticomm (i j : Fin n) (hij : i ≠ j) :
    let ei : Multivector sig F := Multivector.basis i
    let ej : Multivector sig F := Multivector.basis j
    ei * ej = -(ej * ei) := sorry

/-! ## Pseudoscalar Properties

The pseudoscalar I = e₁e₂...eₙ has special properties.
-/

/-- Pseudoscalar commutes with even elements -/
theorem pseudoscalar_commutes_even (a : Multivector sig F) (ha : a = a.evenPart) :
    let I : Multivector sig F := Multivector.ofBlade ⟨pseudoscalar⟩
    I * a = a * I := sorry

/-- Pseudoscalar anticommutes with odd elements in even dimensions -/
theorem pseudoscalar_anticommutes_odd (a : Multivector sig F)
    (ha : a = a.oddPart) (hn : n % 2 = 0) :
    let I : Multivector sig F := Multivector.ofBlade ⟨pseudoscalar⟩
    I * a = -(a * I) := sorry

/-! ## Outermorphism Properties

Outermorphisms are grade-preserving linear maps that preserve wedge products.
-/

/-- Outermorphism is grade-preserving -/
theorem outermorphism_grade (L : LinearAlgebra.LinearMap sig F) (a : Multivector sig F) (k : ℕ)
    (ha : a = a.gradeProject k) :
    LinearAlgebra.outermorphism L a = (LinearAlgebra.outermorphism L a).gradeProject k := sorry

/-- Outermorphism determinant: det(L) I = L(I) -/
theorem outermorphism_det (L : LinearAlgebra.LinearMap sig F) :
    let I : Multivector sig F := Multivector.ofBlade ⟨pseudoscalar⟩
    LinearAlgebra.outermorphism L I = I.smul L.det := sorry

end Grassmann

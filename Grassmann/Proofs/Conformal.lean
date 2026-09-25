/-
The conformal (null-basis) geometric product, by transport of structure.

Conformal spaces (`S!"∞∅+…"`) are not diagonal: the null generators `∞`, `∅`
(bits 0 and 1) have Gram matrix `g(∞,∞) = g(∅,∅) = 0`, `g(∞,∅) = -1`, and the
implementation multiplies in the outer-product basis `e_A = e_{a₁} ∧ ⋯ ∧ e_{a_k}`
by the Chevalley recursion (`DirectSum.TensorBundle.cliffordProduct`). Its
specification is the Clifford algebra of that Gram form, which is isometric to
a diagonal one: with `e₊² = 1`, `e₋² = -1`,

  `n∞ = e₊ + e₋`,  `n∅ = (e₋ - e₊)/2`   (so `n∞² = n∅² = 0`, `n∞·n∅ = -1`).

The outermorphism `T` of this change of basis (`toDiag`; on blades it is sign
free because the null pair holds the two lowest generators, and
`n∞ ∧ n∅ = e₊ ∧ e₋`) maps the null outer-product basis to `Cl(1, -1, 1, …)`,
with inverse `fromDiag` (`conf_inverse_*`, checked by `decide`).

**Proved in general** (`toDiag_implMul`, `implMul_assoc_of_conf`): if the
implementation's blade table transports, `T(e_a e_b) = T(e_a) T(e_b)` for every
pair of blades (`ConfTable`), then `T(x y) = T(x) T(y)` for **all**
multivectors, so the conformal product is the Clifford product of the diagonal
form in the null basis, and it is associative (`CGA2_mul_assoc`,
`CGA3_mul_assoc`).

**Checked exhaustively by the test suite, not by the kernel**: `ConfTable` for
`S!"∞∅+"`, `CGA2` and `CGA3` (`Tests.Proofs.Model`, which evaluates the
decision procedure of `ConfTable` in compiled code). Kernel evaluation stops at
`Terms.sortBasis`, which uses `Array.qsort`: the kernel cannot reduce it (not
even `#[3,1,2].qsort`), and its auxiliary definitions are private to core, so
no permutation lemma can be proved here. The Chevalley recursion itself is
kernel-friendly: a copy without the sort decides the `CGA2` table in about
25 s. A structural sort in `Terms.sortBasis` would make these kernel-checked
theorems.
-/
import Grassmann.Proofs.Tables

namespace Grassmann.Proofs

open DirectSum DirectSum.Proofs Grassmann.Spec Lean.Grind

variable {n : Nat}

/-! ## Sparse multivectors -/

/-- A sparse multivector: a list of `(blade, coefficient)` terms. -/
abbrev Sparse (n : Nat) := List (BitVec n × Rat)

/-- The coefficient function of a sparse multivector (terms on the same blade add). -/
def sfun : Sparse n → BitVec n → Rat
  | [], _ => 0
  | (s, α) :: xs, d => α * delta s d + sfun xs d

/-- The product of two sparse multivectors under the blade rule
`e_s ⋆ e_t = k(s,t) e_{s⊕t}`, term by term. -/
def smul (k : BitVec n → BitVec n → Rat) (xs ys : Sparse n) : Sparse n :=
  xs.flatMap fun (s, α) => ys.map fun (t, β) => (s ^^^ t, α * β * k s t)

/-- The image of a sparse multivector under the linear map with blade images `f`. -/
def sapply (f : BitVec n → Sparse n) (xs : Sparse n) : Sparse n :=
  xs.flatMap fun (s, α) => (f s).map fun (t, β) => (t, α * β)

/-- The linear map with blade images `f`, on coefficient functions:
`(lmap f x)(d) = Σ_c x(c) · f(c)(d)`. -/
def lmap (f : BitVec n → Sparse n) (x : BitVec n → Rat) : BitVec n → Rat :=
  fun d => bsum n fun c => x c * sfun (f c) d

/-- Concatenated sparse multivectors add. -/
theorem sfun_append (xs ys : Sparse n) (d : BitVec n) : sfun (xs ++ ys) d = sfun xs d + sfun ys d := by
  induction xs with
  | nil => simp [sfun]; grind
  | cons p xs ih => obtain ⟨s, α⟩ := p; simp only [List.cons_append, sfun, ih]; grind

/-- Scaling every term scales the coefficient function. -/
theorem sfun_map_scale (xs : Sparse n) (α : Rat) (d : BitVec n) :
    sfun (xs.map fun (t, β) => (t, α * β)) d = α * sfun xs d := by
  induction xs with
  | nil => simp [sfun]
  | cons p xs ih => obtain ⟨t, β⟩ := p; simp only [List.map_cons, sfun, ih]; grind

/-- A single-blade sparse multivector times another, under `twist k`. -/
private theorem twist_delta_sfun (k : BitVec n → BitVec n → Rat) (s : BitVec n) (α : Rat) (ys : Sparse n) :
    twist k (fun c => α * delta s c) (sfun ys)
      = sfun (ys.map fun (t, β) => (s ^^^ t, α * β * k s t)) := by
  induction ys with
  | nil =>
    funext d; simp only [List.map_nil, sfun]
    unfold twist; rw [bsum_congr (f' := fun _ => (0 : Rat)) (fun a => by grind), bsum_const_zero]
  | cons p ys ih =>
    obtain ⟨t, β⟩ := p
    funext d
    have h1 : twist k (fun c => α * delta s c) (fun c => β * delta t c) d
        = α * β * k s t * delta (s ^^^ t) d := by
      rw [twist_smul_left, twist_smul_right, twist_delta_delta]; grind
    show twist k (fun c => α * delta s c) (fun c => β * delta t c + sfun ys c) d
      = α * β * k s t * delta (s ^^^ t) d + sfun (ys.map fun (t, β) => (s ^^^ t, α * β * k s t)) d
    rw [twist_add_right, ← ih]
    show twist k (fun c => α * delta s c) (fun c => β * delta t c) d
      + twist k (fun c => α * delta s c) (sfun ys) d = _
    rw [h1]

/-- **Sparse products compute the twisted convolution.** -/
theorem sfun_smul (k : BitVec n → BitVec n → Rat) (xs ys : Sparse n) :
    sfun (smul k xs ys) = twist k (sfun xs) (sfun ys) := by
  induction xs with
  | nil =>
    funext d; simp only [smul, List.flatMap_nil, sfun]
    unfold twist; rw [bsum_congr (f' := fun _ => (0 : Rat)) (fun a => by grind), bsum_const_zero]
  | cons p xs ih =>
    obtain ⟨s, α⟩ := p
    funext d
    have hsplit : sfun ((s, α) :: xs) = fun c => α * delta s c + sfun xs c := rfl
    simp only [smul, List.flatMap_cons] at ih ⊢
    rw [sfun_append, hsplit, twist_add_left, ← twist_delta_sfun, ← ih]

/-- The linear map applied to a basis blade. -/
theorem lmap_delta (f : BitVec n → Sparse n) (a : BitVec n) : lmap f (delta a) = sfun (f a) := by
  funext d
  unfold lmap delta
  have : ∀ c, (if c = a then (1 : Rat) else 0) * sfun (f c) d = if c = a then sfun (f a) d else 0 := by
    intro c; by_cases h : c = a
    · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]; grind
    · rw [ite_eq_right h, ite_eq_right h]; grind
  rw [bsum_congr this, bsum_ite_eq]

/-- The linear map applied to a sparse multivector. -/
theorem lmap_sfun (f : BitVec n → Sparse n) (xs : Sparse n) : lmap f (sfun xs) = sfun (sapply f xs) := by
  induction xs with
  | nil =>
    funext d; simp only [sapply, List.flatMap_nil, sfun, lmap]
    rw [bsum_congr (f' := fun _ => (0 : Rat)) (fun a => by grind), bsum_const_zero]
  | cons p xs ih =>
    obtain ⟨s, α⟩ := p
    funext d
    simp only [sapply, List.flatMap_cons] at ih ⊢
    rw [sfun_append, sfun_map_scale, ← ih]
    have hd := congrFun (lmap_delta f s) d
    unfold lmap at hd ⊢
    rw [show (fun c => sfun ((s, α) :: xs) c * sfun (f c) d)
        = fun c => α * (delta s c * sfun (f c) d) + sfun xs c * sfun (f c) d from by
      funext c; simp only [sfun]; grind, bsum_add, ← mul_bsum, hd]

/-- `lmap` is linear in its argument, for coefficient functions given as
combinations `Σ_a x(a) F(a)`. -/
theorem lmap_bsum (f : BitVec n → Sparse n) (x : BitVec n → Rat) (F : BitVec n → BitVec n → Rat) :
    lmap f (fun c => bsum n fun a => x a * F a c) = fun d => bsum n fun a => x a * lmap f (F a) d := by
  funext d
  unfold lmap
  simp only [bsum_mul, mul_bsum]
  rw [bsum_comm]
  exact bsum_congr fun a => bsum_congr fun c => by grind

/-- Every coefficient function is the combination of its basis blades. -/
theorem eq_bsum_delta (x : BitVec n → Rat) : x = fun c => bsum n fun a => x a * delta a c := by
  funext c
  unfold delta
  have : ∀ a, x a * (if c = a then (1 : Rat) else 0) = if c = a then x c else 0 := by
    intro a; by_cases h : c = a
    · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]; grind
    · rw [ite_eq_right h, ite_eq_right h]; grind
  rw [bsum_congr this, bsum_ite_eq']

/-- The twisted convolution of two combinations is the double combination of
the pairwise convolutions. -/
theorem twist_bsum (k : BitVec n → BitVec n → Rat) (x y : BitVec n → Rat) (F G : BitVec n → BitVec n → Rat) :
    twist k (fun c => bsum n fun a => x a * F a c) (fun c => bsum n fun b => y b * G b c)
      = fun d => bsum n fun a => bsum n fun b => x a * y b * twist k (F a) (G b) d := by
  funext d
  unfold twist
  have lhs : ∀ c, (bsum n fun a => x a * F a c) * (bsum n fun b => y b * G b (c ^^^ d)) * k c (c ^^^ d)
      = bsum n fun a => bsum n fun b => x a * y b * (F a c * G b (c ^^^ d) * k c (c ^^^ d)) := by
    intro c
    rw [bsum_mul, bsum_mul]
    refine bsum_congr fun a => ?_
    rw [mul_bsum, bsum_mul]
    exact bsum_congr fun b => by grind
  rw [bsum_congr lhs, bsum_comm]
  refine bsum_congr fun a => ?_
  rw [bsum_comm]
  refine bsum_congr fun b => ?_
  rw [mul_bsum]

/-! ## The conformal change of basis -/

/-- `T(e_A)`: the image of a null outer-product basis blade in the diagonal
basis. The null pair sits at bits 0 (`∞`) and 1 (`∅`); `n∞ ↦ e₊ + e₋`,
`n∅ ↦ (e₋ - e₊)/2`, `n∞ ∧ n∅ ↦ e₊ ∧ e₋`, other generators fixed (no sign: the
pair holds the lowest generators). -/
def toDiagBlade (a : BitVec n) : Sparse n :=
  let r := a &&& ~~~(3 : BitVec n)
  match a.toNat % 4 with
  | 1 => [(r ||| 1, 1), (r ||| 2, 1)]
  | 2 => [(r ||| 1, -1/2), (r ||| 2, 1/2)]
  | _ => [(a, 1)]

/-- `T⁻¹`: `e₊ ↦ n∞/2 - n∅`, `e₋ ↦ n∞/2 + n∅`, `e₊ ∧ e₋ ↦ n∞ ∧ n∅`. -/
def fromDiagBlade (a : BitVec n) : Sparse n :=
  let r := a &&& ~~~(3 : BitVec n)
  match a.toNat % 4 with
  | 1 => [(r ||| 1, 1/2), (r ||| 2, -1)]
  | 2 => [(r ||| 1, 1/2), (r ||| 2, 1)]
  | _ => [(a, 1)]

/-- The diagonal metric `(1, -1, 1, …, 1)` isometric to a conformal space with
a Euclidean base (`e₊`, `e₋`, then the base generators). -/
def gConf (n : Nat) : Fin n → Rat := fun i => if i.1 = 1 then -1 else 1

/-- The change of basis on multivectors. -/
def toDiag {g : Fin n → Rat} (x : Cl g) : Cl g := ⟨lmap toDiagBlade x.coeff⟩

/-- Its inverse. -/
def fromDiag {g : Fin n → Rat} (x : Cl g) : Cl g := ⟨lmap fromDiagBlade x.coeff⟩

/-- The implementation's blade rule transported: `T(e_a e_b) = T(e_a) T(e_b)`
on every pair of blades, as functions (checked by `decide`). -/
def ConfTable (V : TensorBundle) (g : Fin n → Rat) : Prop :=
  ∀ a b d : BitVec n, lmap toDiagBlade (ofTerms g (V.terms₂ .mul (mask a) (mask b))).coeff d
    = sfun (smul (coef g) (toDiagBlade a) (toDiagBlade b)) d

/-- `ConfTable` is decidable (finitely many blades, exact arithmetic); the test
suite runs this decision procedure. -/
instance (V : TensorBundle) (g : Fin n → Rat) : Decidable (ConfTable V g) := by
  unfold ConfTable; infer_instance

/-- `T⁻¹ ∘ T` is the identity on every blade (checked by `decide`). -/
def ConfInverse (n : Nat) : Prop :=
  ∀ a d : BitVec n, sfun (sapply fromDiagBlade (toDiagBlade a)) d = delta a d

/-- **Transport**: a transported table makes `T` multiplicative on all multivectors. -/
theorem toDiag_implMul {V : TensorBundle} {g : Fin n → Rat} (h : ConfTable V g) (x y : Cl g) :
    toDiag (implMul V x y) = toDiag x * toDiag y := by
  ext d
  show lmap toDiagBlade (bilin (fun a b => ofTerms g (V.terms₂ .mul (mask a) (mask b))) x y).coeff d
    = twist (coef g) (lmap toDiagBlade x.coeff) (lmap toDiagBlade y.coeff) d
  have hx : lmap toDiagBlade x.coeff = fun c => bsum n fun a => x.coeff a * sfun (toDiagBlade a) c := by
    conv => lhs; rw [eq_bsum_delta x.coeff]
    rw [lmap_bsum]; simp only [lmap_delta]
  have hy : lmap toDiagBlade y.coeff = fun c => bsum n fun b => y.coeff b * sfun (toDiagBlade b) c := by
    conv => lhs; rw [eq_bsum_delta y.coeff]
    rw [lmap_bsum]; simp only [lmap_delta]
  have hb : (bilin (fun a b => ofTerms g (V.terms₂ .mul (mask a) (mask b))) x y).coeff
      = fun c => bsum n fun a => x.coeff a * (fun c => bsum n fun b =>
          y.coeff b * (ofTerms g (V.terms₂ .mul (mask a) (mask b))).coeff c) c := by
    funext c
    show (bsum n fun a => bsum n fun b =>
      x.coeff a * y.coeff b * (ofTerms g (V.terms₂ .mul (mask a) (mask b))).coeff c) = _
    refine bsum_congr fun a => ?_
    rw [mul_bsum]
    exact bsum_congr fun b => by grind
  rw [hx, hy, twist_bsum, hb, lmap_bsum]
  refine bsum_congr fun a => ?_
  rw [lmap_bsum, mul_bsum]
  refine bsum_congr fun b => ?_
  rw [h a b d, sfun_smul]; grind

/-- `T⁻¹ ∘ T = id` on all multivectors, from the blade check. -/
theorem fromDiag_toDiag (h : ConfInverse n) {g : Fin n → Rat} (x : Cl g) : fromDiag (toDiag x) = x := by
  ext d
  show lmap fromDiagBlade (lmap toDiagBlade x.coeff) d = x.coeff d
  conv => lhs; rw [eq_bsum_delta x.coeff]
  rw [lmap_bsum, lmap_bsum]
  simp only [lmap_delta, lmap_sfun]
  rw [bsum_congr fun a => by rw [h a d]]
  exact congrFun (eq_bsum_delta x.coeff).symm d

/-- A transported product is associative. -/
theorem implMul_assoc_of_conf {V : TensorBundle} {g : Fin n → Rat} (h : ConfTable V g) (hi : ConfInverse n)
    (x y z : Cl g) : implMul V (implMul V x y) z = implMul V x (implMul V y z) := by
  have e : ∀ u v : Cl g, implMul V u v = fromDiag (toDiag u * toDiag v) := fun u v => by
    rw [← toDiag_implMul h, fromDiag_toDiag hi]
  rw [e (implMul V x y), toDiag_implMul h, e x (implMul V y z), toDiag_implMul h, Cl.mul_assoc]

/-! ## The conformal spaces -/

theorem conf_inverse_3 : ConfInverse 3 := by unfold ConfInverse; decide +kernel
/-- `T⁻¹ ∘ T = id` on the blades of `CGA2` (`n = 4`). -/
theorem conf_inverse_4 : ConfInverse 4 := by unfold ConfInverse; decide +kernel
/-- `T⁻¹ ∘ T = id` on the blades of `CGA3` (`n = 5`). -/
theorem conf_inverse_5 : ConfInverse 5 := by unfold ConfInverse; decide +kernel

/-- `CGA2`: if the transported table holds (it is checked exhaustively on every
blade pair by `Tests.Proofs`; the kernel cannot evaluate it because
`Terms.sortBasis` uses `Array.qsort`), the conformal product is the Clifford
product of `Cl(3,1)` in the null basis, and is associative. -/
theorem CGA2_mul_assoc (h : ConfTable CGA2 (gConf 4)) (x y z : Cl (gConf 4)) :
    implMul CGA2 (implMul CGA2 x y) z = implMul CGA2 x (implMul CGA2 y z) :=
  implMul_assoc_of_conf h conf_inverse_4 x y z

/-- `CGA3` (the conformal model of Euclidean 3-space): the same, for `Cl(4,1)`. -/
theorem CGA3_mul_assoc (h : ConfTable CGA3 (gConf 5)) (x y z : Cl (gConf 5)) :
    implMul CGA3 (implMul CGA3 x y) z = implMul CGA3 x (implMul CGA3 y z) :=
  implMul_assoc_of_conf h conf_inverse_5 x y z

end Grassmann.Proofs

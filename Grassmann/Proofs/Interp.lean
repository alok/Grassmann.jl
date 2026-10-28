/-
The plan interpreter, proved.

`Grassmann.Kernel.Plan.eval₂`/`eval₁` (DESIGN.md §5.3) run every reference
kernel: tail-recursive `USize`-style loops over a gather-form plan, pushing one
accumulator per output into packed storage. PROOFS.md listed them as *tested,
not proved*: "a proof of `eval₂` would carry every §3 theorem to
`Multivector V α`". This file is that proof, in three layers.

1. **Exact, for every coefficient type** (`get_eval₂`, `get_eval₁`): output `c`
   of a plan is the left fold of its row, `acc` over the entries
   `rowStart[c] ≤ t < rowStart[c+1]` starting from `Coeff.zero`. Nothing is
   assumed about `α`: at `Float` this is a statement about the bits the
   compiled loop produces (it is the definition of the order of operations).
2. **Exact rationals** (`row₂_rat`, `row₁_rat`): at `Rat`, for a plan whose
   coefficient codes are the `±1` shortcuts or literal values (`Coded`), the
   fold is the sum `Σ coef t · x[ia t] · y[ib t]`.
3. **Plans that are spec tables** (`eval₂_eq_twist`): if a plan's entries are
   the spec product table in a storage order that is a bijection onto the
   blades (`*_mul_plan` in `Grassmann.Proofs.Tables` checks this per space),
   the interpreter computes the spec product: reading storage as a spec
   multivector, `coeffs (eval₂ p x y) = twist k (coeffs x) (coeffs y)`.
4. **The reference kernels** (`refBin_eq_twist`, `R3_refMul`, …): a `decide +kernel`
   check of the built plan (`RefSpec`) carries layer 3 to `refBin` itself, here
   for the geometric product of `ℝ3`, `D!"1,2,-3"`, `STA` and `PGA3` and the
   exterior product of `ℝ3`.
-/
import Grassmann.Proofs.Tables

namespace Grassmann.Proofs.Interp

open DirectSum StaticVectors AbstractTensors Grassmann.Kernel Grassmann.Kernel.Plan

/-! ## 1. The loops, exactly -/

section Exact

variable {α : Type} [Coeff α]

/-- `rows₂` pushes exactly one value per remaining output. -/
theorem size_rows₂ (p : Plan) (ha : p.Aligned) (x y : Packed.Arr α) (k c : Nat) (out : Packed.Arr α) :
    Packed.size (rows₂ p ha x y k c out) = Packed.size out + (k - c) := by
  induction c, out using rows₂.induct p ha x y k with
  | case1 c out hc s e ih =>
    rw [rows₂, ite_eq_left hc, ih, Packed.size_push]; omega
  | case2 c out hc =>
    rw [rows₂, ite_eq_right hc]; omega

/-- `rows₁` pushes exactly one value per remaining output. -/
theorem size_rows₁ (p : Plan) (ha : p.Aligned) (x : Packed.Arr α) (k c : Nat) (out : Packed.Arr α) :
    Packed.size (rows₁ p ha x k c out) = Packed.size out + (k - c) := by
  induction c, out using rows₁.induct p ha x k with
  | case1 c out hc s e ih =>
    rw [rows₁, ite_eq_left hc, ih, Packed.size_push]; omega
  | case2 c out hc =>
    rw [rows₁, ite_eq_right hc]; omega

/-- Start of row `c` (as the interpreter reads it). -/
def rowS (p : Plan) (c : Nat) : Nat := (p.rowStart[c]?.getD 0).toNat

/-- End of row `c` (as the interpreter reads it, clamped to the entries). -/
def rowE (p : Plan) (c : Nat) : Nat := min (p.rowStart[c + 1]?.getD 0).toNat p.ia.size

theorem rowE_le (p : Plan) (c : Nat) : rowE p c ≤ p.ia.size := Nat.min_le_right _ _

/-- Packed reads through equal arrays agree. -/
theorem get_congr {a b : Packed.Arr α} (h : a = b) (i : Nat) (hi : i < Packed.size a) :
    Packed.get a ⟨i, hi⟩ = Packed.get b ⟨i, h ▸ hi⟩ := by subst h; rfl

/-- What `rows₂` leaves at position `i`: the old contents below `size out`,
then the row folds of outputs `c, c+1, …`. -/
theorem get_rows₂ (p : Plan) (ha : p.Aligned) (x y : Packed.Arr α) (k c : Nat) (out : Packed.Arr α)
    (i : Nat) (hi : i < Packed.size (rows₂ p ha x y k c out)) :
    Packed.get (rows₂ p ha x y k c out) ⟨i, hi⟩ =
      if h : i < Packed.size out then Packed.get out ⟨i, h⟩
      else row₂ p ha x y (rowE p (c + (i - Packed.size out))) (rowE_le _ _)
        (rowS p (c + (i - Packed.size out))) Coeff.zero := by
  induction c, out using rows₂.induct p ha x y k with
  | case1 c out hc s e ih =>
    have hi' : i < Packed.size (rows₂ p ha x y k (c + 1)
        (Packed.push out (row₂ p ha x y e (Nat.min_le_right _ _) s Coeff.zero))) := by
      rw [rows₂, ite_eq_left hc] at hi; exact hi
    rw [get_congr (by rw [rows₂, ite_eq_left hc]) i hi, ih hi']
    by_cases h1 : i < Packed.size out
    · rw [dite_eq_left (by rw [Packed.size_push]; omega), dite_eq_left h1]
      exact Packed.get_push_lt out _ i h1
    · by_cases h2 : i = Packed.size out
      · subst h2
        rw [dite_eq_left (by rw [Packed.size_push]; omega), dite_eq_right h1]
        rw [Packed.get_push_size]
        simp only [Nat.sub_self, Nat.add_zero]
        rfl
      · rw [dite_eq_right (by rw [Packed.size_push]; omega), dite_eq_right h1]
        have : c + 1 + (i - Packed.size (Packed.push out (row₂ p ha x y e (Nat.min_le_right _ _) s Coeff.zero)))
            = c + (i - Packed.size out) := by rw [Packed.size_push]; omega
        rw [this]
  | case2 c out hc =>
    have : i < Packed.size out := by
      rw [size_rows₂, show k - c = 0 by omega] at hi; omega
    rw [get_congr (by rw [rows₂, ite_eq_right hc]) i hi, dite_eq_left this]

/-- What `rows₁` leaves at position `i`. -/
theorem get_rows₁ (p : Plan) (ha : p.Aligned) (x : Packed.Arr α) (k c : Nat) (out : Packed.Arr α)
    (i : Nat) (hi : i < Packed.size (rows₁ p ha x k c out)) :
    Packed.get (rows₁ p ha x k c out) ⟨i, hi⟩ =
      if h : i < Packed.size out then Packed.get out ⟨i, h⟩
      else row₁ p ha x (rowE p (c + (i - Packed.size out))) (rowE_le _ _)
        (rowS p (c + (i - Packed.size out))) Coeff.zero := by
  induction c, out using rows₁.induct p ha x k with
  | case1 c out hc s e ih =>
    have hi' : i < Packed.size (rows₁ p ha x k (c + 1)
        (Packed.push out (row₁ p ha x e (Nat.min_le_right _ _) s Coeff.zero))) := by
      rw [rows₁, ite_eq_left hc] at hi; exact hi
    rw [get_congr (by rw [rows₁, ite_eq_left hc]) i hi, ih hi']
    by_cases h1 : i < Packed.size out
    · rw [dite_eq_left (by rw [Packed.size_push]; omega), dite_eq_left h1]
      exact Packed.get_push_lt out _ i h1
    · by_cases h2 : i = Packed.size out
      · subst h2
        rw [dite_eq_left (by rw [Packed.size_push]; omega), dite_eq_right h1]
        rw [Packed.get_push_size]
        simp only [Nat.sub_self, Nat.add_zero]
        rfl
      · rw [dite_eq_right (by rw [Packed.size_push]; omega), dite_eq_right h1]
        have : c + 1 + (i - Packed.size (Packed.push out (row₁ p ha x e (Nat.min_le_right _ _) s Coeff.zero)))
            = c + (i - Packed.size out) := by rw [Packed.size_push]; omega
        rw [this]
  | case2 c out hc =>
    have : i < Packed.size out := by
      rw [size_rows₁, show k - c = 0 by omega] at hi; omega
    rw [get_congr (by rw [rows₁, ite_eq_right hc]) i hi, dite_eq_left this]

/-- **The binary interpreter, exactly:** output `c` of `eval₂ p x y` is the fold
of row `c` from `Coeff.zero`, in the plan's entry order (every coefficient
type; at `Float` this fixes the rounding). -/
theorem get_eval₂ {n m k : Nat} (p : Plan) (ha : p.Aligned) (x : Values α n) (y : Values α m) (c : Fin k) :
    (p.eval₂ x y : Values α k).get c =
      row₂ p ha x.data y.data (rowE p c) (rowE_le _ _) (rowS p c) Coeff.zero := by
  have hs := size_rows₂ p ha x.data y.data k 0 (Packed.mkEmpty k)
  rw [Packed.size_mkEmpty] at hs
  unfold eval₂ finish
  rw [dite_eq_left ha, dite_eq_left (by omega)]
  show Packed.get _ ⟨c.1, _⟩ = _
  rw [get_rows₂, dite_eq_right (by rw [Packed.size_mkEmpty]; omega)]
  simp [Packed.size_mkEmpty]

/-- **The unary interpreter, exactly.** -/
theorem get_eval₁ {n k : Nat} (p : Plan) (ha : p.Aligned) (x : Values α n) (c : Fin k) :
    (p.eval₁ x : Values α k).get c =
      row₁ p ha x.data (rowE p c) (rowE_le _ _) (rowS p c) Coeff.zero := by
  have hs := size_rows₁ p ha x.data k 0 (Packed.mkEmpty k)
  rw [Packed.size_mkEmpty] at hs
  unfold eval₁ finish
  rw [dite_eq_left ha, dite_eq_left (by omega)]
  show Packed.get _ ⟨c.1, _⟩ = _
  rw [get_rows₁, dite_eq_right (by rw [Packed.size_mkEmpty]; omega)]
  simp [Packed.size_mkEmpty]

end Exact

/-! ## 2. Lawful coefficients: the fold is a sum -/

section Lawful

open Lean.Grind

/-- `Σ_{t ∈ [s, e)} f t`. -/
def isum (s e : Nat) (f : Nat → Rat) : Rat := ((List.range' s (e - s)).map f).sum

theorem isum_step {s e : Nat} (f : Nat → Rat) (h : s < e) : isum s e f = f s + isum (s + 1) e f := by
  unfold isum
  rw [show e - s = (e - (s + 1)) + 1 by omega, List.range'_succ]
  simp

theorem isum_stop {s e : Nat} (f : Nat → Rat) (h : ¬ s < e) : isum s e f = 0 := by
  unfold isum; rw [show e - s = 0 by omega]; simp

/-- Entry `t`'s first-operand position (`0` past the end). -/
def iaAt (p : Plan) (t : Nat) : Nat := (p.ia[t]?.getD 0).toNat
/-- Entry `t`'s second-operand position. -/
def ibAt (p : Plan) (t : Nat) : Nat := (p.ib[t]?.getD 0).toNat
/-- Entry `t`'s exact coefficient. -/
def coefAt (p : Plan) (t : Nat) : Rat := p.coef[t]?.getD 0

/-- Every entry's class code agrees with its coefficient (`0` is `+1`, `1` is
`-1`), so the interpreter's shortcuts compute `coef · v`. -/
def Coded (p : Plan) : Bool :=
  (List.range p.ia.size).all fun t => match p.code[t]?, p.coef[t]? with
    | some 0, some r => r == 1
    | some 1, some r => r == -1
    | some _, some _ => true
    | _, _ => false

theorem acc_rat (p : Plan) (ha : p.Aligned) (hc : Coded p = true) (t : Nat) (ht : t < p.ia.size)
    (o v : Rat) : p.acc ha t ht o v = o + coefAt p t * v := by
  have h2 : t < p.code.size := by have := ha.2.1; omega
  have h3 : t < p.coef.size := by have := ha.2.2; omega
  have hall := List.all_eq_true.1 hc t (List.mem_range.2 ht)
  rw [getElem?_pos p.code t h2, getElem?_pos p.coef t h3] at hall
  unfold acc coefAt
  rw [getElem?_pos p.coef t h3, Option.getD_some]
  generalize p.code[t] = c at hall ⊢
  generalize p.coef[t] = r at hall ⊢
  by_cases c0 : c = 0
  · subst c0; simp at hall; subst hall; simp <;> grind
  · by_cases c1 : c = 1
    · subst c1; simp at hall; subst hall; simp <;> grind
    · simp [c0, c1]; rfl

/-- **The row fold is a sum** (exact rational coefficients). -/
theorem row₂_rat (p : Plan) (ha : p.Aligned) (hc : Coded p = true) (x y : Packed.Arr Rat) (e : Nat)
    (he : e ≤ p.ia.size) (t : Nat) (o : Rat) :
    row₂ p ha x y e he t o = o + isum t e (fun u => coefAt p u * (rd x (iaAt p u) * rd y (ibAt p u))) := by
  induction t, o using row₂.induct p ha x y e he with
  | case1 t o ht h1 v ih =>
    rw [row₂, dite_eq_left ht, ih, acc_rat p ha hc t h1, isum_step _ ht]
    have hv : v = rd x (iaAt p t) * rd y (ibAt p t) := by
      simp only [v, iaAt, ibAt, getElem?_pos p.ia t h1, getElem?_pos p.ib t (by have := ha.1; omega),
        Option.getD_some]
    rw [hv]; grind
  | case2 t o ht =>
    rw [row₂, dite_eq_right ht, isum_stop _ ht]; grind

/-- **The unary row fold is a sum.** -/
theorem row₁_rat (p : Plan) (ha : p.Aligned) (hc : Coded p = true) (x : Packed.Arr Rat) (e : Nat)
    (he : e ≤ p.ia.size) (t : Nat) (o : Rat) :
    row₁ p ha x e he t o = o + isum t e (fun u => coefAt p u * rd x (iaAt p u)) := by
  induction t, o using row₁.induct p ha x e he with
  | case1 t o ht h1 ih =>
    rw [row₁, dite_eq_left ht, ih, acc_rat p ha hc t h1, isum_step _ ht]
    have hv : rd x (p.ia[t]'h1).toNat = rd x (iaAt p t) := by
      simp only [iaAt, getElem?_pos p.ia t h1, Option.getD_some]
    rw [hv]; grind
  | case2 t o ht =>
    rw [row₁, dite_eq_right ht, isum_stop _ ht]; grind

end Lawful

/-! ## 3. Plans that are spec tables compute the spec product -/

section Spec

open Grassmann.Spec Lean.Grind

variable {n : Nat}

/-- Every blade of `BitVec n`, in the order `bsum` adds them. -/
def allBlades : (n : Nat) → List (BitVec n)
  | 0 => [0#0]
  | n + 1 => (allBlades n).map (BitVec.cons false) ++ (allBlades n).map (BitVec.cons true)

theorem mem_allBlades : ∀ {n : Nat} (a : BitVec n), a ∈ allBlades n
  | 0, a => by
    have : a = 0#0 := BitVec.eq_of_toNat_eq (by have := a.isLt; simp at this; simp [this])
    simp [allBlades, this]
  | n + 1, a => by
    rw [← BitVec.cons_msb_setWidth a]
    unfold allBlades
    cases a.msb
    · exact List.mem_append_left _ (List.mem_map_of_mem (mem_allBlades _))
    · exact List.mem_append_right _ (List.mem_map_of_mem (mem_allBlades _))

theorem sum_append' (l₁ l₂ : List Rat) : (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  induction l₁ with
  | nil => simp; grind
  | cons a l ih => simp [ih]; grind

theorem bsum_eq_sum (f : BitVec n → Rat) : bsum n f = ((allBlades n).map f).sum := by
  induction n with
  | zero => simp [allBlades, bsum]; grind
  | succ n ih =>
    rw [bsum_succ, ih, ih, allBlades, List.map_append, sum_append', List.map_map, List.map_map]
    rfl

theorem perm_sum {l₁ l₂ : List Rat} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp [ih]
  | swap a b l => simp; grind
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- The storage order `blade 0, …, blade (N-1)` as a list. -/
def order (N : Nat) (blade : Nat → BitVec n) : List (BitVec n) := (List.range N).map blade

/-- The storage position of a blade. -/
def pos (N : Nat) (blade : Nat → BitVec n) (a : BitVec n) : Nat := (order N blade).idxOf a

/-- A storage order: the positions `0 … N-1` hit every blade exactly once. -/
def IsOrder (N : Nat) (blade : Nat → BitVec n) : Prop :=
  (order N blade).Nodup ∧ (order N blade).Perm (allBlades n)

instance (N : Nat) (blade : Nat → BitVec n) : Decidable (IsOrder N blade) := by
  unfold IsOrder; exact inferInstance

theorem sum_order {N : Nat} {blade : Nat → BitVec n} (f : BitVec n → Rat) :
    ((List.range N).map fun i => f (blade i)) = (order N blade).map f := by
  simp [order, List.map_map]

theorem bsum_order {N : Nat} {blade : Nat → BitVec n} (h : IsOrder N blade) (f : BitVec n → Rat) :
    ((List.range N).map fun i => f (blade i)).sum = bsum n f := by
  rw [sum_order, bsum_eq_sum]; exact perm_sum (h.2.map f)

theorem pos_blade {N : Nat} {blade : Nat → BitVec n} (h : IsOrder N blade) {i : Nat} (hi : i < N) :
    pos N blade (blade i) = i := by
  have hl : i < (order N blade).length := by simp [order, hi]
  have := List.Nodup.idxOf_getElem h.1 i hl
  simp only [order, List.getElem_map, List.getElem_range] at this
  exact this

theorem pos_lt {N : Nat} {blade : Nat → BitVec n} (h : IsOrder N blade) (a : BitVec n) :
    pos N blade a < N := by
  have hm : a ∈ order N blade := (h.2.mem_iff).2 (mem_allBlades a)
  have := List.idxOf_lt_length_of_mem hm
  simpa [pos, order] using this

theorem blade_pos {N : Nat} {blade : Nat → BitVec n} (h : IsOrder N blade) (a : BitVec n) :
    blade (pos N blade a) = a := by
  have hm : a ∈ order N blade := (h.2.mem_iff).2 (mem_allBlades a)
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < N ∧ blade i = a := by simpa [order] using hm
  rw [pos_blade h hi]

/-- Row `c` of a plan, as `(ia, ib, coef)` entries in order. -/
def rowList (p : Plan) (c : Nat) : List (Nat × Nat × Rat) :=
  (List.range' (rowS p c) (rowE p c - rowS p c)).map fun t => (iaAt p t, ibAt p t, coefAt p t)

/-- Row `c` of the spec table `e_a ⋆ e_b = k(a,b) e_{a⊕b}` in storage order: every operand pair
landing on `blade c` with a nonzero coefficient, first operand major. -/
def specRow (N : Nat) (blade : Nat → BitVec n) (k : BitVec n → BitVec n → Rat) (c : Nat) :
    List (Nat × Nat × Rat) :=
  (List.range N).flatMap fun ia => (List.range N).filterMap fun ib =>
    if blade ia ^^^ blade ib = blade c ∧ k (blade ia) (blade ib) ≠ 0 then
      some (ia, ib, k (blade ia) (blade ib)) else none

/-- **A plan is the spec table** `k` in the storage order `blade`: it is well formed
(`Aligned`, `Coded`) and each of its `N` rows lists exactly the spec's contributions.
Decidable, so `decide +kernel` checks it for a concrete space. -/
def IsSpecPlan (p : Plan) (N : Nat) (blade : Nat → BitVec n) (k : BitVec n → BitVec n → Rat) : Prop :=
  p.Aligned ∧ Coded p = true ∧ ∀ c < N, rowList p c = specRow N blade k c

instance (p : Plan) (N : Nat) (blade : Nat → BitVec n) (k : BitVec n → BitVec n → Rat) :
    Decidable (IsSpecPlan p N blade k) := by
  unfold IsSpecPlan; exact inferInstance

/-- `Σ r · F a b` over a list of entries. -/
def lsum (F : Nat → Nat → Rat) : List (Nat × Nat × Rat) → Rat
  | [] => 0
  | (a, b, r) :: l => r * F a b + lsum F l

theorem lsum_append (F : Nat → Nat → Rat) (l₁ l₂ : List (Nat × Nat × Rat)) :
    lsum F (l₁ ++ l₂) = lsum F l₁ + lsum F l₂ := by
  induction l₁ with
  | nil => simp [lsum]; grind
  | cons e l ih => obtain ⟨a, b, r⟩ := e; simp [lsum, ih]; grind

theorem lsum_flatMap (F : Nat → Nat → Rat) (L : List Nat) (g : Nat → List (Nat × Nat × Rat)) :
    lsum F (L.flatMap g) = (L.map fun i => lsum F (g i)).sum := by
  induction L with
  | nil => rfl
  | cons i L ih => simp [List.flatMap_cons, lsum_append, ih]

theorem lsum_filterMap (F : Nat → Nat → Rat) (L : List Nat) (g : Nat → Option (Nat × Nat × Rat)) :
    lsum F (L.filterMap g) = (L.map fun i => match g i with
      | some (a, b, r) => r * F a b | none => 0).sum := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    cases h : g i with
    | none => simp [List.filterMap_cons_none h, ih, h]; grind
    | some e => obtain ⟨a, b, r⟩ := e; simp [List.filterMap_cons_some h, lsum, ih, h]

theorem isum_rowList (p : Plan) (c : Nat) (F : Nat → Nat → Rat) :
    isum (rowS p c) (rowE p c) (fun u => coefAt p u * F (iaAt p u) (ibAt p u)) = lsum F (rowList p c) := by
  unfold isum rowList
  generalize List.range' (rowS p c) (rowE p c - rowS p c) = L
  induction L with
  | nil => rfl
  | cons t L ih => simp [lsum, ih]

/-- The spec row's sum is the twisted convolution. -/
theorem lsum_specRow {N : Nat} {blade : Nat → BitVec n} (h : IsOrder N blade) (k : BitVec n → BitVec n → Rat)
    (X Y : BitVec n → Rat) (c : Nat) :
    lsum (fun a b => X (blade a) * Y (blade b)) (specRow N blade k c) = twist k X Y (blade c) := by
  unfold specRow twist
  rw [lsum_flatMap]
  have inner : ∀ ia, lsum (fun a b => X (blade a) * Y (blade b)) ((List.range N).filterMap fun ib =>
      if blade ia ^^^ blade ib = blade c ∧ k (blade ia) (blade ib) ≠ 0 then
        some (ia, ib, k (blade ia) (blade ib)) else none)
      = X (blade ia) * Y (blade ia ^^^ blade c) * k (blade ia) (blade ia ^^^ blade c) := by
    intro ia
    rw [lsum_filterMap]
    let G : BitVec n → Rat := fun B =>
      if B = blade ia ^^^ blade c then k (blade ia) B * (X (blade ia) * Y B) else 0
    have hG : ∀ ib, (match (if blade ia ^^^ blade ib = blade c ∧ k (blade ia) (blade ib) ≠ 0 then
        some (ia, ib, k (blade ia) (blade ib)) else none) with
        | some (a, b, r) => r * (X (blade a) * Y (blade b)) | none => 0) = G (blade ib) := by
      intro ib
      simp only [G]
      have hx : (blade ia ^^^ blade ib = blade c) ↔ (blade ib = blade ia ^^^ blade c) := by
        constructor
        · intro e; rw [← e, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
        · intro e; rw [e, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
      by_cases h1 : blade ib = blade ia ^^^ blade c
      · rw [ite_eq_left h1]
        by_cases hk : k (blade ia) (blade ib) = 0
        · rw [ite_eq_right (by intro ⟨_, h⟩; exact h hk)]; simp [hk]
        · rw [ite_eq_left ⟨hx.2 h1, hk⟩]
      · rw [ite_eq_right h1, ite_eq_right (by intro ⟨e, _⟩; exact h1 (hx.1 e))]
    rw [List.map_congr_left (fun ib _ => hG ib), bsum_order h G]
    simp only [G]
    rw [bsum_ite_eq]; grind
  rw [List.map_congr_left (fun ia _ => inner ia)]
  exact bsum_order h (fun A => X A * Y (A ^^^ blade c) * k A (A ^^^ blade c))

/-- Read raw storage as spec coefficients: the coefficient of blade `a` sits at its
storage position. -/
def coeffs (N : Nat) (blade : Nat → BitVec n) (x : Packed.Arr Rat) : BitVec n → Rat :=
  fun a => rd x (pos N blade a)

/-- **The interpreter computes the spec product.** If a plan is the spec table `k`
in a storage order, then running it (`Plan.eval₂`, the loop every reference kernel
executes) yields, read back as coefficients, the twisted convolution
`(x ⋆ y)(c) = Σ_a x(a) y(a⊕c) k(a, a⊕c)` of the operands. -/
theorem eval₂_eq_twist {N na nb : Nat} {blade : Nat → BitVec n} {k : BitVec n → BitVec n → Rat} {p : Plan}
    (ho : IsOrder N blade) (hp : IsSpecPlan p N blade k) (x : Values Rat na) (y : Values Rat nb) :
    coeffs N blade (p.eval₂ x y : Values Rat N).data =
      twist k (coeffs N blade x.data) (coeffs N blade y.data) := by
  funext C
  obtain ⟨ha, hc, hrows⟩ := hp
  have hC := pos_lt ho C
  have hread : coeffs N blade (p.eval₂ x y : Values Rat N).data C =
      (p.eval₂ x y : Values Rat N).get ⟨pos N blade C, hC⟩ := by
    unfold coeffs rd; rw [dite_eq_left]; rfl
  rw [hread, get_eval₂ p ha, row₂_rat p ha hc]
  have hF : ∀ a b, a < N → b < N → rd x.data a * rd y.data b =
      coeffs N blade x.data (blade a) * coeffs N blade y.data (blade b) := by
    intro a b ha hb; simp [coeffs, pos_blade ho ha, pos_blade ho hb]
  rw [isum_rowList p _ (fun a b => rd x.data a * rd y.data b), hrows _ hC]
  rw [show lsum (fun a b => rd x.data a * rd y.data b) (specRow N blade k (pos N blade C)) =
      lsum (fun a b => coeffs N blade x.data (blade a) * coeffs N blade y.data (blade b))
        (specRow N blade k (pos N blade C)) from ?_]
  · rw [lsum_specRow ho, blade_pos ho, show (Coeff.zero : Rat) = 0 from rfl, Rat.zero_add]
  · -- every entry of a spec row has in-range positions
    unfold specRow
    rw [lsum_flatMap, lsum_flatMap]
    refine congrArg List.sum (List.map_congr_left fun ia hia => ?_)
    rw [lsum_filterMap, lsum_filterMap]
    refine congrArg List.sum (List.map_congr_left fun ib hib => ?_)
    split <;> simp_all <;> grind

end Spec

/-! ## The reference kernels

`refBin V op la lb lc` runs `eval₂` on the cached plan, which is logically `build`. So a
decidable check on the built plan carries `eval₂_eq_twist` to the kernel itself. -/

section Reference

open Grassmann.Spec

variable {n : Nat}

/-- Julia's `indexbasis` storage order of a full multivector, as blades. -/
def fullOrder (n : Nat) (i : Nat) : BitVec n := BitVec.ofNat n ((Leibniz.indexBasisAll n)[i]!).toNat

/-- The plan that `refBin V op la lb lc` runs is the spec table `k` in storage order
`blade`. One `decide +kernel` per space and operation. -/
def RefSpec (V : TensorBundle) (op : BinOp) (la lb lc : Layout) (N : Nat)
    (blade : Nat → BitVec n) (k : BitVec n → BitVec n → Rat) : Bool :=
  match build { V, op := .bin op, la, lb, lc } with
  | .ok p => decide (IsSpecPlan p N blade k)
  | .error _ => false

/-- **The reference binary kernel computes the spec product**, at `Rat`, whenever its
plan checks out as the spec table in a storage order that is a bijection onto the blades. -/
theorem refBin_eq_twist {V : TensorBundle} {op : BinOp} {la lb lc : Layout} {N : Nat}
    {blade : Nat → BitVec n} {k : BitVec n → BitVec n → Rat}
    (hN : lc.size V.n = N) (ho : IsOrder N blade) (hs : RefSpec V op la lb lc N blade k = true)
    (x : Values Rat (la.size V.n)) (y : Values Rat (lb.size V.n)) :
    coeffs N blade (refBin V op la lb lc x y).data =
      twist k (coeffs N blade x.data) (coeffs N blade y.data) := by
  subst hN
  unfold RefSpec at hs
  unfold refBin plan
  split at hs
  · rename_i p hp
    rw [hp]
    exact eval₂_eq_twist ho (of_decide_eq_true hs) x y
  · cases hs

/-! ### Per space: the geometric product kernel of `ℝ3`, `STA`, `PGA3` and `D!"1,2,-3"` -/

theorem fullOrder3 : IsOrder (2 ^ 3) (fullOrder 3) := by decide +kernel
theorem fullOrder4 : IsOrder (2 ^ 4) (fullOrder 4) := by decide +kernel

theorem R3_refMul_spec : RefSpec ℝ3 .mul .full .full .full (2 ^ 3) (fullOrder 3) (coef (gEuclid 3)) = true := by
  decide +kernel

/-- `ℝ3`'s reference geometric-product kernel, run on any two full multivectors over
`Rat`, returns their spec (Clifford) product. -/
theorem R3_refMul (x y : Values Rat (Layout.full.size ℝ3.n)) :
    coeffs (2 ^ 3) (fullOrder 3) (refBin ℝ3 .mul .full .full .full x y).data =
      twist (coef (gEuclid 3)) (coeffs (2 ^ 3) (fullOrder 3) x.data) (coeffs (2 ^ 3) (fullOrder 3) y.data) :=
  refBin_eq_twist (by decide) fullOrder3 R3_refMul_spec x y

theorem R3_refWedge_spec : RefSpec ℝ3 .wedge .full .full .full (2 ^ 3) (fullOrder 3) (wcoef (R := Rat)) = true := by
  decide +kernel

/-- `ℝ3`'s reference exterior-product kernel returns the spec wedge. -/
theorem R3_refWedge (x y : Values Rat (Layout.full.size ℝ3.n)) :
    coeffs (2 ^ 3) (fullOrder 3) (refBin ℝ3 .wedge .full .full .full x y).data =
      twist (wcoef (R := Rat)) (coeffs (2 ^ 3) (fullOrder 3) x.data) (coeffs (2 ^ 3) (fullOrder 3) y.data) :=
  refBin_eq_twist (by decide) fullOrder3 R3_refWedge_spec x y

theorem D123_refMul_spec : RefSpec D!"1,2,-3" .mul .full .full .full (2 ^ 3) (fullOrder 3) (coef gD123) = true := by
  decide +kernel

/-- The reference geometric-product kernel of the diagonal metric `diag(1,2,-3)`. -/
theorem D123_refMul (x y : Values Rat (Layout.full.size D!"1,2,-3".n)) :
    coeffs (2 ^ 3) (fullOrder 3) (refBin D!"1,2,-3" .mul .full .full .full x y).data =
      twist (coef gD123) (coeffs (2 ^ 3) (fullOrder 3) x.data) (coeffs (2 ^ 3) (fullOrder 3) y.data) :=
  refBin_eq_twist (by decide) fullOrder3 D123_refMul_spec x y

theorem STA_refMul_spec : RefSpec STA .mul .full .full .full (2 ^ 4) (fullOrder 4) (coef gSTA) = true := by
  decide +kernel

/-- Spacetime algebra's reference geometric-product kernel. -/
theorem STA_refMul (x y : Values Rat (Layout.full.size STA.n)) :
    coeffs (2 ^ 4) (fullOrder 4) (refBin STA .mul .full .full .full x y).data =
      twist (coef gSTA) (coeffs (2 ^ 4) (fullOrder 4) x.data) (coeffs (2 ^ 4) (fullOrder 4) y.data) :=
  refBin_eq_twist (by decide) fullOrder4 STA_refMul_spec x y

theorem PGA3_refMul_spec : RefSpec PGA3 .mul .full .full .full (2 ^ 4) (fullOrder 4) (coef (gPGA 4)) = true := by
  decide +kernel

/-- 3D projective geometric algebra's reference geometric-product kernel (degenerate metric). -/
theorem PGA3_refMul (x y : Values Rat (Layout.full.size PGA3.n)) :
    coeffs (2 ^ 4) (fullOrder 4) (refBin PGA3 .mul .full .full .full x y).data =
      twist (coef (gPGA 4)) (coeffs (2 ^ 4) (fullOrder 4) x.data) (coeffs (2 ^ 4) (fullOrder 4) y.data) :=
  refBin_eq_twist (by decide) fullOrder4 PGA3_refMul_spec x y

end Reference

end Grassmann.Proofs.Interp

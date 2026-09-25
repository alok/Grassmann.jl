import Dendriform.Arith

/-!
# Arithmetree is a dendriform algebra

Loday ("Arithmetree", J. Algebra 258 (2002)) shows that planar binary trees with the
half-sums `⊣`, `⊢` form a **dendriform algebra**, i.e. for trees of positive degree

1. `(x ⊣ y) ⊣ z = x ⊣ (y + z)`
2. `(x ⊢ y) ⊣ z = x ⊢ (y ⊣ z)`
3. `(x + y) ⊢ z = x ⊢ (y ⊢ z)`

where `+ = ⊣ + ⊢` and every operation is extended bilinearly to formal sums. Summing the
three axioms makes `+` associative. Julia's `Dendriform.jl` relies on these identities
(e.g. `Y_p + Y_q = Y_{p+q}`) but never states them.

Here they are **theorems about the very functions that reproduce Julia's rows**, stated
up to reordering (`List.Perm`), for all trees, by one strong induction on the total
degree: the associativity of `+` at total degree `n` needs axioms 1-3 at degree `n`,
which need associativity only at smaller degrees. The involution `σ` is proved to be an
anti-automorphism (`σ(x ⊣ y) ≅ σy ⊢ σx`, `σ(x + y) ≅ σy + σx`, DF test/runtests.jl:56).
-/

namespace Dendriform

open List

/-! ## Permutation bookkeeping for bilinear sums -/

section Perm

variable {α β γ : Type}

/-- `flatMap` respects pointwise equality on the members. -/
theorem flatMap_congr_mem {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [flatMap_cons, h a (by simp), ih fun b hb => h b (by simp [hb])]

/-- `flatMap` respects pointwise permutation. -/
theorem perm_flatMap_congr {l : List α} {f g : α → List β} (h : ∀ a ∈ l, (f a).Perm (g a)) :
    (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => exact .refl _
  | cons a l ih =>
    simp only [flatMap_cons]
    exact (h a (by simp)).append (ih fun b hb => h b (by simp [hb]))

/-- A sum of concatenations is a concatenation of sums (up to order). -/
theorem flatMap_append_perm (l : List α) (f g : α → List β) :
    (l.flatMap fun a => f a ++ g a).Perm (l.flatMap f ++ l.flatMap g) := by
  induction l with
  | nil => exact .refl _
  | cons a l ih =>
    simp only [flatMap_cons, append_assoc]
    refine (Perm.append_left _ (Perm.append_left _ ih)).trans ?_
    exact Perm.append_left _ (perm_append_comm_assoc _ _ _)

/-- Double sums can be swapped: `Σ_a Σ_b f a b ≅ Σ_b Σ_a f a b`. -/
theorem flatMap_swap_perm (l₁ : List α) (l₂ : List β) (f : α → β → List γ) :
    (l₁.flatMap fun a => l₂.flatMap (f a)).Perm (l₂.flatMap fun b => l₁.flatMap (f · b)) := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    simp only [flatMap_cons]
    exact (Perm.append_left _ ih).trans (flatMap_append_perm l₂ (f a) _).symm

/-- `flatMap_swap_perm` for singleton summands. -/
theorem map_swap_perm (l₁ : List α) (l₂ : List β) (f : α → β → γ) :
    (l₁.flatMap fun a => l₂.map (f a)).Perm (l₂.flatMap fun b => l₁.map (f · b)) := by
  have := flatMap_swap_perm l₁ l₂ fun a b => [f a b]
  simpa [flatMap_singleton', ← map_eq_flatMap] using this

end Perm

namespace Tree

/-! ## Unfolding lemmas for non-leaf arguments -/

theorem dashv_node (a b t : Tree) (ht : t ≠ leaf) : dashv (node a b) t = (sum b t).map (node a) := by
  cases t with
  | leaf => exact absurd rfl ht
  | node => rfl

theorem vdash_node (x c d : Tree) (hx : x ≠ leaf) : vdash x (node c d) = (sum x c).map (node · d) := by
  cases x with
  | leaf => exact absurd rfl hx
  | node => rfl

theorem sum_of_ne_leaf {x y : Tree} (hx : x ≠ leaf) (hy : y ≠ leaf) :
    sum x y = dashv x y ++ vdash x y := by
  cases x with
  | leaf => exact absurd rfl hx
  | node => cases y with
    | leaf => exact absurd rfl hy
    | node => rfl

/-- Associativity of `+` at `(x, y, z)`, bilinearly extended: `(x + y) + z ≅ x + (y + z)`. -/
def AssocAt (x y z : Tree) : Prop :=
  ((sum x y).flatMap (sum · z)).Perm ((sum y z).flatMap (sum x ·))

/-! ## The three axioms -/

/-- Dendriform axiom 1, `(x ⊣ y) ⊣ z ≅ x ⊣ (y + z)`, from associativity at the smaller
triple `(right x, y, z)`. -/
theorem dashv_dashv_of (a b y z : Tree) (hy : y ≠ leaf) (hz : z ≠ leaf) (h : AssocAt b y z) :
    ((dashv (node a b) y).flatMap (dashv · z)).Perm ((sum y z).flatMap (dashv (node a b) ·)) := by
  rw [dashv_node a b y hy, flatMap_map]
  have hl : ∀ s ∈ sum b y, dashv (node a s) z = (sum s z).map (node a) :=
    fun s _ => dashv_node a s z hz
  have hr : ∀ t ∈ sum y z, dashv (node a b) t = (sum b t).map (node a) :=
    fun t ht => dashv_node a b t (ne_leaf_of_mem_sum ht hy)
  rw [flatMap_congr_mem hl, flatMap_congr_mem hr, ← map_flatMap, ← map_flatMap]
  exact h.map _

/-- Dendriform axiom 2, `(x ⊢ y) ⊣ z ≅ x ⊢ (y ⊣ z)`: a swap of a double sum. -/
theorem vdash_dashv (x c d z : Tree) (hx : x ≠ leaf) (hz : z ≠ leaf) :
    ((vdash x (node c d)).flatMap (dashv · z)).Perm
      ((dashv (node c d) z).flatMap (vdash x ·)) := by
  rw [vdash_node x c d hx, dashv_node c d z hz, flatMap_map, flatMap_map]
  have hl : ∀ s ∈ sum x c, dashv (node s d) z = (sum d z).map (node s) :=
    fun s _ => dashv_node s d z hz
  have hr : ∀ t ∈ sum d z, vdash x (node c t) = (sum x c).map (node · t) :=
    fun t _ => vdash_node x c t hx
  rw [flatMap_congr_mem hl, flatMap_congr_mem hr]
  exact map_swap_perm _ _ node

/-- Dendriform axiom 3, `(x + y) ⊢ z ≅ x ⊢ (y ⊢ z)`, from associativity at the smaller
triple `(x, y, left z)`. -/
theorem sum_vdash_of (x y e f : Tree) (hx : x ≠ leaf) (h : AssocAt x y e) :
    ((sum x y).flatMap (vdash · (node e f))).Perm ((vdash y (node e f)).flatMap (vdash x ·)) := by
  cases y with
  | leaf => simp [AssocAt] at h ⊢
  | node c d =>
    rw [vdash_node (node c d) e f (by simp), flatMap_map]
    have hl : ∀ s ∈ sum x (node c d), vdash s (node e f) = (sum s e).map (node · f) :=
      fun s hs => vdash_node s e f (ne_leaf_of_mem_sum hs hx)
    have hr : ∀ t ∈ sum (node c d) e, vdash x (node t f) = (sum x t).map (node · f) :=
      fun t _ => vdash_node x t f hx
    rw [flatMap_congr_mem hl, flatMap_congr_mem hr, ← map_flatMap, ← map_flatMap]
    exact h.map _

/-! ## Associativity by strong induction on the total degree -/

theorem assoc_aux (n : Nat) : ∀ x y z : Tree, x.deg + y.deg + z.deg = n → AssocAt x y z := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro x y z hn
  cases x with
  | leaf => simp [AssocAt, flatMap_singleton']
  | node a b =>
  cases y with
  | leaf => simp [AssocAt]
  | node c d =>
  cases z with
  | leaf => simp [AssocAt, flatMap_singleton']
  | node e f =>
  simp only [deg_node] at hn
  let x := node a b
  let y := node c d
  let z := node e f
  have hx : x ≠ leaf := by simp [x]
  have hy : y ≠ leaf := by simp [y]
  have hz : z ≠ leaf := by simp [z]
  -- the three axioms at (x, y, z)
  have A1 := dashv_dashv_of a b y z hy hz (ih _ (by simp [y, z]; omega) b y z rfl)
  have A2 := vdash_dashv x c d z hx hz
  have A3 := sum_vdash_of x y e f hx (ih _ (by simp [x, y]; omega) x y e rfl)
  -- expand the left side: (x + y) + z = (x⊣y)⊣z + (x⊣y)⊢z + (x⊢y)⊣z + (x⊢y)⊢z
  have hL : ((sum x y).flatMap (sum · z)).Perm
      ((dashv x y).flatMap (dashv · z) ++ ((vdash x y).flatMap (dashv · z) ++
        (sum x y).flatMap (vdash · z))) := by
    rw [sum_of_ne_leaf hx hy, flatMap_append, flatMap_append]
    have e1 : ((dashv x y).flatMap (sum · z)).Perm
        ((dashv x y).flatMap (dashv · z) ++ (dashv x y).flatMap (vdash · z)) := by
      refine (perm_flatMap_congr fun s hs => ?_).trans (flatMap_append_perm _ _ _)
      rw [sum_of_ne_leaf ?_ hz]
      exact deg_pos_iff.mp (by rw [deg_of_mem_dashv hs]; simp [x, y]; omega)
    have e2 : ((vdash x y).flatMap (sum · z)).Perm
        ((vdash x y).flatMap (dashv · z) ++ (vdash x y).flatMap (vdash · z)) := by
      refine (perm_flatMap_congr fun s hs => ?_).trans (flatMap_append_perm _ _ _)
      rw [sum_of_ne_leaf ?_ hz]
      exact deg_pos_iff.mp (by rw [deg_of_mem_vdash hs]; simp [x, y]; omega)
    refine (e1.append e2).trans ?_
    simp only [append_assoc]
    exact Perm.append_left _ (perm_append_comm_assoc _ _ _)
  -- expand the right side: x + (y + z) = x⊣(y+z) + x⊢(y⊣z) + x⊢(y⊢z)
  have hR : ((sum y z).flatMap (sum x ·)).Perm
      ((sum y z).flatMap (dashv x ·) ++ ((dashv y z).flatMap (vdash x ·) ++
        (vdash y z).flatMap (vdash x ·))) := by
    have e : (sum y z).flatMap (sum x ·) = (sum y z).flatMap (fun t => dashv x t ++ vdash x t) :=
      flatMap_congr_mem fun t ht => sum_of_ne_leaf hx (ne_leaf_of_mem_sum ht hy)
    rw [e]
    refine (flatMap_append_perm _ _ _).trans ?_
    rw [sum_of_ne_leaf hy hz]
    simp only [flatMap_append, append_assoc]
    exact .refl _
  exact hL.trans ((A1.append (A2.append A3)).trans hR.symm)

/-- **Associativity of the Loday sum**: `(x + y) + z ≅ x + (y + z)` for all trees. -/
theorem sum_assoc (x y z : Tree) : AssocAt x y z := assoc_aux _ x y z rfl

/-- **Dendriform axiom 1**: `(x ⊣ y) ⊣ z ≅ x ⊣ (y + z)`. -/
theorem dashv_dashv (x y z : Tree) (hx : x ≠ leaf) (hy : y ≠ leaf) (hz : z ≠ leaf) :
    ((dashv x y).flatMap (dashv · z)).Perm ((sum y z).flatMap (dashv x ·)) := by
  cases x with
  | leaf => exact absurd rfl hx
  | node a b => exact dashv_dashv_of a b y z hy hz (sum_assoc b y z)

/-- **Dendriform axiom 2**: `(x ⊢ y) ⊣ z ≅ x ⊢ (y ⊣ z)`. -/
theorem vdash_dashv' (x y z : Tree) (hx : x ≠ leaf) (hy : y ≠ leaf) (hz : z ≠ leaf) :
    ((vdash x y).flatMap (dashv · z)).Perm ((dashv y z).flatMap (vdash x ·)) := by
  cases y with
  | leaf => exact absurd rfl hy
  | node c d => exact vdash_dashv x c d z hx hz

/-- **Dendriform axiom 3**: `(x + y) ⊢ z ≅ x ⊢ (y ⊢ z)`. -/
theorem sum_vdash (x y z : Tree) (hx : x ≠ leaf) (hz : z ≠ leaf) :
    ((sum x y).flatMap (vdash · z)).Perm ((vdash y z).flatMap (vdash x ·)) := by
  cases z with
  | leaf => exact absurd rfl hz
  | node e f => exact sum_vdash_of x y e f hx (sum_assoc x y e)

/-! ## The involution is an anti-automorphism -/

/-- `σ` reverses the sum and exchanges `⊣` and `⊢`: `σ(x ⊣ y) ≅ σy ⊢ σx` and
`σ(x + y) ≅ σy + σx`. Proved jointly by induction on the total degree. -/
theorem σ_aux (n : Nat) : ∀ x y : Tree, x.deg + y.deg = n →
    ((sum x y).map σ).Perm (sum y.σ x.σ) ∧ ((dashv x y).map σ).Perm (vdash y.σ x.σ) ∧
      ((vdash x y).map σ).Perm (dashv y.σ x.σ) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro x y hn
  cases x with
  | leaf => cases y <;> simp
  | node a b =>
  cases y with
  | leaf => simp
  | node c d =>
  simp only [deg_node] at hn
  -- σ(x ⊣ y) = σ(b + y) ∨ σa  and  σy ⊢ σx = (σy + σb) ∨ σa
  have hd : ((dashv (node a b) (node c d)).map σ).Perm (vdash (node c d).σ (node a b).σ) := by
    have h := (ih (b.deg + (c.deg + d.deg + 1)) (by omega) b (node c d) (by simp)).1
    have e : ((sum b (node c d)).map (node a)).map σ =
        ((sum b (node c d)).map σ).map (node · a.σ) := by
      simp [map_map, Function.comp_def]
    simp only [σ_node] at h ⊢
    rw [dashv_node_node, vdash_node_node, e]
    exact h.map _
  have hv : ((vdash (node a b) (node c d)).map σ).Perm (dashv (node c d).σ (node a b).σ) := by
    have h := (ih (a.deg + b.deg + 1 + c.deg) (by omega) (node a b) c (by simp)).1
    have e : ((sum (node a b) c).map (node · d)).map σ =
        ((sum (node a b) c).map σ).map (node d.σ) := by
      simp [map_map, Function.comp_def]
    simp only [σ_node] at h ⊢
    rw [vdash_node_node, dashv_node_node, e]
    exact h.map _
  refine ⟨?_, hd, hv⟩
  rw [sum_node_node, map_append, σ_node, σ_node, sum_node_node]
  simp only [σ_node] at hd hv
  exact (hd.append hv).trans perm_append_comm

/-- `σ(x + y) ≅ σ(y) + σ(x)` (DF test/runtests.jl:56, `σ(x+y) == σ(y)+σ(x)`). -/
theorem σ_sum (x y : Tree) : ((sum x y).map σ).Perm (sum y.σ x.σ) := (σ_aux _ x y rfl).1

/-- `σ(x ⊣ y) ≅ σ(y) ⊢ σ(x)`. -/
theorem σ_dashv (x y : Tree) : ((dashv x y).map σ).Perm (vdash y.σ x.σ) := (σ_aux _ x y rfl).2.1

/-- `σ(x ⊢ y) ≅ σ(y) ⊣ σ(x)`. -/
theorem σ_vdash (x y : Tree) : ((vdash x y).map σ).Perm (dashv y.σ x.σ) := (σ_aux _ x y rfl).2.2

end Tree

end Dendriform

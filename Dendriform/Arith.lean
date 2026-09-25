import Dendriform.Tree

/-!
# Loday arithmetic on formal sums of trees

Julia source: DF/arithmetic.jl:87-274. A grove is a formal sum (ordered multiset) of trees;
the dendriform half-sums `⊣`, `⊢`, the sum `+ = ⊣ ∪ ⊢` and Loday's product `*` act on
trees and extend bilinearly. All functions here return **lists in Julia's row order**:
`⊣`, `⊢`, `*` iterate the left operand outermost, `+` the right operand outermost
(DF/arithmetic.jl:226-239, `vcat(ij...)` is column-major).

Julia's degenerate conventions (port-notes §4.4.4, Appendix A #12): `| ⊣ y = 0`,
`x ⊣ | = x`, `x ⊢ | = 0`, `| ⊢ y = y`, `| + y = y`, `x + | = x`, `| * y = 0`,
`[1] * y = y`. Inside `*` Julia's zero grove doubles as `|` (`0 ⊢ y = y`, `z ⊣ 0 = z`);
`mul` spells those two cases out, so it agrees with Julia row for row.

Structural recursion throughout (the sum is structural in the left tree with an inner
structural recursion on the right tree), so every definition reduces in the kernel and
small identities are checked by `decide`.
-/

namespace Dendriform

namespace Tree

/-- The sum `x + y` for `x = a ∨ b`, by structural recursion on `y`, given `sb = (b + ·)`:
`x + | = x`, and `x + (c ∨ d) = (a ∨ (b + y)) ++ ((x + c) ∨ d)`. -/
def sumAux (x a : Tree) (sb : Tree → List Tree) : Tree → List Tree
  | leaf => [x]
  | node c d => (sb (node c d)).map (node a) ++ (sumAux x a sb c).map (node · d)

/-- Julia `PBTree + PBTree` (DF/arithmetic.jl:226-243): `| + y = y`, `x + | = x`, and
`x + y = (x ⊣ y) ++ (x ⊢ y)` otherwise. -/
def sum : Tree → Tree → List Tree
  | leaf => fun y => [y]
  | node a b => sumAux (node a b) a (sum b)

/-- Julia `PBTree ⊣ PBTree` (DF/arithmetic.jl:94-106): `| ⊣ y = 0`, `x ⊣ | = x`, and
`(a ∨ b) ⊣ y = a ∨ (b + y)`. -/
def dashv : Tree → Tree → List Tree
  | leaf, _ => []
  | node a b, leaf => [node a b]
  | node a b, node c d => (sum b (node c d)).map (node a)

/-- Julia `PBTree ⊢ PBTree` (DF/arithmetic.jl:160-172): `x ⊢ | = 0`, `| ⊢ y = y`, and
`x ⊢ (c ∨ d) = (x + c) ∨ d`. -/
def vdash : Tree → Tree → List Tree
  | _, leaf => []
  | leaf, node c d => [node c d]
  | node a b, node c d => (sum (node a b) c).map (node · d)

@[simp] theorem sum_leaf_left (y : Tree) : sum leaf y = [y] := rfl
@[simp] theorem sum_leaf_right (x : Tree) : sum x leaf = [x] := by cases x <;> rfl

theorem sum_node_node (a b c d : Tree) :
    sum (node a b) (node c d) = dashv (node a b) (node c d) ++ vdash (node a b) (node c d) := rfl

@[simp] theorem dashv_leaf_left (y : Tree) : dashv leaf y = [] := rfl
@[simp] theorem vdash_leaf_right (x : Tree) : vdash x leaf = [] := by cases x <;> rfl
@[simp] theorem dashv_node_leaf (a b : Tree) : dashv (node a b) leaf = [node a b] := rfl
@[simp] theorem vdash_leaf_node (c d : Tree) : vdash leaf (node c d) = [node c d] := rfl
@[simp] theorem dashv_node_node (a b c d : Tree) :
    dashv (node a b) (node c d) = (sum b (node c d)).map (node a) := rfl
@[simp] theorem vdash_node_node (a b c d : Tree) :
    vdash (node a b) (node c d) = (sum (node a b) c).map (node · d) := rfl

/-- **Degree homomorphism** of the sum: every tree of `x + y` has degree
`deg x + deg y`. -/
theorem deg_of_mem_sum : ∀ {x y t : Tree}, t ∈ sum x y → t.deg = x.deg + y.deg := by
  intro x
  induction x with
  | leaf => intro y t h; simp at h; simp [h]
  | node a b _ ihb =>
    intro y
    induction y with
    | leaf => intro t h; simp at h; simp [h]
    | node c d ihc _ =>
      intro t h
      rw [sum_node_node, dashv_node_node, vdash_node_node, List.mem_append,
        List.mem_map, List.mem_map] at h
      rcases h with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
      · have := ihb hs; simp at this ⊢; omega
      · have := ihc hs; simp at this ⊢; omega

theorem deg_of_mem_dashv {x y t : Tree} (h : t ∈ dashv x y) : t.deg = x.deg + y.deg := by
  cases x with
  | leaf => simp at h
  | node a b =>
    cases y with
    | leaf => simp at h; simp [h]
    | node c d =>
      rw [dashv_node_node, List.mem_map] at h
      obtain ⟨s, hs, rfl⟩ := h
      have := deg_of_mem_sum hs; simp at this ⊢; omega

theorem deg_of_mem_vdash {x y t : Tree} (h : t ∈ vdash x y) : t.deg = x.deg + y.deg := by
  cases y with
  | leaf => simp at h
  | node c d =>
    cases x with
    | leaf => simp at h; simp [h]
    | node a b =>
      rw [vdash_node_node, List.mem_map] at h
      obtain ⟨s, hs, rfl⟩ := h
      have := deg_of_mem_sum hs; simp at this ⊢; omega

theorem ne_leaf_of_mem_sum {x y t : Tree} (h : t ∈ sum x y) (hx : x ≠ leaf) : t ≠ leaf := by
  have := deg_of_mem_sum h
  have := deg_pos_iff.mpr hx
  exact deg_pos_iff.mp (by omega)

theorem ne_leaf_of_mem_sum' {x y t : Tree} (h : t ∈ sum x y) (hy : y ≠ leaf) : t ≠ leaf := by
  have := deg_of_mem_sum h
  have := deg_pos_iff.mpr hy
  exact deg_pos_iff.mp (by omega)

end Tree

/-! ## Bilinear extensions (Julia's grove methods) -/

/-- Julia `Grove ⊣ Grove` rows (DF/arithmetic.jl:130-139): `x`-major concatenation of the
tree products. (Julia's grove-level shortcuts for degree-0 operands live in
`Dendriform.Julia`.) -/
def dashvL (xs ys : List Tree) : List Tree := xs.flatMap fun x => ys.flatMap (Tree.dashv x)

/-- Julia `Grove ⊢ Grove` rows (DF/arithmetic.jl:196-205), `x`-major. -/
def vdashL (xs ys : List Tree) : List Tree := xs.flatMap fun x => ys.flatMap (Tree.vdash x)

/-- Julia `Grove + Grove` rows (DF/arithmetic.jl:226-239): **`y`-major** (`vcat(ij...)`
on the `lx × ly` block matrix is column-major). -/
def sumL (xs ys : List Tree) : List Tree := ys.flatMap fun y => xs.flatMap fun x => Tree.sum x y

namespace Tree

/-- Julia `PBTree * Grove` (DF/arithmetic.jl:252-256): `| * y = 0`, `[1] * y = y`, and
`(l ∨ r) * y = ((l * y) ⊢ y) ⊣ (r * y)`, where Julia's zero grove `| * y` acts as the
unit of `⊢` on the left and of `⊣` on the right. Structural in the tree. -/
def mul : Tree → List Tree → List Tree
  | leaf, _ => []
  | node leaf leaf, ys => ys
  | node l r, ys =>
    let L := match l with
      | leaf => ys
      | node _ _ => vdashL (mul l ys) ys
    match r with
    | leaf => L
    | node _ _ => dashvL L (mul r ys)

end Tree

/-- Julia `Grove * Grove` rows (DF/arithmetic.jl:258-266): `x`-major. -/
def mulL (xs ys : List Tree) : List Tree := xs.flatMap fun x => Tree.mul x ys

/-! ## Degree homomorphisms of the bilinear operations -/

section Degrees

variable {a b : Nat} {xs ys : List Tree}

theorem deg_of_mem_dashvL (hx : ∀ x ∈ xs, x.deg = a) (hy : ∀ y ∈ ys, y.deg = b)
    {t : Tree} (h : t ∈ dashvL xs ys) : t.deg = a + b := by
  simp only [dashvL, List.mem_flatMap] at h
  obtain ⟨x, hxm, y, hym, ht⟩ := h
  rw [Tree.deg_of_mem_dashv ht, hx x hxm, hy y hym]

theorem deg_of_mem_vdashL (hx : ∀ x ∈ xs, x.deg = a) (hy : ∀ y ∈ ys, y.deg = b)
    {t : Tree} (h : t ∈ vdashL xs ys) : t.deg = a + b := by
  simp only [vdashL, List.mem_flatMap] at h
  obtain ⟨x, hxm, y, hym, ht⟩ := h
  rw [Tree.deg_of_mem_vdash ht, hx x hxm, hy y hym]

theorem deg_of_mem_sumL (hx : ∀ x ∈ xs, x.deg = a) (hy : ∀ y ∈ ys, y.deg = b)
    {t : Tree} (h : t ∈ sumL xs ys) : t.deg = a + b := by
  simp only [sumL, List.mem_flatMap] at h
  obtain ⟨y, hym, x, hxm, ht⟩ := h
  rw [Tree.deg_of_mem_sum ht, hx x hxm, hy y hym]

/-- **Loday's degree law for the product**: `deg (x * y) = deg x · deg y`. -/
theorem Tree.deg_of_mem_mul (hy : ∀ y ∈ ys, y.deg = b) :
    ∀ (x t : Tree), t ∈ Tree.mul x ys → t.deg = x.deg * b
  | .leaf, t, h => by simp [Tree.mul] at h
  | .node .leaf .leaf, t, h => by simp only [Tree.mul] at h; simp [hy t h]
  | .node (.node l₁ l₂) .leaf, t, h => by
    simp only [Tree.mul] at h
    have ih := Tree.deg_of_mem_mul hy (.node l₁ l₂)
    have := deg_of_mem_vdashL (a := (Tree.node l₁ l₂).deg * b) (fun s hm => ih s hm) hy h
    rw [this]; simp only [Tree.deg_node, Tree.deg_leaf, Nat.add_mul, Nat.one_mul, Nat.zero_mul]; omega
  | .node .leaf (.node r₁ r₂), t, h => by
    simp only [Tree.mul] at h
    have ih := Tree.deg_of_mem_mul hy (.node r₁ r₂)
    have := deg_of_mem_dashvL hy (fun s hm => ih s hm) h
    rw [this]; simp only [Tree.deg_node, Tree.deg_leaf, Nat.add_mul, Nat.one_mul, Nat.zero_mul]; omega
  | .node (.node l₁ l₂) (.node r₁ r₂), t, h => by
    simp only [Tree.mul] at h
    have ihl := Tree.deg_of_mem_mul hy (.node l₁ l₂)
    have ihr := Tree.deg_of_mem_mul hy (.node r₁ r₂)
    have hL := fun s (hs : s ∈ vdashL (Tree.mul (.node l₁ l₂) ys) ys) =>
      deg_of_mem_vdashL (a := (Tree.node l₁ l₂).deg * b) (fun s hm => ihl s hm) hy hs
    have := deg_of_mem_dashvL hL (fun s hm => ihr s hm) h
    rw [this]; simp only [Tree.deg_node, Nat.add_mul, Nat.one_mul]; omega

theorem deg_of_mem_mulL (hx : ∀ x ∈ xs, x.deg = a) (hy : ∀ y ∈ ys, y.deg = b)
    {t : Tree} (h : t ∈ mulL xs ys) : t.deg = a * b := by
  simp only [mulL, List.mem_flatMap] at h
  obtain ⟨x, hxm, ht⟩ := h
  rw [Tree.deg_of_mem_mul hy x t ht, hx x hxm]

end Degrees

end Dendriform

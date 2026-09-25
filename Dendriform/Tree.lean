import AbstractLattices

/-!
# Planar binary trees and Loday names

Julia source: `Dendriform.jl` (DF), `src/Dendriform.jl`, `src/arithmetic.jl`,
`src/poset.jl`, `src/morphism.jl`. Julia's `PBTree` (DF/Dendriform.jl:27-30) stores a
tree as its **Loday name**: the word of length `n` (the degree = number of internal
vertices) whose `k`-th letter is the degree of the subtree rooted at the `k`-th internal
vertex in in-order, `ω(τ) = [ω(τ_l); n; ω(τ_r)]` (port-notes §3.4). Julia accepts any
`Vector{Int}` as a tree and never validates it.

Lean design:
* `Tree` is the inductive planar binary tree; grafting `l ∨ r` (Julia `∨`/`graft`,
  DF/arithmetic.jl:38-57) *is* the constructor `node`, `left`/`right` are total projections
  and every name produced is valid by construction. `Tree.name` and `Tree.ofName?`
  convert to and from Loday names (the latter rejects the invalid words Julia accepts).
* `PBTree n := {t : Tree // t.deg = n}` is the degree-indexed facade: `graft` has type
  `PBTree a → PBTree b → PBTree (a + b + 1)`, and the proofs are erased at runtime.
* Grafting is Julia's `∨`, which extends `AbstractLattices.vee` (DF/arithmetic.jl:5), so
  `Tree` gets an `HVee` instance.
-/

namespace Dendriform

open AbstractLattices

/-- A planar binary tree. `leaf` is Julia's degree-0 tree `|` (empty name); `node l r`
is the graft `l ∨ r` (DF/arithmetic.jl:38-47). -/
inductive Tree where
  /-- the tree `|` with no internal vertex -/
  | leaf
  /-- the graft `l ∨ r`: a new root with left subtree `l` and right subtree `r` -/
  | node (l r : Tree)
  deriving DecidableEq, Inhabited, Hashable, Repr, Ord

namespace Tree

/-- The degree: number of internal vertices (Julia `degr`, DF/Dendriform.jl:28). The tree
has `deg + 1` leaves. -/
def deg : Tree → Nat
  | leaf => 0
  | node l r => l.deg + r.deg + 1

@[simp] theorem deg_leaf : leaf.deg = 0 := rfl
@[simp] theorem deg_node (l r : Tree) : (node l r).deg = l.deg + r.deg + 1 := rfl

theorem deg_pos_iff {t : Tree} : 0 < t.deg ↔ t ≠ leaf := by
  cases t <;> simp

/-- Julia `graft(l, r) = l ∨ r` (DF/arithmetic.jl:38-57). -/
@[inline] def graft (l r : Tree) : Tree := node l r

instance : HVee Tree Tree Tree := ⟨graft⟩

/-- Julia `left(t)`: the subtree left of the root (`|` for `|`, DF/arithmetic.jl:66-72). -/
def left : Tree → Tree
  | leaf => leaf
  | node l _ => l

/-- Julia `right(t)`: the subtree right of the root (DF/arithmetic.jl:79-85). -/
def right : Tree → Tree
  | leaf => leaf
  | node _ r => r

@[simp] theorem left_node (l r : Tree) : (node l r).left = l := rfl
@[simp] theorem right_node (l r : Tree) : (node l r).right = r := rfl

/-- The involution `σ` (DF/Dendriform.jl:216-219): mirror the tree, which reverses its
Loday name. -/
def σ : Tree → Tree
  | leaf => leaf
  | node l r => node r.σ l.σ

@[simp] theorem σ_leaf : σ leaf = leaf := rfl
@[simp] theorem σ_node (l r : Tree) : σ (node l r) = node r.σ l.σ := rfl
@[simp] theorem σ_σ (t : Tree) : t.σ.σ = t := by induction t <;> simp [*]
@[simp] theorem deg_σ (t : Tree) : t.σ.deg = t.deg := by induction t <;> simp [*]; omega

theorem σ_injective {s t : Tree} (h : s.σ = t.σ) : s = t := by
  rw [← σ_σ s, h, σ_σ]

/-- Julia `over(x, y)` / `x / y` (DF/poset.jl:184-192): graft `x` onto the leftmost leaf of
`y`. -/
def over (x : Tree) : Tree → Tree
  | leaf => x
  | node l r => node (over x l) r

/-- Julia `under(x, y)` / `x \ y` (DF/poset.jl:199-207): graft `y` onto the rightmost leaf
of `x`. -/
def under : Tree → Tree → Tree
  | leaf, y => y
  | node l r, y => node l (under r y)

@[simp] theorem deg_over (x y : Tree) : (over x y).deg = x.deg + y.deg := by
  induction y <;> simp [over, *]; omega
@[simp] theorem deg_under (x y : Tree) : (under x y).deg = x.deg + y.deg := by
  induction x <;> simp [under, *]; omega

/-- Julia `x / y = over(x, y)` (DF/poset.jl:192). -/
instance : Div Tree := ⟨over⟩
/-- Julia `x \ y = under(x, y)` (DF/poset.jl:207). -/
instance : SDiff Tree := ⟨under⟩

/-- `σ` exchanges over and under: `σ(x / y) = σ(y) \ σ(x)` (DF test/runtests.jl:57). -/
theorem σ_over (x y : Tree) : (over x y).σ = under y.σ x.σ := by
  induction y <;> simp [over, under, *]

/-- Julia `LeftInherited(t) = right(t).degr == 0` (DF/morphism.jl:13). -/
def leftInherited (t : Tree) : Bool := t.right == leaf
/-- Julia `RightInherited(t) = left(t).degr == 0` (DF/morphism.jl:21). -/
def rightInherited (t : Tree) : Bool := t.left == leaf
/-- Julia `PrimitiveTree(t)` (DF/morphism.jl:29). -/
def isPrimitive (t : Tree) : Bool := t.leftInherited || t.rightInherited

/-! ## Loday names -/

/-- The Loday name `ω(τ) = [ω(τ_l); n; ω(τ_r)]` (port-notes §3.4): Julia's `PBTree.Y`. -/
def name : Tree → List Nat
  | leaf => []
  | node l r => l.name ++ [l.deg + r.deg + 1] ++ r.name

@[simp] theorem length_name (t : Tree) : t.name.length = t.deg := by
  induction t <;> simp [name, *]; omega

/-- `σ` reverses the name (DF/Dendriform.jl:219). -/
theorem name_σ (t : Tree) : t.σ.name = t.name.reverse := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr => simp [name, ihl, ihr]; omega

/-- Parse a word as a Loday name: split at the **first** occurrence of the length (the
root label, as Julia's `left`/`right` do with `findfirst`), recurse, and accept only if
the result reproduces the word. `fuel` bounds the recursion depth. -/
def parseName : (fuel : Nat) → List Nat → Option Tree
  | _, [] => some leaf
  | 0, _ :: _ => none
  | fuel + 1, ys =>
    match ys.idxOf? ys.length with
    | none => none
    | some p => do
      let l ← parseName fuel (ys.take p)
      let r ← parseName fuel (ys.drop (p + 1))
      some (node l r)

/-- The tree with Loday name `ys`, or `none` if `ys` is not a valid name (Julia's
`PBTree(t::Vector)` accepts anything, DF/Dendriform.jl:107, 153-155). -/
def ofName? (ys : List Nat) : Option Tree :=
  match parseName ys.length ys with
  | some t => if t.name == ys then some t else none
  | none => none

/-- Julia `show(Int.(Y))`: `[1, 2, 3]`. -/
def nameString (t : Tree) : String :=
  "[" ++ ", ".intercalate (t.name.map toString) ++ "]"

end Tree

/-! ## The degree-indexed facade -/

/-- A planar binary tree of degree `n` (`n` internal vertices, `n + 1` leaves): Julia's
`PBTree` with its `degr` field lifted to the type. -/
abbrev PBTree (n : Nat) := {t : Tree // t.deg = n}

namespace PBTree

/-- The tree `|`. -/
def leaf : PBTree 0 := ⟨.leaf, rfl⟩

/-- Grafting, with Loday's degree law in the type: `deg (l ∨ r) = deg l + deg r + 1`. -/
def graft {a b : Nat} (l : PBTree a) (r : PBTree b) : PBTree (a + b + 1) :=
  ⟨.node l.1 r.1, by simp [l.2, r.2]⟩

/-- The involution preserves the degree. -/
def σ {n : Nat} (t : PBTree n) : PBTree n := ⟨t.1.σ, by simp [t.2]⟩

/-- `over` adds degrees (DF/poset.jl:184). -/
def over {a b : Nat} (x : PBTree a) (y : PBTree b) : PBTree (a + b) :=
  ⟨Tree.over x.1 y.1, by simp [x.2, y.2]⟩

/-- `under` adds degrees (DF/poset.jl:199). -/
def under {a b : Nat} (x : PBTree a) (y : PBTree b) : PBTree (a + b) :=
  ⟨Tree.under x.1 y.1, by simp [x.2, y.2]⟩

/-- `x / y : PBTree (a + b)` (Julia `over`). -/
instance {a b : Nat} : HDiv (PBTree a) (PBTree b) (PBTree (a + b)) := ⟨over⟩

/-- `x ∨ y : PBTree (a + b + 1)` (Julia graft, extending `AbstractLattices.vee`). -/
instance {a b : Nat} : HVee (PBTree a) (PBTree b) (PBTree (a + b + 1)) := ⟨graft⟩

/-- Split a tree of positive degree into its root's subtrees, with the degree bookkeeping
`k + (n - k) = n` recorded in the result type. -/
def split {n : Nat} (t : PBTree (n + 1)) : (k : Fin (n + 1)) × PBTree k × PBTree (n - k) :=
  match t with
  | ⟨.node l r, h⟩ =>
    ⟨⟨l.deg, by simp at h; omega⟩, ⟨l, rfl⟩, ⟨r, by simp at h ⊢; omega⟩⟩

end PBTree

/-! ## Catalan numbers and all trees of a degree -/

/-- Insert into a list sorted by `le` (structural, kernel-reducible). -/
def insertSorted {α : Type} (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: insertSorted le x ys

/-- Insertion sort (structural, so `decide` can evaluate it; `List.mergeSort` is
well-founded recursion and does not reduce in the kernel). -/
def isort {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insertSorted le x (isort le xs)

/-- Catalan numbers by the product recurrence `C(n+1) = C(n)·2(2n+1)/(n+2)` (structural,
so the kernel evaluates it). Julia `Cn = catalannum` (DF/Dendriform.jl:87). -/
def catalan : Nat → Nat
  | 0 => 1
  | n + 1 => catalan n * (2 * (2 * n + 1)) / (n + 2)

/-- All trees of each degree `0..n`, by the recurrence `Y_{n+1} = ⋃_k Y_k ∨ Y_{n-k}`
(structural on `n`). The order within a degree is generation order, not Julia's. -/
def allTreesUpTo : Nat → List (List Tree)
  | 0 => [[.leaf]]
  | n + 1 =>
    let t := allTreesUpTo n
    t ++ [(List.range (n + 1)).flatMap fun k =>
      (t.getD k []).flatMap fun l => (t.getD (n - k) []).map fun r => .node l r]

/-- All planar binary trees of degree `n` (unsorted). -/
def allTrees (n : Nat) : List Tree := (allTreesUpTo n).getD n []

theorem length_allTreesUpTo (n : Nat) : (allTreesUpTo n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allTreesUpTo, ih]

theorem deg_of_mem_allTreesUpTo (n : Nat) :
    ∀ k t, t ∈ (allTreesUpTo n).getD k [] → t.deg = k := by
  induction n with
  | zero =>
    intro k t h
    cases k <;> simp [allTreesUpTo] at h
    simp [h]
  | succ n ih =>
    intro k t h
    simp only [allTreesUpTo, List.getD_eq_getElem?_getD] at h
    by_cases hk : k < n + 1
    · rw [List.getElem?_append_left (by simp [length_allTreesUpTo]; omega)] at h
      exact ih k t (by simpa [List.getD_eq_getElem?_getD] using h)
    · rw [List.getElem?_append_right (by simp [length_allTreesUpTo]; omega)] at h
      by_cases hk' : k = n + 1
      · subst hk'
        simp only [length_allTreesUpTo, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
          List.mem_flatMap, List.mem_range, List.mem_map] at h
        obtain ⟨j, hj, l, hl, r, hr, rfl⟩ := h
        have := ih j l hl
        have := ih (n - j) r hr
        simp; omega
      · have : k - (allTreesUpTo n).length ≠ 0 := by simp [length_allTreesUpTo]; omega
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero this
        simp [hm] at h

/-- Every tree listed by `allTrees n` has degree `n`. -/
theorem deg_of_mem_allTrees {n : Nat} {t : Tree} (h : t ∈ allTrees n) : t.deg = n :=
  deg_of_mem_allTreesUpTo n n t h

-- The number of trees of degree n is the Catalan number (kernel-checked for n ≤ 7).
example : (List.range 8).all (fun n => (allTrees n).length == catalan n) = true := by decide
example : (List.range 8).map catalan = [1, 1, 2, 5, 14, 42, 132, 429] := by decide
-- every generated tree has the right degree, and they are pairwise distinct (n ≤ 5)
example : (List.range 6).all (fun n => (allTrees n).all (·.deg == n)) = true := by decide
example : (List.range 6).all (fun n => (allTrees n).eraseDups.length == catalan n) = true := by
  decide

end Dendriform

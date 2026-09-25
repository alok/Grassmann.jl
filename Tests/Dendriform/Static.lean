import Dendriform

/-!
Compile-time checks for Dendriform: the degree laws are in the types, small instances of
Loday's identities are decided by the kernel, and the general theorems specialize.
-/

open Dendriform Dendriform.Grove

namespace Tests.Dendriform.Static

/-! Degrees live in the types: these only typecheck because `3 + 2 = 5`, `2 * 3 = 6`, … -/

example : Grove 5 := total 3 + total 2
example : Grove 6 := total 2 * total 3
example : Grove 7 := (total 3 ⊣ total 2) ⊢ total 2
example (x : PBTree 2) (y : PBTree 3) : PBTree 6 := x.graft y
example (x : PBTree 2) (y : PBTree 3) : PBTree 5 := x / y

/-! Kernel-checked instances of Loday's identities (`List.Perm` is decidable). -/

-- Y₁ + Y₁ = Y₂ and Y₂ + Y₁ = Y₃ = Y₁ + Y₂ (port-notes §6.4, `Grove(2)+Grove(1)`)
example : (sumL (allTrees 1) (allTrees 1)).Perm (allTrees 2) := by decide
example : (sumL (allTrees 2) (allTrees 1)).Perm (allTrees 3) := by decide
example : (sumL (allTrees 1) (allTrees 2)).Perm (allTrees 3) := by decide
-- Y₂ * Y₂ = Y₄ (14 trees)
example : (mulL (allTrees 2) (allTrees 2)).Perm (allTrees 4) := by decide
-- [1] is the multiplicative unit and | the additive one
example : (allTrees 3).all (fun t => Tree.mul (.node .leaf .leaf) [t] == [t]) = true := by decide
example : (allTrees 3).all (fun t => Tree.sum .leaf t == [t] && Tree.sum t .leaf == [t]) = true := by
  decide
-- σ is multiplicative on small trees (DF test/runtests.jl:56), row for row up to order
example : (allTrees 2).all (fun x => (allTrees 2).all fun y =>
    ((Tree.mul x [y]).map Tree.σ).isPerm (Tree.mul x.σ [y.σ])) = true := by decide
-- the Julia row order of `[1,2] + [1]` (port-notes §6.4)
example : (Tree.sum (.node (.node .leaf .leaf) .leaf) (.node .leaf .leaf)).map Tree.name =
    [[1, 3, 1], [1, 2, 3]] := by decide

/-! The general theorems, specialized. -/

example (x : Grove 1) (y : Grove 2) (z : Grove 3) : (x ⊣ y) ⊣ z ≅ x ⊣ (y + z) :=
  dashv_dashv x y z (by decide) (by decide) (by decide)
example (x : Grove 1) (y : Grove 2) (z : Grove 3) : (x ⊢ y) ⊣ z ≅ x ⊢ (y ⊣ z) :=
  vdash_dashv x y z (by decide) (by decide) (by decide)
example (x : Grove 1) (y : Grove 2) (z : Grove 3) : (x + y) ⊢ z ≅ x ⊢ (y ⊢ z) :=
  add_vdash x y z (by decide) (by decide)
example (x : Grove 4) (y : Grove 0) (z : Grove 2) : (x + y) + z ≅ x + (y + z) := add_assoc x y z

/-! Julia's notation (README.md, DF/poset.jl): tree literals, graft `∨`, the Tamari order. -/

example : PBTree 7 := tree![2, 1, 7, 4, 1, 3, 1]
example : Grove 2 := grove![[1, 2], [2, 1]]
example : PBTree 3 := tree![1] ∨ tree![1]
example (x : PBTree 2) (y : PBTree 3) : PBTree 5 := x \ y
-- README: `[2,1,7,4,1,3,1] < [2,1,7,4,3,2,1]`
#guard tree![2, 1, 7, 4, 1, 3, 1] < tree![2, 1, 7, 4, 3, 2, 1]
#guard !(tree![2, 1, 7, 4, 3, 2, 1] < tree![2, 1, 7, 4, 1, 3, 1])
#guard tree![2, 1, 7, 4, 3, 2, 1] > tree![2, 1, 7, 4, 1, 3, 1]
#guard tree![1, 2, 3] ≤ tree![1, 2, 3] && tree![1, 2, 3] ≤ tree![3, 2, 1]
#guard tree![1, 2] ⋖ tree![2, 1] && tree![2, 1] ⋗ tree![1, 2] && !(tree![2, 1] ⋖ tree![1, 2])
#guard (tree![1, 2, 3] ⊴ tree![3, 2, 1]).size == 5
#guard (tree![1] ∨ tree![1]).1.name == [1, 3, 1]
#guard (Tree.leaf ∨ Tree.leaf) == .node .leaf .leaf
#guard (tree![1] \ tree![1]).1.name == [2, 1] && (tree![1] / tree![1]).1.name == [1, 2]
#guard toString tree![1, 3, 1].1 == "[1, 3, 1]\n"
-- README: `Grove(3,7) ⊣ [1,2]∪[2,1]` with literals; groves compare in grove-index order
#guard (Grove.ofIndex 3 7 ⊣ (grove![[1, 2]] ∪ grove![[2, 1]])).rows ==
  (Grove.ofIndex 3 7 ⊣ (Grove.ofIndex 2 1 ∪ Grove.ofIndex 2 2)).rows
#guard Grove.ofIndex 3 7 < Grove.ofIndex 3 8 && Grove.ofIndex 3 7 ≤ Grove.ofIndex 3 7
-- `∨` on Props is still `Or` under `open Dendriform`
example : False ∨ True := .inr trivial

end Tests.Dendriform.Static

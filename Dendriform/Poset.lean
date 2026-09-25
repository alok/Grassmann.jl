import Dendriform.Grove
import Std.Data.HashSet
import Std.Data.HashMap

/-!
# The Tamari poset

Julia source: DF/poset.jl. The upper covers of a tree are obtained by one right rotation
`(A ∨ B) ∨ C ↦ A ∨ (B ∨ C)` at some vertex (`posetnext_list`, poset.jl:8-29); lower covers
by a left rotation (`posetprev_list`, poset.jl:47-68). Julia decides `a < b` by an
exponential depth-first search over upper covers (poset.jl:93-103). The same relation is
computed here by breadth-first reachability with a visited set; the structural
`ltFuel` (bounded by the maximal chain length `n(n-1)/2`) is the kernel-reducible version
used by `decide`. `between` (Julia `⊴`, poset.jl:144-173) keeps Julia's depth-first
first-seen order and memoizes the sub-intervals.
-/

namespace Dendriform

namespace Tree

/-- Julia `posetnext_list(t)` (DF/poset.jl:8-29): the trees covering `t` in the Tamari
order, in Julia's order (root rotation, then covers inside the left, then the right
subtree). -/
def nextList : Tree → List Tree
  | leaf => []
  | node l r =>
    (match l with
      | leaf => []
      | node ll lr => [node ll (node lr r)]) ++
    (nextList l).map (node · r) ++ (nextList r).map (node l ·)

/-- Julia `posetprev_list(t)` (DF/poset.jl:47-68): the trees covered by `t`. -/
def prevList : Tree → List Tree
  | leaf => []
  | node l r =>
    (match r with
      | leaf => []
      | node rl rr => [node (node l rl) rr]) ++
    (prevList l).map (node · r) ++ (prevList r).map (node l ·)

/-- Julia `a ⋖ b` (DF/poset.jl:44): `b` covers `a`. -/
def covers (a b : Tree) : Bool := (nextList a).contains b

/-- Julia `a ⋗ b` (DF/poset.jl:83): `a` covers `b`. -/
def coveredBy (a b : Tree) : Bool := (prevList a).contains b

/-- Strict Tamari order by bounded depth-first search (structural, for `decide`): Julia's
`<` (DF/poset.jl:93-103) with `fuel` bounding the chain length. -/
def ltFuel : Nat → Tree → Tree → Bool
  | 0, _, _ => false
  | fuel + 1, a, b => (nextList a).any fun h => h == b || ltFuel fuel h b

/-- The maximal length of a chain of covers among trees of degree `n` is `n(n-1)/2`; this
bound (plus one) is the fuel of the searches below. -/
def chainBound (n : Nat) : Nat := n * n + 1

/-- Whether `b` is reachable from `a` in one or more `step`s: breadth-first search with a
visited set, at most `chainBound (deg a)` layers. -/
def reach (step : Tree → List Tree) (a b : Tree) : Bool :=
  go (chainBound a.deg) [a] (Std.HashSet.emptyWithCapacity.insert a)
where
  /-- one BFS layer -/
  go : Nat → List Tree → Std.HashSet Tree → Bool
    | 0, _, _ => false
    | fuel + 1, frontier, seen =>
      let next := frontier.flatMap step
      if next.contains b then true
      else
        let (fresh, seen) := next.foldl (fun (acc : List Tree × Std.HashSet Tree) t =>
          if acc.2.contains t then acc else (t :: acc.1, acc.2.insert t)) ([], seen)
        if fresh.isEmpty then false else go fuel fresh seen

/-- Julia `a < b` in the Tamari order (DF/poset.jl:93-103): `b` is reachable from `a` by
upper covers. -/
def tamariLt (a b : Tree) : Bool := a.deg == b.deg && a != b && reach nextList a b

/-- Julia `a ≤ b` (DF/poset.jl:112): `a == b || a < b`. -/
def tamariLe (a b : Tree) : Bool := a == b || tamariLt a b

/-- Julia `a > b` (DF/poset.jl:120-130), via lower covers. -/
def tamariGt (a b : Tree) : Bool := a.deg == b.deg && a != b && reach prevList a b

/-- Julia `a ≥ b` (DF/poset.jl:139). -/
def tamariGe (a b : Tree) : Bool := a == b || tamariGt a b

end Tree

/-- Julia `between_list(a, b)` (DF/poset.jl:144-158): the Tamari interval `[a, b]` in
depth-first first-seen order, `[]` when `a ≰ b`. Sub-intervals are memoized. -/
def betweenList (a b : Tree) : List Tree :=
  (go (Tree.chainBound a.deg) a).run' {} |>.toList
where
  /-- the memoized recursion, fuelled by the chain bound -/
  go : Nat → Tree → StateM (Std.HashMap Tree (Array Tree)) (Array Tree)
    | 0, _ => pure #[]
    | fuel + 1, a => do
      if let some r := (← get).get? a then return r
      let r ← if a == b then pure #[b] else do
        let mut g : Array Tree := #[a]
        let mut seen : Std.HashSet Tree := Std.HashSet.emptyWithCapacity.insert a
        for h in Tree.nextList a do
          if Tree.tamariLe h b then
            for t in ← go fuel h do
              if !seen.contains t then
                g := g.push t
                seen := seen.insert t
        pure (if g.size > 1 then g else #[])
      modify (·.insert a r)
      return r

/-- Julia `between(a, b)` / `a ⊴ b` (DF/poset.jl:165-173) as a grove. -/
def between {n : Nat} (a b : PBTree n) : Grove n :=
  ⟨(betweenList a.1 b.1).filter (·.deg == n), fun t h => by
    simp only [List.mem_filter, beq_iff_eq] at h; exact h.2⟩

/-- Julia `between_list_full(a, b)` (DF/poset.jl:252-264). -/
def betweenFull (a b : Tree) : Bool :=
  go (Tree.chainBound a.deg) a
where
  /-- the recursion, fuelled by the chain bound -/
  go : Nat → Tree → Bool
    | 0, _ => false
    | fuel + 1, a =>
      if a == b then true
      else (Tree.nextList a).foldl (fun acc h =>
        if Tree.tamariLe h b then acc && go fuel h else false) true

/-- Julia `posetnext(t)` (DF/poset.jl:36) as a grove. -/
def posetNext {n : Nat} (t : PBTree n) : Grove n :=
  ⟨(Tree.nextList t.1).filter (·.deg == n), fun t h => by
    simp only [List.mem_filter, beq_iff_eq] at h; exact h.2⟩

/-- Julia `posetprev(t)` (DF/poset.jl:75) as a grove. -/
def posetPrev {n : Nat} (t : PBTree n) : Grove n :=
  ⟨(Tree.prevList t.1).filter (·.deg == n), fun t h => by
    simp only [List.mem_filter, beq_iff_eq] at h; exact h.2⟩

/-! ## Interval research tools (DF/poset.jl:211-296) -/

/-- Julia `intervals(d)` (DF/poset.jl:211-218): the sorted grove indices of all non-empty
intervals `PBTree(d,i) ⊴ PBTree(d,j)`. -/
def intervals (d : Nat) : Array Nat :=
  let Y := (totalGrove d).trees
  let gs := Y.toList.flatMap fun a => Y.toList.filterMap fun b =>
    let t := betweenList a b
    if t.isEmpty then none else some (groveIndexOf t)
  gs.toArray.qsort (· < ·)

/-- Count, for each interval, how many sums land on it; `(counts, misses)`. -/
private def countHits (ins : Array Nat) (zs : List Nat) : Array Nat × Nat :=
  zs.foldl (fun (cc, cn) z =>
    let hits := (List.range ins.size).filter fun k => ins[k]! == z
    if hits.isEmpty then (cc, cn + 1) else (hits.foldl (fun c k => c.modify k (· + 1)) cc, cn))
    (Array.replicate ins.size 0, 0)

/-- Julia `intcomp(d)` (DF/poset.jl:220-234): for every split `q + (d-q)` and all non-empty
groves `Grove(q,i)`, `Grove(d-q,j)`, count which interval their sum is; returns the counts
and the number of non-intervals (Julia logs `@info "Non-intervals: $cn"`). -/
def intcomp (d : Nat) : Array Nat × Nat :=
  let ins := intervals d
  let zs := (List.range (d - 1)).flatMap fun q' =>
    let q := q' + 1
    (List.range (2 ^ catalan q - 1)).flatMap fun i =>
      (List.range (2 ^ catalan (d - q) - 1)).map fun j =>
        groveIndexOf (sumL (rowsOfIndex q (i + 1)) (rowsOfIndex (d - q) (j + 1)))
  countHits ins zs

/-- Julia `intcompt(d)` (DF/poset.jl:236-250): the same over single trees. -/
def intcompt (d : Nat) : Array Nat × Nat :=
  let ins := intervals d
  let zs := (List.range (d - 1)).flatMap fun q' =>
    let q := q' + 1
    ((totalGrove q).trees.toList).flatMap fun x =>
      ((totalGrove (d - q)).trees.toList).map fun y => groveIndexOf (Tree.sum x y)
  countHits ins zs

/-- Julia `intervals_full(d)` (DF/poset.jl:266-274): whether each interval (in grove-index
order, stable) is "full". -/
def intervalsFull (d : Nat) : Array Bool :=
  let Y := (totalGrove d).trees
  let gs := Y.toList.flatMap fun a => Y.toList.filterMap fun b =>
    let t := betweenList a b
    if t.isEmpty then none else some (groveIndexOf t, betweenFull a b)
  (gs.toArray.zipIdx.qsort fun p q => p.1.1 < q.1.1 || (p.1.1 == q.1.1 && p.2 < q.2)).map (·.1.2)

/-- `lpad(string(i, base=2), Cn(d), "0")`. -/
def binaryString (width i : Nat) : String :=
  let s := String.ofList (Nat.toDigits 2 i)
  String.ofList (List.replicate (width - s.length) '0') ++ s

/-- Julia `print_interval_bin(d)` (DF/poset.jl:276-281), as the printed text. -/
def printIntervalBin (d : Nat) : String :=
  String.join ((intervals d).toList.map fun i => binaryString (catalan d) i ++ "\n")

/-- Julia `print_intcompt_bin(d)` (DF/poset.jl:291-296). -/
def printIntcomptBin (d : Nat) : String :=
  let ins := intervals d
  let cc := (intcompt d).1
  String.join ((List.range ins.size).filterMap fun k =>
    if cc[k]! > 0 then some (binaryString (catalan d) ins[k]! ++ "\n") else none)

/-- Julia `print_intcomp_bin(d)` (DF/poset.jl:283-289). -/
def printIntcompBin (d : Nat) : String :=
  let ins := intervals d
  let cc := (intcomp d).1
  let ct := (intcompt d).1
  let inst := (List.range ins.size).filterMap fun k => if ct[k]! > 0 then some ins[k]! else none
  String.join ((List.range ins.size).filterMap fun k =>
    if cc[k]! > 0 && !inst.contains ins[k]! then some (binaryString (catalan d) ins[k]! ++ "\n")
    else none)

/-! ## Notation: Julia's order relations on trees (DF/poset.jl) -/

namespace Tree

/-- Julia `a < b` on trees: the Tamari order (DF/poset.jl:93-103). -/
instance : LT Tree := ⟨fun a b => tamariLt a b = true⟩
/-- Julia `a ≤ b` on trees (DF/poset.jl:112). -/
instance : LE Tree := ⟨fun a b => tamariLe a b = true⟩
instance (a b : Tree) : Decidable (a < b) := inferInstanceAs (Decidable (tamariLt a b = true))
instance (a b : Tree) : Decidable (a ≤ b) := inferInstanceAs (Decidable (tamariLe a b = true))

end Tree

/-- The Tamari order on degree-`n` trees (Julia `<` on `PBTree`s). -/
instance {n : Nat} : LT (PBTree n) := ⟨fun a b => a.1 < b.1⟩
/-- The non-strict Tamari order on degree-`n` trees. -/
instance {n : Nat} : LE (PBTree n) := ⟨fun a b => a.1 ≤ b.1⟩
instance {n : Nat} (a b : PBTree n) : Decidable (a < b) := inferInstanceAs (Decidable (a.1 < b.1))
instance {n : Nat} (a b : PBTree n) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.1 ≤ b.1))

/-- Julia `a ⋖ b` (DF/poset.jl:44): `b` covers `a` in the Tamari order. -/
scoped infix:50 " ⋖ " => Tree.covers
/-- Julia `a ⋗ b` (DF/poset.jl:83): `a` covers `b`. -/
scoped infix:50 " ⋗ " => Tree.coveredBy
/-- Julia `a ⊴ b` (DF/poset.jl:173): the Tamari interval `[a, b]` as a grove. -/
scoped infix:50 " ⊴ " => between
/-- Julia `x \ y = under(x, y)` on degree-typed trees (DF/poset.jl:207):
`PBTree a → PBTree b → PBTree (a + b)`. Overloads the `SDiff` token (which `Tree` uses). -/
scoped infixl:70 " \\ " => PBTree.under

/-- Julia `x < y` on groves: grove-index order (DF/morphism.jl:346). -/
instance {n : Nat} : LT (Grove n) := ⟨fun x y => Grove.indexLt x y = true⟩
/-- Julia `x ≤ y` on groves (DF/morphism.jl:348). -/
instance {n : Nat} : LE (Grove n) := ⟨fun x y => Grove.indexLe x y = true⟩
instance {n : Nat} (x y : Grove n) : Decidable (x < y) :=
  inferInstanceAs (Decidable (Grove.indexLt x y = true))
instance {n : Nat} (x y : Grove n) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (Grove.indexLe x y = true))

-- The Tamari order on small trees, decided by the kernel (port-notes §6.4)
example : Tree.ltFuel 3 (.node (.node (.node .leaf .leaf) .leaf) .leaf)
    (.node .leaf (.node .leaf (.node .leaf .leaf))) = true := by decide
example : Tree.ltFuel 3 (.node .leaf (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf) = false := by
  decide

end Dendriform

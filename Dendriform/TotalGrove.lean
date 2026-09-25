import Dendriform.Order

/-!
# Total groves, tree indices and grove indices

Julia source: DF/Dendriform.jl:227-318 (the total-grove repository `Υ`/`ΥI`) and
DF/morphism.jl:63-187 (`treeindex`, `grovebit`, `groveindex`, `TreeLoday`).

The total grove `Y_d` is the list of all `Cn(d)` trees of degree `d` in ascending tree
integer (Julia's default `grovesort(true)`; the unsorted build order of
`GroveExtend!` is dropped, port-notes §4.4.3). The **tree index** of a tree is its
1-based rank there, and a **grove index** is a bitset of tree indices.

Julia extends a global cache degree by degree and prints progress to stdout
(DF/Dendriform.jl:236-286); here the tables for `d ≤ 12` are lazily-forced `Thunk`s in
a closed term (docs/DESIGN.md §3), with no output. Julia looks tree integers up by a
linear `findfirst` (DF/morphism.jl:75, 85); here it is a binary search.
-/

namespace Dendriform

/-- The sorted total grove of degree `d` (Julia `Υ(d)` and `ΥI(d)`). -/
structure TotalGrove (d : Nat) where
  /-- all trees of degree `d`, in ascending tree integer (Julia `Υ(d).Y` rows) -/
  trees : Array Tree
  /-- their tree integers, ascending (Julia `ΥI(d)`) -/
  tis : Array Nat
  /-- every listed tree has degree `d` (erased at runtime) -/
  deg_trees : ∀ t ∈ trees, t.deg = d

/-- Build `Y_d` by generating all trees and sorting by tree integer. The degree proof
rides along in the sorted pairs, so no lemma about `qsort` is needed. -/
def TotalGrove.build (d : Nat) : TotalGrove d :=
  let typed : List (PBTree d) := (allTrees d).attach.map fun t => ⟨t.1, deg_of_mem_allTrees t.2⟩
  let pairs := (typed.map fun t => (t.1.treeInteger, t)).toArray.qsort (·.1 < ·.1)
  { trees := pairs.map (·.2.1)
    tis := pairs.map (·.1)
    deg_trees := by
      intro t ht
      simp only [Array.mem_map] at ht
      obtain ⟨p, _, rfl⟩ := ht
      exact p.2.2 }

/-- Lazily built tables for `d ≤ 12` (Cn(12) = 208012 trees). -/
def TotalGrove.cache : Array (Thunk ((d : Nat) × TotalGrove d)) :=
  (Array.range 13).map fun d => Thunk.mk fun _ => ⟨d, TotalGrove.build d⟩

/-- The total grove `Y_d` (Julia `Υ(d)`), cached for `d ≤ 12`. The cached entry's degree
is checked (one `Nat` comparison) to transport it to the requested type. -/
def totalGrove (d : Nat) : TotalGrove d :=
  if h : d < TotalGrove.cache.size then
    match TotalGrove.cache[d].get with
    | ⟨d', Y⟩ => if hd : d' = d then hd ▸ Y else TotalGrove.build d
  else TotalGrove.build d

/-- First index `i ∈ [lo, hi)` with `a[i] ≥ x` (binary search on a sorted array). -/
def lowerBound (a : Array Nat) (x : Nat) (lo hi : Nat) : Nat :=
  if h : lo < hi then
    let mid := (lo + hi) / 2
    if a[mid]! < x then lowerBound a x (mid + 1) hi else lowerBound a x lo mid
  else lo
termination_by hi - lo

namespace Tree

/-- Julia `treeindex(t)` (DF/morphism.jl:84-85): the 1-based rank of `t` in `Y_deg`
(0 if absent, which cannot happen for a `Tree`). -/
def treeIndex (t : Tree) : Nat :=
  let Y := totalGrove t.deg
  let ti := t.treeInteger
  let i := lowerBound Y.tis ti 0 Y.tis.size
  if Y.tis[i]? == some ti then i + 1 else 0

end Tree

/-- Julia `PBTree(deg, ind)` (DF/Dendriform.jl:96-100): row `ind` (1-based) of `Y_deg`.
Julia ignores its own `treecheck` and throws `BoundsError`; here out of range is `none`. -/
def treeOfIndex? (d i : Nat) : Option Tree :=
  if d == 0 then (if i == 1 then some .leaf else none) else (totalGrove d).trees[i - 1]?

/-- Julia `treecheck(d, t) = 0 < t ≤ Cn(d)` (DF/morphism.jl:39). -/
def treeCheck (d t : Nat) : Bool := 0 < t && t ≤ catalan d

/-- Julia `grovecheck(d, gi) = 0 ≤ gi < 2^Cn(d)` (DF/morphism.jl:50). -/
def groveCheck (d gi : Nat) : Bool := gi < 2 ^ catalan d

/-- Julia `groveindex(g)` (DF/morphism.jl:122-137): `Σ_rows 2^(treeindex - 1)`.
**Counts multiplicity**, so duplicate rows corrupt it (quirk, Appendix A #7); this is the
value Julia stores in `GroveBin.gbin`. -/
def groveIndexOf (rows : List Tree) : Nat :=
  rows.foldl (fun acc t => acc + 2 ^ (t.treeIndex - 1)) 0

/-- Julia `grovebit(g)` (DF/morphism.jl:96-108) as a bitset: bit `i - 1` is set iff tree
index `i` occurs (duplicates collapse). -/
def groveBitsOf (rows : List Tree) : Nat :=
  rows.foldl (fun acc t => acc ||| 2 ^ (t.treeIndex - 1)) 0

/-- Julia `Grove(d, s)` / `TreeLoday(d, s)` (DF/Dendriform.jl:135, DF/morphism.jl:150-165):
the trees of `Y_d` at the set bits of `s`, in ascending index order. Bits beyond `Cn(d)`
are ignored (Julia throws). As in Julia, degree 0 always decodes to the zero grove
(`TreeLoday` returns `Υ(0)`, DF/morphism.jl:156-157). -/
def rowsOfIndex (d s : Nat) : List Tree :=
  if d == 0 then []
  else (totalGrove d).trees.toList.zipIdx.filterMap fun (t, i) => if s.testBit i then some t else none

theorem deg_of_mem_rowsOfIndex {d s : Nat} {t : Tree} (h : t ∈ rowsOfIndex d s) : t.deg = d := by
  unfold rowsOfIndex at h
  split at h
  · simp at h
  · simp only [List.mem_filterMap] at h
    obtain ⟨⟨t', i⟩, hm, he⟩ := h
    split at he
    · cases he
      exact (totalGrove d).deg_trees t' (by simpa using List.fst_mem_of_mem_zipIdx hm)
    · cases he

/-- Julia `CnInv(n)` (DF/Dendriform.jl:201-209): the smallest `d ≥ 1` with `Cn(d) = n`. -/
def catalanInv? (n : Nat) : Option Nat :=
  go 1 (n + 2)
where
  /-- search `d, d+1, …` while `Cn(d) < n`, with fuel -/
  go (d fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      let k := catalan d
      if k < n then go (d + 1) fuel else if k == n then some d else none

/-- Julia `treeindexCn(d) = [1:Cn(d)] .// Cn(d)` (DF/morphism.jl:87). -/
def treeIndexCn (d : Nat) : List Rat :=
  (List.range (catalan d)).map fun i => ((i + 1 : Nat) : Rat) / (catalan d : Rat)

/-- Julia `TreeRational(d)` (DF/morphism.jl:320, 331): `1 - s - (-1)^s Θ/ΘMax(d)` over the
sorted tree integers `Θ`, `s = treeshift`. -/
def treeRationals (d : Nat) (treeshift : Bool := true) : List Rat :=
  (totalGrove d).tis.toList.map fun (θ : Nat) =>
    let r : Rat := (θ : Rat) / (Tree.thetaMax d : Rat)
    if treeshift then r else 1 - r

/-- Julia `treeindex(d, j)` (DF/morphism.jl:85): the tree index of the tree with tree
integer `j` in degree `d` (0 if there is none; Julia throws). -/
def treeIndexOfInteger (d j : Nat) : Nat :=
  let Y := totalGrove d
  let i := lowerBound Y.tis j 0 Y.tis.size
  if Y.tis[i]? == some j then i + 1 else 0

/-- Julia `GroveError(g)` (DF/morphism.jl:59-61): `[1:size] - sortperm(TreeInteger(g))`,
all zeros iff the rows are in canonical order. -/
def groveError (rows : List Tree) : List Int :=
  let perm := (rows.zipIdx.toArray.qsort fun p q =>
    p.1.treeInteger < q.1.treeInteger || (p.1.treeInteger == q.1.treeInteger && p.2 < q.2)).toList
  (perm.zipIdx.map fun ((_, j), i) => (i : Int) - (j : Int))

end Dendriform

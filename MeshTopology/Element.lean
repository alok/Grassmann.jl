import MeshTopology.Simplex
import MeshTopology.Sparse
import Std.Data.HashMap

/-!
# Simplex combinatorics

MeshTopology.jl `src/element.jl`: columns, incidence and adjacency matrices, edges and faces
with their orderings, element→edge / element→facet tables, oriented boundary coefficients,
neighbors, degrees and weights.

Orderings that downstream numbering depends on (port-notes/meshtopology.md §4.9, §8.4):
* `edges` are **colex** sorted (by larger then smaller id), as Julia's `findall` over `triu` of the
  adjacency matrix returns them; degenerate elements contribute self-edges `[v, v]`.
* `faces`/`facets` of dimension `3 ≤ k < N` are sorted `k`-subsets in order of first appearance.
* Triangle local edges are opposite-vertex (`(v₂v₃, v₁v₃, v₁v₂)`); other simplices use
  lexicographic pairs.
* `_facetsindices` numbers facets by positional subsets of the *unsorted* element, so the facet
  opposite local vertex `k` lands in slot `k`.

Julia builds these through sparse matrices and `findfirst` on growing vectors (quadratic in the
number of faces); here edges are sorted once and faces are looked up in hash maps, with identical
results.
-/

namespace MeshTopology

namespace SimplexTopology

variable {N : Nat}

/-- The distinct entries of an element in order of first appearance (pairwise comparison: no
node-sized scratch array per element). -/
@[inline] def dedupSmall (a : Array Nat) : Array Nat :=
  a.foldl (fun acc v => if acc.contains v then acc else acc.push v) #[]

/-- Julia `columns(t)` (element.jl:27-28): column `k` holds vertex `k` of every subspace element
(full ids). -/
def columns (m : SimplexTopology N) : Vector (Array Nat) N :=
  let top := m.topology
  Vector.ofFn fun k => top.map (·[k])

/-- Julia `reducedcolumns(m)` (element.jl:30): `columns` with subspace vertex numbers. -/
def reducedColumns (m : SimplexTopology N) : Vector (Array Nat) N :=
  if m.isCover then m.columns else
  let top := m.subtopology
  Vector.ofFn fun k => top.map (·[k])

/-- Julia `sparse(t, cols, np)` (element.jl:51-57): `A[cols[a][e], cols[b][e]] += 1` over the
local pairs `a < b`. -/
def sparseWith (cols : Vector (Array Nat) N) (np : Nat) : SparseInt := Id.run do
  let mut I : Array Nat := #[]
  let mut J : Array Nat := #[]
  for c in combo N 2 do
    let a := cols.toArray[c[0]! - 1]!
    let b := cols.toArray[c[1]! - 1]!
    I := I ++ a
    J := J ++ b
  return SparseInt.ofTriplets np np I J (Array.replicate I.size 1)

/-- Julia `sparse(t)` with its defaults (`reducedcolumns(t)`, `nodes(t)`). -/
def sparse (m : SimplexTopology N) : SparseInt := sparseWith m.reducedColumns m.nodes

/-- Julia `adjacency(t)` (element.jl:50): `A + Aᵀ`, in subspace vertex numbers. -/
def adjacency (m : SimplexTopology N) : SparseInt := let A := m.sparse; A + A.transpose

/-- Julia `antiadjacency(t)` (element.jl:49): `A - Aᵀ`. -/
def antiadjacency (m : SimplexTopology N) : SparseInt := let A := m.sparse; A - A.transpose

/-- Julia `incidence(t)` (element.jl:320-327): the `totalnodes × elements` node-element
incidence (`A[v, e]` = multiplicity of full vertex `v` in subspace element `e`). -/
def incidence (m : SimplexTopology N) : SparseInt := Id.run do
  let ne := m.elements
  let mut colPtr : Array Nat := (Array.mkEmpty (ne + 1)).push 0
  let mut rowVal : Array Nat := Array.mkEmpty (N * ne)
  let mut nzVal : Array Int := Array.mkEmpty (N * ne)
  for k in [0:ne] do
    let base := N * (m.sub.get k - 1)
    let mut ids : Array Nat := Array.mkEmpty N
    for j in [0:N] do
      ids := ids.push m.conn[base + j]!
    -- the element's distinct vertices, ascending, with multiplicities
    let sorted := ids.insertionSort (· < ·)
    let mut prev := 0
    let mut cnt : Int := 0
    for v in sorted do
      if v == prev then cnt := cnt + 1
      else
        if cnt > 0 then
          rowVal := rowVal.push prev
          nzVal := nzVal.push cnt
        prev := v
        cnt := 1
    if cnt > 0 then
      rowVal := rowVal.push prev
      nzVal := nzVal.push cnt
    colPtr := colPtr.push rowVal.size
  return ⟨m.totalNodes, ne, colPtr, rowVal, nzVal⟩

/-- Julia `degrees(t)` (element.jl:303-309): the number of subspace elements containing each
full node (length `totalnodes`; a repeated vertex counts once per element, as Julia's
`b[tk] .+= 1`). -/
def degrees (m : SimplexTopology N) : Array Nat :=
  go 0 (Array.replicate m.totalNodes 0)
where
  /-- `v` occurs among the first `j` vertices of the element starting at `base`. -/
  seen (base j v i : Nat) : Bool :=
    if i < j then m.conn[base + i]! == v || seen base j v (i + 1) else false
  termination_by j - i
  /-- Walk the subspace elements' vertex slots `q = N·k + j`. -/
  go (q : Nat) (out : Array Nat) : Array Nat :=
    if q < N * m.elements then
      let base := N * (m.sub.get (q / N) - 1)
      let j := q % N
      let v := m.conn[base + j]!
      go (q + 1) (if seen base j v 0 then out else out.modify (v - 1) (· + 1))
    else out
  termination_by N * m.elements - q

/-- Julia `weights(t) = inv.(degrees(t))` (element.jl:300); `Inf` for unused nodes. -/
def weights (m : SimplexTopology N) : FloatArray :=
  m.degrees.foldl (fun (acc : FloatArray) d => acc.push (1.0 / d.toFloat)) (FloatArray.emptyWithCapacity m.totalNodes)

/-- Julia `degrees(t, B) = B * ones(size(B, 2))` (element.jl:302, Q20 fixed): row sums. -/
def degreesOf (B : SparseInt) : Array Int := B.rowSums

/-- Julia `weights(t, B) = inv.(degrees(t, B))` (element.jl:301). -/
def weightsOf (B : SparseInt) : FloatArray :=
  (degreesOf B).foldl (fun (acc : FloatArray) d => acc.push (1.0 / Float.ofInt d))
    (FloatArray.emptyWithCapacity B.m)

/-- Julia `interp(t, B = incidence(t)) = Diagonal(weights(t, B)) * B` (element.jl:329; the
`SimplexTopology` method is ambiguous upstream, Q20): node values as weighted averages of the
values of their elements. -/
def interpMatrix (B : SparseInt) : SparseFloat := SparseFloat.scaleRows (weightsOf B) B

/-- Julia `interp(t)`. -/
def interp (m : SimplexTopology N) : SparseFloat := interpMatrix m.incidence

/-- Julia `pretni(t) = interp(t, sparse(incidence(t)'))` (element.jl:333): element averages of
node values. -/
def pretni (m : SimplexTopology N) : SparseFloat := interpMatrix m.incidence.transpose

/-- Julia `assembleincidence(t, w, b, Val(true))` = `interp(t, b, w)` (element.jl:311-332):
scatter the element values `b` onto the nodes, weighted by `w` (default `weights(t)`). -/
def interpValues (m : SimplexTopology N) (b : FloatArray) (w : FloatArray := m.weights) : FloatArray :=
  let top := m.topology
  (Array.range top.size).foldl (fun (acc : FloatArray) k =>
    top[k]!.toArray.foldl (fun acc v => acc.set! (v - 1) (acc[v - 1]! + w[v - 1]! * b[k]!)) acc)
    (FloatArray.mk (Array.replicate m.totalNodes 0.0))

/-! ## Edges -/

/-- Julia `edgetopology(adjacency(t, columns(t), totalnodes(t)))` (element.jl:63-70): the
distinct vertex pairs of the subspace elements (full ids), `[min, max]`, colex-sorted. -/
def edgeList (m : SimplexTopology N) : Array (Vector Nat 2) :=
  let P := m.totalNodes + 1
  let keys := m.topology.foldl (fun (acc : Array Nat) e =>
    (combinationsIdx N 2).foldl (fun acc c =>
      let a := e.toArray[c[0]!]!
      let b := e.toArray[c[1]!]!
      acc.push (max a b * P + min a b)) acc) #[]
  let sorted := keys.qsort (· < ·)
  let uniq := sorted.foldl (fun (acc : Array Nat) k => if acc.back? == some k then acc else acc.push k) #[]
  uniq.map fun k => #v[k % P, k / P]

/-- Julia `edges(t)` (element.jl:59-66): the edge topology of the subspace elements, sharing the
node count of `t` (`edges` of an edge topology is itself). -/
def edges (m : SimplexTopology N) : SimplexTopology 2 :=
  if h : N = 2 then h ▸ m else ofElements m.edgeList 0 (some m.totalNodes)

/-- Lookup of edge ids by vertex pair (Julia's `A = sparse(edges…); A += A'`, element.jl:346),
stored CSR-style: the edges whose larger endpoint is `v` are `start[v] ..< start[v+1]`. -/
structure EdgeIndex where
  /-- Bucket starts by larger endpoint (size `maxId + 2`). -/
  start : Array Nat
  /-- Smaller endpoint of each bucketed edge. -/
  lo : Array Nat
  /-- Edge id (1-based) of each bucketed edge. -/
  id : Array Nat

/-- Build the `EdgeIndex` of an edge topology (counting sort by larger endpoint, O(E)). -/
def edgeIndex (et : SimplexTopology 2) : EdgeIndex := Id.run do
  let ne := et.totalElements
  let P := et.conn.foldl max 0
  let mut start : Array Nat := Array.replicate (P + 2) 0
  for k in [0:ne] do
    let hi := max et.conn[2 * k]! et.conn[2 * k + 1]!
    start := start.modify (hi + 1) (· + 1)
  for v in [1:P + 2] do
    start := start.set! v (start[v]! + start[v - 1]!)
  let mut pos := start
  let mut lo : Array Nat := Array.replicate ne 0
  let mut id : Array Nat := Array.replicate ne 0
  for k in [0:ne] do
    let (a, b) := (et.conn[2 * k]!, et.conn[2 * k + 1]!)
    let hi := max a b
    let p := pos[hi]!
    lo := lo.set! p (min a b)
    id := id.set! p (k + 1)
    pos := pos.modify hi (· + 1)
  return ⟨start, lo, id⟩

/-- Julia `A[a, b]` of the symmetric edge-id matrix (`0` if `{a, b}` is not an edge; a self-edge
`[v, v]` reads twice its id, as `A + A'` doubles the diagonal). -/
def EdgeIndex.find (E : EdgeIndex) (a b : Nat) : Nat :=
  let hi := max a b
  let lo := min a b
  let id := if hi + 1 < E.start.size then go lo E.start[hi]! E.start[hi + 1]! else 0
  if a == b then 2 * id else id
where
  /-- Scan the bucket `p ..< stop`. -/
  go (lo p stop : Nat) : Nat :=
    if p < stop then (if E.lo[p]! == lo then E.id[p]! else go lo (p + 1) stop) else 0
  termination_by stop - p

/-- Julia `localedge(A, v)` (element.jl:350-366): the edge ids of an element, opposite-vertex for
triangles (`v₂v₃, v₁v₃, v₁v₂`) and lexicographic pairs otherwise. -/
def localEdges (A : EdgeIndex) (v : Vector Nat N) : Array Nat :=
  if N = 3 then #[A.find v[1]! v[2]!, A.find v[0]! v[2]!, A.find v[0]! v[1]!]
  else (combinationsIdx N 2).map fun c => A.find v[c[0]!]! v[c[1]!]!

/-- Julia `edgesindices(t, et = edges(t))` (element.jl:344-349; Q21 fixed): for each subspace
element, the ids of its edges in `et`, as a topology over `OneTo(#edges)`. -/
def edgesIndicesWith (m : SimplexTopology N) (et : SimplexTopology 2) :
    SimplexTopology (N * (N - 1) / 2) :=
  let A := edgeIndex et
  let ne := et.totalElements
  let rows := m.topology.map fun e =>
    let l := localEdges A e
    Vector.ofFn fun k : Fin (N * (N - 1) / 2) => l[k.1]!
  ofElements rows 0 (some ne) (some (.oneTo ne))

/-- Julia `edgesindices(t)`. -/
def edgesIndices (m : SimplexTopology N) : SimplexTopology (N * (N - 1) / 2) :=
  m.edgesIndicesWith m.edges

/-! ## Faces -/

/-- Sorted copy of an element. -/
def sortedElem (e : Vector Nat N) : Array Nat := e.toArray.qsort (· < ·)

/-- The sorted `k`-subsets of the subspace elements in order of first appearance, and for each
subset occurrence whether it was new (used by `faces`, `facetsInterior`). -/
def faceOccurrences (m : SimplexTopology N) (k : Nat) : Array (Array Nat) × Array Nat := Id.run do
  let mut ids : Std.HashMap (Array Nat) Nat := {}
  let mut out : Array (Array Nat) := #[]
  let mut again : Array Nat := #[]
  for e in m.topology do
    for w in combinations (sortedElem e) k do
      match ids[w]? with
      | some j => again := again.push j
      | none =>
        out := out.push w
        ids := ids.insert w out.size
  return (out, again)

/-- Rebuild typed elements from arrays of length `k`. -/
def toVecs {k : Nat} (a : Array (Array Nat)) : Array (Vector Nat k) :=
  a.map fun w => Vector.ofFn fun i => w[i.1]!

/-- Julia `faces(t, Val(k))` (element.jl:101-114): `t` itself for `k = N`, `edges` for `k = 2`,
vertex singletons for `k = 1`, and otherwise the sorted `k`-subsets in order of first appearance
(sharing `t`'s vertex list and node count). -/
def faces (m : SimplexTopology N) (k : Nat) : SimplexTopology k :=
  if h : k = N then h ▸ m
  else if h2 : k = 2 then h2 ▸ m.edges
  else if h1 : k = 1 then
    h1 ▸ ofElements (m.verts.toArray.map fun v => #v[v]) 0 (some m.totalNodes) (some m.verts)
  else ofElements (toVecs (m.faceOccurrences k).1) 0 (some m.totalNodes) (some m.verts)

/-- Julia `facets(t) = faces(t, Val(N-1))` (element.jl:97). -/
def facets (m : SimplexTopology N) : SimplexTopology (N - 1) := m.faces (N - 1)

/-- Julia `facetsinterior(t)` (element.jl:84-96): the facets (first appearance) and the ids of
the facets met again (interior facets, one entry per repeat). -/
def facetsInterior (m : SimplexTopology N) : SimplexTopology (N - 1) × Array Nat :=
  let (out, again) := m.faceOccurrences (N - 1)
  (ofElements (toVecs out) 0 (some m.totalNodes) (some m.verts), again)

/-- Julia `faces(t, h, Val(k), g)` (element.jl:142-166): the `k`-faces with coefficients
`Σ h[e] · ±val`, where `val` is the boundary sign pattern `(-1)^(N-j)` when `k = N-1` (and `1`
otherwise) and the sign flips with the parity of the sort of each element. `g` is applied to each
contribution (`abs` in `skeleton`). -/
def facesWith (m : SimplexTopology N) (h : Array Int) (k : Nat) (g : Int → Int := fun x => x) :
    SimplexTopology k × Array Int := Id.run do
  let val : Array Int := if k + 1 == N then boundarySigns N else Array.replicate (choose N k) 1
  let mut ids : Std.HashMap (Array Nat) Nat := {}
  let mut out : Array (Array Nat) := #[]
  let mut bnd : Array Int := #[]
  let top := m.topology
  for hi : i in [0:top.size] do
    let (odd, s) := indexParity (top[i].toArray.map Int.ofNat)
    let sorted := s.map Int.toNat
    let ws := combinations sorted k
    for hj : j in [0:ws.size] do
      let w := ws[j]
      let v := h[i]! * (if odd then -val[j]! else val[j]!)
      match ids[w]? with
      | some p => bnd := bnd.modify (p - 1) (· + g v)
      | none =>
        out := out.push w
        bnd := bnd.push (g v)
        ids := ids.insert w out.size
  return (ofElements (toVecs out) 0 (some m.totalNodes), bnd)

/-- Julia `facets(t, h)` = `faces(t, h, Val(N-1))` (element.jl:98): boundary coefficients of the
facets (nonzero ⇔ boundary facet for `h = ones`). -/
def facetsWith (m : SimplexTopology N) (h : Array Int) : SimplexTopology (N - 1) × Array Int :=
  m.facesWith h (N - 1)

/-- Julia `skeleton(t)` (element.jl:193): `faces(t, ones, Val(k), abs)` for `k = 1..N+1`
(incidence counts of every face; the last entry is empty). -/
def skeleton (m : SimplexTopology N) : Array ((k : Nat) × SimplexTopology k × Array Int) :=
  (Array.range (N + 1)).map fun k =>
    ⟨k + 1, m.facesWith (Array.replicate m.elements 1) (k + 1) Int.natAbs'⟩
where
  /-- `abs` as an `Int → Int`. -/
  Int.natAbs' (x : Int) : Int := x.natAbs

/-- Julia `_facetsindices(t)` (element.jl:115-141): the facets (sorted, first appearance over
positional subsets of each element) and each element's facet ids, the facet opposite local
vertex `k` in slot `k`. For triangles: `(edges, edgesindices)`. -/
def facetsIndices (m : SimplexTopology N) : SimplexTopology (N - 1) × SimplexTopology N :=
  if h : N = 3 then
    let e := m.edges
    let ei := m.edgesIndicesWith e
    (h ▸ e, ⟨ei.id, ei.totalNodes, ei.totalElements, ei.conn, by
      have := ei.size_conn; subst h; simpa using this, ei.verts, ei.sub, ei.fullVerts, ei.vinv,
      ei.isTotal, ei.isFull⟩)
  else Id.run do
    let mut ids : Std.HashMap (Array Nat) Nat := {}
    let mut out : Array (Array Nat) := #[]
    let mut outi : Array (Vector Nat N) := #[]
    for e in m.topology do
      let cs := combinations e.toArray (N - 1)
      let mut row : Array Nat := Array.replicate N 0
      for hj : j in [0:cs.size] do
        let cj := cs[j].qsort (· < ·)
        let id ← match ids[cj]? with
          | some k => pure k
          | none => do
            out := out.push cj
            ids := ids.insert cj out.size
            pure out.size
        row := row.set! (N - 1 - j) id
      outi := outi.push (Vector.ofFn fun k => row[k.1]!)
    let nf := out.size
    return (ofElements (toVecs out) 0 (some m.totalNodes) (some m.verts),
      ofElements outi 0 (some nf) (some (.oneTo nf)))

/-! ## Neighbors and signs -/

/-- Julia `neighbors(t, n2e = incidence(t))` (element.jl:368-393): for each subspace element,
the element across the facet opposite each local vertex (the first element, ascending, sharing
all other vertices), `0` on the boundary. -/
def neighbors (m : SimplexTopology N) : Array (Vector Nat N) :=
  let top := m.topology
  -- node → ascending subspace elements containing it
  let n2e := (Array.range top.size).foldl (fun (acc : Array (Array Nat)) e =>
    (dedupSmall top[e]!.toArray).foldl (fun acc v => acc.modify (v - 1) (·.push (e + 1))) acc)
    (Array.replicate m.totalNodes #[])
  (Array.range top.size).map fun e =>
    let v := top[e]!
    Vector.ofFn fun j =>
      let others := (List.finRange N).filter (· ≠ j)
      match others with
      | [] => 0
      | o :: rest =>
        let common := rest.foldl (fun (acc : Array Nat) l =>
          let s := n2e[v[l] - 1]!
          acc.filter s.contains) n2e[v[o] - 1]!
        (common.find? (· ≠ e + 1)).getD 0

/-- Julia `facetsign(i, ni) = i < ni ? 1 : -1` (element.jl:395). -/
@[inline] def facetSign (i ni : Nat) : Int := if i < ni then 1 else -1

/-- Julia `facetsigns(t)` (element.jl:397): `+1` where the neighbor across a facet has a smaller
index (and on the boundary, Q27), else `-1`. -/
def facetSigns (m : SimplexTopology N) : Array (Vector Int N) :=
  m.neighbors.mapIdx fun k nb => nb.map (facetSign · (k + 1))

end SimplexTopology

/-- Julia `edgesigns(i)` (element.jl:399-402): orientation of each local edge (`+1` when it runs
from the smaller to the larger id), in local edge order. -/
def edgeSigns {N : Nat} (v : Vector Nat N) : Array Int :=
  let s (a b : Nat) : Int := if v[a]! < v[b]! then 1 else -1
  if N = 3 then #[s 1 2, s 2 0, s 0 1]
  else (combinationsIdx N 2).map fun c => s c[0]! c[1]!

/-- Julia `facets(i::Values)` (element.jl:404-407): the oriented local facets of one element
(the fifth facet of a 4-simplex fixed to `(i₄,i₃,i₂,i₁)`, Q22). -/
def localFacets {N : Nat} (v : Vector Nat N) : Array (Array Nat) :=
  let i (k : Nat) := v[k - 1]!
  match N with
  | 2 => #[#[i 2], #[i 1]]
  | 3 => #[#[i 2, i 3], #[i 3, i 1], #[i 1, i 2]]
  | 4 => #[#[i 2, i 3, i 4], #[i 4, i 3, i 1], #[i 1, i 2, i 4], #[i 3, i 2, i 1]]
  | 5 => #[#[i 2, i 3, i 4, i 5], #[i 5, i 3, i 2, i 1], #[i 1, i 2, i 4, i 5],
      #[i 5, i 4, i 3, i 1], #[i 4, i 3, i 2, i 1]]
  | _ => #[]

/-- Julia `invmap(t, n)` (element.jl:336): the local position of `n` in a triangle (default 3). -/
def invmap (t : Vector Nat 3) (n : Nat) : Nat := if n == t[0] then 1 else if n == t[1] then 2 else 3

/-- Julia `findmissing(n)` (element.jl:337): the local index in `{1,2,3}` missing from `n`. -/
def findmissing (n : Vector Nat 2) : Nat :=
  if !n.toList.contains 1 then 1 else if !n.toList.contains 2 then 2 else 3

/-- Julia `neighbor(k, ab...)` (element.jl:368-371): the first element of the intersection of
the lists other than `k`, or `0`. -/
def neighbor (k : Nat) (ab : List (Array Nat)) : Nat :=
  match ab with
  | [] => 0
  | a :: rest => ((rest.foldl (fun acc s => acc.filter s.contains) a).find? (· ≠ k)).getD 0

/-- Julia `interior(fixed, neq) = sort!(setdiff(1:neq, fixed))` (element.jl:340). -/
def interior (fixed : Array Nat) (neq : Nat) : Array Nat :=
  (Array.range neq).filterMap fun k => if fixed.contains (k + 1) then none else some (k + 1)

namespace SimplexTopology

variable {N : Nat}

/-- Julia `interior(e) = interior(vertices(e), totalnodes(e))` (element.jl:339, Q19 fixed): the
nodes not on `e` (e.g. not on the boundary). -/
def interiorNodes (e : SimplexTopology N) : Array Nat := interior e.verts.toArray e.totalNodes

/-- Julia `isedge(e, t) = all(e .∈ t)` (element.jl:196-197). -/
def isEdge {k : Nat} (e : Vector Nat k) (t : Vector Nat N) : Bool := e.toList.all t.toList.contains

end SimplexTopology

namespace DiscontinuousTopology

variable {N : Nat}

/-- Julia `edges(d::DiscontinuousTopology{3})` (element.jl:71-82): per element the edges
`(t₁,t₂), (t₂,t₃), (t₃,t₁)` in discontinuous node ids. -/
def edges (d : DiscontinuousTopology 3) : SimplexTopology 2 :=
  let out := (Array.range d.elements).flatMap fun i =>
    let t := d.get (i + 1)
    #[#v[t[0], t[1]], #v[t[1], t[2]], #v[t[2], t[0]]]
  SimplexTopology.ofElements out 0 (some (3 * d.elements)) (some (.oneTo (3 * d.elements)))

/-- Julia `interp(d, b) = view(b, discontinuousvertices(d))` (element.jl:331): element values
spread onto the discontinuous nodes. -/
def interp {α : Type} [Inhabited α] (d : DiscontinuousTopology N) (b : Array α) : Array α :=
  d.discontinuousVertices.map fun e => b[e - 1]!

/-- Julia `discontinuousboundary(dt, e)` (element.jl:198-207): each continuous edge of `e`
(`[a, b]` in a triangle mesh) as the discontinuous node pair of the first element containing it. -/
def boundary (d : DiscontinuousTopology 3) (e : SimplexTopology 2) : SimplexTopology 2 :=
  let top := d.t.topology
  let out := e.topology.map fun ei =>
    match top.findIdx? (SimplexTopology.isEdge ei) with
    | none => ei
    | some j =>
      let dj := d.get (j + 1)
      Vector.ofFn fun k => dj[invmap top[j]! ei[k] - 1]!
  SimplexTopology.ofElements out 0 (some d.totalNodes)

end DiscontinuousTopology

/-- Julia `assemblelocal!(M, mat, m, tk)` (element.jl:285-298) on a dense column-major `n × n`
matrix: `M[tk[i], tk[j]] += mat[i, j] * m` for the local `k × k` matrix `mat`. -/
def assembleLocal (M : FloatArray) (n : Nat) {k : Nat} (mat : FloatArray) (m : Float)
    (tk : Vector Nat k) : FloatArray :=
  go 0 M
where
  /-- Loop over the `k²` local entries (tail-recursive, Float accumulator in the array). -/
  go (ij : Nat) (M : FloatArray) : FloatArray :=
    if _h : ij < k * k then
      let i := ij % k
      let j := ij / k
      let r := tk[i]! - 1
      let c := tk[j]! - 1
      let p := r + c * n
      go (ij + 1) (M.set! p (M[p]! + mat[i + j * k]! * m))
    else M
  termination_by k * k - ij

end MeshTopology

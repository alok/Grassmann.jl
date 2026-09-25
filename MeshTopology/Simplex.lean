import MeshTopology.Basic

/-!
# SimplexTopology and DiscontinuousTopology

Julia `SimplexTopology{N,P,F,T}` (MeshTopology.jl `src/MeshTopology.jl:210-466`) and
`DiscontinuousTopology{N,P,T}` (MT:468-625): unstructured meshes of `N`-vertex simplices, and
sub-meshes that are views into a full mesh.

## Representation

* `N` (vertices per element) is a type index; every element read returns a `Vector Nat N`.
* The full element list (Julia `t::Vector{Values{N,Int}}`) is stored flat, stride `N`, with its
  length in the type of the proof `size_conn`: element reads need no bounds checks. Vertex ids are
  Julia's 1-based ids; `valid` checks `1 ≤ id ≤ totalNodes` once, after which `vertexFin` gives
  bounds-check-free gathers into per-node data.
* `verts`, `sub`, `fullVerts` and `vinv` are Julia's `i`, `f`, `I` and `v`: `OneTo(n)` or an
  explicit vector (`IdxVec`), a distinction Julia dispatches on.
* Julia's `T = (istotal, isfull)` type parameter becomes two `Bool`s.
* Julia shares the node count between views through a mutable `RefValue{Int}` (`totalnodes!`
  mutates every view) and hands out fresh bundle ids from a global counter (`top_id`). Here the
  count is a plain field and ids are explicit (default `0`, "uncached").
-/

namespace MeshTopology

/-- `N * e + k < N * te` for `e < te`, `k < N`: the flat index of an element's vertex is in
range. -/
theorem flat_index_lt {N e te k : Nat} (he : e < te) (hk : k < N) : N * e + k < N * te := by
  have : N * e + N ≤ N * te := by
    have := Nat.mul_le_mul_left N (Nat.succ_le_of_lt he)
    simpa [Nat.mul_succ] using this
  omega

/-- Flatten fixed-length elements into one stride-`N` array. -/
def flattenElems {N : Nat} (es : Array (Vector Nat N)) : {a : Array Nat // a.size = N * es.size} :=
  ⟨Array.ofFn (n := N * es.size) fun i =>
    have hN : 0 < N := Nat.pos_of_ne_zero fun h => by have := i.2; simp [h] at this
    (es[i.1 / N]'(Nat.div_lt_of_lt_mul i.2))[i.1 % N]'(Nat.mod_lt _ hN), Array.size_ofFn⟩

/-- Julia `SimplexTopology{N}` (MT:235-249). -/
structure SimplexTopology (N : Nat) where
  /-- Bundle cache id (Julia `id`, `bundle(m)`); `0` = uncached. -/
  id : Nat
  /-- Node count of the full mesh (Julia `p[]`, `totalnodes`). -/
  totalNodes : Nat
  /-- Number of elements of the full mesh (Julia `totalelements`). -/
  totalElements : Nat
  /-- The full element list, flat with stride `N` (Julia `t`, `fulltopology`). -/
  conn : Array Nat
  /-- One stride of `N` ids per element. -/
  size_conn : conn.size = N * totalElements
  /-- Subspace vertices, full ids (Julia `i`, `vertices`). -/
  verts : IdxVec
  /-- Subspace elements, full element ids (Julia `f`, `subelements`). -/
  sub : IdxVec
  /-- Vertices of the parent (Julia `I`, `fullvertices`). -/
  fullVerts : IdxVec
  /-- Inverse of `verts` over full ids, `0` elsewhere (Julia `v`, `verticesinv`). -/
  vinv : IdxVec
  /-- Julia `istotal` (type parameter `T[1]`). -/
  isTotal : Bool
  /-- Julia `isfull` (type parameter `T[2]`). -/
  isFull : Bool

namespace SimplexTopology

variable {N : Nat}

/-- Julia's inner constructor (MT:243-248): `v = verticesinv(p, i, istotal && isfull)`, and a
`OneTo` parent vertex list is collected when `i` is a vector. -/
def raw (id : Nat) (conn : Array Nat) (te : Nat) (h : conn.size = N * te) (i : IdxVec) (p : Nat)
    (f : IdxVec := .oneTo te) (I : IdxVec := i) (ist : Bool := i.size == p)
    (isf : Bool := f.size == te) : SimplexTopology N :=
  { id, totalNodes := p, totalElements := te, conn, size_conn := h, verts := i, sub := f
    fullVerts := if !i.isOneTo && I.isOneTo then I.collect else I
    vinv := verticesInv p i (ist && isf), isTotal := ist, isFull := isf }

/-- Julia `SimplexTopology(id, t, i = vertices(t), p = maximum(i))` (MT:251-257): the full
topology of the element list `t` (default node count: the largest id). -/
def ofElements (t : Array (Vector Nat N)) (id : Nat := 0) (p : Option Nat := none)
    (i : Option IdxVec := none) : SimplexTopology N :=
  let ⟨conn, h⟩ := flattenElems t
  let i := i.getD (verticesOf conn)
  let p := p.getD i.maximum
  raw (N := N) id conn t.size h i p (.oneTo t.size) i (i.size == p) true

/-! ## Accessors (MT:260-380) -/

/-- Julia `bundle(m)`. -/
@[inline] def bundle (m : SimplexTopology N) : Nat := m.id

/-- Element `e` (0-based) of the full mesh (Julia `fulltopology(m)[e+1]`). -/
@[inline] def fullElem (m : SimplexTopology N) (e : Fin m.totalElements) : Vector Nat N :=
  Vector.ofFn fun k => m.conn[N * e.1 + k.1]'(m.size_conn ▸ flat_index_lt e.2 k.2)

/-- Element `e` (0-based) of the full mesh, `0`s out of range. -/
@[inline] def fullElem! (m : SimplexTopology N) (e : Nat) : Vector Nat N :=
  if h : e < m.totalElements then m.fullElem ⟨e, h⟩ else Vector.replicate N 0

/-- Julia `fulltopology(m)`: every element of the full mesh. -/
def fulltopology (m : SimplexTopology N) : Array (Vector Nat N) :=
  (Array.finRange m.totalElements).map m.fullElem

/-- Julia `elements(m)`: the number of subspace elements. -/
@[inline] def elements (m : SimplexTopology N) : Nat := m.sub.size

/-- Julia `nodes(m)`: the number of subspace vertices. -/
@[inline] def nodes (m : SimplexTopology N) : Nat := m.verts.size

/-- Julia `iscover(m) = isfull(m) && istotal(m)`. -/
@[inline] def isCover (m : SimplexTopology N) : Bool := m.isFull && m.isTotal

/-- Julia `getfacet(m, i)` (MT:358-359): full element id of subspace element `i` (1-based). -/
@[inline] def getFacet (m : SimplexTopology N) (i : Nat) : Nat :=
  if m.sub.isOneTo || m.isFull then i else m.sub.get1 i

/-- Julia `getimage(m, i)` (MT:350-351): full vertex id of subspace vertex `i` (1-based). -/
@[inline] def getImage (m : SimplexTopology N) (i : Nat) : Nat :=
  if m.verts.isOneTo || m.isCover then i else m.verts.get1 i

/-- Julia `m[i]` (MT:342): subspace element `i` (1-based), full vertex ids. -/
@[inline] def get (m : SimplexTopology N) (i : Nat) : Vector Nat N := m.fullElem! (m.getFacet i - 1)

/-- Julia `topology(m)` (MT:279): the subspace elements, full vertex ids. -/
def topology (m : SimplexTopology N) : Array (Vector Nat N) :=
  (Array.range m.elements).map fun k => m.get (k + 1)

/-- The subspace elements flattened (stride `N`), full ids. -/
def topologyFlat (m : SimplexTopology N) : Array Nat :=
  if m.isFull then m.conn else (m.topology.flatMap (·.toArray))

/-- `true` when every stored id lies in `1..totalNodes` (Julia's implicit invariant). -/
def valid (m : SimplexTopology N) : Bool := m.conn.all fun v => 0 < v && v ≤ m.totalNodes

/-- Vertex `k` of full element `e`, as a 0-based node index: with `valid`, gathers into
per-node arrays of length `totalNodes` need no bounds checks. -/
@[inline] def vertexFin (m : SimplexTopology N) (h : m.valid = true) (e : Fin m.totalElements)
    (k : Fin N) : Fin m.totalNodes :=
  have hi : N * e.1 + k.1 < m.conn.size := m.size_conn ▸ flat_index_lt e.2 k.2
  have hv := (Array.all_eq_true.mp h) _ hi
  ⟨m.conn[N * e.1 + k.1] - 1, by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    omega⟩

/-- Julia's type string `SimplexTopology{N, P, F, (istotal, isfull)}`. -/
def typeString (m : SimplexTopology N) : String :=
  s!"SimplexTopology\{{N}, {m.verts.typeString}, {m.sub.typeString}, ({m.isTotal}, {m.isFull})}"

/-- Julia `summary(m)` (MT:704-714): `8×3⊆9 SimplexTopology{3, …}` (`⊂` unless a cover). -/
def summary (m : SimplexTopology N) : String :=
  s!"{m.elements}×{N}{if m.isCover then "⊆" else "⊂"}{m.totalNodes} {m.typeString}"

/-! ## Sub-meshes (MT:382-466) -/

/-- Julia `untotal(t, p)` (MT:382-384): the same (full) topology with node count `p`, marked not
total. -/
def untotal (m : SimplexTopology N) (p : Nat) : SimplexTopology N :=
  raw m.id m.conn m.totalElements m.size_conn m.verts p m.sub m.fullVerts false true

/-- Julia `fullimmersion_vertices(m)` (MT:386-394). -/
def fullImmersionVertices (m : SimplexTopology N) : IdxVec :=
  if m.isTotal then .oneTo m.totalNodes
  else if m.fullVerts.maximum == m.fullVerts.size then .oneTo m.fullVerts.size else m.fullVerts

/-- Julia `fullimmersion(m)` (MT:396-399): the full mesh of a sub-mesh. -/
def fullImmersion (m : SimplexTopology N) : SimplexTopology N :=
  let ind := m.fullImmersionVertices
  raw m.id m.conn m.totalElements m.size_conn ind m.totalNodes (.oneTo m.totalElements) ind
    m.isTotal true

/-- Julia `m[ks]` (MT:401-405): the sub-mesh of the subspace elements `ks` (1-based). Its
vertices are those of the chosen elements in order of first appearance; `istotal` is inherited
(Q28, replicated). -/
def getSub (m : SimplexTopology N) (ks : Array Nat) : SimplexTopology N :=
  let ind := ks.map m.getFacet
  let ver := verticesOf (ind.flatMap fun e => (m.fullElem! (e - 1)).toArray)
  raw m.id m.conn m.totalElements m.size_conn ver m.totalNodes (.arr ind) m.verts m.isTotal

/-- Julia `m(vs)` = `subtopology(m, vs)` (MT:407-415): the elements all of whose vertices lie
in `vs`, with vertex list `vs` as given. -/
def byVertices (m : SimplexTopology N) (vs : Array Nat) : SimplexTopology N :=
  let mx := vs.foldl max m.totalNodes
  let mark := vs.foldl (fun (acc : Array Bool) v => acc.set! v true) (Array.replicate (mx + 1) false)
  let ind := (Array.range m.elements).filterMap fun k =>
    let j := m.sub.get k
    if (m.fullElem! (j - 1)).toList.all (mark[·]!) then some j else none
  raw m.id m.conn m.totalElements m.size_conn (.arr vs) m.totalNodes (.arr ind) m.verts m.isTotal

/-- Julia `getelement(m, i)` (MT:417-420): subspace element `i` with subspace vertex numbers. -/
def getElement (m : SimplexTopology N) (i : Nat) : Vector Nat N :=
  if m.verts.isOneTo || m.isCover then m.get i else (m.get i).map m.vinv.get1

/-- Julia `subtopology(m)` (MT:422-425): every subspace element with subspace vertex numbers. -/
def subtopology (m : SimplexTopology N) : Array (Vector Nat N) :=
  if m.verts.isOneTo || m.isCover then m.topology
  else (Array.range m.elements).map fun k => m.getElement (k + 1)

/-- Julia `subimmersion(m)` (MT:432-442): the sub-mesh as a standalone cover (id `0`), vertices
renumbered `1..nodes` (kept as full ids when they already are `OneTo`). -/
def subImmersion (m : SimplexTopology N) : SimplexTopology N :=
  if m.isCover then m else
  let top := m.subtopology
  let ⟨conn, h⟩ := flattenElems top
  let p := m.nodes
  let ver : IdxVec := if m.verts.isOneTo then m.verts else .oneTo p
  raw 0 conn top.size h ver p (.oneTo top.size) ver true true

/-- Julia `refine(m)` (MT:453-466): the same topology with `OneTo` vertex and element lists
materialized as vectors (Julia does this before refining a mesh in place). -/
def refine (m : SimplexTopology N) : SimplexTopology N :=
  if !m.verts.isOneTo && !m.sub.isOneTo then m else
  let i := m.verts.collect
  let fi := if m.verts.eqv m.fullVerts then i else m.fullVerts.collect
  let I := if m.verts.isOneTo then fi else m.fullVerts
  raw m.id m.conn m.totalElements m.size_conn i m.totalNodes m.sub.collect I m.isTotal m.isFull

/-- Julia `complement(t)` (element.jl:188-190): the full mesh's elements not in `t`. -/
def complement (m : SimplexTopology N) : SimplexTopology N :=
  let mark := (Array.range m.elements).foldl (fun (acc : Array Bool) k => acc.set! (m.sub.get k) true)
    (Array.replicate (m.totalElements + 1) false)
  let rest := (Array.range m.totalElements).filterMap fun e => if mark[e + 1]! then none else some (e + 1)
  m.fullImmersion.getSub rest

end SimplexTopology

/-! ## DiscontinuousTopology (MT:468-625) -/

/-- Julia `DiscontinuousTopology{N}` (MT:483-488): every element of the continuous topology `t`
owns `N` private nodes; element `e` owns `N(e-1)+1 … N e`. -/
structure DiscontinuousTopology (N : Nat) where
  /-- Bundle id. -/
  id : Nat
  /-- The continuous topology (Julia `t`, `SimplexTopology(d)`). -/
  t : SimplexTopology N
  /-- Continuous vertex id of each discontinuous node of the subspace (Julia `i`), or `OneTo`
  when disconnected. -/
  verts : IdxVec
  /-- The same for the full mesh (Julia `I`). -/
  fullVerts : IdxVec

namespace DiscontinuousTopology

variable {N : Nat}

/-- The vertex ids of the given elements, interleaved (`out[N(e-1)+k] = t[e][k]`). -/
def interleave (els : Array (Vector Nat N)) : Array Nat := els.flatMap (·.toArray)

/-- Julia `DiscontinuousTopology(id, m, I)` (MT:505-517; Q17 fixed for non-full `m`). -/
def ofWith (id : Nat) (m : SimplexTopology N) (I : IdxVec) : DiscontinuousTopology N :=
  ⟨id, m, if m.isFull then I else .arr (interleave m.topology), I⟩

/-- Julia `DiscontinuousTopology(id, m)` (MT:496-504). -/
def ofSimplex (m : SimplexTopology N) (id : Nat := m.id) : DiscontinuousTopology N :=
  ofWith id m (.arr (interleave m.fulltopology))

/-- Julia `discontinuous(m)` = `DiscontinuousTopology(0, m)` (MT:596). -/
def _root_.MeshTopology.SimplexTopology.discontinuous (m : SimplexTopology N) :
    DiscontinuousTopology N := ofSimplex m 0

/-- Julia `continuous(d)` (MT:588). -/
@[inline] def continuous (d : DiscontinuousTopology N) : SimplexTopology N := d.t

/-- Julia `totalelements(d)`. -/
@[inline] def totalElements (d : DiscontinuousTopology N) : Nat := d.t.totalElements
/-- Julia `elements(d)`. -/
@[inline] def elements (d : DiscontinuousTopology N) : Nat := d.t.elements
/-- Julia `totalnodes(d) = N * totalelements` (MT:536). -/
@[inline] def totalNodes (d : DiscontinuousTopology N) : Nat := N * d.t.totalElements
/-- Julia `nodes(d) = N * elements` (MT:537). -/
@[inline] def nodes (d : DiscontinuousTopology N) : Nat := N * d.t.elements
/-- Julia `iscover(d)`. -/
@[inline] def isCover (d : DiscontinuousTopology N) : Bool := d.t.isCover
/-- Julia `isdisconnected(d)` (MT:554-556): the vertex list is `OneTo`. -/
@[inline] def isDisconnected (d : DiscontinuousTopology N) : Bool := d.verts.isOneTo

/-- Julia `d[k]` (MT:561): the discontinuous node ids of subspace element `k`. -/
@[inline] def get (d : DiscontinuousTopology N) (k : Nat) : Vector Nat N :=
  Vector.ofFn fun j => j.1 + 1 + N * (d.t.getFacet k - 1)

/-- Julia `collect(d)` = `topology(d)` (MT:535). -/
def topology (d : DiscontinuousTopology N) : Array (Vector Nat N) :=
  (Array.range d.elements).map fun k => d.get (k + 1)

/-- Julia `getimage(d, i)` (MT:564-565): continuous vertex of discontinuous node `i`. -/
@[inline] def getImage (d : DiscontinuousTopology N) (i : Nat) : Nat :=
  if d.verts.isOneTo then i else d.verts.get1 i

/-- Julia `discontinuousvertices(d)` (MT:520-528): the owning element of each node. -/
def discontinuousVertices (d : DiscontinuousTopology N) : Array Nat :=
  (Array.range d.totalNodes).map fun k => k / N + 1

/-- Julia `fullimmersion(d)` (MT:568-571). A total topology becomes disconnected (its vertex
list is `OneTo(totalnodes)`), as upstream. -/
def fullImmersion (d : DiscontinuousTopology N) : DiscontinuousTopology N :=
  let ind : IdxVec :=
    if d.t.isTotal then .oneTo d.totalNodes
    else if d.fullVerts.maximum == d.fullVerts.size then .oneTo d.fullVerts.size else d.fullVerts
  ⟨d.id, d.t.fullImmersion, ind, ind⟩

/-- Julia `d[ks]` (MT:573-575). -/
def getSub (d : DiscontinuousTopology N) (ks : Array Nat) : DiscontinuousTopology N :=
  ofWith d.id (d.t.getSub ks) d.fullVerts

/-- Julia `d(vs)` (MT:577-580). -/
def byVertices (d : DiscontinuousTopology N) (vs : Array Nat) : DiscontinuousTopology N :=
  ofWith d.id (d.t.byVertices vs) d.fullVerts

/-- Julia `disconnect(d)` (MT:604): vertex list `OneTo(totalnodes)`. -/
def disconnect (d : DiscontinuousTopology N) : DiscontinuousTopology N :=
  ofWith d.id d.t (.oneTo d.totalNodes)

/-- Julia `disconnect(m)` for a `SimplexTopology` (MT:603). -/
def _root_.MeshTopology.SimplexTopology.disconnect (m : SimplexTopology N) :
    DiscontinuousTopology N := m.discontinuous.disconnect

/-- Julia `getelement(d, i)` (MT:606-609). -/
def getElement (d : DiscontinuousTopology N) (i : Nat) : Vector Nat N :=
  if d.t.verts.isOneTo || d.isCover then d.get i
  else Vector.ofFn fun j => j.1 + 1 + N * (i - 1)

/-- Julia `subtopology(d)` (MT:611-614). -/
def subtopology (d : DiscontinuousTopology N) : Array (Vector Nat N) :=
  if d.t.verts.isOneTo || d.isCover then d.topology
  else (Array.range d.elements).map fun k => d.getElement (k + 1)

/-- Julia `subimmersion(d)` (MT:616-618). -/
def subImmersion (d : DiscontinuousTopology N) : DiscontinuousTopology N :=
  if d.isCover then d else ofSimplex d.t.subImmersion

/-- Julia `refine(d)` (MT:620-625). -/
def refine (d : DiscontinuousTopology N) : DiscontinuousTopology N :=
  if d.verts.isOneTo then ⟨d.id, d.t.refine, d.verts.collect, d.fullVerts.collect⟩
  else ⟨d.id, d.t.refine, d.verts, d.fullVerts⟩

/-- Julia's type string `DiscontinuousTopology{N, P, SimplexTopology{…}}`. -/
def typeString (d : DiscontinuousTopology N) : String :=
  s!"DiscontinuousTopology\{{N}, {d.verts.typeString}, {d.t.typeString}}"

/-- Julia `summary(d)` (MT:704-714). -/
def summary (d : DiscontinuousTopology N) : String :=
  s!"{d.elements}×{N}{if d.isCover then "⊆" else "⊂"}{d.totalNodes} {d.typeString}"

end DiscontinuousTopology

end MeshTopology

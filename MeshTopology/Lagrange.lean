import MeshTopology.Element

/-!
# Lagrange topologies

Julia `LagrangeEdges{M}`, `LagrangeTriangles{M}` and `LagrangeTetrahedra{M}` (MeshTopology.jl
`src/lagrange.jl`): the node numbering of degree-`M` Lagrange elements on a simplex mesh, built
from the corner mesh, its edges (colex) and, for tetrahedra, its facets (first appearance).

Global node layout (port-notes/meshtopology.md §4.7), with `np` corners, `ne` edges, `nf` facets,
`nt` elements, `es = M-1`, `fs = facetSimplex 4 M`, `cs = centerSimplex d M`:

```
corners        1 .. np
edge E, k-th   np + es(E-1) + k
facet F, k-th  np + es·ne + fs(F-1) + k                 (tetrahedra)
cell  T, k-th  np + es·ne [+ fs·nf] + cs(T-1) + k
```

Element node lists (`get`) follow Julia exactly: triangles list their edge nodes along the local
edge traversal (conforming); tetrahedra list edge and facet nodes without orientation (Julia Q18c,
replicated; `LagrangeTetrahedra.getConforming` is an oriented variant). The upstream typos and
wrong counts (Q18a/b/d/e/f) are fixed.

The degree `M` is a type index; node counts per element are `lagrangeSimplex d M`.
-/

namespace MeshTopology

/-! ## Node-number generators (LG:192-251) -/

/-- Julia `edgesindex(ei, np, Val(M))` (LG:192-198): the interior nodes of the edges `ei`, all
first nodes, then all second nodes, … (`np + es·e - (es-k)`), without orientation. -/
def edgesIndex (ei : Array Nat) (np M : Nat) : Array Nat :=
  let es := M - 1
  (Array.range es).flatMap fun k => ei.map fun e => np + es * e - (es - (k + 1))

/-- Julia `edgesindex(ei, σ, np, Val(M))` (LG:199-205): the interior nodes of each edge in turn,
reversed when the local traversal runs from the larger to the smaller vertex id (`σ = -1`). -/
def edgesIndexSigned (ei : Array Nat) (σ : Array Int) (np M : Nat) : Array Nat :=
  let es := M - 1
  (Array.range ei.size).flatMap fun j =>
    let base := es * (ei[j]! - 1) + np
    (Array.range es).map fun k => base + (if σ[j]! == 1 then k + 1 else es - k)

/-- Julia `facetsindex(fi, np, ne, Val(M))` (LG:206-212): tetrahedral facet-interior nodes. -/
def facetsIndex (fi : Array Nat) (np ne M : Nat) : Array Nat :=
  let fs := facetSimplex 4 M
  let n := np + (M - 1) * ne
  (Array.range fs).flatMap fun k => fi.map fun f => n + fs * f - (fs - (k + 1))

/-- Julia `centerindex(i, np, …, Val(M))` (LG:213-251): the `cs` cell-interior nodes of the
elements `i` after the first `n` nodes, all first nodes, then all second nodes, … -/
def centerIndex (i : Array Nat) (n cs : Nat) : Array Nat :=
  (Array.range cs).flatMap fun k => i.map fun e => n + cs * (e - 1) + (k + 1)

/-! ## LagrangeEdges -/

/-- Julia `LagrangeEdges{M}` (LG:71-82): degree-`M` elements on a mesh of segments. -/
structure LagrangeEdges (M : Nat) where
  /-- Bundle id. -/
  id : Nat
  /-- The segment mesh (Julia `t`, `cornertopology`). -/
  t : SimplexTopology 2
  /-- Subspace nodes (Julia `i`). -/
  verts : IdxVec
  /-- Full nodes (Julia `I`). -/
  fullVerts : IdxVec

namespace LagrangeEdges

variable {M : Nat}

/-- Julia `lagrangevertices2(t, np, Val(M))` (LG:173-177). -/
def lagrangeVertices (t : SimplexTopology 2) (M : Nat) : IdxVec :=
  if M = 1 then t.verts
  else .arr (t.verts.toArray ++ centerIndex t.sub.toArray t.totalNodes (M - 1))

/-- Julia `LagrangeEdges{M}(id, t)` (LG:116-122). -/
def ofCorners (t : SimplexTopology 2) (id : Nat := t.id) : LagrangeEdges M :=
  let I : IdxVec := .oneTo (t.totalNodes + (M - 1) * t.totalElements)
  ⟨id, t, if t.isCover then I else lagrangeVertices t M, if t.isCover then I else I.collect⟩

/-- Julia `totalnodes(m)` (LG:166). -/
def totalNodes (m : LagrangeEdges M) : Nat := m.t.totalNodes + (M - 1) * m.t.totalElements

/-- Julia `nodes(m)` (LG:169). -/
def nodes (m : LagrangeEdges M) : Nat := m.t.nodes + (M - 1) * m.t.elements

/-- Julia `m[i]` (LG:274-275, Q18f fixed): the corners, then the edge's own interior nodes. -/
def get (m : LagrangeEdges M) (i : Nat) : Array Nat :=
  m.t.get i |>.toArray |> (· ++ if M = 1 then #[] else edgesIndex #[m.t.getFacet i] m.t.totalNodes M)

/-- Julia `collect(m)`. -/
def topology (m : LagrangeEdges M) : Array (Array Nat) :=
  (Array.range m.t.elements).map fun k => m.get (k + 1)

/-- Julia `totaledges(m)` (the segments are the edges). -/
def totalEdges (m : LagrangeEdges M) : Nat := m.t.totalElements
/-- Julia `totalcornernodes(m)`. -/
def totalCornerNodes (m : LagrangeEdges M) : Nat := m.t.totalNodes
/-- Julia `totaledgesnodes(m)`. -/
def totalEdgesNodes (m : LagrangeEdges M) : Nat := (M - 1) * m.totalEdges
/-- Julia `cornernodes(m)`. -/
def cornerNodes (m : LagrangeEdges M) : Nat := m.t.nodes
/-- Julia `edgesnodes(m)`. -/
def edgesNodes (m : LagrangeEdges M) : Nat := (M - 1) * m.t.elements

/-- Julia `m[ks]` (LG:297-302). -/
def getSub (m : LagrangeEdges M) (ks : Array Nat) : LagrangeEdges M :=
  let t := m.t.getSub ks
  ⟨m.id, t, if t.isCover then m.fullVerts else lagrangeVertices t M, m.fullVerts⟩

/-- Julia `getelement(m, i)` (LG:338-346, 361-362): element `i` in subspace numbering. -/
def getElement (m : LagrangeEdges M) (i : Nat) : Array Nat :=
  if m.verts.isOneTo then m.get i else
  if M = 1 then (m.t.getElement i).toArray else
  let ind := m.t.getFacet i
  let full := m.t.fullElem! (ind - 1)
  let ti := if m.t.isCover then full else full.map m.t.vinv.get1
  ti.toArray ++ edgesIndex #[ind] m.t.nodes M

/-- Julia `subtopology(m)`. -/
def subtopology (m : LagrangeEdges M) : Array (Array Nat) :=
  if m.verts.isOneTo || m.t.isCover then m.topology
  else (Array.range m.t.elements).map fun k => m.getElement (k + 1)

/-- Julia `fullimmersion(m)` (LG:284-287). -/
def fullImmersion (m : LagrangeEdges M) : LagrangeEdges M :=
  let ind : IdxVec :=
    if m.t.isTotal then .oneTo m.totalNodes
    else if m.fullVerts.maximum == m.fullVerts.size then .oneTo m.fullVerts.size else m.fullVerts
  ⟨m.id, m.t.fullImmersion, ind, ind⟩

/-- Julia `subimmersion(m)` (LG:371-380, Q18b fixed). -/
def subImmersion (m : LagrangeEdges M) : LagrangeEdges M :=
  if m.t.isCover then m else
  let ver : IdxVec := if m.verts.isOneTo then m.verts else .oneTo m.nodes
  ⟨0, m.t.subImmersion, ver, ver⟩

/-- Julia `refine(m)` (LG:404-417). -/
def refine (m : LagrangeEdges M) : LagrangeEdges M :=
  if !m.verts.isOneTo && !m.t.sub.isOneTo then m else
  let (i, fi) :=
    if m.verts.isOneTo then
      let i := m.verts.collect
      (i, if m.verts.eqv m.fullVerts then i else m.fullVerts.collect)
    else (m.verts, m.fullVerts)
  ⟨m.id, m.t.refine, i, fi⟩

/-- Julia's type string `LagrangeEdges{M, N, P, F, T}`. -/
def typeString (m : LagrangeEdges M) : String :=
  s!"LagrangeEdges\{{M}, {lagrangeSimplex 2 M}, {m.verts.typeString}, {m.t.sub.typeString}, ({m.t.isTotal}, {m.t.isFull})}"

/-- Julia `summary(m)`. -/
def summary (m : LagrangeEdges M) : String :=
  s!"{m.t.elements}×{lagrangeSimplex 2 M}{if m.t.isCover then "⊆" else "⊂"}{m.totalNodes} {m.typeString}"

end LagrangeEdges

/-! ## LagrangeTriangles -/

/-- Julia `LagrangeTriangles{M}` (LG:84-97). -/
structure LagrangeTriangles (M : Nat) where
  /-- Bundle id. -/
  id : Nat
  /-- The triangle mesh (Julia `t`, `cornertopology`). -/
  t : SimplexTopology 3
  /-- Its edges (Julia `e`, `edges`). -/
  e : SimplexTopology 2
  /-- Element → edge ids, opposite-vertex order (Julia `ei`, `edgesindices`). -/
  ei : SimplexTopology 3
  /-- Subspace nodes (Julia `i`). -/
  verts : IdxVec
  /-- Full nodes (Julia `I`). -/
  fullVerts : IdxVec

namespace LagrangeTriangles

variable {M : Nat}

/-- Julia `lagrangevertices3(t, ei, np, ne, Val(M))` (LG:179-183). -/
def lagrangeVertices (t : SimplexTopology 3) (ei : SimplexTopology 3) (M : Nat) : IdxVec :=
  if M = 1 then t.verts else
  let np := t.totalNodes
  let ne := ei.totalNodes
  .arr (t.verts.toArray ++ edgesIndex ei.verts.toArray np M ++
    centerIndex t.sub.toArray (np + (M - 1) * ne) (centerSimplex 3 M))

/-- Julia `LagrangeTriangles{M}(id, t, e, ei)` (LG:124-132). -/
def ofParts (t : SimplexTopology 3) (e : SimplexTopology 2) (ei : SimplexTopology 3)
    (id : Nat := t.id) : LagrangeTriangles M :=
  let I : IdxVec := .oneTo (t.totalNodes + (M - 1) * ei.totalNodes + centerSimplex 3 M * t.totalElements)
  ⟨id, t, e, ei, if t.isCover then I else lagrangeVertices t ei M, if t.isCover then I else I.collect⟩

/-- Julia `LagrangeTriangles{M}(t)` (LG:124): edges and element→edge table from the mesh. -/
def ofCorners (t : SimplexTopology 3) (id : Nat := t.id) : LagrangeTriangles M :=
  let e := t.edges
  ofParts t e (t.edgesIndicesWith e) id

/-- Julia `totaledges(m)`. -/
def totalEdges (m : LagrangeTriangles M) : Nat := m.ei.totalNodes
/-- Julia `totalcornernodes(m)`. -/
def totalCornerNodes (m : LagrangeTriangles M) : Nat := m.t.totalNodes
/-- Julia `totaledgesnodes(m)`. -/
def totalEdgesNodes (m : LagrangeTriangles M) : Nat := (M - 1) * m.totalEdges
/-- Julia `totalcenternodes(m)`. -/
def totalCenterNodes (m : LagrangeTriangles M) : Nat := centerSimplex 3 M * m.t.totalElements
/-- Julia `totalnodes(m)` (LG:167). -/
def totalNodes (m : LagrangeTriangles M) : Nat :=
  m.totalCornerNodes + m.totalEdgesNodes + m.totalCenterNodes
/-- Julia `cornernodes(m)`. -/
def cornerNodes (m : LagrangeTriangles M) : Nat := m.t.nodes
/-- Julia `edgesnodes(m)`. -/
def edgesNodes (m : LagrangeTriangles M) : Nat := (M - 1) * m.ei.nodes
/-- Julia `centernodes(m)`. -/
def centerNodes (m : LagrangeTriangles M) : Nat := centerSimplex 3 M * m.t.elements
/-- Julia `nodes(m)` (LG:170). -/
def nodes (m : LagrangeTriangles M) : Nat := m.cornerNodes + m.edgesNodes + m.centerNodes

/-- Julia `m[i]` (LG:255-278): the node list of subspace element `i`: corners, the interior
nodes of each local edge along its traversal (`v₂→v₃, v₃→v₁, v₁→v₂`), then the cell nodes of the
full element (Q18d fixed). -/
def get (m : LagrangeTriangles M) (i : Nat) : Array Nat :=
  let ind := m.t.getFacet i
  let ti := m.t.fullElem! (ind - 1)
  if M = 1 then ti.toArray else
  let np := m.t.totalNodes
  let ei := (m.ei.fullElem! (ind - 1)).toArray
  if M = 2 then ti.toArray ++ ei.map (· + np) else
  let ne := m.ei.totalNodes
  ti.toArray ++ edgesIndexSigned ei (edgeSigns ti) np M ++
    centerIndex #[ind] (np + (M - 1) * ne) (centerSimplex 3 M)

/-- Julia `collect(m)` = `topology(m)`. -/
def topology (m : LagrangeTriangles M) : Array (Array Nat) :=
  (Array.range m.t.elements).map fun k => m.get (k + 1)

/-- Julia `m[ks]` (LG:303-310). -/
def getSub (m : LagrangeTriangles M) (ks : Array Nat) : LagrangeTriangles M :=
  let t := m.t.getSub ks
  let ei := m.ei.getSub ks
  let e := m.e.getSub ei.verts.toArray
  ⟨m.id, t, e, ei, if t.isCover then m.fullVerts else lagrangeVertices t ei M, m.fullVerts⟩

/-- Julia `getelement(m, i)` (LG:338-365, Q18a fixed): element `i` in subspace numbering
(corners through `verticesinv`; edge nodes keep upstream's unsigned formula with the full edge
ids). -/
def getElement (m : LagrangeTriangles M) (i : Nat) : Array Nat :=
  if m.verts.isOneTo then m.get i else
  if M = 1 then (m.t.getElement i).toArray else
  let ind := m.t.getFacet i
  let full := m.t.fullElem! (ind - 1)
  let ti := if m.t.isCover then full else full.map m.t.vinv.get1
  let np := m.t.nodes
  let ei := (m.ei.fullElem! (ind - 1)).toArray
  let base := ti.toArray ++ edgesIndex ei np M
  if M = 2 then base else base ++ centerIndex #[i] (np + (M - 1) * m.ei.nodes) (centerSimplex 3 M)

/-- Julia `subtopology(m)` (LG:64-67). -/
def subtopology (m : LagrangeTriangles M) : Array (Array Nat) :=
  if m.verts.isOneTo || m.t.isCover then m.topology
  else (Array.range m.t.elements).map fun k => m.getElement (k + 1)

/-- Julia `fullimmersion(m)` (LG:288-291). -/
def fullImmersion (m : LagrangeTriangles M) : LagrangeTriangles M :=
  let ind : IdxVec :=
    if m.t.isTotal then .oneTo m.totalNodes
    else if m.fullVerts.maximum == m.fullVerts.size then .oneTo m.fullVerts.size else m.fullVerts
  ⟨m.id, m.t.fullImmersion, m.e.fullImmersion, m.ei.fullImmersion, ind, ind⟩

/-- Julia `subimmersion(m)` (LG:382-391, Q18b fixed). -/
def subImmersion (m : LagrangeTriangles M) : LagrangeTriangles M :=
  if m.t.isCover then m else
  let ver : IdxVec := if m.verts.isOneTo then m.verts else .oneTo m.nodes
  ⟨0, m.t.subImmersion, m.e.subImmersion, m.ei.subImmersion, ver, ver⟩

/-- Julia `refine(m)` (LG:419-432). -/
def refine (m : LagrangeTriangles M) : LagrangeTriangles M :=
  if !m.verts.isOneTo && !m.t.sub.isOneTo then m else
  let (i, fi) :=
    if m.verts.isOneTo then
      let i := m.verts.collect
      (i, if m.verts.eqv m.fullVerts then i else m.fullVerts.collect)
    else (m.verts, m.fullVerts)
  ⟨m.id, m.t.refine, m.e.refine, m.ei.refine, i, fi⟩

/-- Julia's type string `LagrangeTriangles{M, N, P, F, T}`. -/
def typeString (m : LagrangeTriangles M) : String :=
  s!"LagrangeTriangles\{{M}, {lagrangeSimplex 3 M}, {m.verts.typeString}, {m.t.sub.typeString}, ({m.t.isTotal}, {m.t.isFull})}"

/-- Julia `summary(m)` (MT:704-714). -/
def summary (m : LagrangeTriangles M) : String :=
  s!"{m.t.elements}×{lagrangeSimplex 3 M}{if m.t.isCover then "⊆" else "⊂"}{m.totalNodes} {m.typeString}"

end LagrangeTriangles

/-! ## LagrangeTetrahedra -/

/-- Julia `LagrangeTetrahedra{M}` (LG:99-114). -/
structure LagrangeTetrahedra (M : Nat) where
  /-- Bundle id. -/
  id : Nat
  /-- The tetrahedral mesh (Julia `t`). -/
  t : SimplexTopology 4
  /-- Its facets, first appearance (Julia `f`). -/
  f : SimplexTopology 3
  /-- Its edges, colex (Julia `e`). -/
  e : SimplexTopology 2
  /-- Element → facet ids, the facet opposite local vertex `k` in slot `k` (Julia `fi`). -/
  fi : SimplexTopology 4
  /-- Element → edge ids, lexicographic local pairs (Julia `ei`). -/
  ei : SimplexTopology 6
  /-- Subspace nodes (Julia `i`). -/
  verts : IdxVec
  /-- Full nodes (Julia `I`). -/
  fullVerts : IdxVec

namespace LagrangeTetrahedra

variable {M : Nat}

/-- Julia `lagrangevertices4(t, ei, fi, np, ne, nf, Val(M))` (LG:185-190). -/
def lagrangeVertices (t : SimplexTopology 4) (ei : SimplexTopology 6) (fi : SimplexTopology 4)
    (M : Nat) : IdxVec :=
  if M = 1 then t.verts else
  let np := t.totalNodes
  let ne := ei.totalNodes
  let nf := fi.totalNodes
  .arr (t.verts.toArray ++ edgesIndex ei.verts.toArray np M ++
    (if M ≤ 2 then #[] else facetsIndex fi.verts.toArray np ne M) ++
    centerIndex t.sub.toArray (np + (M - 1) * ne + facetSimplex 4 M * nf) (centerSimplex 4 M))

/-- Julia `LagrangeTetrahedra{M}(id, t, f, e, fi, ei)` (LG:145-150, Q18e fixed: the node count
includes facet and cell nodes). -/
def ofParts (t : SimplexTopology 4) (f : SimplexTopology 3) (e : SimplexTopology 2)
    (fi : SimplexTopology 4) (ei : SimplexTopology 6) (id : Nat := t.id) : LagrangeTetrahedra M :=
  let I : IdxVec := .oneTo (t.totalNodes + (M - 1) * ei.totalNodes + facetSimplex 4 M * fi.totalNodes +
    centerSimplex 4 M * t.totalElements)
  ⟨id, t, f, e, fi, ei, if t.isCover then I else lagrangeVertices t ei fi M,
    if t.isCover then I else I.collect⟩

/-- Julia `LagrangeTetrahedra{M}(t)` (LG:134-141). -/
def ofCorners (t : SimplexTopology 4) (id : Nat := t.id) : LagrangeTetrahedra M :=
  let e := t.edges
  let (f, fi) := t.facetsIndices
  ofParts t f e fi (t.edgesIndicesWith e) id

/-- Julia `totaledges(m)`. -/
def totalEdges (m : LagrangeTetrahedra M) : Nat := m.ei.totalNodes
/-- Julia `totalfacets(m)`. -/
def totalFacets (m : LagrangeTetrahedra M) : Nat := m.fi.totalNodes
/-- Julia `totalcornernodes(m)`. -/
def totalCornerNodes (m : LagrangeTetrahedra M) : Nat := m.t.totalNodes
/-- Julia `totaledgesnodes(m)`. -/
def totalEdgesNodes (m : LagrangeTetrahedra M) : Nat := (M - 1) * m.totalEdges
/-- Julia `totalfacetsnodes(m)`. -/
def totalFacetsNodes (m : LagrangeTetrahedra M) : Nat := facetSimplex 4 M * m.totalFacets
/-- Julia `totalcenternodes(m)`. -/
def totalCenterNodes (m : LagrangeTetrahedra M) : Nat := centerSimplex 4 M * m.t.totalElements
/-- Julia `totalnodes(m)` (LG:168). -/
def totalNodes (m : LagrangeTetrahedra M) : Nat :=
  m.totalCornerNodes + m.totalEdgesNodes + m.totalFacetsNodes + m.totalCenterNodes
/-- Julia `cornernodes(m)`. -/
def cornerNodes (m : LagrangeTetrahedra M) : Nat := m.t.nodes
/-- Julia `edgesnodes(m)`. -/
def edgesNodes (m : LagrangeTetrahedra M) : Nat := (M - 1) * m.ei.nodes
/-- Julia `facetsnodes(m)`. -/
def facetsNodes (m : LagrangeTetrahedra M) : Nat := facetSimplex 4 M * m.fi.nodes
/-- Julia `centernodes(m)`. -/
def centerNodes (m : LagrangeTetrahedra M) : Nat := centerSimplex 4 M * m.t.elements
/-- Julia `nodes(m)` (LG:171). -/
def nodes (m : LagrangeTetrahedra M) : Nat :=
  m.cornerNodes + m.edgesNodes + m.facetsNodes + m.centerNodes

/-- Julia `m[i]` (LG:268-282): corners, the edge nodes (all local edges' first nodes, then second
nodes, …, no orientation, Q18c), the facet nodes likewise, then the cell nodes of the full element
(Q18d fixed). -/
def get (m : LagrangeTetrahedra M) (i : Nat) : Array Nat :=
  let ind := m.t.getFacet i
  let ti := (m.t.fullElem! (ind - 1)).toArray
  if M = 1 then ti else
  let np := m.t.totalNodes
  let ei := (m.ei.fullElem! (ind - 1)).toArray
  if M = 2 then ti ++ ei.map (· + np) else
  let ne := m.ei.totalNodes
  let nf := m.fi.totalNodes
  let fi := (m.fi.fullElem! (ind - 1)).toArray
  ti ++ edgesIndex ei np M ++ facetsIndex fi np ne M ++
    centerIndex #[ind] (np + (M - 1) * ne + facetSimplex 4 M * nf) (centerSimplex 4 M)

/-- Julia `collect(m)`. -/
def topology (m : LagrangeTetrahedra M) : Array (Array Nat) :=
  (Array.range m.t.elements).map fun k => m.get (k + 1)

/-- Julia `m[ks]` (LG:311-320). -/
def getSub (m : LagrangeTetrahedra M) (ks : Array Nat) : LagrangeTetrahedra M :=
  let t := m.t.getSub ks
  let fi := (m.fi.getSub ks).refine
  let ei := m.ei.getSub ks
  let f := (m.f.getSub fi.verts.toArray).refine
  let e := m.e.getSub ei.verts.toArray
  ⟨m.id, t, f, e, fi, ei, if t.isCover then m.fullVerts else lagrangeVertices t ei fi M, m.fullVerts⟩

/-- Julia `getelement(m, i)` (LG:338-369, Q18a fixed; degree 3 uses the triangle formula, as
upstream dispatches). -/
def getElement (m : LagrangeTetrahedra M) (i : Nat) : Array Nat :=
  if m.verts.isOneTo then m.get i else
  if M = 1 then (m.t.getElement i).toArray else
  let ind := m.t.getFacet i
  let full := m.t.fullElem! (ind - 1)
  let ti := (if m.t.isCover then full else full.map m.t.vinv.get1).toArray
  let np := m.t.nodes
  let ne := m.ei.nodes
  let ei := (m.ei.fullElem! (ind - 1)).toArray
  if M = 2 then ti ++ edgesIndex ei np M
  else if M = 3 then ti ++ edgesIndex ei np M ++ centerIndex #[i] (np + (M - 1) * ne) (centerSimplex 3 M)
  else
    let nf := m.fi.nodes
    let fi := (m.fi.fullElem! (ind - 1)).toArray
    ti ++ edgesIndex ei np M ++ facetsIndex fi np ne M ++
      centerIndex #[i] (np + (M - 1) * ne + facetSimplex 4 M * nf) (centerSimplex 4 M)

/-- Julia `subtopology(m)` (LG:64-67). -/
def subtopology (m : LagrangeTetrahedra M) : Array (Array Nat) :=
  if m.verts.isOneTo || m.t.isCover then m.topology
  else (Array.range m.t.elements).map fun k => m.getElement (k + 1)

/-- Julia `fullimmersion(m)` (LG:292-295). -/
def fullImmersion (m : LagrangeTetrahedra M) : LagrangeTetrahedra M :=
  let ind : IdxVec :=
    if m.t.isTotal then .oneTo m.totalNodes
    else if m.fullVerts.maximum == m.fullVerts.size then .oneTo m.fullVerts.size else m.fullVerts
  ⟨m.id, m.t.fullImmersion, m.f.fullImmersion, m.e.fullImmersion, m.fi.fullImmersion,
    m.ei.fullImmersion, ind, ind⟩

/-- Julia `subimmersion(m)` (LG:393-402, Q18b fixed). -/
def subImmersion (m : LagrangeTetrahedra M) : LagrangeTetrahedra M :=
  if m.t.isCover then m else
  let ver : IdxVec := if m.verts.isOneTo then m.verts else .oneTo m.nodes
  ⟨0, m.t.subImmersion, m.f.subImmersion, m.e.subImmersion, m.fi.subImmersion, m.ei.subImmersion,
    ver, ver⟩

/-- Julia `refine(m)` (LG:434-447). -/
def refine (m : LagrangeTetrahedra M) : LagrangeTetrahedra M :=
  if !m.verts.isOneTo && !m.t.sub.isOneTo then m else
  let (i, fi) :=
    if m.verts.isOneTo then
      let i := m.verts.collect
      (i, if m.verts.eqv m.fullVerts then i else m.fullVerts.collect)
    else (m.verts, m.fullVerts)
  ⟨m.id, m.t.refine, m.f.refine, m.e.refine, m.fi.refine, m.ei.refine, i, fi⟩

/-- Julia's type string `LagrangeTetrahedra{M, N, P, F, T}`. -/
def typeString (m : LagrangeTetrahedra M) : String :=
  s!"LagrangeTetrahedra\{{M}, {lagrangeSimplex 4 M}, {m.verts.typeString}, {m.t.sub.typeString}, ({m.t.isTotal}, {m.t.isFull})}"

/-- Julia `summary(m)`. -/
def summary (m : LagrangeTetrahedra M) : String :=
  s!"{m.t.elements}×{lagrangeSimplex 4 M}{if m.t.isCover then "⊆" else "⊂"}{m.totalNodes} {m.typeString}"

/-! ### Oriented (conforming) node lists -/

/-- The lattice points with all weights `≥ 1` summing to `M` over `k` vertices (the interior
nodes of a `k`-vertex entity of a degree-`M` element), in a fixed canonical order: by the total
weight of vertices `2..k`, then recursively. -/
def interiorLattice (k M : Nat) : Array (Array Nat) :=
  go k M
where
  /-- Compositions of `m` into `k` positive parts. -/
  go : Nat → Nat → Array (Array Nat)
    | 0, _ => #[]
    | 1, m => if m ≥ 1 then #[#[m]] else #[]
    | k + 1, m =>
      -- the first weight is determined by the rest
      (Array.range m).flatMap fun r =>
        if 1 ≤ m - r ∧ r ≥ k then (go k r).map fun w => #[m - r] ++ w else #[]

/-- The canonical interior-node number (1-based) of an entity point with weights `w` on
the entity's vertices sorted by global id. -/
def latticeIndex (k M : Nat) (w : Array Nat) : Nat :=
  ((interiorLattice k M).findIdx? (· == w)).map (· + 1) |>.getD 0

/-- Weights of a point listed on vertices `vs` (element-local order), re-expressed on the same
vertices sorted by global id. -/
def sortWeights (vs w : Array Nat) : Array Nat :=
  let order := (Array.range vs.size).qsort fun a b => vs[a]! < vs[b]!
  order.map (w[·]!)

/-- The node list of element `i` with oriented edge and facet nodes (not in Julia): every edge
and facet interior node is numbered by its lattice point relative to the entity's vertices
sorted by global id, so elements sharing an edge or facet agree on its nodes whatever their
vertex order (Julia's `get` agrees only for elements whose tuples are sorted, Q18c). Local order:
corners, each lexicographic local edge from its first to its second vertex, each facet (Julia's
slot order) through its lattice points in local vertex order, then the cell nodes. -/
def getConforming (m : LagrangeTetrahedra M) (i : Nat) : Array Nat :=
  let ind := m.t.getFacet i
  let ti := (m.t.fullElem! (ind - 1)).toArray
  if M ≤ 1 then ti else
  let np := m.t.totalNodes
  let ne := m.ei.totalNodes
  let nf := m.fi.totalNodes
  let es := M - 1
  let fs := facetSimplex 4 M
  let ei := (m.ei.fullElem! (ind - 1)).toArray
  let fi := (m.fi.fullElem! (ind - 1)).toArray
  let pairs := combinationsIdx 4 2
  let edgeNodes := (Array.range 6).flatMap fun j =>
    let (a, b) := (pairs[j]![0]!, pairs[j]![1]!)
    (Array.range es).map fun k =>
      -- weight k+1 on the second vertex
      let w := sortWeights #[ti[a]!, ti[b]!] #[M - (k + 1), k + 1]
      np + es * (ei[j]! - 1) + (latticeIndex 2 M w)
  let facetNodes := (Array.range 4).flatMap fun slot =>
    -- slot k holds the facet opposite local vertex k
    let loc := (Array.range 4).filter (· ≠ slot)
    let vs := loc.map (ti[·]!)
    (interiorLattice 3 M).map fun w =>
      np + es * ne + fs * (fi[slot]! - 1) + latticeIndex 3 M (sortWeights vs w)
  ti ++ edgeNodes ++ facetNodes ++
    centerIndex #[ind] (np + es * ne + fs * nf) (centerSimplex 4 M)

end LagrangeTetrahedra

/-! ## Refinement (element.jl:409-465) -/

/-- Julia `refinetriangle(t)` (element.jl:419-455): the linear triangles (as local node indices,
1-based) subdividing a degree-`M` triangle, `M ≤ 4`. -/
def refineTriangleTable : Nat → Option (Array (Vector Nat 3))
  | 1 => some #[#v[1, 2, 3]]
  | 2 => some #[#v[1, 6, 5], #v[2, 4, 6], #v[3, 5, 4], #v[4, 5, 6]]
  | 3 => some #[#v[1, 8, 7], #v[2, 4, 9], #v[3, 6, 5], #v[8, 9, 10], #v[9, 4, 10], #v[4, 5, 10],
      #v[5, 6, 10], #v[6, 7, 10], #v[7, 8, 10]]
  | 4 => some #[#v[1, 10, 9], #v[2, 4, 12], #v[3, 7, 6], #v[11, 12, 15], #v[12, 4, 15], #v[4, 5, 15],
      #v[5, 6, 14], #v[6, 7, 14], #v[7, 8, 14], #v[8, 9, 13], #v[9, 10, 13], #v[10, 11, 13],
      #v[11, 15, 13], #v[5, 14, 15], #v[8, 13, 14], #v[13, 15, 14]]
  | _ => none

namespace LagrangeTriangles

variable {M : Nat}

/-- Julia `refinement(t::LagrangeTriangles)` (element.jl:413-417): the linear triangle mesh of
the degree-`M` nodes (`M²` triangles per element); `none` for `M ≥ 5` (no table upstream). -/
def refinement (m : LagrangeTriangles M) : Option (SimplexTopology 3) :=
  if M = 1 then some m.t else do
  let tbl ← refineTriangleTable M
  let out := m.topology.flatMap fun el => tbl.map fun r => r.map (el[· - 1]!)
  return SimplexTopology.ofElements out 0 (some m.nodes) (some m.verts)

end LagrangeTriangles

/-- Julia `refinement(t::LagrangeTetrahedra)` (element.jl:459-465): only degree 1 (`none`
otherwise, as upstream has no table). -/
def LagrangeTetrahedra.refinement {M : Nat} (m : LagrangeTetrahedra M) : Option (SimplexTopology 4) :=
  if M = 1 then some m.t else none

end MeshTopology

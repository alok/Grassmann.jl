import Tests.MeshTopology.Util

/-!
SimplexTopology / DiscontinuousTopology goldens (`simplex.json`): hand-made and randomly
relabelled triangle, tetrahedron, edge and 4-simplex meshes (non-contiguous ids, degenerate
elements, dropped elements), every accessor, sub-mesh and element-level quantity of
MeshTopology.jl's `element.jl`, on the full mesh and on element and vertex subsets.
-/

open Lean MeshTopology Tests.Small

namespace Tests.MeshTopology.Simplex

/-- An element list of a golden mesh. -/
def elemsOf (N : Nat) (j : Json) : TestM (Array (Vector Nat N)) := do
  (← jArr j).mapM fun e => do vecOf (← natsOf e) N

/-- The accessor dump of a simplex topology (`infoj`). -/
def jinfo {N : Nat} (t : SimplexTopology N) : Json :=
  let kind (v : IdxVec) : Json := if v.isOneTo then "OneTo" else "Vector"
  Json.mkObj [("elements", jvecsN t.topology), ("vertices", jnats t.verts.toArray),
    ("vkind", kind t.verts), ("fullvertices", jnats t.fullVerts.toArray),
    ("verticesinv", jnats t.vinv.toArray), ("subelements", jnats t.sub.toArray),
    ("fkind", kind t.sub), ("totalnodes", jnat t.totalNodes), ("totalelements", jnat t.totalElements),
    ("nodes", jnat t.nodes), ("elementcount", jnat t.elements), ("istotal", jbool t.isTotal),
    ("isfull", jbool t.isFull), ("iscover", jbool t.isCover), ("summary", jstr t.summary)]

/-- The accessor dump of a discontinuous topology (`dinfoj`). -/
def jdinfo {N : Nat} (d : DiscontinuousTopology N) : Json :=
  let kind (v : IdxVec) : Json := if v.isOneTo then "OneTo" else "Vector"
  Json.mkObj [("elements", jvecsN d.topology), ("vertices", jnats d.verts.toArray),
    ("vkind", kind d.verts), ("fullvertices", jnats d.fullVerts.toArray),
    ("subelements", jnats d.t.sub.toArray), ("totalnodes", jnat d.totalNodes),
    ("totalelements", jnat d.totalElements), ("nodes", jnat d.nodes),
    ("elementcount", jnat d.elements), ("istotal", jbool d.t.isTotal), ("isfull", jbool d.t.isFull),
    ("iscover", jbool d.isCover), ("isdisconnected", jbool d.isDisconnected),
    ("summary", jstr d.summary)]

/-- A dense integer matrix `{dims, colmajor}`. -/
def jdense (A : SparseInt) : Json := jgrid [A.m, A.n] (A.toDense.map jint)

/-- `[elements, coefficients]` of an oriented face list (`facesj`). -/
def jfaces {k : Nat} (r : SimplexTopology k × Array Int) : Json :=
  Json.arr #[jvecsN r.1.topology, jints r.2]

/-- A golden float (`"Inf"` for infinity). -/
def floatOf (j : Json) : TestM Float := do
  match j with
  | .str "Inf" => return 1.0 / 0.0
  | .str "-Inf" => return -1.0 / 0.0
  | .num n => return n.toFloat
  | _ => throw <| IO.userError s!"not a float: {j.compress}"

/-- Compare floats exactly (the goldens are exact reciprocals and their sums). -/
def checkFloats (label : String) (got : FloatArray) (golden : Json) : TestM Unit := do
  let e := expected golden
  if isError e then return
  let xs ← (← jArr e).mapM floatOf
  check label (xs.size == got.size && (Array.range xs.size).all fun k => xs[k]! == got[k]!)
    fun _ => s!"got {got.toList.take 12}, expected {xs.toList.take 12}"

/-- Compare a dense float matrix. -/
def checkDenseF (label : String) (A : SparseFloat) (golden : Json) : TestM Unit := do
  let e := expected golden
  if isError e then return
  checkJ s!"{label} dims" (toJson #[A.m, A.n]) (← jField e "dims")
  checkFloats label A.toDense (← jField e "colmajor")

/-- Element-level quantities (`elementops`). -/
def checkOps {N : Nat} (lbl : String) (t : SimplexTopology N) (c : Json) : TestM Unit := do
  let cols (v : Vector (Array Nat) N) : Json := Json.arr (v.toArray.map jnats)
  checkJ s!"{lbl} columns" (cols t.columns) (← jField c "columns")
  checkJ s!"{lbl} reducedcolumns" (cols t.reducedColumns) (← jField c "reducedcolumns")
  checkJ s!"{lbl} incidence" (jdense t.incidence) (← jField c "incidence")
  checkJ s!"{lbl} degrees" (jnats t.degrees) (← jField c "degrees")
  checkFloats s!"{lbl} weights" t.weights (← jField c "weights")
  checkJ s!"{lbl} degrees(t,B)" (jints (SimplexTopology.degreesOf t.incidence)) (← jField c "degrees_B")
  checkDenseF s!"{lbl} interp" t.interp (← jField c "interp")
  checkDenseF s!"{lbl} pretni" t.pretni (← jField c "pretni")
  if 2 ≤ N then
    checkJ s!"{lbl} sparse" (jdense t.sparse) (← jField c "sparse")
    checkJ s!"{lbl} adjacency" (jdense t.adjacency) (← jField c "adjacency")
    checkJ s!"{lbl} antiadjacency" (jdense t.antiadjacency) (← jField c "antiadjacency")
    checkJ s!"{lbl} edges" (jinfo t.edges) (← jField c "edges")
    checkJ s!"{lbl} edgesindices" (jinfo t.edgesIndices) (← jField c "edgesindices")
    checkJ s!"{lbl} neighbors" (jvecsN t.neighbors) (← jField c "neighbors")
    checkJ s!"{lbl} facetsigns" (jvecs t.facetSigns) (← jField c "facetsigns")
    checkJ s!"{lbl} facets" (jinfo t.facets) (← jField c "facets")
    let ones := Array.replicate t.elements (1 : Int)
    checkJ s!"{lbl} facets(t,1)" (jfaces (t.facetsWith ones)) (← jField c "facets_h")
    checkJ s!"{lbl} facets(t,1:n)"
      (jfaces (t.facetsWith ((Array.range t.elements).map fun (k : Nat) => Int.ofNat k + 1))) (← jField c "facets_h2")
    let (fi, again) := t.facetsInterior
    checkJ s!"{lbl} facetsinterior" (Json.arr #[jvecsN fi.topology, jnats again])
      (← jField c "facetsinterior")
    let fs ← gArr c "faces"
    for k in [0:N] do
      checkJ s!"{lbl} faces {k + 1}" (jinfo (t.faces (k + 1))) fs[k]!
    let fh ← gArr c "faces_h"
    for k in [0:N - 1] do
      checkJ s!"{lbl} faces(t,1,{k + 1})" (jfaces (t.facesWith ones (k + 1))) fh[k]!
    checkJ s!"{lbl} skeleton" (Json.arr (t.skeleton.map fun ⟨_, r⟩ => jfaces r)) (← jField c "skeleton")
  if 3 ≤ N then
    let (f, fi) := t.facetsIndices
    checkJ s!"{lbl} facetsindices" (Json.arr #[jinfo f, jinfo fi]) (← jField c "facetsindices")

/-- One mesh of `simplex.json`. -/
def checkMesh {N : Nat} (name : String) (t : SimplexTopology N) (c : Json) : TestM Unit := do
  checkJ s!"{name} info" (jinfo t) (← jField c "info")
  checkOps name t c
  if 2 ≤ N ∧ N ≤ 5 then
    let es ← gArr c "edgesigns"
    let lf ← gArr c "localfacets"
    for k in [0:t.elements] do
      let e := t.get (k + 1)
      -- a segment's `edgesigns` is a scalar in Julia
      let sg := edgeSigns e
      checkJ s!"{name} edgesigns {k + 1}" (if N = 2 then jint sg[0]! else jints sg) es[k]!
      checkJ s!"{name} localfacets {k + 1}" (Json.arr ((localFacets e).map jnats)) lf[k]!
  let ks ← natsOf (← jField c "ks")
  let vs ← natsOf (← jField c "vs")
  let s := t.getSub ks
  checkJ s!"{name} t[ks]" (jinfo s) (← jField c "subset")
  checkOps s!"{name} t[ks]" s (← jField c "subset_ops")
  checkJ s!"{name} t[ks] subtopology" (jvecsN s.subtopology) (← jField c "subset_subtopology")
  checkJ s!"{name} t[ks] subimmersion" (jinfo s.subImmersion) (← jField c "subset_subimmersion")
  checkJ s!"{name} t[ks] complement" (jinfo s.complement) (← jField c "subset_complement")
  checkJ s!"{name} t[ks] fullimmersion" (jinfo s.fullImmersion) (← jField c "subset_fullimmersion")
  checkJ s!"{name} t[ks] getelement"
    (jvecsN ((Array.range s.elements).map fun k => s.getElement (k + 1))) (← jField c "subset_getelement")
  checkJ s!"{name} t[ks] getimage"
    (jnats ((Array.range s.nodes).map fun k => s.getImage (k + 1))) (← jField c "subset_getimage")
  checkJ s!"{name} t[ks] refine" (jinfo s.refine) (← jField c "subset_refine")
  checkJ s!"{name} t[ks][[end]]" (jinfo (s.getSub #[ks.size])) (← jField c "subsubset")
  checkJ s!"{name} t[ks](vs)" (jinfo (s.byVertices vs)) (← jField c "subset_byvertices")
  let b := t.byVertices vs
  checkJ s!"{name} t(vs)" (jinfo b) (← jField c "byvertices")
  checkJ s!"{name} t(vs) subtopology" (jvecsN b.subtopology) (← jField c "byvertices_subtopology")
  checkJ s!"{name} t(vs) subimmersion" (jinfo b.subImmersion) (← jField c "byvertices_subimmersion")
  checkJ s!"{name} t(vs) complement" (jinfo b.complement) (← jField c "byvertices_complement")
  checkJ s!"{name} untotal" (jinfo (t.untotal (t.totalNodes + 2))) (← jField c "untotal")
  checkJ s!"{name} refine" (jinfo t.refine) (← jField c "refine")
  checkJ s!"{name} fullimmersion" (jinfo t.fullImmersion) (← jField c "fullimmersion")
  checkJ s!"{name} subimmersion" (jinfo t.subImmersion) (← jField c "subimmersion")
  checkJ s!"{name} subtopology" (jvecsN t.subtopology) (← jField c "subtopology")
  checkJ s!"{name} getimage" (jnats ((Array.range t.nodes).map fun k => t.getImage (k + 1)))
    (← jField c "getimage")
  -- discontinuous
  let d := t.discontinuous
  checkJ s!"{name} discontinuous" (jdinfo d) (← jField c "discontinuous")
  checkJ s!"{name} discontinuousvertices" (jnats d.discontinuousVertices) (← jField c "discontinuousvertices")
  checkJ s!"{name} disconnect" (jdinfo t.disconnect) (← jField c "disconnect")
  checkJ s!"{name} d fullimmersion" (jdinfo d.fullImmersion) (← jField c "d_fullimmersion")
  let ds := d.getSub ks
  checkJ s!"{name} d[ks]" (jdinfo ds) (← jField c "d_subset")
  checkJ s!"{name} d[ks] fullimmersion" (jdinfo ds.fullImmersion) (← jField c "d_subset_fullimmersion")
  checkJ s!"{name} d[ks] subimmersion" (jdinfo ds.subImmersion) (← jField c "d_subset_subimmersion")
  checkJ s!"{name} d[ks] subtopology" (jvecsN ds.subtopology) (← jField c "d_subset_subtopology")
  checkJ s!"{name} d[ks] getimage" (jnats ((Array.range ds.nodes).map fun k => ds.getImage (k + 1)))
    (← jField c "d_subset_getimage")
  checkJ s!"{name} d[ks] disconnect" (jdinfo ds.disconnect) (← jField c "d_subset_disconnect")
  checkJ s!"{name} d[ks] refine" (jdinfo ds.refine) (← jField c "d_subset_refine")
  checkJ s!"{name} d(vs)" (jdinfo (d.byVertices vs)) (← jField c "d_byvertices")
  checkJ s!"{name} d neighbors" (jvecsN d.t.neighbors) (← jField c "d_neighbors")
  checkJ s!"{name} interp(d, b)"
    (jnats (d.interp ((Array.range t.totalElements).map fun k => 10 * (k + 1)))) (← jField c "d_interp")
  if h : N = 3 then
    let d3 : DiscontinuousTopology 3 := h ▸ d
    let t3 : SimplexTopology 3 := h ▸ t
    checkJ s!"{name} edges(d)" (jinfo d3.edges) (← jField c "d_edges")
    let (top, coef) := t3.facetsWith (Array.replicate t3.elements 1)
    let bnd := SimplexTopology.ofElements
      ((Array.range top.elements).filterMap fun k => if coef[k]! != 0 then some (top.get (k + 1)) else none)
      0 (some t3.totalNodes)
    checkJ s!"{name} boundary" (jinfo bnd) (← jField c "boundary")
    checkJ s!"{name} interior" (jnats bnd.interiorNodes) (← jField c "interior")
    checkJ s!"{name} discontinuousboundary" (jvecsN (d3.boundary bnd).topology)
      (← jField c "discontinuousboundary")

/-- The standalone helpers of `simplex.json`'s `misc`. -/
def checkMisc (j : Json) : TestM Unit := do
  for c in ← gArr j "interior" do
    checkJ "interior" (jnats (interior (← natsOf (← jField c "fixed")) (← gNat c "neq"))) (← jField c "out")
  for c in ← gArr j "invmap" do
    checkJ "invmap" (jnat (invmap #v[4, 7, 9] (← gNat c "n"))) (← jField c "out")
  for c in ← gArr j "findmissing" do
    let n ← vecOf (← natsOf (← jField c "n")) 2
    checkJ s!"findmissing {n.toArray}" (jnat (findmissing n)) (← jField c "out")
  for c in ← gArr j "neighbor" do
    let ab ← (← gArr c "ab").mapM natsOf
    checkJ "neighbor" (jnat (neighbor (← gNat c "k") ab.toList)) (← jField c "out")
  for c in ← gArr j "facetsign" do
    checkJ "facetsign" (jint (SimplexTopology.facetSign (← gNat c "i") (← gNat c "ni"))) (← jField c "out")
  for c in ← gArr j "verticesinv" do
    let v := verticesInv (← gNat c "n") (.arr (← natsOf (← jField c "ind")))
    checkJ "verticesinv" (jnats v.toArray) (← jField c "out")
  for c in ← gArr j "vertices" do
    let els ← (← gArr c "t").mapM natsOf
    let v := verticesOf (els.flatMap id)
    checkJ "vertices" (jnats v.toArray) (← jField c "out")
    checkJ "vertices kind" (jstr (if v.isOneTo then "OneTo" else "Vector")) (← jField c "kind")
  -- assemblelocal! into a 4×4 zero matrix
  let M := FloatArray.mk (Array.replicate 16 0.0)
  let M := assembleLocal M 4 (FloatArray.mk #[1.0, 3.0, 2.0, 4.0]) 0.5 #v[2, 4]
  let M := assembleLocal M 4 (FloatArray.mk #[1.0, -1.0, 0.0, -1.0, 2.0, 1.0, 0.0, 1.0, 3.0]) 1.0 #v[1, 2, 4]
  checkFloats "assemblelocal!" M (← jField (← jField j "assemblelocal") "colmajor")

/-- Run `simplex.json`. -/
def run : TestM Unit := do
  let j ← readJson "oracle/golden/meshtopology/simplex.json"
  for c in ← gArr j "meshes" do
    let name ← gStr c "name"
    match ← gNat c "N" with
    | 2 => checkMesh name (.ofElements (← elemsOf 2 (← jField c "mesh"))) c
    | 3 => checkMesh name (.ofElements (← elemsOf 3 (← jField c "mesh"))) c
    | 4 => checkMesh name (.ofElements (← elemsOf 4 (← jField c "mesh"))) c
    | 5 => checkMesh name (.ofElements (← elemsOf 5 (← jField c "mesh"))) c
    | n => throw <| IO.userError s!"unsupported N = {n}"
  checkMisc (← jField j "misc")

end Tests.MeshTopology.Simplex

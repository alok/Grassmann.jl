import Tests.MeshTopology.Simplex

/-!
Lagrange goldens (`lagrange.json`): degree 1-5 Lagrange edges, triangles and tetrahedra on every
mesh of `simplex.json`, with node counts, element node lists, vertex lists, subsets, renumbered
elements, sub- and full immersions, refinement and the local refinement tables. Plus property
tests of conformity: elements sharing an edge or facet must give its interior lattice points the
same node ids (Julia's triangles and the oriented tetrahedra do; Julia's tetrahedra only on
sorted element tuples, Q18c).
-/

open Lean MeshTopology Tests.Small Tests.MeshTopology.Simplex

namespace Tests.MeshTopology.Lagrange

/-- Node lists. -/
def jlists (a : Array (Array Nat)) : Json := Json.arr (a.map jnats)

/-- Common fields of `linfoj`. -/
def jcommon {N : Nat} (summary : String) (totalNodes nodes : Nat) (els : Array (Array Nat)) (verts fullVerts : IdxVec)
    (t : SimplexTopology N) (tcn ten cn en te : Nat) : List (String × Json) :=
  [("summary", jstr summary), ("totalnodes", jnat totalNodes), ("nodes", jnat nodes),
   ("elements", jlists els), ("vertices", jnats verts.toArray),
   ("vkind", jstr (if verts.isOneTo then "OneTo" else "Vector")),
   ("fullvertices", jnats fullVerts.toArray), ("elementcount", jnat t.elements),
   ("totalelements", jnat t.totalElements), ("iscover", jbool t.isCover),
   ("totalcornernodes", jnat tcn), ("totaledgesnodes", jnat ten), ("cornernodes", jnat cn),
   ("edgesnodes", jnat en), ("totaledges", jnat te)]

/-- `linfoj` of Lagrange edges. -/
def jedges {M : Nat} (m : LagrangeEdges M) : Json :=
  Json.mkObj (jcommon m.summary m.totalNodes m.nodes m.topology m.verts m.fullVerts m.t
    m.totalCornerNodes m.totalEdgesNodes m.cornerNodes m.edgesNodes m.totalEdges)

/-- `linfoj` of Lagrange triangles. -/
def jtris {M : Nat} (m : LagrangeTriangles M) : Json :=
  Json.mkObj (jcommon m.summary m.totalNodes m.nodes m.topology m.verts m.fullVerts m.t
    m.totalCornerNodes m.totalEdgesNodes m.cornerNodes m.edgesNodes m.totalEdges ++
    [("totalcenternodes", jnat m.totalCenterNodes), ("centernodes", jnat m.centerNodes),
     ("totalfacets", jnat m.totalEdges)])

/-- `linfoj` of Lagrange tetrahedra. -/
def jtets {M : Nat} (m : LagrangeTetrahedra M) : Json :=
  Json.mkObj (jcommon m.summary m.totalNodes m.nodes m.topology m.verts m.fullVerts m.t
    m.totalCornerNodes m.totalEdgesNodes m.cornerNodes m.edgesNodes m.totalEdges ++
    [("totalcenternodes", jnat m.totalCenterNodes), ("centernodes", jnat m.centerNodes),
     ("totalfacets", jnat m.totalFacets), ("totalfacetsnodes", jnat m.totalFacetsNodes),
     ("facetsnodes", jnat m.facetsNodes)])

/-- The golden checks shared by the three families. -/
structure Family (L : Type) where
  info : L → Json
  refinement : L → Option Json
  subtopology : L → Array (Array Nat)
  getSub : L → Array Nat → L
  getElement : L → Nat → Array Nat
  elements : L → Nat
  subImmersion : L → L
  fullImmersion : L → L
  refine : L → L

/-- Check one `lagrange.json` case. -/
def checkFamily {L : Type} (F : Family L) (lbl : String) (m : L) (c : Json) : TestM Unit := do
  let ks ← natsOf (← jField c "ks")
  checkJ s!"{lbl} info" (F.info m) (← jField c "info")
  checkOptJ s!"{lbl} refinement" (F.refinement m) (← jField c "refinement")
  checkJ s!"{lbl} subtopology" (jlists (F.subtopology m)) (← jField c "subtopology")
  let s := F.getSub m ks
  checkJ s!"{lbl} [ks]" (F.info s) (← jField c "subset")
  checkJ s!"{lbl} [ks] getelement"
    (jlists ((Array.range (F.elements s)).map fun k => F.getElement s (k + 1))) (← jField c "subset_getelement")
  checkJ s!"{lbl} [ks] subimmersion" (F.info (F.subImmersion s)) (← jField c "subset_subimmersion")
  checkJ s!"{lbl} [ks] fullimmersion" (F.info (F.fullImmersion s)) (← jField c "subset_fullimmersion")
  checkJ s!"{lbl} [ks] refine" (F.info (F.refine s)) (← jField c "subset_refine")
  checkJ s!"{lbl} refine" (F.info (F.refine m)) (← jField c "refine")

/-- Lagrange edges. -/
def edgesFamily (M : Nat) : Family (LagrangeEdges M) :=
  { info := jedges, refinement := fun _ => none, subtopology := (·.subtopology)
    getSub := (·.getSub ·), getElement := (·.getElement ·), elements := (·.t.elements)
    subImmersion := (·.subImmersion), fullImmersion := (·.fullImmersion), refine := (·.refine) }

/-- Lagrange triangles. -/
def trisFamily (M : Nat) : Family (LagrangeTriangles M) :=
  { info := jtris, refinement := fun m => m.refinement.map jinfo, subtopology := (·.subtopology)
    getSub := (·.getSub ·), getElement := (·.getElement ·), elements := (·.t.elements)
    subImmersion := (·.subImmersion), fullImmersion := (·.fullImmersion), refine := (·.refine) }

/-- Lagrange tetrahedra. -/
def tetsFamily (M : Nat) : Family (LagrangeTetrahedra M) :=
  { info := jtets, refinement := fun m => m.refinement.map jinfo, subtopology := (·.subtopology)
    getSub := (·.getSub ·), getElement := (·.getElement ·), elements := (·.t.elements)
    subImmersion := (·.subImmersion), fullImmersion := (·.fullImmersion), refine := (·.refine) }

/-! ## Conformity -/

/-- The physical lattice point of each listed node of an element, when it lies on an edge or a
facet: the entity's global vertex ids sorted, with the weights on them. -/
abbrev Key := Array Nat × Array Nat

/-- Keys of an entity point given by weights `w` on the global vertices `vs`. -/
def keyOf (vs w : Array Nat) : Key :=
  let order := (Array.range vs.size).qsort fun a b => vs[a]! < vs[b]!
  (order.map (vs[·]!), order.map (w[·]!))

/-- Keys of Julia's triangle node list (`LagrangeTriangles.get`): local edge `v₂→v₃, v₃→v₁,
v₁→v₂`, node `j` at weight `j` on the traversal target. -/
def triKeys (M : Nat) (ti : Array Nat) : Array (Option Key) :=
  let edges : Array (Nat × Nat) := #[(1, 2), (2, 0), (0, 1)]
  #[none, none, none] ++ edges.flatMap fun (u, w) =>
    (Array.range (M - 1)).map fun j => some (keyOf #[ti[u]!, ti[w]!] #[M - (j + 1), j + 1])

/-- Keys of a tetrahedral node list, given how each list orders edge and facet nodes:
`edgeMajor` (oriented variant: each edge's nodes consecutively) or Julia's `k`-major order. -/
def tetKeys (M : Nat) (ti : Array Nat) (edgeMajor : Bool) : Array (Option Key) :=
  let es := M - 1
  let pairs := combinationsIdx 4 2
  let lattice := LagrangeTetrahedra.interiorLattice 3 M
  let edgeKey (j k : Nat) : Option Key :=
    let (a, b) := (pairs[j]![0]!, pairs[j]![1]!)
    some (keyOf #[ti[a]!, ti[b]!] #[M - (k + 1), k + 1])
  let facetKey (slot k : Nat) : Option Key :=
    let loc := (Array.range 4).filter (· ≠ slot)
    some (keyOf (loc.map (ti[·]!)) lattice[k]!)
  let edgeNodes := if edgeMajor then (Array.range 6).flatMap fun j => (Array.range es).map (edgeKey j)
    else (Array.range es).flatMap fun k => (Array.range 6).map (edgeKey · k)
  let facetNodes := if edgeMajor then (Array.range 4).flatMap fun s => (Array.range lattice.size).map (facetKey s)
    else (Array.range lattice.size).flatMap fun k => (Array.range 4).map (facetKey · k)
  #[none, none, none, none] ++ edgeNodes ++ facetNodes

/-- `true` when the keyed node ids are consistent across elements and injective. -/
def conforming (els : Array (Array Nat)) (keys : Array (Array (Option Key))) : Bool := Id.run do
  let mut byKey : Std.HashMap Key Nat := {}
  let mut byId : Std.HashMap Nat Key := {}
  for h : e in [0:els.size] do
    let ks := keys[e]!
    for h2 : j in [0:els[e].size] do
      if let some k := ks[j]?.join then
        let id := els[e][j]
        match byKey[k]?, byId[id]? with
        | some id', _ => if id' != id then return false
        | none, some k' => if k' != k then return false
        | none, none => pure ()
        byKey := byKey.insert k id
        byId := byId.insert id k
  return true

/-- Conformity of the triangle and tetrahedron node lists of a mesh. -/
def checkConformity {N : Nat} (name : String) (t : SimplexTopology N) : TestM Unit := do
  for M in [2, 3, 4, 5, 6] do
    if h : N = 3 then
      let L : LagrangeTriangles M := .ofCorners (h ▸ t)
      let els := L.topology
      check s!"{name} P{M} triangles conform"
        (conforming els (L.t.topology.map fun ti => triKeys M ti.toArray))
    if h : N = 4 then
      let L : LagrangeTetrahedra M := .ofCorners (h ▸ t)
      let tops := L.t.topology.map (·.toArray)
      let oriented := (Array.range L.t.elements).map fun k => L.getConforming (k + 1)
      check s!"{name} P{M} oriented tetrahedra conform"
        (conforming oriented (tops.map fun ti => tetKeys M ti true))
      -- oriented lists are permutations of Julia's
      check s!"{name} P{M} oriented tetrahedra reorder Julia's"
        ((Array.range L.t.elements).all fun k =>
          (L.get (k + 1)).qsort (· < ·) == (oriented[k]!).qsort (· < ·))
      let sorted := tops.all fun ti => ti == ti.qsort (· < ·)
      if sorted then
        check s!"{name} P{M} Julia tetrahedra conform (sorted tuples)"
          (conforming L.topology (tops.map fun ti => tetKeys M ti false))

/-- Run `lagrange.json` and the conformity properties. -/
def run : TestM Unit := do
  let s ← readJson "oracle/golden/meshtopology/simplex.json"
  let mut meshes : Std.HashMap String (Nat × Json) := {}
  for c in ← gArr s "meshes" do
    meshes := meshes.insert (← gStr c "name") (← gNat c "N", ← jField c "mesh")
  let j ← readJson "oracle/golden/meshtopology/lagrange.json"
  for c in ← gArr j "cases" do
    let name ← gStr c "mesh"
    let M ← gNat c "M"
    let some (N, mj) := meshes[name]? | throw <| IO.userError s!"unknown mesh {name}"
    let lbl := s!"{name} P{M}"
    match N with
    | 2 => checkFamily (edgesFamily M) lbl (.ofCorners (.ofElements (← elemsOf 2 mj))) c
    | 3 => checkFamily (trisFamily M) lbl (.ofCorners (.ofElements (← elemsOf 3 mj))) c
    | 4 => checkFamily (tetsFamily M) lbl (.ofCorners (.ofElements (← elemsOf 4 mj))) c
    | _ => pure ()
  for (n, tbl) in (← jField j "refinetriangle").getObj?.toOption.getD {} |>.toArray do
    let M := match n with | "6" => 2 | "10" => 3 | "15" => 4 | _ => 1
    checkOptJ s!"refinetriangle {n}" ((refineTriangleTable M).map fun a => jvecsN a) tbl
  for (name, (N, mj)) in meshes.toArray do
    match N with
    | 3 => checkConformity name (.ofElements (← elemsOf 3 mj))
    | 4 => checkConformity name (.ofElements (← elemsOf 4 mj))
    | _ => pure ()

end Tests.MeshTopology.Lagrange

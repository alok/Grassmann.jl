import Tests.Cartan.Solve
import Cartan.Element

/-!
# Finite elements (`oracle/golden/cartan/element/fem.json`)

Generator `oracle/cartan/element/fem.jl` (Cartan.jl `src/element.jl` with MeshTopology's missing
imports supplied, defect B1). Meshes: two triangles; a 3×2 jittered structured triangulation of
the unit square, and a copy with every other triangle reversed (clockwise); the unit
tetrahedron and Kuhn's 6-tetrahedron cube; two triangles embedded in 3-D; `initmesh(0:0.25:1)`
and a random 1-D mesh. Every quantity is compared bit for bit, except where Julia is fixed:
the gradients of clockwise triangles (B3: Julia's are negated; the test negates Julia's values
for the elements with negative orientation) and `refinemesh!` (the golden records the intended
refinement, upstream throws).
-/

open Lean Tests.Small Cartan JuliaBase Grassmann MeshTopology
open Tests.CartanTests.SolveTests (randFloats)

namespace Tests.CartanTests.ElementTests

/-- Build the mesh of a golden case: `d`-dimensional points made homogeneous in `V`. -/
def mesh (n : Nat) (V : TensorBundle) (c : Json) : TestM (SimplexBundle n (HPoint V)) := do
  let d ← jNat (← jField c "d")
  let raw ← gFloats (← jField c "points")
  let np := raw.size / d
  let pts : Array (HPoint V) := (Array.range np).map fun k =>
    Chain.ofFn fun i => if i.1 = 0 then 1 else raw.get! (k * d + i.1 - 1)
  let els ← jArr (← jField c "elements")
  let els ← els.mapM fun e => do
    let a ← jNats e
    return (Vector.ofFn fun (i : Fin n) => a[i.1]!)
  return SimplexBundle.ofPoints pts els

/-- Flatten homogeneous chains. -/
def flatChains {W : TensorBundle} {G : Nat} (xs : Array (Chain W G Float)) : FloatArray :=
  xs.foldl (fun acc x => x.v.toList.foldl FloatArray.push acc) .empty

/-- A golden topology (elements, vertices, sub-elements, node count) against a bundle's. -/
def checkTop {n : Nat} {V : TensorBundle} (label : String) (m : SimplexBundle n (HPoint V))
    (j : Json) : TestM Unit := do
  let els ← (← jArr (← jField j "elements")).mapM jNats
  checkEq s!"{label} elements" (m.arrayTop.toList.map (·.toList)) (els.toList.map (·.toList))
  let full ← (← jArr (← jField j "full")).mapM jNats
  checkEq s!"{label} full" ((m.top.fulltopology).toList.map (·.toList)) (full.toList.map (·.toList))
  checkEq s!"{label} vertices" m.top.verts.toArray.toList (← jNats (← jField j "vertices")).toList
  checkEq s!"{label} sub" m.top.sub.toArray.toList (← jNats (← jField j "sub")).toList
  checkEq s!"{label} fullvertices" m.top.fullVerts.toArray.toList
    (← jNats (← jField j "fullvertices")).toList
  checkEq s!"{label} nodes" m.top.totalNodes (← jNat (← jField j "nodes"))

/-- A golden bundle (flat full points and topology). -/
def checkBundle {n : Nat} {V : TensorBundle} (label : String) (m : SimplexBundle n (HPoint V))
    (j : Json) : TestM Unit := do
  checkFloats s!"{label} points" m.cloud.points (← gFloats (← jField j "points"))
  checkTop label m (← jField j "top")

/-- A golden matrix (rows of floats). -/
def matOf (j : Json) : TestM (List (List UInt64)) := do
  let rows ← jArr j
  rows.toList.mapM fun r => do return (← gFloats r).toList.map Float.toBits

/-- The mesh-data constructors (`meshdata.json`). -/
def runMeshData : TestM Unit := do
  let g ← load "element/meshdata"
  let P ← (← jArr (← jField g "P")).mapM fun r => do return (← gFloats r).toList.toArray
  let E ← (← jArr (← jField g "E")).mapM jNats
  let T ← (← jArr (← jField g "T")).mapM jNats
  let bits (rows : Array (Array Float)) : List (List UInt64) := rows.toList.map (·.toList.map Float.toBits)
  checkBundle "meshdata initpointsdata" (SimplexBundle.initpointsdata ℝ3 2 P E) (← jField g "initpointsdata")
  let (t, e) := SimplexBundle.initmeshdata ℝ3 2 P E T
  let im ← jField g "initmeshdata"
  checkBundle "meshdata initmeshdata t" t (← jField im "t")
  checkBundle "meshdata initmeshdata e" e (← jField im "e")
  checkEq "meshdata submesh t" (bits t.submesh) (← matOf (← jField im "submesh_t"))
  checkEq "meshdata submesh e" (bits e.submesh) (← matOf (← jField im "submesh_e"))
  checkEq "meshdata array t" (bits t.array) (← matOf (← jField im "array_t"))
  checkEq "meshdata array(immersion t)" (t.arrayTop.toList.map (·.toList))
    ((← (← jArr (← jField im "array_top")).mapM jNats).toList.map (·.toList))
  let (tt, te) := SimplexBundle.totalmeshdata ℝ3 P E T
  let tm ← jField g "totalmeshdata"
  checkBundle "meshdata totalmeshdata t" tt (← jField tm "t")
  checkBundle "meshdata totalmeshdata e" te (← jField tm "e")
  let P3 : Array (Array Float) := #[#[0, 1, 0, 0, 0.25], #[0, 0, 1, 0, 0.25], #[0, 0, 0, 1, 0.25]]
  let E3 : Array (Array Nat) := #[#[1, 2, 3], #[1, 2, 4], #[1, 3, 4], #[2, 3, 4]]
  let T3 : Array (Array Nat) := #[#[1, 2, 3, 5], #[1, 2, 4, 5], #[1, 3, 4, 5], #[2, 3, 4, 5]]
  let (t3, e3) := SimplexBundle.initmeshdata ℝ4 3 P3 E3 T3
  let i3 ← jField g "initmeshdata3"
  checkBundle "meshdata initmeshdata3 t" t3 (← jField i3 "t")
  checkBundle "meshdata initmeshdata3 e" e3 (← jField i3 "e")
  checkEq "meshdata submesh t3" (bits t3.submesh) (← matOf (← jField i3 "submesh_t"))

/-- The checks of one mesh. -/
def runCase (n : Nat) (V : TensorBundle) (name : String) (c : Json) (flipB3 : Bool := false) :
    TestM Unit := do
  let m ← mesh n V c
  let fl (k : String) : TestM (Option FloatArray) := do
    let j ← jField c k
    if isErr j then return none
    return some (← gFloats j)
  let cmp (k : String) (got : FloatArray) (tol : Tol := exact) : TestM Unit := do
    match ← fl k with
    | some w => checkFloats s!"fem {name} {k}" got w tol
    | none => pure ()
  let np := m.totalNodes
  let ne := m.elements
  cmp "volumes" m.volumes.data
  -- gradienthat: Julia negates the gradients of negatively oriented elements (B3)
  match ← fl "gradienthat" with
  | some w =>
    let d := (Forms.drop1 V).n
    let fixed : FloatArray := ⟨(Array.range w.size).map fun q =>
      let e := q / (n * d)
      if flipB3 && m.signedVolumeAt e < 0 then -(w.get! q) else w.get! q⟩
    checkFloats s!"fem {name} gradienthat" m.gradienthat.data fixed
  | none => pure ()
  let degs ← jNats (← jField c "degrees")
  check s!"fem {name} degrees" (m.degrees == degs) fun _ => s!"{m.degrees} vs {degs}"
  cmp "weights" m.weights
  cmp "load1" m.assembleload
  cmp "loadx" (m.assembleload fun x => getD x.v 1)
  let dd ← jNat (← jField c "d")
  cmp "loadxy" (m.assembleload fun x =>
    if dd ≥ 2 then getD x.v 1 * getD x.v 2 + 1 else getD x.v 1 * getD x.v 1 + 1)
  let fe := randFloats ne 0xface (-1) 1
  cmp "interp" (m.interp ((TensorField.ofFlat? m.faces' fe).get!)).data
  let un := randFloats np 0x40de (-1) 1
  cmp "pretni" (m.pretni un).data
  cmp "means" m.means.data
  cmp "barycenters" m.barycenters.data
  cmp "centroids" m.centroids.data
  cmp "curls" m.curls.data
  let g2fix (w : FloatArray) : FloatArray :=
    let d := (Forms.drop1 V).n
    ⟨(Array.range w.size).map fun q =>
      let e := q / d
      if flipB3 && m.signedVolumeAt e < 0 then -(w.get! q) else w.get! q⟩
  match ← fl "grad2" with
  | some w => checkFloats s!"fem {name} grad2" (m.gradient2 un).data (g2fix w)
  | none => pure ()
  if !flipB3 then
    cmp "grad" (flatChains (m.gradient un))
    let lin : FloatArray := ⟨(Array.range np).map fun v =>
      2 * m.coord (v + 1) 1 - (if dd ≥ 2 then m.coord (v + 1) 2 else 0) + 3⟩
    cmp "gradlin" (flatChains (m.gradient lin))
  cmp "wedge" ⟨(Array.range ne).flatMap m.wedgeAt⟩
  cmp "detsimplex" ⟨(Array.range ne).flatMap m.detsimplexAt⟩
  match c.getObjVal? "query" with
  | .ok (.arr _) =>
      let qs ← gFloats (← jField c "query")
      let ff ← jNats (← jField c "findfirst")
      let d := dd
      let pts : Array (HPoint V) := (Array.range (qs.size / d)).map fun k =>
        Chain.ofFn fun i => if i.1 = 0 then 1 else qs.get! (k * d + i.1 - 1)
      let got := pts.map m.findfirst
      check s!"fem {name} findfirst" (got == ff) fun _ => s!"{got} vs {ff}"
      cmp "sinterp" ⟨pts.map (m.sinterp un)⟩
  | _ => pure ()

/-- Run the finite-element checks. -/
def run : TestM Unit := do
  runMeshData
  let g ← load "element/fem"
  runCase 3 ℝ3 "two" (← jField g "two")
  runCase 3 ℝ3 "grid" (← jField g "grid")
  runCase 3 ℝ3 "gridflip" (← jField g "gridflip") (flipB3 := true)
  runCase 4 ℝ4 "tet" (← jField g "tet")
  runCase 4 ℝ4 "cube" (← jField g "cube")
  runCase 3 ℝ4 "surf" (← jField g "surf")
  runCase 2 ℝ2 "line_rand" (← jField g "line_rand")
  let l ← jField g "line"
  runCase 2 ℝ2 "line" l
  -- initmesh and refinement
  let (t, e) := SimplexBundle.initmesh #[0, 0.25, 0.5, 0.75, 1]
  check "fem initmesh boundary" (e.top.verts.toArray == (← jNats (← jField l "bnd_vertices")))
  let (rt, re) := SimplexBundle.refine1 t #[2, 4]
  checkFloats "fem refine points" ⟨(Array.range rt.totalNodes).map fun v => rt.coord (v + 1) 1⟩
    (← gFloats (← jField l "refined_points"))
  check "fem refine boundary" (re.top.verts.toArray == (← jNats (← jField l "refined_bnd")))
  checkFloats "fem refine volumes" rt.volumes.data (← gFloats (← jField l "refined_volumes"))
  -- markers and the Laplacian
  let misc ← jField g "misc"
  let two ← mesh 3 ℝ3 (← jField g "two")
  let η := (TensorField.ofFlat? two.faces' ⟨#[0.1, 2.0]⟩).get!
  check "fem select" (η.select == (← jNats (← jField misc "select")))
  check "fem select 0.05" (η.select 0.05 == (← jNats (← jField misc "select05")))
  checkFloat "fem rms" ((TensorField.ofFlat? two.faces' ⟨#[3.0, 4.0]⟩).get!.rms) (← jField misc "rms34")
  let tri : SimplexBundle 3 (HPoint ℝ3) := SimplexBundle.ofPoints
    #[Chain.ofFn fun i => #[1, 0, 0][i.1]!, Chain.ofFn fun i => #[1, 1, 0][i.1]!,
      Chain.ofFn fun i => #[1, 0, 1][i.1]!] #[#v[1, 2, 3]]
  let L := tri.laplacian.toDense
  let want ← jArr (← jField misc "laplacian")
  let wantRows ← want.mapM fun r => do (← jArr r).mapM fun x => do return Float.ofInt (← jInt x)
  check "fem laplacian (Julia convention)" (L.toRows == wantRows) fun _ => s!"{L.toRows}"
  check "fem graph laplacian rows sum to zero"
    ((tri.graphLaplacian.toDense.toRows).all fun r => r.foldl (· + ·) 0 == 0)

end Tests.CartanTests.ElementTests

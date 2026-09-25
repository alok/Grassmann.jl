import Tests.FlowGeometry.Common
import Tests.Util.Random

/-!
# Meshes and point utilities (`mesh.json`, `sphere.json`, `wing.json`, `show.json`)

Structured triangles and boundary loops, the Rakich stretching and C-mesh (including the default
`initrakich()`, 5 151 points), rectangles, boxes, the icosahedron and its subdivision onto the
sphere (two levels), `rectcirc`, edge loops (`edgeslist!`, `addbound`, `initedges` as intended),
the convex hull on five point sets, intervals, the `decsg` geometry, and the wing surfaces.
-/

open Lean Tests.Small Tests.CartanTests JuliaBase FlowGeometry Grassmann DirectSum

namespace Tests.FlowGeometryTests.Meshes

/-- A `FloatArray` from a list. -/
def fa (xs : List Float) : FloatArray := xs.foldl FloatArray.push .empty

/-- Elements as arrays of ids. -/
def els {n : Nat} (xs : Array (Vector Nat n)) : Array (Array Nat) := xs.map (·.toArray)

/-- Homogeneous `ℝ3` points from a flat golden array. -/
def pts3 (a : FloatArray) : Array (Chain ℝ3 1 Float) :=
  (Array.range (a.size / 3)).map fun i => vecOf #[a[3 * i]!, a[3 * i + 1]!, a[3 * i + 2]!]

/-- Homogeneous `ℝ4` points from a flat golden array. -/
def pts4 (a : FloatArray) : Array (Chain ℝ4 1 Float) :=
  (Array.range (a.size / 4)).map fun i => vecOf #[a[4 * i]!, a[4 * i + 1]!, a[4 * i + 2]!, a[4 * i + 3]!]

/-- A number that the generator wrote as a JSON number or as hex bits. -/
def num (j : Json) : TestM Float := do
  match j.getNat? with
  | .ok n => return n.toFloat
  | .error _ =>
    match j.getNum? with
    | .ok n => return n.toFloat
    | .error _ => gFloat j

/-- The structured-grid and Rakich checks. -/
def runGrid (m : Json) : TestM Unit := do
  for c in ← jArr (← jField m "rectangletriangle") do
    let mm ← gNat c "m"
    let want ← jArr (← jField c "tris")
    let got := (Array.range want.size).map fun i => (rectangletriangle (i + 1) mm).toArray
    checkNats s!"rectangletriangle m={mm}" got (← jField c "tris")
  for c in ← jArr (← jField m "rectangletriangles") do
    let (mm, jl) := (← gNat c "m", ← gNat c "JL")
    checkNats s!"rectangletriangles {mm} {jl}" (els (rectangletriangles mm jl).topology) (← jField c "tris")
  for c in ← jArr (← jField m "rectanglebounds") do
    let (n, jl) := (← gNat c "n", ← gNat c "JL")
    checkNats s!"rectanglebounds {n} {jl}" (els (rectanglebounds n jl).topology) (← jField c "edges")
  for c in ← jArr (← jField m "FittedPoint") do
    let (k, jl) := (← gNat c "k", ← gNat c "JL")
    checkFs s!"FittedPoint {k}" (flatPoints #[fittedPoint k jl]) (← jField c "pt")
  for c in ← jArr (← jField m "RakichNewton") do
    let D ← gFloat (← jField c "D")
    let jl ← gNat c "JL"
    let dy ← gFloat (← jField c "dy")
    checkF s!"RakichNewton {D} {jl} {dy}" (rakichNewton D jl dy) (← jField c "k")
  for c in ← jArr (← jField m "RakichLine") do
    let y ← gFloat (← jField c "y")
    let D ← gFloat (← jField c "D")
    let jl ← gNat c "JL"
    let dy ← gFloat (← jField c "dy")
    checkFs s!"RakichLine {y} {D} {jl} {dy}" (rakichLine y D jl dy) (← jField c "v")
  for c in ← jArr (← jField m "Rakich") do
    checkF "Rakich" (rakich (← gFloat (← jField c "k")) (← gNat c "j") (← gFloat (← jField c "y0"))
      (← gFloat (← jField c "D")) (← gNat c "JL")) (← jField c "v")
  let plates : List (String × Nat) :=
    [("CircularArc{6, 5}", 5), ("CircularArc{6, 21}", 21), ("CircularArc{6, 61}", 61), ("ClarkY{12, 0.21, 9}", 9)]
  for c in ← jArr (← jField m "RakichPlate") do
    let ty ← gStr c "type"
    match plates.lookup ty with
    | some n => checkFs s!"RakichPlate {ty}" (rakichPlate n (← num (← jField c "D")) (← gNat c "JL")) (← jField c "v")
    | none => check s!"RakichPlate {ty}" false
  let arcs : List (String × Num × Nat) := [("CircularArc{6, 5}", 6, 5), ("CircularArc{6, 21}", 6, 21), ("CircularArc{10, 9}", 10, 9)]
  for c in ← jArr (← jField m "rakichpoints") do
    let ty ← gStr c "type"
    match arcs.lookup ty with
    | some (T, mm) =>
      checkFs s!"rakichpoints {ty}" (rakichpoints T mm (← num (← jField c "D")) (← gNat c "n") (← gNat c "JL")).points
        (← jField c "v")
    | none => check s!"rakichpoints {ty}" false
  let ir ← jField m "initrakich"
  let (pt, pe) := initrakich
  checkFs "initrakich points" pt.cloud.points (← jField ir "points")
  checkNats "initrakich triangles" (els pt.top.topology) (← jField ir "tris")
  checkNats "initrakich bounds" (els pe.top.topology) (← jField ir "bounds")
  check "initrakich segments" ((Mesh.edgeSegments pt).size == 4 * 3 * (2 * 100 * 50) &&
    (Mesh.edgeSegments pe).size == 4 * (2 * 100 + 2 * 50))
  check "initrakich nodes" (Cartan.card pt == (← gNat ir "nodes_tris") && Cartan.card pe == (← gNat ir "nodes_bounds"))
    fun _ => s!"{Cartan.card pt} {Cartan.card pe}"

/-- The polyhedra, boundary points, edges, intervals, hulls and `decsg`. -/
def runPoints (m : Json) : TestM Unit := do
  let flat3 (xs : Array (Chain ℝ3 1 Float)) : FloatArray := flatPoints xs
  let flat4 (xs : Array (Chain ℝ4 1 Float)) : FloatArray := flatPoints xs
  for c in ← jArr (← jField m "rectangle") do
    let a ← gFloats (← jField c "args")
    checkFs "rectangle" (flat3 (rectangle a[0]! a[1]! a[2]! a[3]!)) (← jField c "v")
  for c in ← jArr (← jField m "square") do
    let a ← gFloats (← jField c "args")
    checkFs "square" (flat3 (if a.size == 1 then square1 a[0]! else square a[0]! a[1]!)) (← jField c "v")
  for c in ← jArr (← jField m "box") do
    let a ← gFloats (← jField c "args")
    checkFs "box" (flat4 (box a[0]! a[1]! a[2]! a[3]! a[4]! a[5]!)) (← jField c "v")
  for c in ← jArr (← jField m "cube") do
    let a ← gFloats (← jField c "args")
    checkFs "cube" (flat4 (if a.size == 1 then cube1 a[0]! else cube a[0]! a[1]!)) (← jField c "v")
  for c in ← jArr (← jField m "icosahedron") do
    checkFs "icosahedron" (flat4 (icosahedron (← gFloat (← jField c "a")))) (← jField c "v")
  for c in ← jArr (← jField m "icosahedron_ab") do
    checkFs "icosahedron(a,b)" (flat4 (icosahedron (← gFloat (← jField c "a")) (← gFloat (← jField c "b"))))
      (← jField c "v")
  for c in ← jArr (← jField m "sphere") do
    checkFs "sphere" (flat4 (sphere (← gFloat (← jField c "r")))) (← jField c "v")
  for c in ← jArr (← jField m "circlemid") do
    let x := (pts4 (← gFloats (← jField c "x")))[0]!
    checkFs "circlemid" (flatPoints #[circlemid x (← gFloat (← jField c "r"))]) (← jField c "v")
  for c in ← jArr (← jField m "rectcirc") do
    let n ← gNat c "n"
    let a ← gFloats (← jField c "args")
    let cc := (pts3 (← gFloats (← jField c "c")))[0]!
    checkFs s!"rectcirc {n}" (flat3 (rectcirc n a[0]! a[1]! a[2]! a[3]! cc)) (← jField c "v")
  -- edges
  for c in ← jArr (← jField m "edgeslist") do
    let n ← gNat c "n"
    checkNats s!"edgeslist {n}" (els (edgeslist (Profile.clarkYDefault 12 n).points)) (← jField c "edges")
  let ep ← jField m "edgeslist!_patched"
  let (p', e') := edgeslistPush (Profile.clarkYDefault 12 5).points (rectangle (-1) 2 (-1) 1)
  checkNats "edgeslist! (patched) edges" (els e') (← jField ep "edges")
  checkFs "edgeslist! (patched) points" p'.points (← jField ep "points")
  for c in ← jArr (← jField m "airfoiledges") do
    let s ← gStr c "name"
    checkNats s!"airfoiledges {s}" (els (airfoiledges (NACA.parse! s))) (← jField c "edges")
  let ap ← jField m "addbound_patched"
  let (p2, e2) := airfoilbox (.american (.naca4 24 9) (Profile.clarkYDefault 12 9)) (-1.5) 3.5 (-1.5) 1.5
  checkNats "addbound (patched) edges" (els e2) (← jField ap "edges")
  checkFs "addbound (patched) points" p2.points (← jField ap "points")
  let ip ← jField m "initedges_patched"
  let ie := (Profile.clarkYDefault 12 5).initedges
  checkFs "initedges (patched) points" ie.cloud.points (← jField ip "points")
  checkNats "initedges (patched) edges" (els ie.top.topology) (← jField ip "edges")
  checkFs "chord" (FlowGeometry.chord 5).toFloatArray (← jField m "chord")
  -- intervals
  for c in ← jArr (← jField m "interval") do
    let p ← gNat c "p"
    let a := FlowGeometry.interval p (← gFloat (← jField c "c")) (← gFloat (← jField c "x0"))
    checkS s!"interval {p} repr" (toString a) (← jField c "repr")
    checkFs s!"interval {p}" a.toFloatArray (← jField c "v")
  checkFs "interval(150)[1:4]" (sliceAxis (FlowGeometry.interval 150) 1 4).toFloatArray (← jField m "interval150_1_4")
  for c in ← jArr (← jField m "doubleinterval") do
    let p ← gNat c "p"
    let a := doubleinterval (FlowGeometry.interval p)
    checkS s!"doubleinterval {p} repr" (toString a) (← jField c "repr")
    checkFs s!"doubleinterval {p}" a.toFloatArray (← jField c "v")
  -- convex hulls
  for c in ← jArr (← jField m "convhull") do
    let ps := pts3 (← gFloats (← jField c "points"))
    let cloud : Cartan.PointCloud (Chain ℝ3 1 Float) := .ofArray ps
    checkNats s!"convhull ({ps.size} points)" (els (convhull cloud).topology) (← jField c "edges")
    checkNats s!"convhull r ({ps.size} points)" (els (convhull cloud (some 1.5)).topology) (← jField c "edges_r")
  for c in ← jArr (← jField m "decsg") do
    let s ← gStr c "name"
    let (R, A) := decsgGeometry (NACA.parse! s)
    checkFs s!"decsg {s} R" R (← jField c "R")
    checkFs s!"decsg {s} A" A (← jField c "A")

/-- The sphere subdivision from the icosahedron's faces. -/
def runSphere : TestM Unit := do
  let j ← jField (← load "sphere") "sphere"
  let faces := (← (← jArr (← jField j "faces")).mapM jNats).map fun f => #v[f[0]!, f[1]!, f[2]!]
  for (r, key) in [((1 : Float), "r=1.0"), (2, "r=2.0")] do
    let d ← jField j key
    let ico : Cartan.SimplexBundle 3 (Chain ℝ4 1 Float) :=
      ⟨.ofArray (sphere r), MeshTopology.SimplexTopology.ofElements faces (p := some 12)⟩
    let s1 := sphereRefine ico r
    let s2 := sphereRefine s1 r
    checkFs s!"sphere {key} level 1 points" s1.cloud.points (← jField d "level1_points")
    checkNats s!"sphere {key} level 1 faces" (els s1.top.topology) (← jField d "level1_faces")
    checkFs s!"sphere {key} level 2 points" s2.cloud.points (← jField d "level2_points")
    checkNats s!"sphere {key} level 2 faces" (els s2.top.topology) (← jField d "level2_faces")

/-- The wing surfaces. -/
def runWing : TestM Unit := do
  let ws ← jArr (← jField (← load "wing") "wings")
  let am := Airfoil.american (.naca4 24 9) (Profile.clarkYDefault 12 9)
  let cases : List Airfoil := [am, am, .american (.naca4 44 21) (Profile.modifiedM 12 64 21)]
  for (a, d) in cases.zip (ws.toList.take 3) do
    let w := wing a (← gFloat (← jField d "lambda")) (← gFloat (← jField d "sigma"))
    let n ← gStr d "name"
    checkFs s!"wing {n}" w.data (← jField d "fiber")
    checkS s!"wing {n} base" (toString (wingBase a).space) (← jField d "base")
  let d := ws[3]!
  let a := NACA.parse! "6511"
  let w := wing a
  let np := a.upperSamples
  let sums := Cartan.buildFlat (F := Float) (w.data.size / 3) fun k =>
    w.data[3 * k]! + w.data[3 * k + 1]! + w.data[3 * k + 2]!
  checkF "wing 6511 checksum" (F64.sum sums) (← jField d "checksum")
  let corner (k : Nat) : List Float := [w.data[3 * k]!, w.data[3 * k + 1]!, w.data[3 * k + 2]!]
  let last := np * (2 * np - 1) - 1
  checkFs "wing 6511 corners" ((corner 0 ++ corner last ++ corner (74 + np * 149)).foldl FloatArray.push .empty)
    (← jField d "corner")
  checkS "wing 6511 base" (toString (wingBase a).space) (← jField d "base")

/-- Grassmann's display of the homogeneous points. -/
def runShow : TestM Unit := do
  let j ← load "show"
  let ps := (Profile.clarkYDefault 12 5).points
  let want ← (← jArr (← jField j "points")).mapM jStr
  for i in [0:want.size] do
    checkEq s!"show point {i}" (toString (ps.get i)) want[i]!
  let qs := (Airfoil.american (.naca4 24 5) (Profile.clarkYDefault 12 5)).points
  let want ← (← jArr (← jField j "airfoil")).mapM jStr
  for i in [0:want.size] do
    checkEq s!"show airfoil point {i}" (toString (qs.get i)) want[i]!

/-- Properties of the hand-inlined kernels: `det3` is the Grassmann wedge `(a ∧ b) ∧ c` (random
triples, integer grids with exact and zero determinants), `pow4` is Julia's `x^4`. -/
def runKernels : TestM Unit := do
  let triples := Gen.run 20260925 (Gen.array 20000 do
    let grid := (← Gen.nat 2) == 0
    let coord : Gen Float := if grid then do return Float.ofInt (← Gen.int (-3) 3) else Gen.floatIn (-10) 10
    return ((← coord), (← coord), (← coord), (← coord), (← coord), (← coord), (← Gen.floatIn 0.5 2)))
  for (ax, ay, bx, «by», cx, cy, w) in triples do
    let a := pt3 ax ay
    let b := pt3 bx «by»
    let c : Chain ℝ3 1 Float := vecOf #[w, cx, cy]
    let d1 := det3 1 ax ay 1 bx «by» w cx cy
    let d2 := det3Chain a b c
    check "det3 = wedge" (d1 == d2 || (d1.isNaN && d2.isNaN)) fun _ => s!"{d1} vs {d2}"
  let xs := Gen.run 7 (Gen.array 20000 (Gen.floatIn (-50) 50))
  let special : List Float := [0, -0.0, 1, -1, 1e-300, -1e-300, 5e-324, 1e300, 1e77, 1e78, -1e78,
    F64.inf, -F64.inf, F64.nan, 0.1, 0.3, 1.0000000000000002]
  for x in xs.toList ++ special do
    let (p, q) := (pow4 x, F64.literalPow x 4)
    check "pow4 = x^4" (p.toBits == q.toBits || (p.isNaN && q.isNaN)) fun _ => s!"{x}: {p} vs {q}"

/-- Bitwise equality of two `TwicePrecision` ranges (every field). -/
def sameRange (a b : StepRangeLen) : Bool :=
  a.ref.hi.toBits == b.ref.hi.toBits && a.ref.lo.toBits == b.ref.lo.toBits &&
  a.step.hi.toBits == b.step.hi.toBits && a.step.lo.toBits == b.step.lo.toBits &&
  a.len == b.len && a.offset == b.offset

/-- The direct constructions of the unit interval and its doubled range are Julia's
(`range(0, 1, length = n)` and `0:step:2` through `rat`) for `n = 2 … 3000`. -/
def runRanges : TestM Unit := do
  for n in [2:3001] do
    let u := unitRange n
    check s!"unitRange {n}" (sameRange u (JuliaBase.range 0 1 n))
    let fast := doubleinterval (.stepLen u)
    let slow := doubleinterval.doubleintervalGeneric (.stepLen u)
    match fast, slow with
    | .stepLen a, .stepLen b => check s!"doubleinterval {n}" (sameRange a b)
    | _, _ => check s!"doubleinterval {n}" false fun _ => "not a range"

/-- The direct Joukowski angles are Julia's `range(0, 2π, length = n)` for `n = 1 … 3000`. -/
def runAngles : TestM Unit := do
  for n in [1:3001] do
    match Joukowski.angles n, Cartan.Axis.range 0 Cartan.twoPiF n with
    | .stepLen a, .stepLen b => check s!"angles {n}" (sameRange a b)
    | _, _ => check s!"angles {n}" false fun _ => "not a range"

/-- `grid1` is Cartan's `GridBundle.ofAxis` with faster coordinates: same axes, same
coordinates bit for bit, same topology size. -/
def runGrids : TestM Unit := do
  let axes : List Cartan.Axis := [FlowGeometry.interval 150, FlowGeometry.interval 9 2 1,
    doubleinterval (FlowGeometry.interval 150), Joukowski.angles 149, .explicit (fa [0.1, 0.5, 0.3])]
  for a in axes do
    let g := grid1 a
    let h := Cartan.GridBundle.ofAxis a
    check s!"grid1 {a}" (g == h && (g.space.coords[0].toList.zip h.space.coords[0].toList).all
      (fun (x, y) => x.toBits == y.toBits) && g.space.coords[0].size == h.space.coords[0].size)

/-- Run the mesh checks. -/
def run : TestM Unit := do
  runRanges
  runGrids
  runAngles
  runKernels
  let m ← jField (← load "mesh") "mesh"
  runGrid m
  runPoints m
  runSphere
  runWing
  runShow

end Tests.FlowGeometryTests.Meshes

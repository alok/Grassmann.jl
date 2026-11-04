import Tests.FlowGeometry.Common
import FlowGeometry.Spheres
import Adapode.Element

/-!
# Sphere and cube meshes (`FlowGeometry.Spheres`)

* `spheresurf`: the icosahedron's hull in Julia's order is `sphere.json`'s `faces`, so both
  refinements agree with Julia bit for bit; the surface is closed and faces outward.
* `cubesphere`: the 320 sphere triangles plus 12 outward cube triangles on 320 points.
* `cubemesh`, `spheremesh`: TetGen's contract `q1.414a…` (radius–edge ≤ √2, volume ≤ a), positive
  tetrahedra, volumes adding up to the region's, the boundary made of the input surfaces (every
  `spheresurf` triangle is a mesh face, pointing into the hole).
* Potential flow past the unit sphere (Adapode README R19's set-up): with the exact potential
  `x(1 + 1/(2r³))` on the cube, the P1 solution with the natural condition `∂ₙφ = 0` on the sphere
  matches it to the accuracy of the 320-face polyhedral sphere.
-/

open Lean Tests.Small JuliaBase FlowGeometry Grassmann Cartan Cartan.Delaunay3

namespace Tests.FlowGeometryTests.Spheres

/-- The 0-based tetrahedra of a bundle. -/
def tetsOf (m : SimplexBundle 4 (Chain ℝ4 1 Float)) : Array (Nat × Nat × Nat × Nat) :=
  (Array.range m.elements).map fun k => (m.vertexOf k 0 - 1, m.vertexOf k 1 - 1, m.vertexOf k 2 - 1, m.vertexOf k 3 - 1)

/-- The points of a bundle. -/
def ptsOf (pts : FloatArray) : Array P3 := (Array.range (pts.size / 4)).map (cloudP3 pts)

/-- Six times the signed volume (positive for `orient3d > 0`). -/
def vol6 (a b c d : P3) : Float :=
  let (adx, ady, adz) := (a.x - d.x, a.y - d.y, a.z - d.z)
  let (bdx, bdy, bdz) := (b.x - d.x, b.y - d.y, b.z - d.z)
  let (cdx, cdy, cdz) := (c.x - d.x, c.y - d.y, c.z - d.z)
  adx * (bdy * cdz - bdz * cdy) + bdx * (cdy * adz - cdz * ady) + cdx * (ady * bdz - adz * bdy)

/-- `(a − o) · ((b − o) × (c − o))`: six times the volume of the cone from `o`. -/
def cone (o a b c : P3) : Float := vol6 a b c o

/-- A key for exact point identity. -/
def pkey (p : P3) : UInt64 × UInt64 × UInt64 := (p.x.toBits, p.y.toBits, p.z.toBits)

/-- Lexicographic order on point keys. -/
def klt (a b : UInt64 × UInt64 × UInt64) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)))

/-- Volume enclosed by outward triangles (divergence theorem from the origin). -/
def enclosed (pts : Array P3) (fs : Array (Nat × Nat × Nat)) : Float :=
  fs.foldl (fun s (a, b, c) => s + cone ⟨0, 0, 0⟩ pts[a]! pts[b]! pts[c]!) 0 / 6

/-- Mesh checks shared by `cubemesh` and `spheremesh`. -/
def checkMesh (name : String) (m : SimplexBundle 4 (Chain ℝ4 1 Float)) (amax volume : Float) : TestM Unit := do
  let pts := ptsOf m.cloud.points
  let ts := tetsOf m
  check s!"{name}: tetrahedra positively oriented" (ts.all fun (a, b, c, d) =>
    orient3d pts[a]! pts[b]! pts[c]! pts[d]! > 0)
  let q := ts.foldl (fun s (a, b, c, d) => max s (radiusEdge pts[a]! pts[b]! pts[c]! pts[d]!)) 0
  check s!"{name}: radius–edge ratio ≤ 1.414 (TetGen q1.414)" (q ≤ 1.414) fun _ => s!"{q}"
  let vmax := ts.foldl (fun s (a, b, c, d) => max s (vol6 pts[a]! pts[b]! pts[c]! pts[d]! / 6)) 0
  check s!"{name}: volume ≤ {amax} (TetGen a{amax})" (vmax ≤ amax) fun _ => s!"{vmax}"
  let V := ts.foldl (fun s (a, b, c, d) => s + vol6 pts[a]! pts[b]! pts[c]! pts[d]!) 0 / 6
  check s!"{name}: volumes add up to the region's" ((V - volume).abs < 1e-11 * volume) fun _ => s!"{V} vs {volume}"
  let used := ts.foldl (fun (s : Std.HashSet Nat) (a, b, c, d) => (((s.insert a).insert b).insert c).insert d) {}
  checkEq s!"{name}: every point is a vertex" used.size pts.size

/-- The checks. -/
def run : TestM Unit := do
  -- spheresurf: Julia's hull order, then the golden refinement
  let j ← jField (← load "sphere") "sphere"
  let want := (← (← jArr (← jField j "faces")).mapM jNats).map fun f => (f[0]! - 1, f[1]! - 1, f[2]! - 1)
  let ico := sphere 1
  let got := canonicalFaces (convexHull3 (ico.map toP3))
  check "spheresurf: icosahedron hull in Julia's order (sphere.json faces)" (got == want) fun _ => s!"{got}"
  for (r, key) in [((1 : Float), "r=1.0"), (2, "r=2.0")] do
    let s := spheresurf r
    checkFs s!"spheresurf {r}: points (sphere.json level 2)" s.cloud.points (← jField (← jField j key) "level2_points")
    let tri := triangles s
    let pts := ptsOf s.cloud.points
    checkEq s!"spheresurf {r}: 320 triangles on 312 points" (tri.size, pts.size) (320, 312)
    check s!"spheresurf {r}: outward" (tri.all fun (a, b, c) => cone ⟨0, 0, 0⟩ pts[a]! pts[b]! pts[c]! > 0)
    let V := enclosed pts tri
    check s!"spheresurf {r}: encloses just under the ball's volume" (V < 4.18879020478639 * r ^ 3 &&
      V > 0.96 * 4.18879020478639 * r ^ 3) fun _ => s!"{V}"
    -- closed: every edge (by coordinates) in exactly two triangles, once each way
    let ek := fun (a b : Nat) => (pkey pts[a]!, pkey pts[b]!)
    let es := tri.foldl (fun (m : Std.HashMap _ Nat) (a, b, c) =>
      [ek a b, ek b c, ek c a].foldl (fun m k => m.insert k (m.getD k 0 + 1)) m) {}
    check s!"spheresurf {r}: closed and consistently oriented" (es.toList.all fun ((p, q), n) =>
      n == 1 && es.getD (q, p) 0 == 1)
  -- cubesphere
  let cs := cubesphere
  let cpts := ptsOf cs.cloud.points
  let ctri := triangles cs
  checkEq "cubesphere: 332 triangles on 320 points" (ctri.size, cpts.size) (332, 320)
  check "cubesphere: the last 8 points are cube(2)" ((cpts.extract 312 320).map pkey ==
    ((cube1 2).map toP3).map pkey)
  let box := ctri.extract 320 332
  check "cubesphere: cube triangles face outward and enclose 64"
    ((box.all fun (a, b, c) => cone ⟨0, 0, 0⟩ cpts[a]! cpts[b]! cpts[c]! > 0) && (enclosed cpts box - 64).abs < 1e-12)
  -- cubemesh
  for a in [(0.1 : Float), 0.01] do
    let (m, e) := cubemesh a
    checkMesh s!"cubemesh {a}" m a 64
    let pts := ptsOf m.cloud.points
    let bt := triangles e
    check s!"cubemesh {a}: boundary on the cube's faces, outward, enclosing 64"
      ((bt.all fun (x, y, z) => [pts[x]!, pts[y]!, pts[z]!].all fun p =>
        p.x.abs == 2 || p.y.abs == 2 || p.z.abs == 2) && (enclosed pts bt - 64).abs < 1e-11)
  -- spheremesh
  let (m, e) := spheremesh
  let pts := ptsOf m.cloud.points
  let s := spheresurf 1
  let sp := ptsOf s.cloud.points
  let ball := enclosed sp (triangles s)
  checkMesh "spheremesh" m 0.1 (64 - ball)
  let bt := triangles e
  let bkeys : Std.HashSet _ := bt.foldl (fun h (a, b, c) =>
    let k := #[pkey pts[a]!, pkey pts[b]!, pkey pts[c]!]
    h.insert (k.qsort klt)) {}
  check "spheremesh: every spheresurf triangle is a boundary face" ((triangles s).all fun (a, b, c) =>
    bkeys.contains (#[pkey sp[a]!, pkey sp[b]!, pkey sp[c]!].qsort klt))
  let onSphere := bt.filter fun (a, _, _) => ((pts[a]!.x ^ 2 + pts[a]!.y ^ 2 + pts[a]!.z ^ 2) - 1).abs < 1e-9
  check "spheremesh: 320 sphere faces pointing into the hole, the rest on the cube"
    (onSphere.size == 320 && (onSphere.all fun (a, b, c) => cone ⟨0, 0, 0⟩ pts[a]! pts[b]! pts[c]! < 0) &&
     (enclosed pts bt - (64 - ball)).abs < 1e-11) fun _ => s!"{onSphere.size}"
  -- potential flow past the sphere, on two lattice sizes
  let φ := fun (p : P3) => let r3 := (p.x ^ 2 + p.y ^ 2 + p.z ^ 2) ^ (1.5 : Float); p.x * (1 + 1 / (2 * r3))
  let errs := [(0.5 : Float), 0.3].map fun h =>
    let (m, _) := spheremesh h
    let pts := ptsOf m.cloud.points
    let A := Adapode.FEM.assembleStiffness m
    let cubeNodes := (Array.range pts.size).filter fun i =>
      let p := pts[i]!
      p.x.abs == 2 || p.y.abs == 2 || p.z.abs == 2
    let u := Adapode.FEM.solveDirichlet A ⟨Array.replicate pts.size 0⟩ cubeNodes ⟨cubeNodes.map fun i => φ pts[i]!⟩
    (List.range pts.size).foldl (fun s i => max s (u.get! i - φ pts[i]!).abs) (0 : Float)
  check "spheremesh: potential flow past the sphere approaches x(1 + 1/2r³)"
    (errs[1]! < 0.7 * errs[0]! && errs[1]! < 0.06) fun _ => s!"{errs}"

end Tests.FlowGeometryTests.Spheres

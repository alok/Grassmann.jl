import FlowGeometry.Mesh
import Cartan.Delaunay3

/-!
# Sphere and cube meshes (`FlowGeometry` `MiniQhullExt` / `TetGenExt`)

FlowGeometry.jl's `ext/MiniQhullExt.jl` and `ext/TetGenExt.jl`, on `Cartan.Delaunay3`:

* `spheresurf r`: the icosahedron's hull (`∂(MiniQhull.delaunay(sphere(r)))`) subdivided twice by
  `sphere(fac, r)`: 320 triangles on 312 points (shared midpoints duplicated, as in Julia). With the
  hull listed in Julia's order this is Julia's surface bit for bit (`sphere.json`).
* `cubesphere r c`: those triangles plus the 12 hull triangles of the cube `[-cr, cr]³`, one
  boundary `SimplexBundle` on 320 points (Julia's `p(SimplexTopology(0, out, np))`).
* `cubemesh hmax` and `spheremesh h`: TetGen's `tetrahedralize(…, "vpq1.414a…")` of the cube
  `[-2, 2]³`, and of the cube with the `cubesphere` ball removed (the `holes` seed at the origin).

TetGen's meshes cannot be reproduced vertex for vertex: TetGen inserts Steiner points by its own
Delaunay refinement. The port meets the same contract instead. Both meshes are Delaunay
tetrahedralizations of a body-centred cubic lattice (the cube's grid points plus the cell
centres), which keep every face of the input surface, have radius–edge ratio at most `√2` (TetGen
`q1.414`) and volume at most `a` (`a0.1`); `Tests/FlowGeometry/Spheres.lean` checks all three. For
`spheremesh` the lattice points within `0.7h` of the unit sphere are dropped, and every triangle of
`spheresurf` is a face of the mesh: its vertices are on the unit sphere and every other point is
outside it, so a ball through the triangle slightly pushed outward is empty.

Faces and tetrahedra are 1-based in the returned bundles, as in Julia; boundary triangles are
oriented outward from the meshed region (into the hole for the sphere).
-/

namespace FlowGeometry

open JuliaBase Cartan Grassmann DirectSum MeshTopology Cartan.Delaunay3

/-- The spatial part `(x, y, z)` of a homogeneous point of `ℝ4`. -/
@[inline] def toP3 (c : Chain ℝ4 1 Float) : P3 := ⟨c.v.get! 1, c.v.get! 2, c.v.get! 3⟩

/-- Point `i` (0-based) of a flat `ℝ4` cloud. -/
@[inline] def cloudP3 (pts : FloatArray) (i : Nat) : P3 :=
  ⟨pts.get! (4 * i + 1), pts.get! (4 * i + 2), pts.get! (4 * i + 3)⟩

/-- The 0-based vertices of the triangles of a `SimplexBundle 3`. -/
def triangles (s : SimplexBundle 3 (Chain ℝ4 1 Float)) : Array (Nat × Nat × Nat) :=
  (Array.range s.elements).map fun k => (s.vertexOf k 0 - 1, s.vertexOf k 1 - 1, s.vertexOf k 2 - 1)

/-- Outward triangles in the order Julia's `∂(MiniQhull.delaunay(p))` lists them: each rotated to
start at its smallest vertex, sorted by their sorted vertex triples. -/
def canonicalFaces (fs : Array (Nat × Nat × Nat)) : Array (Nat × Nat × Nat) :=
  let rot := fs.map fun (a, b, c) =>
    if a ≤ b && a ≤ c then (a, b, c) else if b ≤ a && b ≤ c then (b, c, a) else (c, a, b)
  let key := fun ((a, b, c) : Nat × Nat × Nat) => (min a (min b c), a + b + c - min a (min b c) - max a (max b c),
    max a (max b c))
  rot.qsort fun x y =>
    let (p, q) := (key x, key y)
    p.1 < q.1 || (p.1 == q.1 && (p.2.1 < q.2.1 || (p.2.1 == q.2.1 && p.2.2 < q.2.2)))

/-- Julia `spheresurf(r = 1)` (`MiniQhullExt.jl:19-23`): the hull of `sphere(r)` refined twice
onto the sphere of radius `r`. -/
def spheresurf (r : Float := 1) : SimplexBundle 3 (Chain ℝ4 1 Float) :=
  let p := sphere r
  let fac := SimplexBundle.ofPoints p ((canonicalFaces (convexHull3 (p.map toP3))).map fun (a, b, c) =>
    #v[a + 1, b + 1, c + 1])
  sphereRefine (sphereRefine fac r) r

/-- The triangles of `s` and of the hull of the cube `[-L, L]³`, whose corners are appended to the
points of `s`. -/
def cubesphereOf (s : SimplexBundle 3 (Chain ℝ4 1 Float)) (L : Float) : SimplexBundle 3 (Chain ℝ4 1 Float) :=
  let np0 := s.cloud.points.size / 4
  let cb := cube1 L
  let old : Array (Chain ℝ4 1 Float) := (Array.range np0).map fun i =>
    let q := cloudP3 s.cloud.points i
    pt4 q.x q.y q.z
  let sph : Array (Vector Nat 3) := (triangles s).map fun (a, b, d) => #v[a + 1, b + 1, d + 1]
  let box : Array (Vector Nat 3) :=
    (convexHull3 (cb.map toP3)).map fun (a, b, d) => #v[np0 + a + 1, np0 + b + 1, np0 + d + 1]
  SimplexBundle.ofPoints (old ++ cb) (sph ++ box)

/-- Julia `cubesphere(r = 1, c = 2)` (`MiniQhullExt.jl:24-31`): `spheresurf r` together with the
hull triangles of the cube `cube(c·r)`, whose eight corners are appended to the points. -/
def cubesphere (r : Float := 1) (c : Float := 2) : SimplexBundle 3 (Chain ℝ4 1 Float) :=
  cubesphereOf (spheresurf r) (c * r)

/-- The body-centred cubic lattice of `[-L, L]³` with `n` cells per side: the `(n+1)³` grid points
followed by the `n³` cell centres, keeping those `p` with `keep p`. -/
def bccLattice (L : Float) (n : Nat) (keep : P3 → Bool := fun _ => true) : Array P3 :=
  let h := 2 * L / n.toFloat
  let grid := (Array.range ((n + 1) ^ 3)).map fun q =>
    (⟨-L + (q % (n + 1)).toFloat * h, -L + (q / (n + 1) % (n + 1)).toFloat * h,
      -L + (q / (n + 1) ^ 2).toFloat * h⟩ : P3)
  let centres := (Array.range (n ^ 3)).map fun q =>
    (⟨-L + ((q % n).toFloat + 0.5) * h, -L + ((q / n % n).toFloat + 0.5) * h,
      -L + ((q / n ^ 2).toFloat + 0.5) * h⟩ : P3)
  (grid ++ centres).filter keep

/-- A tetrahedral mesh and its boundary on the same points (Julia's `pt, pe`). -/
def tetBundles (pts : Array P3) (ts : Array (Nat × Nat × Nat × Nat)) :
    SimplexBundle 4 (Chain ℝ4 1 Float) × SimplexBundle 3 (Chain ℝ4 1 Float) :=
  let hp := pts.map fun p => pt4 p.x p.y p.z
  (SimplexBundle.ofPoints hp (ts.map fun (a, b, c, d) => #v[a + 1, b + 1, c + 1, d + 1]),
   SimplexBundle.ofPoints hp ((boundaryFaces pts ts).map fun (a, b, c) => #v[a + 1, b + 1, c + 1]))

/-- Julia `cubemesh(hmax = 0.1)` (`TetGenExt.jl:20`, TetGen `"vpq1.414a$hmax"` on the cube
`[-2, 2]³`): a BCC tetrahedralization whose tetrahedra (volume `h³/12` for cell size `h`) have
volume at most `hmax`. -/
def cubemesh (hmax : Float := 0.1) :
    SimplexBundle 4 (Chain ℝ4 1 Float) × SimplexBundle 3 (Chain ℝ4 1 Float) :=
  let n := max 1 (4 / (12 * hmax) ^ (1 / 3 : Float)).ceil.toUInt64.toNat
  let pts := bccLattice 2 n
  tetBundles pts (delaunay3 pts)

/-- Julia `spheremesh()` (`TetGenExt.jl:19`, TetGen `"vpq1.414a0.1"` on `cubesphere()` with a hole
at the origin): the region between `spheresurf 1` and the cube `[-2, 2]³`, meshed from the distinct
sphere points and a BCC lattice of cell size about `h` thinned near the sphere. Points are numbered
sphere first (in `spheresurf` order, duplicates removed), then the lattice. -/
def spheremesh (h : Float := 0.5) :
    SimplexBundle 4 (Chain ℝ4 1 Float) × SimplexBundle 3 (Chain ℝ4 1 Float) :=
  let s := spheresurf 1
  let sp := (Array.range (s.cloud.points.size / 4)).map (cloudP3 s.cloud.points)
  let key := fun (p : P3) => (p.x.toBits, p.y.toBits, p.z.toBits)
  let uniq := sp.foldl (fun (acc : Array P3 × Std.HashSet (UInt64 × UInt64 × UInt64)) p =>
    if acc.2.contains (key p) then acc else (acc.1.push p, acc.2.insert (key p))) (#[], {}) |>.1
  let n := max 2 (4 / h).ceil.toUInt64.toNat
  let hh := 4 / n.toFloat
  let lat := bccLattice 2 n fun p => (p.x * p.x + p.y * p.y + p.z * p.z).sqrt ≥ 1 + 0.7 * hh
  let pts := uniq ++ lat
  let ns := uniq.size
  let shell := (delaunay3 pts).filter fun (a, b, c, d) => !(a < ns && b < ns && c < ns && d < ns)
  tetBundles pts shell

end FlowGeometry

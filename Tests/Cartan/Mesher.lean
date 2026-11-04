import Tests.Cartan.Delaunay
import Cartan.Mesher

/-!
# Quality triangulation of planar domains (`Cartan.Mesher`)

Triangle numbers its output in its own order, so the checks test the guarantees of Ruppert's
algorithm instead of comparing node lists:

* every triangle is counter-clockwise, and the mesh is a valid triangulation of the domain:
  the triangle areas add up to the domain's area, and the boundary edges are subsegments
  whose lengths add up to the domain's perimeter, holes included;
* every angle is at least the requested minimum, and every area at most the requested
  maximum;
* the mesh is conforming Delaunay: no mesh point lies strictly inside any triangle's
  circumcircle (the exact `incircle`);
* no triangle lies in a hole.

The domains are a square, a 32-gon disk, a non-convex L, a square with a square hole, a thin
strip, a square with an interior constraint segment, and an annulus.
-/

open Lean Tests.Small Cartan Cartan.Delaunay Cartan.Mesher

namespace Tests.CartanTests.MesherTests

/-- The signed area of a triangle. -/
def triArea (a b c : Pt) : Float := ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)) / 2

/-- The area of a counter-clockwise polygon (a fan). -/
def polyArea (vs : Array Pt) : Float :=
  (Array.range (vs.size - 2)).foldl (fun s i => s + triArea vs[0]! vs[i + 1]! vs[i + 2]!) 0

/-- The perimeter of a closed polygon. -/
def perimeter (vs : Array Pt) : Float :=
  (Array.range vs.size).foldl (fun s i => s + Float.sqrt (len2 vs[i]! vs[(i + 1) % vs.size]!)) 0

/-- The checks on one refined domain with known area and boundary length. -/
def checkDomain (label : String) (g : PSLG) (o : Mesher.Options) (area perim : Float) : TestM Unit := do
  let r := triangulate g o
  let P := r.points
  check s!"{label}: not capped" (!r.capped)
  check s!"{label}: triangles are counter-clockwise"
    (r.triangles.all fun (a, b, c) => orient2d P[a]! P[b]! P[c]! == 1)
  let total := r.triangles.foldl (fun s (a, b, c) => s + triArea P[a]! P[b]! P[c]!) 0
  check s!"{label}: areas add up to the domain's" ((total - area).abs ≤ 1e-9 * area)
    fun _ => s!"{total} vs {area}"
  let minA := r.triangles.foldl (fun m (a, b, c) => min m (minAngleDeg P[a]! P[b]! P[c]!)) 180
  check s!"{label}: min angle ≥ {o.minAngle}°" (minA ≥ o.minAngle - 1e-9)
    fun _ => s!"min angle {minA}"
  if o.maxArea > 0 then
    let maxA := r.triangles.foldl (fun m (a, b, c) => max m (triArea P[a]! P[b]! P[c]!)) (0 : Float)
    check s!"{label}: max area ≤ {o.maxArea}" (maxA ≤ o.maxArea) fun _ => s!"max area {maxA}"
  let dir := r.triangles.foldl (fun acc (a, b, c) => ((acc.push (a, b)).push (b, c)).push (c, a)) #[]
  let set : Std.HashSet (Nat × Nat) := dir.foldl (·.insert ·) {}
  check s!"{label}: directed edges are unique" (set.size == dir.size)
  let segs : Std.HashSet (Nat × Nat) := r.segments.foldl (·.insert ·) {}
  let boundary := dir.filter fun (u, v) => !set.contains (v, u)
  check s!"{label}: boundary edges are subsegments" (boundary.all fun (u, v) => segs.contains (key u v))
  let blen := boundary.foldl (fun s (u, v) => s + Float.sqrt (len2 P[u]! P[v]!)) 0
  check s!"{label}: boundary length = perimeter" ((blen - perim).abs ≤ 1e-9 * perim)
    fun _ => s!"{blen} vs {perim}"
  let used : Std.HashSet Nat := r.triangles.foldl (fun acc (a, b, c) => ((acc.insert a).insert b).insert c) {}
  let viol := r.triangles.filter fun (a, b, c) =>
    used.toArray.any fun l => l != a && l != b && l != c && incircle P[a]! P[b]! P[c]! P[l]! > 0
  check s!"{label}: conforming Delaunay (empty circumcircles)" viol.isEmpty
    fun _ => s!"{viol.size} triangles violate"
  for h in g.holes do
    check s!"{label}: no triangle contains the hole seed {h}"
      (r.triangles.all fun (a, b, c) =>
        !(orient2d P[a]! P[b]! h ≥ 0 && orient2d P[b]! P[c]! h ≥ 0 && orient2d P[c]! P[a]! h ≥ 0))

/-- Run the mesher checks. -/
def run : TestM Unit := do
  let sq : Array Pt := #[(0, 0), (1, 0), (1, 1), (0, 1)]
  checkDomain "mesher square a=0.01" (polygon sq) { maxArea := 0.01 } 1 4
  checkDomain "mesher square q=30" (polygon sq) { minAngle := 30 } 1 4
  let d := disk 32
  checkDomain "mesher disk 32" d {} (polyArea d.points) (perimeter d.points)
  checkDomain "mesher disk 32 a=0.005" d { maxArea := 0.005 } (polyArea d.points) (perimeter d.points)
  let L : Array Pt := #[(0, 0), (2, 0), (2, 1), (1, 1), (1, 2), (0, 2)]
  checkDomain "mesher L a=0.02" (polygon L) { maxArea := 0.02 } 3 8
  let holed := withHoles #[(0, 0), (4, 0), (4, 4), (0, 4)] #[(#[(1, 1), (1, 3), (3, 3), (3, 1)], (2, 2))]
  checkDomain "mesher square with a hole" holed { maxArea := 0.05 } 12 24
  checkDomain "mesher thin strip q=30" (polygon #[(0, 0), (10, 0), (10, 0.1), (0, 0.1)])
    { minAngle := 30 } 1 20.2
  -- an interior constraint: the segment must appear as a chain of mesh edges
  let cons : PSLG := { polygon sq with
    points := sq ++ #[(0.2, 0.3), (0.8, 0.6)], segments := (polygon sq).segments.push (4, 5) }
  checkDomain "mesher interior constraint" cons { maxArea := 0.02 } 1 4
  let r := triangulate cons { maxArea := 0.02 }
  let onB := fun (i : Nat) => let q := r.points[i]!; q.1 == 0 || q.1 == 1 || q.2 == 0 || q.2 == 1
  let onCons := r.segments.filter fun (u, v) => !onB u || !onB v
  let consLen := onCons.foldl (fun s (u, v) => s + Float.sqrt (len2 r.points[u]! r.points[v]!)) 0
  check "mesher interior constraint is a chain of edges"
    ((consLen - Float.sqrt (0.6 * 0.6 + 0.3 * 0.3)).abs ≤ 1e-12) fun _ => s!"length {consLen}"
  -- an annulus (a disk with a disk-shaped hole)
  let outer := (disk 48 2).points
  let inner := ((disk 24 0.7).points).reverse
  let ann := withHoles outer #[(inner, (0, 0))]
  checkDomain "mesher annulus a=0.05" ann { maxArea := 0.05 }
    (polyArea outer - polyArea inner.reverse) (perimeter outer + perimeter inner)
  -- the SimplexBundle
  let m := triangulateBundle (polygon sq) { maxArea := 0.05 }
  checkEq "mesher bundle elements" m.top.totalElements (triangulate (polygon sq) { maxArea := 0.05 }).triangles.size

end Tests.CartanTests.MesherTests

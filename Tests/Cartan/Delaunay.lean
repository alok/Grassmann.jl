import Tests.Cartan.Solve
import Cartan.Delaunay

/-!
# Planar Delaunay triangulation and convex hull (`Cartan.Delaunay`)

No Julia goldens: Qhull and Triangle number their triangles in their own order. These
checks therefore test the defining properties exactly.

* Every triangle is counter-clockwise and non-degenerate.
* No input point lies strictly inside any triangle's circumcircle. This uses the exact
  `incircle` and covers all points, not just the neighbours.
* Every directed edge belongs to at most one triangle, and every interior edge to two.
* The count is Euler's `2n − 2 − b` (`b`: points on the hull boundary), and the areas add up
  to the hull's area.
* For points in general position the Delaunay triangulation is unique, so it must equal a
  brute-force enumeration of the empty-circumcircle triangles.

The inputs are random clouds, a square grid (every cell cocircular), a regular polygon with
its centre, duplicate points, and a collinear set.
-/

open Lean Tests.Small Cartan Cartan.Delaunay

namespace Tests.CartanTests.DelaunayTests

/-- A deterministic pseudo-random cloud in `[0, 1)²` (SplitMix64). -/
def cloud (n : Nat) (seed : UInt64) : Array Pt := Id.run do
  let mut s := seed
  let mut out := #[]
  for _ in [0:n] do
    let mut xy : Array Float := #[]
    for _ in [0:2] do
      s := s + 0x9E3779B97F4A7C15
      let mut z := s
      z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
      z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
      z := z ^^^ (z >>> 31)
      xy := xy.push ((z >>> 11).toFloat / 9007199254740992.0)
    out := out.push (xy[0]!, xy[1]!)
  return out

/-- Twice the signed area of a triangle. -/
def area2 (a b c : Pt) : Float := (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Twice the area of a counter-clockwise polygon (a fan from its first vertex, so far-off
coordinates do not cancel). -/
def polyArea2 (pts : Array Pt) (h : Array Nat) : Float :=
  if h.size < 3 then 0 else
  (Array.range (h.size - 2)).foldl (fun s i =>
    s + area2 pts[h[0]!]! pts[h[i + 1]!]! pts[h[i + 2]!]!) 0

/-- The number of points on the hull boundary (vertices and points on hull edges). -/
def boundaryCount (pts : Array Pt) (h : Array Nat) : Nat :=
  (sortedUnique pts).foldl (fun c i =>
    let on := (Array.range h.size).any fun k =>
      let a := pts[h[k]!]!; let b := pts[h[(k + 1) % h.size]!]!; let p := pts[i]!
      orient2d a b p == 0 && min a.1 b.1 ≤ p.1 && p.1 ≤ max a.1 b.1 && min a.2 b.2 ≤ p.2 && p.2 ≤ max a.2 b.2
    if on then c + 1 else c) 0

/-- A triangle as its sorted vertex triple. -/
def canon (t : Nat × Nat × Nat) : List Nat :=
  let (a, b, c) := t
  [a, b, c].mergeSort

/-- The empty-circumcircle triangles by brute force (general position only). -/
def bruteForce (pts : Array Pt) : List (List Nat) := Id.run do
  let n := pts.size
  let mut out := #[]
  for i in [0:n] do
    for j in [i + 1:n] do
      for k in [j + 1:n] do
        let o := orient2d pts[i]! pts[j]! pts[k]!
        if o != 0 then
          let (a, b, c) := if o > 0 then (i, j, k) else (i, k, j)
          if (List.range n).all fun l => l == a || l == b || l == c || incircle pts[a]! pts[b]! pts[c]! pts[l]! < 0 then
            out := out.push [i, j, k]
  return out.toList.mergeSort (fun x y => compare x y != .gt)

/-- The structural Delaunay checks on one input. -/
def checkMesh (label : String) (pts : Array Pt) : TestM Unit := do
  let ts := delaunay pts
  let h := convexHull pts
  check s!"{label}: triangles are counter-clockwise"
    (ts.all fun (a, b, c) => orient2d pts[a]! pts[b]! pts[c]! == 1)
  let bad := ts.filter fun (a, b, c) =>
    (sortedUnique pts).any fun l => l != a && l != b && l != c && incircle pts[a]! pts[b]! pts[c]! pts[l]! > 0
  check s!"{label}: empty circumcircles" bad.isEmpty fun _ => s!"{bad.size} triangles violate"
  let dir := ts.foldl (fun acc (a, b, c) => ((acc.push (a, b)).push (b, c)).push (c, a)) #[]
  let set : Std.HashSet (Nat × Nat) := dir.foldl (·.insert ·) {}
  check s!"{label}: directed edges are unique" (set.size == dir.size)
  let boundary := dir.filter fun (u, v) => !set.contains (v, u)
  let b := boundaryCount pts h
  check s!"{label}: boundary edges = hull boundary points" (boundary.size == b)
    fun _ => s!"{boundary.size} vs {b}"
  let n := (sortedUnique pts).size
  check s!"{label}: Euler count 2n − 2 − b" (ts.size + 2 + b == 2 * n)
    fun _ => s!"{ts.size} triangles, n = {n}, b = {b}"
  let a := ts.foldl (fun s (x, y, z) => s + area2 pts[x]! pts[y]! pts[z]!) 0
  let ha := polyArea2 pts h
  check s!"{label}: areas add up to the hull's" ((a - ha).abs ≤ 1e-12 * (1 + ha.abs))
    fun _ => s!"{a} vs {ha}"

/-- Run the Delaunay checks. -/
def run : TestM Unit := do
  -- random clouds (general position), with a brute-force comparison on small ones
  for (n, seed) in [(5, 1), (12, 2), (20, 3), (40, 4), (200, 5)] do
    let pts := cloud n seed.toUInt64
    checkMesh s!"delaunay cloud {n}" pts
    if n ≤ 40 then
      let got := ((delaunay pts).map canon).toList.mergeSort (fun x y => compare x y != .gt)
      check s!"delaunay cloud {n} = brute force" (got == bruteForce pts)
  -- a 7 × 7 grid: every cell is cocircular
  let grid : Array Pt := (Array.range 49).map fun k => ((k % 7).toFloat, (k / 7).toFloat)
  checkMesh "delaunay grid 7×7" grid
  checkEq "delaunay grid 7×7 triangle count" (delaunay grid).size 72
  -- a regular 12-gon (cocircular) with its centre, and a scaled, shifted copy
  let poly : Array Pt := ((Array.range 12).map fun k =>
    let t := 2 * 3.141592653589793 * k.toFloat / 12
    (Float.cos t, Float.sin t)).push (0, 0)
  checkMesh "delaunay 12-gon + centre" poly
  checkMesh "delaunay shifted 12-gon" (poly.map fun (x, y) => (1e6 + 3 * x, -2e5 + 3 * y))
  -- duplicates are triangulated once
  let dup : Array Pt := #[(0, 0), (1, 0), (0, 1), (1, 0), (0, 0), (1, 1)]
  checkMesh "delaunay duplicates" dup
  checkEq "delaunay duplicates triangle count" (delaunay dup).size 2
  -- collinear points: no triangles; a collinear start then an apex
  let line : Array Pt := (Array.range 6).map fun k => (k.toFloat, 2 * k.toFloat)
  checkEq "delaunay collinear" (delaunay line).size 0
  let fan := line.push (1, 5)
  checkMesh "delaunay collinear + apex" fan
  checkEq "delaunay collinear + apex triangle count" (delaunay fan).size 5
  -- convex hull: interior and edge points are omitted; counter-clockwise from the minimum
  let sq : Array Pt := #[(0.5, 0.5), (1, 1), (0, 0), (1, 0), (0, 1), (0.5, 0), (0.25, 0.75)]
  checkEq "chull square" (convexHull sq).toList [2, 3, 1, 4]
  checkEq "chull collinear" (convexHull line).toList [0, 5]
  checkEq "chull single point" (convexHull #[((2 : Float), (3 : Float))]).toList [0]
  -- the SimplexBundle of the triangulation (1-based ids)
  let m := delaunayBundle (cloud 30 7)
  checkEq "delaunay bundle elements" m.top.totalElements (delaunay (cloud 30 7)).size
  checkEq "delaunay bundle points" m.cloud.size 30

end Tests.CartanTests.DelaunayTests

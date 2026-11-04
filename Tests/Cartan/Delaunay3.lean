import Tests.Cartan.Delaunay
import Cartan.Delaunay3

/-!
# Delaunay tetrahedralization and 3-D convex hull (`Cartan.Delaunay3`)

No Julia goldens (TetGen and Qhull number their cells in their own order), so the defining
properties are checked exactly:

* every tetrahedron is positively oriented (`orient3d > 0`, never flat);
* no input point lies strictly inside any circumsphere (exact `insphere`, all points);
* every face is shared by at most two tetrahedra, and the volumes add up to the hull's volume;
* the hull triangles face outward (no point beyond any of them), close up
  (`V − E + F = 2`, every edge in two triangles) and enclose that volume;
* Euler's relation `V − E + F − T = 1` for the tetrahedralized ball.

Inputs: random clouds, a `5³` grid (every cell cospherical, every side coplanar), the cube's
corners, a cloud with duplicates, and coplanar points (no tetrahedra).
-/

open Lean Tests.Small Cartan Cartan.Delaunay3

namespace Tests.CartanTests.Delaunay3Tests

/-- A deterministic pseudo-random cloud in `[0, 1)³`. -/
def cloud (n : Nat) (seed : UInt64) : Array P3 :=
  let xy := Tests.CartanTests.DelaunayTests.cloud (3 * n) seed
  (Array.range n).map fun i =>
    ⟨xy[3 * i]!.1, xy[3 * i + 1]!.1, xy[3 * i + 2]!.1⟩

/-- Six times the signed volume with Shewchuk's sign (positive for positive orientation). -/
def vol6 (a b c d : P3) : Float :=
  let (adx, ady, adz) := (a.x - d.x, a.y - d.y, a.z - d.z)
  let (bdx, bdy, bdz) := (b.x - d.x, b.y - d.y, b.z - d.z)
  let (cdx, cdy, cdz) := (c.x - d.x, c.y - d.y, c.z - d.z)
  adx * (bdy * cdz - bdz * cdy) + bdx * (cdy * adz - cdz * ady) + cdx * (ady * bdz - adz * bdy)

/-- The sorted triple of a face. -/
def key3 (a b c : Nat) : Nat × Nat × Nat :=
  let s := #[a, b, c].qsort (· < ·)
  (s[0]!, s[1]!, s[2]!)

/-- Check one input; `brute` enables the all-points empty-sphere test. -/
def checkCloud (name : String) (pts : Array P3) (brute : Bool := true) : TestM Unit := do
  let ts := delaunay3 pts
  let hull := convexHull3 pts
  check s!"delaunay3 {name}: positively oriented" (ts.all fun (a, b, c, d) =>
    orient3d pts[a]! pts[b]! pts[c]! pts[d]! > 0)
  if brute then
    let bad := ts.foldl (fun n (a, b, c, d) =>
      n + (pts.filter fun p => insphere pts[a]! pts[b]! pts[c]! pts[d]! p > 0).size) 0
    checkEq s!"delaunay3 {name}: empty circumspheres" bad 0
  -- faces: each used by at most two tetrahedra; hull faces exactly once
  let faces := ts.foldl (fun (m : Std.HashMap (Nat × Nat × Nat) Nat) (a, b, c, d) =>
    [key3 b c d, key3 a c d, key3 a b d, key3 a b c].foldl (fun m k => m.insert k (m.getD k 0 + 1)) m) {}
  check s!"delaunay3 {name}: faces shared by at most two tetrahedra" (faces.toList.all (·.2 ≤ 2))
  let once := (faces.toList.filter (·.2 == 1)).map (·.1)
  let hullKeys := hull.map fun (a, b, c) => key3 a b c
  check s!"delaunay3 {name}: boundary faces are the hull" (once.length == hull.size &&
    once.all fun k => hullKeys.contains k) fun _ => s!"{once.length} vs {hull.size}"
  let V := ts.foldl (fun s (a, b, c, d) => s + vol6 pts[a]! pts[b]! pts[c]! pts[d]!) (0 : Float)
  let o := pts[0]!
  let HV := hull.foldl (fun s (a, b, c) => s + vol6 pts[a]! pts[b]! pts[c]! o) (0 : Float)
  check s!"delaunay3 {name}: volumes add up to the hull's" ((V - HV).abs ≤ 1e-12 * (1 + HV.abs))
    fun _ => s!"{V} {HV}"
  check s!"delaunay3 {name}: hull faces outward" (hull.all fun (a, b, c) =>
    pts.all fun p => orient3d pts[a]! pts[b]! pts[c]! p ≥ 0)
  -- Euler: hull sphere and tetrahedralized ball
  let used := ts.foldl (fun (s : Std.HashSet Nat) (a, b, c, d) => ((s.insert a).insert b |>.insert c).insert d) {}
  let edges := ts.foldl (fun (s : Std.HashSet (Nat × Nat)) (a, b, c, d) =>
    [(a, b), (a, c), (a, d), (b, c), (b, d), (c, d)].foldl (fun s (x, y) => s.insert (min x y, max x y)) s) {}
  let E := edges.size
  let F := faces.size
  checkEq s!"delaunay3 {name}: V − E + F − T = 1" ((used.size + F : Int) - E - ts.size) 1
  let hv := hull.foldl (fun (s : Std.HashSet Nat) (a, b, c) => ((s.insert a).insert b).insert c) {}
  let he := hull.foldl (fun (s : Std.HashSet (Nat × Nat)) (a, b, c) =>
    [(a, b), (b, c), (c, a)].foldl (fun s (x, y) => s.insert (min x y, max x y)) s) {}
  checkEq s!"delaunay3 {name}: hull V − E + F = 2" ((hv.size + hull.size : Int) - he.size) 2

/-- Run the checks. -/
def run : TestM Unit := do
  checkCloud "random 300" (cloud 300 1)
  checkCloud "random 60" (cloud 60 2)
  let g := (Array.range 125).map fun q => (⟨(q % 5).toFloat, (q / 5 % 5).toFloat, (q / 25).toFloat⟩ : P3)
  checkCloud "grid 5³" g
  let ts := delaunay3 g
  checkEq "delaunay3 grid 5³: volume 64" (ts.foldl (fun s (a, b, c, d) => s + vol6 g[a]! g[b]! g[c]! g[d]!) (0 : Float) / 6) 64
  let cube : Array P3 := #[⟨0, 0, 0⟩, ⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, 1, 0⟩, ⟨0, 0, 1⟩, ⟨1, 0, 1⟩, ⟨0, 1, 1⟩, ⟨1, 1, 1⟩]
  checkCloud "cube corners" cube
  checkEq "delaunay3 cube corners: 12 hull triangles" (convexHull3 cube).size 12
  let c := cloud 40 3
  checkCloud "duplicates" (c ++ c.extract 0 15)
  checkEq "delaunay3 duplicates: same tetrahedra count" (delaunay3 (c ++ c.extract 0 15)).size (delaunay3 c).size
  let flat := (Array.range 20).map fun i => (⟨i.toFloat, (i * i % 7).toFloat, 2 * i.toFloat⟩ : P3)
  checkEq "delaunay3 coplanar points: no tetrahedra" (delaunay3 flat).size 0
  checkCloud "random 3000 (no brute force)" (cloud 3000 4) false

end Tests.CartanTests.Delaunay3Tests

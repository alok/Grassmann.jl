import Cartan.Bundle
import JuliaBase.IEEE
import Std.Data.HashMap

/-!
# 2-D Delaunay triangulation and convex hull (Cartan's mesher extensions)

Cartan.jl gets its meshes from external meshers through package extensions:
`DelaunayExt`/`MiniQhullExt` (`delaunay`), `QHullExt` (`chull`), `TriangulateExt`
(`triangulate`). These are C libraries (Qhull, Shewchuk's Triangle). This module is a
dependency-free replacement for the planar unconstrained case:

* `convexHull`: Andrew's monotone chain. It returns the hull vertices counter-clockwise from
  the lexicographically smallest point and omits points on hull edges (Qhull's default).
* `delaunay`: a Delaunay triangulation of the distinct points. It sweeps the points in
  lexicographic order, joining each new point to the hull edges it sees. Then it applies
  Lawson's edge flips until every interior edge is locally Delaunay, which makes the whole
  triangulation Delaunay (no point strictly inside any triangle's circumcircle).
  Triangles are counter-clockwise.
* `delaunayBundle`: the triangulation as a `SimplexBundle 3` of homogeneous points
  `(1, x, y)` (Julia's `SimplexBundle(delaunay(points))`, with 1-based vertex ids).

**Robustness.** The two predicates, `orient2d` and `incircle`, are evaluated in floating
point with Shewchuk's forward error bounds (`ccwerrboundA`, `iccerrboundA`). When the
result is too close to zero for that bound, they are recomputed exactly over `ℚ` from the
inputs' exact binary values (`IEEEFloat.toRat?`). So every decision is exact: collinear
and cocircular inputs (grids, regular polygons) are handled exactly and never flip-loop.
Duplicate points are triangulated once, at their first index. A point with a
non-finite coordinate is left out. If all points are collinear, there are no triangles.

**Not ported (yet).** Constrained triangulation (PSLG segments and holes), Ruppert/Chew
refinement by area and angle, `tetrahedralize` and the N-D Qhull variants. These are listed
in `docs/parity-gaps.json`.
-/

namespace Cartan.Delaunay

open JuliaBase

/-- A point of the plane. -/
abbrev Pt := Float × Float

/-! ## Exact predicates -/

/-- The machine epsilon used by Shewchuk's bounds (`2⁻⁵³`). -/
def eps : Float := 1.1102230246251565e-16

/-- An exact rational coordinate (`none` for a non-finite float). -/
@[inline] def q (x : Float) : Option Rat := IEEEFloat.toRat? x

/-- The sign of a rational. -/
@[inline] def sgnQ (x : Rat) : Int := if x > 0 then 1 else if x < 0 then -1 else 0

/-- Exact `orient2d` over `ℚ`. -/
def orientExact (a b c : Pt) : Int :=
  match q a.1, q a.2, q b.1, q b.2, q c.1, q c.2 with
  | some ax, some ay, some bx, some by_, some cx, some cy =>
    sgnQ ((bx - ax) * (cy - ay) - (by_ - ay) * (cx - ax))
  | _, _, _, _, _, _ => 0

/-- The sign of `orient2d(a, b, c)`: `+1` when `a, b, c` turn counter-clockwise, `−1`
clockwise, `0` when collinear. The result is exact (a float filter with an exact fallback). -/
def orient2d (a b c : Pt) : Int :=
  let l := (b.1 - a.1) * (c.2 - a.2)
  let r := (b.2 - a.2) * (c.1 - a.1)
  let det := l - r
  let bound := (3 + 16 * eps) * eps * (l.abs + r.abs)
  if det > bound then 1 else if -det > bound then -1 else orientExact a b c

/-- Exact `incircle` over `ℚ`. -/
def incircleExact (a b c d : Pt) : Int :=
  match q a.1, q a.2, q b.1, q b.2, q c.1, q c.2, q d.1, q d.2 with
  | some ax, some ay, some bx, some by_, some cx, some cy, some dx, some dy =>
    let adx := ax - dx; let ady := ay - dy
    let bdx := bx - dx; let bdy := by_ - dy
    let cdx := cx - dx; let cdy := cy - dy
    let alift := adx * adx + ady * ady
    let blift := bdx * bdx + bdy * bdy
    let clift := cdx * cdx + cdy * cdy
    sgnQ (alift * (bdx * cdy - cdx * bdy) + blift * (cdx * ady - adx * cdy) +
      clift * (adx * bdy - bdx * ady))
  | _, _, _, _, _, _, _, _ => 0

/-- The sign of `incircle(a, b, c, d)` for a counter-clockwise triangle `a, b, c`: `+1` when
`d` lies strictly inside its circumcircle, `−1` outside, `0` on it. The result is exact. -/
def incircle (a b c d : Pt) : Int :=
  let adx := a.1 - d.1; let ady := a.2 - d.2
  let bdx := b.1 - d.1; let bdy := b.2 - d.2
  let cdx := c.1 - d.1; let cdy := c.2 - d.2
  let bdxcdy := bdx * cdy; let cdxbdy := cdx * bdy
  let cdxady := cdx * ady; let adxcdy := adx * cdy
  let adxbdy := adx * bdy; let bdxady := bdx * ady
  let alift := adx * adx + ady * ady
  let blift := bdx * bdx + bdy * bdy
  let clift := cdx * cdx + cdy * cdy
  let det := alift * (bdxcdy - cdxbdy) + blift * (cdxady - adxcdy) + clift * (adxbdy - bdxady)
  let perm := (bdxcdy.abs + cdxbdy.abs) * alift + (cdxady.abs + adxcdy.abs) * blift +
    (adxbdy.abs + bdxady.abs) * clift
  let bound := (10 + 96 * eps) * eps * perm
  if det > bound then 1 else if -det > bound then -1 else incircleExact a b c d

/-! ## Point order -/

/-- Whether a point has finite coordinates. -/
@[inline] def finite (p : Pt) : Bool := (q p.1).isSome && (q p.2).isSome

/-- The indices of the distinct finite points in lexicographic `(x, y)` order (the first
index of each duplicate). -/
def sortedUnique (pts : Array Pt) : Array Nat := Id.run do
  let idx := ((Array.range pts.size).filter fun i => finite pts[i]!).qsort fun i j =>
    let a := pts[i]!; let b := pts[j]!
    a.1 < b.1 || (a.1 == b.1 && (a.2 < b.2 || (a.2 == b.2 && i < j)))
  let mut out : Array Nat := #[]
  for i in idx do
    match out.back? with
    | some j => if pts[j]! != pts[i]! then out := out.push i
    | none => out := out.push i
  return out

/-! ## Convex hull -/

/-- Julia `chull` (Qhull) in the plane: the convex hull vertices (0-based indices into
`pts`), counter-clockwise from the lexicographically smallest point. Points on a hull
edge are omitted. Fewer than three non-collinear points give their distinct
extreme points (at most two). -/
def convexHull (pts : Array Pt) : Array Nat := Id.run do
  let s := sortedUnique pts
  if s.size ≤ 2 then return s
  let mut lower : Array Nat := #[]
  for i in s do
    while lower.size ≥ 2 && orient2d pts[lower[lower.size - 2]!]! pts[lower.back!]! pts[i]! ≤ 0 do
      lower := lower.pop
    lower := lower.push i
  let mut upper : Array Nat := #[]
  for i in s.reverse do
    while upper.size ≥ 2 && orient2d pts[upper[upper.size - 2]!]! pts[upper.back!]! pts[i]! ≤ 0 do
      upper := upper.pop
    upper := upper.push i
  let hull := lower.pop ++ upper.pop
  -- all collinear: the chain doubles back on itself
  return if hull.size == 2 && hull[0]! == hull[1]! then #[hull[0]!] else hull

/-! ## Delaunay triangulation -/

/-- A triangulation under construction: counter-clockwise triangles and the map from each
directed edge `(u, v)` to the triangle that has it. -/
structure Mesh where
  /-- The triangles `(a, b, c)`, counter-clockwise. -/
  tris : Array (Nat × Nat × Nat) := #[]
  /-- Directed edge ↦ triangle index. -/
  edge : Std.HashMap (Nat × Nat) Nat := {}

namespace Mesh

/-- Store triangle `t` at slot `k` (a new slot when `k = tris.size`). -/
def put (m : Mesh) (k : Nat) (t : Nat × Nat × Nat) : Mesh :=
  let (a, b, c) := t
  let tris := if k < m.tris.size then m.tris.set! k t else m.tris.push t
  { tris, edge := ((m.edge.insert (a, b) k).insert (b, c) k).insert (c, a) k }

/-- Add a triangle. -/
@[inline] def add (m : Mesh) (t : Nat × Nat × Nat) : Mesh := m.put m.tris.size t

/-- The vertex of triangle `t` opposite its directed edge `(u, v)`. -/
def opposite (t : Nat × Nat × Nat) (u v : Nat) : Nat :=
  let (a, b, c) := t
  if a != u && a != v then a else if b != u && b != v then b else c

end Mesh

/-- The sweep: a triangulation of the distinct points (not yet Delaunay). -/
def sweep (pts : Array Pt) (s : Array Nat) : Mesh := Id.run do
  let mut m : Mesh := {}
  if s.size < 3 then return m
  -- the first point off the line of s₀ s₁
  let mut k := 2
  while k < s.size && orient2d pts[s[0]!]! pts[s[1]!]! pts[s[k]!]! == 0 do
    k := k + 1
  if k == s.size then return m
  let o := orient2d pts[s[0]!]! pts[s[1]!]! pts[s[k]!]!
  for i in [0:k - 1] do
    m := m.add (if o > 0 then (s[i]!, s[i + 1]!, s[k]!) else (s[i + 1]!, s[i]!, s[k]!))
  -- the hull, counter-clockwise
  let chain := (s.extract 0 k)
  let mut hull : Array Nat := if o > 0 then chain.push s[k]! else chain.reverse.push s[k]!
  for idx in [k + 1:s.size] do
    let p := s[idx]!
    let h := hull.size
    let vis := fun (i : Nat) => orient2d pts[hull[i % h]!]! pts[hull[(i + 1) % h]!]! pts[p]! < 0
    -- a visible edge whose predecessor is not visible starts the chain
    let mut start := h
    for i in [0:h] do
      if start == h && vis i && !vis (i + h - 1) then start := i
    if start == h then continue -- unreachable for a lexicographically last distinct point
    let mut len := 0
    while len < h && vis (start + len) do
      len := len + 1
    for j in [0:len] do
      let a := hull[(start + j) % h]!
      let b := hull[(start + j + 1) % h]!
      m := m.add (b, a, p)
    -- replace the chain's interior vertices by p
    let rot := (hull.extract ((start + len) % h) h) ++ (hull.extract 0 ((start + len) % h))
    -- rot starts at the chain's last vertex; the chain's first vertex is at index h - len
    hull := (rot.extract 0 (h - len + 1)).push p
  return m

/-- Lawson's flips: flip every interior edge whose opposite vertex lies strictly inside the
circumcircle, until there are none. -/
def lawson (pts : Array Pt) (m0 : Mesh) : Mesh := Id.run do
  let mut m := m0
  let mut stack : Array (Nat × Nat) := m.tris.foldl (fun acc (a, b, c) => ((acc.push (a, b)).push (b, c)).push (c, a)) #[]
  -- each flip strictly lowers the triangulation in the lifting map, so this terminates; the
  -- fuel bound only guards against a predicate bug
  let mut fuel := 64 * (stack.size + 1) * (stack.size + 1)
  while fuel > 0 do
    fuel := fuel - 1
    match stack.back? with
    | none => break
    | some (u, v) =>
      stack := stack.pop
      match m.edge.get? (u, v), m.edge.get? (v, u) with
      | some t1, some t2 =>
        let w := Mesh.opposite m.tris[t1]! u v
        let x := Mesh.opposite m.tris[t2]! v u
        if m.tris[t1]! != m.tris[t2]! && incircle pts[u]! pts[v]! pts[w]! pts[x]! > 0 then
          let e := (m.edge.erase (u, v)).erase (v, u)
          m := { m with edge := e }
          m := m.put t1 (u, x, w)
          m := m.put t2 (x, v, w)
          stack := (((stack.push (u, x)).push (x, v)).push (v, w)).push (w, u)
      | _, _ => pure ()
  return m

/-- Julia `delaunay(points)` in the plane: the Delaunay triangles as counter-clockwise
triples of 0-based indices into `pts`. -/
def delaunay (pts : Array Pt) : Array (Nat × Nat × Nat) :=
  (lawson pts (sweep pts (sortedUnique pts))).tris

/-- The triangulation as a `SimplexBundle` of homogeneous points `(1, x, y)` (1-based vertex
ids, as Julia's `SimplexTopology`). -/
def delaunayBundle (pts : Array Pt) : SimplexBundle 3 (Grassmann.Chain Grassmann.ℝ3 1 Float) :=
  let hp := fun (p : Pt) => (Grassmann.Chain.ofFn fun i => #[1, p.1, p.2][i.1]! : Grassmann.Chain Grassmann.ℝ3 1 Float)
  SimplexBundle.ofPoints (pts.map hp) ((delaunay pts).map fun (a, b, c) => #v[a + 1, b + 1, c + 1])

end Cartan.Delaunay

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

/-- Lawson's flips from a stack of edges: flip every interior edge whose opposite vertex lies
strictly inside the circumcircle, pushing the edges a flip exposes, until the stack is empty.
Edges with `fixed u v` (constrained segments) are never flipped. -/
def lawsonFrom (pts : Array Pt) (m0 : Mesh) (stack0 : Array (Nat × Nat))
    (fixed : Nat → Nat → Bool := fun _ _ => false) : Mesh := Id.run do
  let mut m := m0
  let mut stack := stack0
  -- each flip strictly lowers the triangulation in the lifting map, so this terminates; the
  -- fuel bound only guards against a predicate bug
  let mut fuel := 64 * (m.tris.size + stack.size + 1) * (m.tris.size + stack.size + 1)
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
        if m.tris[t1]! != m.tris[t2]! && !fixed u v && incircle pts[u]! pts[v]! pts[w]! pts[x]! > 0 then
          let e := (m.edge.erase (u, v)).erase (v, u)
          m := { m with edge := e }
          m := m.put t1 (u, x, w)
          m := m.put t2 (x, v, w)
          stack := (((stack.push (u, x)).push (x, v)).push (v, w)).push (w, u)
      | _, _ => pure ()
  return m

/-- Lawson's flips over every edge of the mesh. -/
def lawson (pts : Array Pt) (m : Mesh) : Mesh :=
  lawsonFrom pts m (m.tris.foldl (fun acc (a, b, c) => ((acc.push (a, b)).push (b, c)).push (c, a)) #[])

/-! ### The fast path: a sweep over half-edge arrays

The same lexicographic sweep and Lawson flips as `sweep`/`lawson`, on flat arrays (the
representation of Delaunator): half-edge `e` of triangle `e / 3` starts at vertex `tv[e]` and ends
at `tv[next e]`, `twin[e]` is the opposite half-edge (`none` on the hull), the hull is a
doubly linked list with, for each hull vertex `v`, the interior half-edge `hullTri[v]` of the hull
edge `v → hullNext[v]`. Each new point starts its visible chain at the previous point (the
lexicographic maximum is always on the hull), so the sweep is `O(n)` apart from the flips, and a
flip touches only the two triangles of the quadrilateral. -/

/-- "No half-edge". Below `2³²`, so the literal stays a small `Nat` (a larger one is parsed from a
string wherever it is inlined, see `Grassmann.Composite.noCap`). -/
def noEdge : Nat := 1 <<< 31

/-- The state of the fast sweep. -/
structure Fast where
  /-- Coordinates. -/
  xs : FloatArray
  /-- Coordinates. -/
  ys : FloatArray
  /-- Start vertex of each half-edge. -/
  tv : Array Nat
  /-- Opposite half-edge (`noEdge` on the hull). -/
  twin : Array Nat
  /-- Hull successor (counter-clockwise). -/
  hullNext : Array Nat
  /-- Hull predecessor. -/
  hullPrev : Array Nat
  /-- The interior half-edge of the hull edge `v → hullNext[v]`. -/
  hullTri : Array Nat

namespace Fast

/-- The point `i`. -/
@[inline] def pt (F : Fast) (i : Nat) : Pt := (F.xs.get! i, F.ys.get! i)

/-- `orient2d` of three vertices (the float filter on unboxed coordinates, the exact predicate
only when it is inconclusive). -/
@[inline] def orient (F : Fast) (a b c : Nat) : Int :=
  let ax := F.xs.get! a; let ay := F.ys.get! a
  let l := (F.xs.get! b - ax) * (F.ys.get! c - ay)
  let r := (F.ys.get! b - ay) * (F.xs.get! c - ax)
  let det := l - r
  let bound := (3 + 16 * eps) * eps * (l.abs + r.abs)
  if det > bound then 1 else if -det > bound then -1 else orientExact (F.pt a) (F.pt b) (F.pt c)

/-- `incircle` of four vertices (unboxed float filter, exact fallback). -/
@[inline] def inCircle (F : Fast) (a b c d : Nat) : Int :=
  let dx := F.xs.get! d; let dy := F.ys.get! d
  let adx := F.xs.get! a - dx; let ady := F.ys.get! a - dy
  let bdx := F.xs.get! b - dx; let bdy := F.ys.get! b - dy
  let cdx := F.xs.get! c - dx; let cdy := F.ys.get! c - dy
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
  if det > bound then 1 else if -det > bound then -1
  else incircleExact (F.pt a) (F.pt b) (F.pt c) (F.pt d)

/-- The next half-edge in the triangle. -/
@[inline] def nxt (e : Nat) : Nat := if e % 3 == 2 then e - 2 else e + 1

/-- The previous half-edge in the triangle. -/
@[inline] def prv (e : Nat) : Nat := if e % 3 == 0 then e + 2 else e - 1

/-- Pair two half-edges. -/
@[inline] def link (F : Fast) (a b : Nat) : Fast :=
  let F := { F with twin := F.twin.set! a b }
  if b == noEdge then F else { F with twin := F.twin.set! b a }

/-- Append the triangle `(a, b, c)` (counter-clockwise) with the twins of its three half-edges;
returns the index of its first half-edge. -/
def addTri (F : Fast) (a b c ta tb tc : Nat) : Fast × Nat :=
  let e := F.tv.size
  let F := { F with tv := ((F.tv.push a).push b).push c,
                    twin := ((F.twin.push noEdge).push noEdge).push noEdge }
  let F := F.link e ta
  let F := F.link (e + 1) tb
  (F.link (e + 2) tc, e)

/-- Lawson flips from a stack of half-edges. With `full = false` the third vertex of each
stacked half-edge's triangle is the newest point, and after a flip only the two edges opposite
it are pushed (incremental insertion); with `full = true` all four outer edges are. -/
def legalize (F : Fast) (stack : Array Nat) (full : Bool := false) : Nat → Fast
  | 0 => F
  | fuel + 1 =>
    match stack.back? with
    | none => F
    | some a =>
      let stack := stack.pop
      let b := F.twin[a]!
      if b == noEdge then legalize F stack full fuel
      else
        let ar := prv a
        let al := nxt a
        let bl := prv b
        let br := nxt b
        let p0 := F.tv[ar]!
        let pr := F.tv[a]!
        let pl := F.tv[al]!
        let p1 := F.tv[bl]!
        if F.inCircle pr pl p0 p1 > 0 then
          let hbl := F.twin[bl]!
          let har := F.twin[ar]!
          let F := { F with tv := (F.tv.set! a p1).set! b p0 }
          -- a hull edge whose interior half-edge moved
          let F := if hbl == noEdge then { F with hullTri := F.hullTri.set! p1 a } else F
          let F := if har == noEdge then { F with hullTri := F.hullTri.set! p0 b } else F
          let F := F.link a hbl
          let F := F.link b har
          let F := F.link ar bl
          let stack := if full then (((stack.push br).push a).push al).push b
            else (stack.push br).push a
          legalize F stack full fuel
        else legalize F stack full fuel

/-- Insert the point `p` (lexicographically greater than every inserted point) given the
previously inserted point `q`. -/
def insert (F : Fast) (p q : Nat) : Fast := Id.run do
  let vis := fun (F : Fast) (a : Nat) => F.orient a F.hullNext[a]! p < 0
  -- the visible chain start → … → stop around q
  let mut start := q
  let mut guard := F.hullNext.size
  while guard > 0 && vis F F.hullPrev[start]! do
    start := F.hullPrev[start]!
    guard := guard - 1
  let mut stop := q
  guard := F.hullNext.size
  while guard > 0 && vis F stop do
    stop := F.hullNext[stop]!
    guard := guard - 1
  if start == stop then return F
  let mut F := F
  let mut a := start
  let mut prevPb := noEdge  -- the half-edge p → a of the previous new triangle
  let mut firstAp := noEdge
  let mut stack : Array Nat := #[]
  while a != stop do
    let b := F.hullNext[a]!
    -- triangle (b, a, p): b → a twins the interior a → b; a → p twins the previous p → a
    let (F', e) := F.addTri b a p F.hullTri[a]! prevPb noEdge
    F := F'
    if firstAp == noEdge then firstAp := e + 1
    prevPb := e + 2
    stack := stack.push e
    a := b
  -- hull: start → p → stop
  F := { F with hullNext := (F.hullNext.set! start p).set! p stop,
                hullPrev := (F.hullPrev.set! p start).set! stop p,
                hullTri := (F.hullTri.set! start firstAp).set! p prevPb }
  return F.legalize stack false (64 * (F.tv.size + 16))

end Fast

/-- `delaunay` on the half-edge arrays. -/
def delaunayFast (pts : Array Pt) : Array (Nat × Nat × Nat) := Id.run do
  let s := sortedUnique pts
  if s.size < 3 then return #[]
  let n := pts.size
  let xs : FloatArray := ⟨pts.map (·.1)⟩
  let ys : FloatArray := ⟨pts.map (·.2)⟩
  let mut F : Fast := ⟨xs, ys, #[], #[], Array.replicate n noEdge, Array.replicate n noEdge,
    Array.replicate n noEdge⟩
  -- the first point off the line of s₀ s₁
  let mut k := 2
  while k < s.size && F.orient s[0]! s[1]! s[k]! == 0 do
    k := k + 1
  if k == s.size then return #[]
  let o := F.orient s[0]! s[1]! s[k]!
  -- the fan of the collinear prefix to s[k], counter-clockwise, and its hull
  let chain := s.extract 0 k
  let hull : Array Nat := if o > 0 then chain.push s[k]! else chain.reverse.push s[k]!
  let h := hull.size
  for i in [0:h] do
    let v := hull[i]!
    let w := hull[(i + 1) % h]!
    F := { F with hullNext := F.hullNext.set! v w, hullPrev := F.hullPrev.set! w v }
  -- triangles (c_i, c_{i+1}, apex) along the counter-clockwise chain c (hull minus the apex)
  let apex := s[k]!
  let mut prevEdge := noEdge  -- apex → c_i of the previous triangle
  for i in [0:k - 1] do
    let a := hull[i]!
    let b := hull[i + 1]!
    let (F', e) := F.addTri a b apex noEdge noEdge prevEdge
    F := F'
    -- hull edge a → b (bottom chain), interior half-edge e
    F := { F with hullTri := F.hullTri.set! a e }
    if i == 0 then F := { F with hullTri := F.hullTri.set! apex (e + 2) }
    if i + 1 == k - 1 then F := { F with hullTri := F.hullTri.set! b (e + 1) }
    prevEdge := e + 1
  -- the twins between consecutive fan triangles: (b → apex) of i with (apex → b) of i+1
  for i in [0:k - 2] do
    F := F.link (3 * i + 1) (3 * (i + 1) + 2)
  F := F.legalize ((Array.range (k - 2)).map (3 * · + 1)) true (64 * (F.tv.size + 16) * (k + 1))
  let mut q := apex
  for idx in [k + 1:s.size] do
    let p := s[idx]!
    F := F.insert p q
    q := p
  return (Array.range (F.tv.size / 3)).map fun t => (F.tv[3 * t]!, F.tv[3 * t + 1]!, F.tv[3 * t + 2]!)

/-- Julia `delaunay(points)` in the plane: the Delaunay triangles as counter-clockwise
triples of 0-based indices into `pts`. -/
def delaunay (pts : Array Pt) : Array (Nat × Nat × Nat) := delaunayFast pts

/-- The triangulation as a `SimplexBundle` of homogeneous points `(1, x, y)` (1-based vertex
ids, as Julia's `SimplexTopology`). -/
def delaunayBundle (pts : Array Pt) : SimplexBundle 3 (Grassmann.Chain Grassmann.ℝ3 1 Float) :=
  let hp := fun (p : Pt) => (Grassmann.Chain.ofFn fun i => #[1, p.1, p.2][i.1]! : Grassmann.Chain Grassmann.ℝ3 1 Float)
  SimplexBundle.ofPoints (pts.map hp) ((delaunay pts).map fun (a, b, c) => #v[a + 1, b + 1, c + 1])

end Cartan.Delaunay

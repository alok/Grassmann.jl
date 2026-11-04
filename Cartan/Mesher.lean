import Cartan.Delaunay

/-!
# Quality triangulation of planar domains (Cartan's `TriangulateExt`)

Cartan.jl meshes planar domains with Shewchuk's Triangle through `TriangulateExt`
(`triangulate`/`initmesh`). It uses these meshes for the disk eigenmodes, the airfoil domain and
the FEM examples. This module is a dependency-free replacement for the core of Triangle:
**Ruppert's Delaunay refinement** of a planar straight-line graph (PSLG).

**Input** (`PSLG`):
* the domain's vertices;
* its segments, which carry the outer boundary, any inner boundaries and the boundaries of
  holes;
* seed points inside the holes.

The domain need not be convex.

**Algorithm.**
1. Triangulate the vertices (`Delaunay.delaunay`).
2. *Recover the segments.* A segment (or subsegment) is split at its midpoint while it is
   not a mesh edge or is *encroached*. Encroached means that a mesh vertex lies in its
   closed diametral circle; only the two opposite apices are checked, as Triangle does.
   Afterwards every subsegment is an edge, and the triangulation is the conforming Delaunay
   triangulation.
3. *Classify.* A triangle is outside the domain when it can be reached from a hull edge
   that is not a segment, or from a hole seed, without crossing a segment. Only triangles
   inside the domain are refined or returned.
4. *Refine.* A triangle is bad when its smallest angle is below `minAngle`, which means its
   circumradius-to-shortest-edge ratio exceeds `1/(2 sin θ)`, or when its area exceeds
   `maxArea`. A bad triangle is split at its circumcentre. If the circumcentre encroaches a
   subsegment, the subsegment is split at its midpoint instead. With all input angles
   ≥ 60°, Ruppert's theorem guarantees termination for `minAngle ≤ 20.7°`. Triangle's default
   is 20°. Smaller input angles are guarded by the `maxSteiner` cap.

Insertion locates the point by a scan and splits the containing triangle (three ways) or edge
(four ways). It then restores the Delaunay property with Lawson flips that never flip a
subsegment. Every topological decision uses the exact predicates of `Cartan.Delaunay`, so
grid-aligned and cocircular inputs are safe. Circumcentres and midpoints are floats, so
a split subsegment is collinear only to rounding. Triangle has the same limitation.

**Output** (`Result`):
* every point: the input points followed by the Steiner points;
* the domain's triangles, counter-clockwise;
* the subsegments, which make up the boundary edges.

`triangulateBundle` returns the mesh as a `SimplexBundle 3` of homogeneous points.
-/

namespace Cartan.Mesher

open Cartan.Delaunay

/-- A planar straight-line graph: vertices, segments between them (0-based) and one seed point
inside each hole. -/
structure PSLG where
  /-- The vertices. -/
  points : Array Pt
  /-- The segments (boundary and interior constraints). -/
  segments : Array (Nat × Nat)
  /-- A point inside each hole. -/
  holes : Array Pt := #[]

/-- Refinement options (Triangle's `-q` and `-a`). -/
structure Options where
  /-- The smallest angle allowed, in degrees (`0`: no angle bound). -/
  minAngle : Float := 20
  /-- The largest triangle area allowed (`0`: no area bound). -/
  maxArea : Float := 0
  /-- The most Steiner points to insert. -/
  maxSteiner : Nat := 100000

/-- A refined mesh. -/
structure Result where
  /-- Every point: the input points, then the Steiner points. -/
  points : Array Pt
  /-- The triangles of the domain, counter-clockwise (0-based). -/
  triangles : Array (Nat × Nat × Nat)
  /-- The subsegments of the input segments (the boundary and constraint edges). -/
  segments : Array (Nat × Nat)
  /-- Whether the refinement stopped at `maxSteiner` with bad triangles left. -/
  capped : Bool

/-- The unordered key of an edge. -/
@[inline] def key (u v : Nat) : Nat × Nat := if u ≤ v then (u, v) else (v, u)

/-- The refinement state. -/
structure State where
  /-- All points so far. -/
  pts : Array Pt
  /-- The triangulation. -/
  mesh : Mesh
  /-- The subsegments, unordered keys. -/
  segs : Std.HashSet (Nat × Nat)
  /-- Steiner points inserted. -/
  steiner : Nat := 0

namespace State

/-- Whether an edge is a subsegment. -/
@[inline] def isSeg (s : State) (u v : Nat) : Bool := s.segs.contains (key u v)

/-- Restore the Delaunay property from a stack of edges, never flipping a subsegment. -/
def flip (s : State) (stack : Array (Nat × Nat)) : State :=
  { s with mesh := lawsonFrom s.pts s.mesh stack (fun u v => s.isSeg u v) }

/-- Split the mesh edge `(u, v)` at the new point `k` (it lies on the edge up to rounding).
A subsegment `(u, v)` becomes the two subsegments `(u, k)` and `(k, v)`. -/
def splitEdge (s : State) (u v k : Nat) : State := Id.run do
  let (u, v) := if s.mesh.edge.contains (u, v) then (u, v) else (v, u)
  let mut m := s.mesh
  let mut stack : Array (Nat × Nat) := #[]
  let t1? := m.edge.get? (u, v)
  let t2? := m.edge.get? (v, u)
  m := { m with edge := (m.edge.erase (u, v)).erase (v, u) }
  if let some t1 := t1? then
    let w := Mesh.opposite m.tris[t1]! u v
    m := m.put t1 (u, k, w)
    m := m.add (k, v, w)
    stack := (stack.push (v, w)).push (w, u)
  if let some t2 := t2? then
    let x := Mesh.opposite m.tris[t2]! v u
    m := m.put t2 (v, k, x)
    m := m.add (k, u, x)
    stack := (stack.push (u, x)).push (x, v)
  let segs := if s.isSeg u v then ((s.segs.erase (key u v)).insert (key u k)).insert (key k v) else s.segs
  return { s with mesh := m, segs }.flip stack

/-- Classify `p` against triangle `t`: `some (some edge)` / `some none` when `t` contains it
(on that edge / inside), `none` otherwise, with the first edge `p` lies strictly right of. -/
def classify (s : State) (t : Nat) (p : Pt) : Except (Option (Nat × Nat)) (Option (Nat × Nat)) :=
  let (a, b, c) := s.mesh.tris[t]!
  let o1 := orient2d s.pts[a]! s.pts[b]! p
  let o2 := orient2d s.pts[b]! s.pts[c]! p
  let o3 := orient2d s.pts[c]! s.pts[a]! p
  if o1 < 0 then .error (some (a, b))
  else if o2 < 0 then .error (some (b, c))
  else if o3 < 0 then .error (some (c, a))
  else
    let zeros := [o1, o2, o3].filter (· == 0) |>.length
    if zeros ≥ 2 then .error none
    else if o1 == 0 then .ok (some (a, b))
    else if o2 == 0 then .ok (some (b, c))
    else if o3 == 0 then .ok (some (c, a))
    else .ok none

/-- Locate `p` by a visibility walk from triangle `start`: step across an edge `p` lies right
of until a triangle contains it (`none` when the walk leaves the triangulation or hits a
vertex). Walks in Delaunay triangulations do not cycle; the step cap guards the rest. -/
def walk (s : State) (start : Nat) (p : Pt) : Option (Option (Nat × Option (Nat × Nat))) := Id.run do
  let mut t := start
  for _ in [0:s.mesh.tris.size + 8] do
    match s.classify t p with
    | .ok e => return some (some (t, e))
    | .error none => return some none
    | .error (some (u, v)) =>
      match s.mesh.edge.get? (v, u) with
      | some t' => t := t'
      | none => return none
  return none

/-- The triangle containing `p`, and the edge it lies on (if any); `none` when `p` is outside
the triangulation or on a vertex. A walk from the last triangle is tried first, then a scan. -/
def locate (s : State) (p : Pt) : Option (Nat × Option (Nat × Nat)) := Id.run do
  if s.mesh.tris.size > 0 then
    match s.walk (s.mesh.tris.size - 1) p with
    | some r => return r
    | none => pure ()
  for t in [0:s.mesh.tris.size] do
    let (a, b, c) := s.mesh.tris[t]!
    let o1 := orient2d s.pts[a]! s.pts[b]! p
    let o2 := orient2d s.pts[b]! s.pts[c]! p
    let o3 := orient2d s.pts[c]! s.pts[a]! p
    if o1 ≥ 0 && o2 ≥ 0 && o3 ≥ 0 then
      let zeros := [o1, o2, o3].filter (· == 0) |>.length
      if zeros ≥ 2 then return none
      if o1 == 0 then return some (t, some (a, b))
      if o2 == 0 then return some (t, some (b, c))
      if o3 == 0 then return some (t, some (c, a))
      return some (t, none)
  return none

/-- Insert `p` as a new point. The flag is `false` (and the state unchanged) when `p` is outside
the triangulation or duplicates a vertex. The state is consumed, so the mesh arrays are
updated in place. -/
def insert (s : State) (p : Pt) : State × Bool :=
  match s.locate p with
  | none => (s, false)
  | some (t, onEdge) =>
    let k := s.pts.size
    let s := { s with pts := s.pts.push p, steiner := s.steiner + 1 }
    match onEdge with
    | some (u, v) => (s.splitEdge u v k, true)
    | none =>
      let (a, b, c) := s.mesh.tris[t]!
      let m := ((s.mesh.put t (a, b, k)).add (b, c, k)).add (c, a, k)
      ({ s with mesh := m }.flip #[(a, b), (b, c), (c, a)], true)

/-- Split the subsegment `(u, v)` at its midpoint. -/
def splitSeg (s : State) (u v : Nat) : State :=
  let a := s.pts[u]!; let b := s.pts[v]!
  let mid : Pt := ((a.1 + b.1) / 2, (a.2 + b.2) / 2)
  if s.mesh.edge.contains (u, v) || s.mesh.edge.contains (v, u) then
    let k := s.pts.size
    { s with pts := s.pts.push mid, steiner := s.steiner + 1 }.splitEdge u v k
  else
    -- not yet an edge: insert the midpoint wherever it falls and split the subsegment by hand
    let (s', ok) := s.insert mid
    if ok then
      let k := s'.pts.size - 1
      { s' with segs := ((s'.segs.erase (key u v)).insert (key u k)).insert (key k v) }
    else s'

/-- Whether `p` lies in the closed diametral circle of `(u, v)`. -/
@[inline] def encroaches (s : State) (u v : Nat) (p : Pt) : Bool :=
  let a := s.pts[u]!; let b := s.pts[v]!
  (a.1 - p.1) * (b.1 - p.1) + (a.2 - p.2) * (b.2 - p.2) ≤ 0

/-- A subsegment that is not an edge, or whose apex encroaches it. -/
def badSeg? (s : State) : Option (Nat × Nat) := Id.run do
  for (u, v) in s.segs.toList do
    let t1 := s.mesh.edge.get? (u, v)
    let t2 := s.mesh.edge.get? (v, u)
    if t1.isNone && t2.isNone then return some (u, v)
    for (t, a, b) in [(t1, u, v), (t2, v, u)] do
      if let some t := t then
        let w := Mesh.opposite s.mesh.tris[t]! a b
        if s.encroaches u v s.pts[w]! then return some (u, v)
  return none

/-- Split subsegments until every one is an edge and none is encroached. -/
def recover (s0 : State) (cap : Nat) : State := Id.run do
  let mut s := s0
  let mut fuel := cap
  while fuel > 0 do
    fuel := fuel - 1
    match s.badSeg? with
    | none => break
    | some (u, v) =>
      let before := s.pts.size
      s := s.splitSeg u v
      if s.pts.size == before then break -- the midpoint could not be placed
  return s

/-- The triangles inside the domain: those not reachable from a non-segment hull edge or a
hole seed without crossing a subsegment. -/
def interior (s : State) (holes : Array Pt) : Array Bool := Id.run do
  let m := s.mesh
  let n := m.tris.size
  let mut out := Array.replicate n false
  let mut stack : Array Nat := #[]
  for t in [0:n] do
    let (a, b, c) := m.tris[t]!
    for (u, v) in [(a, b), (b, c), (c, a)] do
      if !m.edge.contains (v, u) && !s.isSeg u v then stack := stack.push t
  for h in holes do
    if let some (t, _) := s.locate h then stack := stack.push t
  while !stack.isEmpty do
    let t := stack.back!
    stack := stack.pop
    if !out[t]! then
      out := out.set! t true
      let (a, b, c) := m.tris[t]!
      for (u, v) in [(a, b), (b, c), (c, a)] do
        if !s.isSeg u v then
          if let some t' := m.edge.get? (v, u) then
            if !out[t']! then stack := stack.push t'
  return out.map (!·)

end State

/-- The circumcentre of a triangle. -/
def circumcenter (a b c : Pt) : Pt :=
  let bx := b.1 - a.1; let by_ := b.2 - a.2
  let cx := c.1 - a.1; let cy := c.2 - a.2
  let d := 2 * (bx * cy - by_ * cx)
  let b2 := bx * bx + by_ * by_
  let c2 := cx * cx + cy * cy
  (a.1 + (cy * b2 - by_ * c2) / d, a.2 + (bx * c2 - cx * b2) / d)

/-- The squared length of an edge. -/
@[inline] def len2 (a b : Pt) : Float := (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2

/-- The smallest angle of a triangle, in degrees. -/
def minAngleDeg (a b c : Pt) : Float :=
  let ang := fun (p q r : Pt) =>
    let ux := q.1 - p.1; let uy := q.2 - p.2
    let vx := r.1 - p.1; let vy := r.2 - p.2
    Float.atan2 (ux * vy - uy * vx).abs (ux * vx + uy * vy)
  let m := min (ang a b c) (min (ang b c a) (ang c a b))
  m * 180 / 3.141592653589793

/-- Whether a triangle needs refining under the options. -/
def isBad (o : Options) (a b c : Pt) : Bool :=
  let area := ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)).abs / 2
  (o.maxArea > 0 && area > o.maxArea) ||
  (o.minAngle > 0 &&
    -- R / ℓ_min > 1 / (2 sin θ) ⇔ ℓ_a ℓ_b ℓ_c / (4 A ℓ_min) > 1 / (2 sin θ)
    let la := len2 b c; let lb := len2 c a; let lc := len2 a b
    let lmin := min la (min lb lc)
    let ratio2 := la * lb * lc / (16 * area * area * lmin)
    let s := Float.sin (o.minAngle * 3.141592653589793 / 180)
    ratio2 > 1 / (4 * s * s))

/-- Julia `triangulate(pslg; minangle, maxarea)` (Triangle's `-pq<minAngle>a<maxArea>`): a
quality conforming Delaunay triangulation of the domain. -/
def triangulate (g : PSLG) (o : Options := {}) : Result := Id.run do
  let pts := g.points
  let base := (delaunay pts).foldl Mesh.add {}
  let segs : Std.HashSet (Nat × Nat) :=
    g.segments.foldl (fun acc (u, v) => if u != v then acc.insert (key u v) else acc) {}
  let mut s : State := { pts, mesh := base, segs }
  s := s.recover o.maxSteiner
  let mut capped := false
  -- refinement passes: collect the bad interior triangles, split each that still exists
  let mut passes := 0
  while passes < o.maxSteiner do
    passes := passes + 1
    if s.steiner ≥ o.maxSteiner then
      capped := true
      break
    let inside := s.interior g.holes
    let bad := (Array.range s.mesh.tris.size).filter fun t =>
      inside[t]! && (let (a, b, c) := s.mesh.tris[t]!; isBad o s.pts[a]! s.pts[b]! s.pts[c]!)
    if bad.isEmpty then break
    let mut progress := false
    for t in bad do
      if s.steiner ≥ o.maxSteiner then break
      let tri := s.mesh.tris[t]!
      let (a, b, c) := tri
      -- skip triangles already destroyed in this pass
      if s.mesh.tris[t]! != tri then continue
      if !isBad o s.pts[a]! s.pts[b]! s.pts[c]! then continue
      let cc := circumcenter s.pts[a]! s.pts[b]! s.pts[c]!
      let enc := s.segs.toList.filter fun (u, v) => s.encroaches u v cc
      if !enc.isEmpty then
        for (u, v) in enc do
          if s.isSeg u v then s := s.splitSeg u v
        s := s.recover o.maxSteiner
        progress := true
      else
        -- `cc` encroaches no subsegment, and only its new neighbours changed, so no
        -- subsegment became encroached: no recovery pass is needed
        let (s', ok) := s.insert cc
        s := s'
        if ok then progress := true
    if !progress then break
  let inside := s.interior g.holes
  let tris := (Array.range s.mesh.tris.size).filterMap fun t =>
    if inside[t]! then some s.mesh.tris[t]! else none
  let bad := tris.any fun (a, b, c) => isBad o s.pts[a]! s.pts[b]! s.pts[c]!
  return { points := s.pts, triangles := tris, segments := s.segs.toArray, capped := capped && bad }

/-- The refined mesh as a `SimplexBundle` of homogeneous points `(1, x, y)` (1-based ids). -/
def triangulateBundle (g : PSLG) (o : Options := {}) :
    SimplexBundle 3 (Grassmann.Chain Grassmann.ℝ3 1 Float) :=
  let r := triangulate g o
  let hp := fun (p : Pt) =>
    (Grassmann.Chain.ofFn fun i => #[1, p.1, p.2][i.1]! : Grassmann.Chain Grassmann.ℝ3 1 Float)
  SimplexBundle.ofPoints (r.points.map hp) (r.triangles.map fun (a, b, c) => #v[a + 1, b + 1, c + 1])

/-! ## Domains -/

/-- A closed polygon as a PSLG (vertices in order, segments between neighbours). -/
def polygon (vs : Array Pt) : PSLG :=
  ⟨vs, (Array.range vs.size).map fun i => (i, (i + 1) % vs.size), #[]⟩

/-- The regular `n`-gon inscribed in the circle of radius `r` about `c` (a disk domain,
Julia `initmesh` of the unit circle). -/
def disk (n : Nat) (r : Float := 1) (c : Pt := (0, 0)) : PSLG :=
  polygon ((Array.range n).map fun k =>
    let t := 2 * 3.141592653589793 * k.toFloat / n.toFloat
    (c.1 + r * Float.cos t, c.2 + r * Float.sin t))

/-- A domain with holes: the outer polygon and each hole polygon (with a seed point inside it). -/
def withHoles (outer : Array Pt) (holes : Array (Array Pt × Pt)) : PSLG := Id.run do
  let mut g := polygon outer
  for (h, seed) in holes do
    let off := g.points.size
    g := { points := g.points ++ h,
           segments := g.segments ++ (Array.range h.size).map fun i => (off + i, off + (i + 1) % h.size),
           holes := g.holes.push seed }
  return g

end Cartan.Mesher

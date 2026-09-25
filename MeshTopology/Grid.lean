import MeshTopology.Quotient

/-!
# Node identification and multilinear cells of quotient grids

MeshTopology.jl `src/grid.jl`: turning a `QuotientTopology` into a mesh.

* `elementfuns` (GR:92-152): the canonical linear index of every grid point after the face
  gluings and collapses. It is Julia-exact, including two upstream quirks that are replicated:
  low faces only identify through mirrors and the identification is a single `min` step, so
  gluings with flips (Möbius, Klein, Hopf) leave duplicate nodes (Q7); and for `N ≥ 3` only the
  collapse flags act (Q6). `elementfunsClosed` is the transitive closure (union-find over all
  gluings and collapses) that downstream code should prefer.
* `vertices` (GR:298-308): the compact node numbering; `verticesInv`, `duplicates`,
  `duplicateMap`, `uniqueMap`.
* `linearElements` (GR:21-90): the multilinear cells (segments, quads, hexahedra, …) with Julia's
  corner order (Q4 and Q5 fixed).
* `BilinearTopology` (GR:200-277): quads of a 2-D quotient grid, degenerate quads split into
  triangles.

Grid arrays are flat `Array Nat` in column-major order with the grid's `size`.
-/

namespace MeshTopology

namespace QuotientTopology

variable {N : Nat}

/-- Linear (1-based) index of a multi-index of `m`'s grid. -/
@[inline] def lin (m : QuotientTopology N) (idx : Vector Int N) : Nat :=
  (linearIndex m.size idx).toNat

/-- Julia `getlinear(l, m, Val(0), i, j)` for a 2-D grid point (GR:164-198). -/
def getLinear2 (m : QuotientTopology 2) (idx : Vector Int 2) : Nat :=
  let (i, j) := (idx[0], idx[1])
  let isi := inBounds 0 1 i m.size[0]
  let isj := inBounds 0 2 j m.size[1]
  -- a low face identifies only through a mirror (a low target), a high face always
  let viaFace (a : Fin 2) (low : Bool) : Option Nat :=
    match m.glue[if low then lowFace a else highFace a] with
    | none => none
    | some g =>
      if low && g.target.1 % 2 == 1 then none else some (m.lin (m.resolveAt a idx))
  let r := if isj && !isi then viaFace 0 (i < 2)
    else if isi && !isj then viaFace 1 (j < 2)
    else if !isi && !isj then
      let o1 := m.ghost 1 idx
      let o2 := m.ghost 2 idx
      some (m.lin #v[min o1[0] o2[0], min o1[1] o2[1]])
    else none
  r.getD (m.lin idx)

/-- Julia `elementfun(l, m, idx…) = min(getlinear(l, m, Val(0), idx…), l[idx…])` (GR:147-152):
1-D topologies take the linear index of `m[i]` (Q3 fixed), 2-D ones `getLinear2`, and higher
dimensions the point itself (Q6, replicated). -/
def elementfun (m : QuotientTopology N) (idx : Vector Int N) : Nat :=
  let l := m.lin idx
  let g : Nat :=
    if N = 1 then m.lin (m.get idx)
    else if h : N = 2 then getLinear2 (h ▸ m) (h ▸ idx)
    else l
  min g l

/-- Apply the collapse flags in face order (GR:102-144): a collapsed low face of axis `a` becomes
node `1`, a collapsed high face takes the current value of its point with all other
coordinates `1`. -/
def applyCollapse (m : QuotientTopology N) (out : Array Nat) : Array Nat := Id.run do
  let len := out.size
  let mut out := out
  for h : f in [0:2 * N] do
    if m.collapse[f]'h.2.1 then
      let a := f / 2
      let na := m.size[a]!
      let low := f % 2 == 0
      let pos := if low then 1 else na
      let corner := linearIndex m.size (Vector.ofFn fun k => if k.1 = a then (pos : Int) else 1)
      let v := if low then 1 else out[corner.toNat - 1]!
      for p in [0:len] do
        let idx := cartesianIndex m.size (p + 1)
        if idx[a]! == pos then out := out.set! p v
  return out

/-- Julia `elementfuns(m)` (GR:92-145): the canonical linear index of every grid point,
column-major. The identity for an open topology. -/
def elementfuns (m : QuotientTopology N) : Array Nat :=
  let len := m.length
  if m.isOpen then (Array.range len).map (· + 1) else
  let raw := (Array.range len).map fun p =>
    m.elementfun ((cartesianIndex m.size (p + 1)).map (Int.ofNat ·))
  if N = 1 then raw else m.applyCollapse raw

/-- Union-find root with path halving (0-based). -/
private partial def ufFind (parent : Array Nat) (x : Nat) : Nat × Array Nat :=
  let p := parent[x]!
  if p == x then (x, parent)
  else
    let gp := parent[p]!
    ufFind (parent.set! x gp) gp

/-- Union the classes of `x` and `y`. -/
private def ufUnion (parent : Array Nat) (x y : Nat) : Array Nat :=
  let (rx, parent) := ufFind parent x
  let (ry, parent) := ufFind parent y
  if rx == ry then parent else parent.set! (max rx ry) (min rx ry)

/-- The transitive node identification (not in Julia): every boundary point is merged with its
image under its face's gluing, collapsed faces are merged into one node, and each class is
represented by its smallest linear index. Agrees with `elementfuns` for gluings with identity
transversal maps (torus, cylinder, sphere, ball, cone, …); for flipped gluings (Möbius, Klein,
Hopf) `elementfuns`'s classes refine these (Q7). -/
def elementfunsClosed (m : QuotientTopology N) : Array Nat := Id.run do
  let len := m.length
  let mut parent := Array.range len
  for p in [0:len] do
    let idx := (cartesianIndex m.size (p + 1)).map (Int.ofNat ·)
    for h : a in [0:N] do
      let i := idx[a]'h.2.1
      if i == 1 || i == (m.size[a]'h.2.1 : Int) then
        let r := m.ghost (a + 1) idx
        if (List.finRange N).all fun k => 0 < r[k] && r[k] ≤ (m.size[k] : Int) then
          parent := ufUnion parent p (m.lin r - 1)
  for h : f in [0:2 * N] do
    if m.collapse[f]'h.2.1 then
      let a := f / 2
      let pos : Nat := if f % 2 == 0 then 1 else m.size[a]!
      let mut first : Option Nat := none
      for p in [0:len] do
        if (cartesianIndex m.size (p + 1))[a]! == pos then
          match first with
          | none => first := some p
          | some q => parent := ufUnion parent q p
  let mut rep : Array Nat := Array.replicate len 0
  for p in [0:len] do
    let (r, par) := ufFind parent p
    parent := par
    rep := rep.set! p r
  -- union by smaller index keeps every root the minimum of its class
  return rep.map (· + 1)

/-! ## Node numbering -/

/-- Julia `vertices(elm::Array{Int})` (GR:300-308): renumber the representatives `1, 2, …` in
order of first appearance; every other point takes the number of its representative. -/
def verticesOfFuns (els : Array Nat) : Array Nat := Id.run do
  let len := els.size
  let mut isVal : Array Bool := Array.replicate (len + 1) false
  for e in els do
    isVal := isVal.set! e true
  -- out[unq] .= 1:k
  let mut out : Array Nat := Array.replicate len 0
  let mut seen : Array Bool := Array.replicate (len + 1) false
  let mut k := 0
  for e in els do
    if !seen[e]! then
      seen := seen.set! e true
      k := k + 1
      out := out.set! (e - 1) k
  -- out[dup] .= out[els[dup]] (right-hand side read before writing)
  let snapshot := out
  for d in [0:len] do
    if !isVal[d + 1]! then out := out.set! d snapshot[els[d]! - 1]!
  return out

/-- Julia `vertices(m::QuotientTopology)` (GR:298): the compact node number of every grid point
(column-major); the identity for an open topology. -/
def vertices (m : QuotientTopology N) : Array Nat :=
  if m.isOpen then (Array.range m.length).map (· + 1) else verticesOfFuns m.elementfuns

/-- Distinct values in order of first appearance (Julia `unique`). -/
def uniqueOrdered (els : Array Nat) : Array Nat := Id.run do
  let mx := els.foldl max 0
  let mut seen : Array Bool := Array.replicate (mx + 1) false
  let mut out : Array Nat := #[]
  for e in els do
    if !seen[e]! then
      seen := seen.set! e true
      out := out.push e
  return out

/-- Julia `verticesinv(m)` (GR:281-282): the representatives, in order of first appearance. -/
def verticesInv (m : QuotientTopology N) : Array Nat := uniqueOrdered m.elementfuns

/-- Julia `duplicates(m)` (GR:283-286): the grid points that represent no node, ascending. -/
def duplicates (m : QuotientTopology N) : Array Nat :=
  let els := m.elementfuns
  let isVal := els.foldl (fun (acc : Array Bool) e => acc.set! e true)
    (Array.replicate (els.size + 1) false)
  (Array.range els.size).filterMap fun p => if isVal[p + 1]! then none else some (p + 1)

/-- Julia `duplicatemap(m)` (GR:287-292): each duplicate `=>` its representative. -/
def duplicateMap (m : QuotientTopology N) : Array (Nat × Nat) :=
  let els := m.elementfuns
  m.duplicates.map fun d => (d, els[d - 1]!)

/-- Julia `uniquemap(m)` (GR:293-297): each representative `=>` its node number. -/
def uniqueMap (m : QuotientTopology N) : Array (Nat × Nat) :=
  (uniqueOrdered m.elementfuns).mapIdx fun k v => (v, k + 1)

end QuotientTopology

/-! ## Multilinear cells -/

/-- Corner offsets of a multilinear cell in Julia's order (GR:21-50): counter-clockwise in 2-D,
bottom then top in 3-D, the 3-D cube then a reversed snake in 4-D, and the 4-D pattern twice in
5-D. Higher dimensions (no Julia method) repeat the lower pattern at both ends of the last axis. -/
def cornerOffsets : Nat → List (List Nat)
  | 0 => [[]]
  | 1 => [[0], [1]]
  | 2 => [[0, 0], [1, 0], [1, 1], [0, 1]]
  | 3 => [[0, 0, 0], [1, 0, 0], [1, 1, 0], [0, 1, 0], [0, 0, 1], [1, 0, 1], [1, 1, 1], [0, 1, 1]]
  | 4 => (cornerOffsets 3).map (· ++ [0]) ++
      [[0, 1, 1, 1], [1, 1, 1, 1], [1, 0, 1, 1], [0, 0, 1, 1],
       [0, 1, 0, 1], [1, 1, 0, 1], [1, 0, 0, 1], [0, 0, 0, 1]]
  | n + 1 => (cornerOffsets n).map (· ++ [0]) ++ (cornerOffsets n).map (· ++ [1])

/-- Julia `linearelements(l, s)` (GR:52-56) of a column-major grid array `vals` of sizes `s`:
every cell's corner values, cells in column-major order over `s .- 1` (Q4: 1-D segments;
Q5: the 4-D `w` range uses `s[4]`). -/
def linearElements {N : Nat} (s : Vector Nat N) (vals : Array Nat) : Array (Array Nat) :=
  let cs := s.map (· - 1)
  let offs := cornerOffsets N
  (Array.range (gridLength cs)).map fun c =>
    let base := cartesianIndex cs (c + 1)
    (offs.map fun o =>
      let idx : Vector Int N := Vector.ofFn fun k => (base[k] + o[k.1]! : Nat)
      vals[(linearIndex s idx).toNat - 1]!).toArray

namespace QuotientTopology

variable {N : Nat}

/-- Julia `linearelements(m::QuotientTopology)` (GR:58-59): the cells of `elementfuns m`. -/
def linearElements (m : QuotientTopology N) : Array (Array Nat) :=
  MeshTopology.linearElements m.size m.elementfuns

end QuotientTopology

/-! ## BilinearTopology -/

/-- Julia `BilinearTopology` (GR:204-222): the quads of a 2-D quotient grid (node ids are the
canonical `elementfuns` values), with the quads that degenerate under the identification turned
into triangles. -/
structure BilinearTopology where
  /-- The quotient topology (Julia `m`). -/
  top : QuotientTopology 2
  /-- Non-degenerate quads (Julia `q`). -/
  quads : Array (Vector Nat 4)
  /-- Triangles from degenerate quads (Julia `t`). -/
  tris : Array (Vector Nat 3)
  /-- Compact node number of every grid point, column-major (Julia `i`). -/
  vertices : Array Nat
  /-- Representatives in order of first appearance (Julia `v`). -/
  verticesInv : Array Nat
  /-- Original cell id of each quad (Julia `iq`). -/
  quadIds : Array Nat
  /-- Original cell id of each triangle (Julia `it`). -/
  triIds : Array Nat
  /-- Per cell: `(4, quad index)` or `(3, triangle index)` (Julia `elementsplit`). -/
  split : Array (Nat × Nat)

/-- Julia `detect_tri(quad)` (GR:232-264): remove each quad with two equal consecutive corners
and record the triangle, in one order-preserving pass (Julia deletes in place, O(Q²)). -/
def detectTri (quads : Array (Vector Nat 4)) :
    Array (Vector Nat 4) × Array (Vector Nat 3) × Array Nat × Array Nat :=
  quads.zipIdx.foldl (fun (qs, ts, iq, it) (q, k) =>
    let t? : Option (Vector Nat 3) :=
      if q[0] == q[1] then some #v[q[1], q[2], q[3]]
      else if q[1] == q[2] then some #v[q[0], q[1], q[3]]
      else if q[2] == q[3] then some #v[q[0], q[1], q[2]]
      else if q[3] == q[0] then some #v[q[0], q[1], q[2]]
      else none
    match t? with
    | some t => (qs, ts.push t, iq, it.push (k + 1))
    | none => (qs.push q, ts, iq.push (k + 1), it)) (#[], #[], #[], #[])

/-- Julia `elementsplit(iq, it)` (GR:265-277). -/
def elementSplit (iq it : Array Nat) : Array (Nat × Nat) :=
  let out := Array.replicate (iq.size + it.size) (0, 0)
  let out := iq.zipIdx.foldl (fun o (i, j) => o.set! (i - 1) (4, j + 1)) out
  it.zipIdx.foldl (fun o (i, j) => o.set! (i - 1) (3, j + 1)) out

namespace BilinearTopology

/-- Julia `BilinearTopology(m)` = `MultilinearTopology(m)` (GR:216-222). -/
def ofQuotient (m : QuotientTopology 2) : BilinearTopology :=
  let efs := m.elementfuns
  let cells := (linearElements m.size efs).map fun c =>
    (#v[c[0]!, c[1]!, c[2]!, c[3]!] : Vector Nat 4)
  let (q, t, iq, it) := detectTri cells
  { top := m, quads := q, tris := t
    vertices := if m.isOpen then efs else QuotientTopology.verticesOfFuns efs
    verticesInv := QuotientTopology.uniqueOrdered efs
    quadIds := iq, triIds := it, split := elementSplit iq it }

/-- Julia `nodes(t)` (GR:227): the number of distinct nodes. -/
def nodes (t : BilinearTopology) : Nat := t.verticesInv.size

/-- Number of cells (Julia has no `size` method, Q23). -/
def size (t : BilinearTopology) : Nat := t.split.size

end BilinearTopology

end MeshTopology

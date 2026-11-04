import Cartan.Delaunay

/-!
# Delaunay tetrahedralization (Cartan's `DelaunayExt`/`TetGenExt` in 3-D, `QHullExt.chull`)

Cartan.jl calls Qhull/TetGen for 3-D point clouds. This module is a dependency-free
**Bowyer–Watson** tetrahedralization with exact predicates and *ghost tetrahedra*:

* **Predicates.** `orient3d` and `insphere` are Shewchuk's determinants with his static error
  bounds; when the float value is inside the bound the sign is recomputed over `ℚ`, so every
  topological decision is exact (grids, cospherical and coplanar points are safe).
* **Ghosts.** Every hull face `abc` carries a ghost tetrahedron `(a, b, c, ∞)`, oriented as if
  `∞` were a point far beyond the face. A point `p` conflicts with it when it lies strictly
  beyond the face, or on its plane and strictly inside the face's circumcircle (the limit of a
  circumsphere through a far point). Points outside the current hull then need no special case,
  and there is no super-tetrahedron to remove.
* **Insertion.** Points are inserted in Morton order. The conflict region of `p` is found by a
  visibility walk to a conflicting tetrahedron and a breadth-first search over conflicting
  neighbours (the open circumballs that contain `p`). Each boundary face `F` of the region is
  joined to `p` by replacing, in the cavity tetrahedron behind `F`, the vertex opposite `F` with
  `p`, which keeps the orientation. With the strict conflict test no new tetrahedron is flat:
  if `p` were on the plane of a boundary face it would be on that face's circumcircle, hence on
  the circumsphere of the cavity tetrahedron behind it, which would then not conflict.

The result is a Delaunay tetrahedralization of the distinct points: every tetrahedron is
positively oriented and no point lies strictly inside any circumsphere. The ghost faces are the
convex hull (`convexHull3`). Fewer than four non-coplanar points give no tetrahedra.
-/

namespace Cartan.Delaunay3

open JuliaBase Cartan.Delaunay

/-! ## Exact predicates -/

/-- A point of space. -/
structure P3 where
  /-- `x`. -/
  x : Float
  /-- `y`. -/
  y : Float
  /-- `z`. -/
  z : Float
  deriving Inhabited, BEq, Repr

/-- Exact `orient3d` over `ℚ`. -/
def orientExact (a b c d : P3) : Int :=
  match q a.x, q a.y, q a.z, q b.x, q b.y, q b.z, q c.x, q c.y, q c.z, q d.x, q d.y, q d.z with
  | some ax, some ay, some az, some bx, some by_, some bz, some cx, some cy, some cz,
      some dx, some dy, some dz =>
    let adx := ax - dx; let ady := ay - dy; let adz := az - dz
    let bdx := bx - dx; let bdy := by_ - dy; let bdz := bz - dz
    let cdx := cx - dx; let cdy := cy - dy; let cdz := cz - dz
    sgnQ (adx * (bdy * cdz - bdz * cdy) + bdx * (cdy * adz - cdz * ady) + cdx * (ady * bdz - adz * bdy))
  | _, _, _, _, _, _, _, _, _, _, _, _ => 0

/-- Shewchuk's `orient3d(a, b, c, d)`: `+1` when `d` lies below the plane through `a, b, c`
(counter-clockwise seen from above), `−1` above, `0` coplanar. Exact. -/
def orient3d (a b c d : P3) : Int :=
  let adx := a.x - d.x; let ady := a.y - d.y; let adz := a.z - d.z
  let bdx := b.x - d.x; let bdy := b.y - d.y; let bdz := b.z - d.z
  let cdx := c.x - d.x; let cdy := c.y - d.y; let cdz := c.z - d.z
  let bdxcdy := bdx * cdy; let cdxbdy := cdx * bdy
  let cdxady := cdx * ady; let adxcdy := adx * cdy
  let adxbdy := adx * bdy; let bdxady := bdx * ady
  let det := adz * (bdxcdy - cdxbdy) + bdz * (cdxady - adxcdy) + cdz * (adxbdy - bdxady)
  let perm := (bdxcdy.abs + cdxbdy.abs) * adz.abs + (cdxady.abs + adxcdy.abs) * bdz.abs +
    (adxbdy.abs + bdxady.abs) * cdz.abs
  let bound := (7 + 56 * eps) * eps * perm
  if det > bound then 1 else if -det > bound then -1 else orientExact a b c d

/-- Exact `insphere` over `ℚ`. -/
def insphereExact (a b c d e : P3) : Int :=
  match q a.x, q a.y, q a.z, q b.x, q b.y, q b.z, q c.x, q c.y, q c.z, q d.x, q d.y, q d.z,
      q e.x, q e.y, q e.z with
  | some ax, some ay, some az, some bx, some by_, some bz, some cx, some cy, some cz,
      some dx, some dy, some dz, some ex, some ey, some ez =>
    let aex := ax - ex; let aey := ay - ey; let aez := az - ez
    let bex := bx - ex; let bey := by_ - ey; let bez := bz - ez
    let cex := cx - ex; let cey := cy - ey; let cez := cz - ez
    let dex := dx - ex; let dey := dy - ey; let dez := dz - ez
    let ab := aex * bey - bex * aey; let bc := bex * cey - cex * bey
    let cd := cex * dey - dex * cey; let da := dex * aey - aex * dey
    let ac := aex * cey - cex * aey; let bd := bex * dey - dex * bey
    let abc := aez * bc - bez * ac + cez * ab
    let bcd := bez * cd - cez * bd + dez * bc
    let cda := cez * da + dez * ac + aez * cd
    let dab := dez * ab + aez * bd + bez * da
    let alift := aex * aex + aey * aey + aez * aez
    let blift := bex * bex + bey * bey + bez * bez
    let clift := cex * cex + cey * cey + cez * cez
    let dlift := dex * dex + dey * dey + dez * dez
    sgnQ ((dlift * abc - clift * dab) + (blift * cda - alift * bcd))
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => 0

/-- Shewchuk's `insphere(a, b, c, d, e)` for `orient3d(a, b, c, d) > 0`: `+1` when `e` lies
strictly inside the sphere through `a, b, c, d`, `−1` outside, `0` on it. Exact. -/
def insphere (a b c d e : P3) : Int :=
  let aex := a.x - e.x; let aey := a.y - e.y; let aez := a.z - e.z
  let bex := b.x - e.x; let bey := b.y - e.y; let bez := b.z - e.z
  let cex := c.x - e.x; let cey := c.y - e.y; let cez := c.z - e.z
  let dex := d.x - e.x; let dey := d.y - e.y; let dez := d.z - e.z
  let aexbey := aex * bey; let bexaey := bex * aey
  let bexcey := bex * cey; let cexbey := cex * bey
  let cexdey := cex * dey; let dexcey := dex * cey
  let dexaey := dex * aey; let aexdey := aex * dey
  let aexcey := aex * cey; let cexaey := cex * aey
  let bexdey := bex * dey; let dexbey := dex * bey
  let ab := aexbey - bexaey; let bc := bexcey - cexbey
  let cd := cexdey - dexcey; let da := dexaey - aexdey
  let ac := aexcey - cexaey; let bd := bexdey - dexbey
  let abc := aez * bc - bez * ac + cez * ab
  let bcd := bez * cd - cez * bd + dez * bc
  let cda := cez * da + dez * ac + aez * cd
  let dab := dez * ab + aez * bd + bez * da
  let alift := aex * aex + aey * aey + aez * aez
  let blift := bex * bex + bey * bey + bez * bez
  let clift := cex * cex + cey * cey + cez * cez
  let dlift := dex * dex + dey * dey + dez * dez
  let det := (dlift * abc - clift * dab) + (blift * cda - alift * bcd)
  let pab := aexbey.abs + bexaey.abs; let pbc := bexcey.abs + cexbey.abs
  let pcd := cexdey.abs + dexcey.abs; let pda := dexaey.abs + aexdey.abs
  let pac := aexcey.abs + cexaey.abs; let pbd := bexdey.abs + dexbey.abs
  let perm := ((pcd * bez.abs + pbd * cez.abs + pbc * dez.abs) * alift +
    (pda * cez.abs + pac * dez.abs + pcd * aez.abs) * blift) +
    ((pab * dez.abs + pbd * aez.abs + pda * bez.abs) * clift +
    (pbc * aez.abs + pac * bez.abs + pab * cez.abs) * dlift)
  let bound := (16 + 224 * eps) * eps * perm
  if det > bound then 1 else if -det > bound then -1 else insphereExact a b c d e

/-- A point with rational coordinates. -/
abbrev Q3 := Rat × Rat × Rat

/-- The exact coordinates of a finite point. -/
def toQ (p : P3) : Option Q3 := do return (← q p.x, ← q p.y, ← q p.z)

/-- `orient3d` over `ℚ` (Shewchuk's sign convention). -/
def orientQ (a b c d : Q3) : Int :=
  let (adx, ady, adz) := (a.1 - d.1, a.2.1 - d.2.1, a.2.2 - d.2.2)
  let (bdx, bdy, bdz) := (b.1 - d.1, b.2.1 - d.2.1, b.2.2 - d.2.2)
  let (cdx, cdy, cdz) := (c.1 - d.1, c.2.1 - d.2.1, c.2.2 - d.2.2)
  sgnQ (adx * (bdy * cdz - bdz * cdy) + bdx * (cdy * adz - cdz * ady) + cdx * (ady * bdz - adz * bdy))

/-- `insphere` over `ℚ` (positive inside for positively oriented `a b c d`). -/
def insphereQ (a b c d e : Q3) : Int :=
  let sub := fun (u : Q3) => (u.1 - e.1, u.2.1 - e.2.1, u.2.2 - e.2.2)
  let (aex, aey, aez) := sub a
  let (bex, bey, bez) := sub b
  let (cex, cey, cez) := sub c
  let (dex, dey, dez) := sub d
  let ab := aex * bey - bex * aey; let bc := bex * cey - cex * bey
  let cd := cex * dey - dex * cey; let da := dex * aey - aex * dey
  let ac := aex * cey - cex * aey; let bd := bex * dey - dex * bey
  let abc := aez * bc - bez * ac + cez * ab
  let bcd := bez * cd - cez * bd + dez * bc
  let cda := cez * da + dez * ac + aez * cd
  let dab := dez * ab + aez * bd + bez * da
  let alift := aex * aex + aey * aey + aez * aez
  let blift := bex * bex + bey * bey + bez * bez
  let clift := cex * cex + cey * cey + cez * cez
  let dlift := dex * dex + dey * dey + dez * dez
  sgnQ ((dlift * abc - clift * dab) + (blift * cda - alift * bcd))

/-- Whether `p` lies strictly inside the circumcircle of the triangle `a b c`, all four
coplanar. The sphere through `a, b, c` and `x = a + (b − a) × (c − a)` meets their plane in
that circle, so the test is `insphere(a, b, c, x, p)` over `ℚ` (a projection to a coordinate
plane would preserve orientation but not circles). -/
def incircleCoplanar (a b c p : P3) : Bool :=
  match toQ a, toQ b, toQ c, toQ p with
  | some qa, some qb, some qc, some qp =>
    let (ux, uy, uz) := (qb.1 - qa.1, qb.2.1 - qa.2.1, qb.2.2 - qa.2.2)
    let (vx, vy, vz) := (qc.1 - qa.1, qc.2.1 - qa.2.1, qc.2.2 - qa.2.2)
    let x : Q3 := (qa.1 + (uy * vz - uz * vy), qa.2.1 + (uz * vx - ux * vz), qa.2.2 + (ux * vy - uy * vx))
    let o := orientQ qa qb qc x
    o != 0 && o * insphereQ qa qb qc x qp > 0
  | _, _, _, _ => false

/-! ## The tetrahedralization -/

/-- A tetrahedralization under construction: four vertex ids per tetrahedron (`inf` is the
ghost vertex), the neighbour opposite each vertex, and the live flags. -/
structure Tets where
  /-- The point coordinates. -/
  pts : Array P3
  /-- The ghost vertex id (`pts.size`). -/
  inf : Nat
  /-- `tv[4t + i]`: vertex `i` of tetrahedron `t`. -/
  tv : Array Nat
  /-- `tn[4t + i]`: the tetrahedron across the face opposite vertex `i`. -/
  tn : Array Nat
  /-- Whether tetrahedron `t` is part of the current mesh. -/
  alive : Array Bool
  /-- Dead slots to reuse. -/
  free : Array Nat
  /-- The cavity stamp of each tetrahedron. -/
  stamp : Array Nat
  /-- A live tetrahedron to start walks from. -/
  last : Nat
  deriving Inhabited

namespace Tets

/-- Vertex `i` of `t`. -/
@[inline] def v (T : Tets) (t i : Nat) : Nat := T.tv[4 * t + i]!

/-- Whether `t` is a ghost, and the slot of its ghost vertex. -/
@[inline] def ghostSlot (T : Tets) (t : Nat) : Option Nat :=
  (List.range 4).find? fun i => T.v t i == T.inf

/-- The point of a (finite) vertex id. -/
@[inline] def pt (T : Tets) (i : Nat) : P3 := T.pts[i]!

/-- Whether `p` conflicts with `t` (lies in its open circumball, or beyond its ghost face). -/
def conflict (T : Tets) (t : Nat) (p : P3) : Bool :=
  match T.ghostSlot t with
  | none => insphere (T.pt (T.v t 0)) (T.pt (T.v t 1)) (T.pt (T.v t 2)) (T.pt (T.v t 3)) p > 0
  | some g =>
    -- the face in tetrahedron order with ∞ replaced by p: positive when p is beyond it
    let vs := (List.range 4).map fun i => if i == g then p else T.pt (T.v t i)
    let o := orient3d vs[0]! vs[1]! vs[2]! vs[3]!
    if o > 0 then true else if o < 0 then false else
      let f := (List.range 4).filter (· != g) |>.map fun i => T.pt (T.v t i)
      incircleCoplanar f[0]! f[1]! f[2]! p

/-- A fresh slot for a tetrahedron. -/
def alloc (T : Tets) (vs : Array Nat) : Tets × Nat :=
  match T.free.back? with
  | some t =>
    let tv := (List.range 4).foldl (fun a i => a.set! (4 * t + i) vs[i]!) T.tv
    ({ T with free := T.free.pop, tv, alive := T.alive.set! t true }, t)
  | none =>
    let t := T.alive.size
    let T' : Tets := { T with tv := T.tv ++ vs, tn := T.tn ++ #[0, 0, 0, 0] }
    ({ T' with alive := T'.alive.push true, stamp := T'.stamp.push 0 }, t)

/-- Make `t` and `u` neighbours across the face opposite vertex `i` of `t` and `j` of `u`. -/
@[inline] def link (T : Tets) (t i u j : Nat) : Tets :=
  { T with tn := (T.tn.set! (4 * t + i) u).set! (4 * u + j) t }

/-- A visibility walk from `T.last` to a tetrahedron that conflicts with `p` (a ghost when `p`
is outside the hull); a scan if the walk does not finish in `fuel` steps. -/
def locate (T : Tets) (p : P3) (fuel : Nat) : Nat := Id.run do
  let mut t := T.last
  let mut seed := 0
  for _ in [0:fuel] do
    if T.ghostSlot t |>.isSome then return t
    -- leave through a face that separates t from p (start at a rotating face)
    let mut moved := false
    for k in [0:4] do
      let i := (k + seed) % 4
      let vs := (List.range 4).map fun j => if j == i then p else T.pt (T.v t j)
      if !moved && orient3d vs[0]! vs[1]! vs[2]! vs[3]! < 0 then
        t := T.tn[4 * t + i]!
        moved := true
    seed := seed + 1
    if !moved then return t
  -- fallback
  for u in [0:T.alive.size] do
    if T.alive[u]! && T.conflict u p then return u
  return t

/-- Insert point `pi` (an index into `pts`). -/
def insert (T0 : Tets) (pi stampId : Nat) : Tets := Id.run do
  let p := T0.pt pi
  let s := T0.locate p (4 * T0.alive.size + 16)
  -- a duplicate of a vertex of the containing tetrahedron
  if (List.range 4).any fun i => T0.v s i != T0.inf && T0.pt (T0.v s i) == p then return T0
  let s := if T0.conflict s p then s else
    ((List.range T0.alive.size).find? fun u => T0.alive[u]! && T0.conflict u p).getD s
  if !(T0.conflict s p) then return T0
  let mut T := T0
  -- the conflict region, breadth first
  T := { T with stamp := T.stamp.set! s stampId }
  let mut cavity : Array Nat := #[s]
  let mut k := 0
  let mut bnd : Array (Nat × Nat) := #[]
  while k < cavity.size do
    let t := cavity[k]!
    k := k + 1
    for i in [0:4] do
      let u := T.tn[4 * t + i]!
      if T.stamp[u]! == stampId then continue
      if T.conflict u p then
        T := { T with stamp := T.stamp.set! u stampId }
        cavity := cavity.push u
      else
        bnd := bnd.push (t, i)
  -- new tetrahedra: the cavity tetrahedron behind each boundary face with its opposite vertex → p
  let mut made : Array (Nat × Nat × Nat) := #[]  -- (new tet, face slot i, outside neighbour)
  let olds := cavity
  let vsOf := bnd.map fun (t, i) => (Array.range 4).map fun j => if j == i then pi else T.v t j
  let outs := bnd.map fun (t, i) => (T.tn[4 * t + i]!, t)
  for t in olds do
    T := { T with alive := T.alive.set! t false }
  let mut faces : Std.HashMap (Nat × Nat) (Nat × Nat) := {}
  for b in [0:bnd.size] do
    let (_, i) := bnd[b]!
    let (T', nt) := T.alloc vsOf[b]!
    T := T'
    let (u, told) := outs[b]!
    -- u's pointer to the old cavity tetrahedron now points to nt
    let j := (List.range 4).find? (fun j => T.tn[4 * u + j]! == told) |>.getD 0
    T := T.link nt i u j
    made := made.push (nt, i, u)
    -- the three faces through p: opposite each other vertex; key = the two vertices besides p
    for jj in [0:4] do
      if jj != i then
        let others := (List.range 4).filter (fun r => r != i && r != jj) |>.map (T.v nt ·)
        let key := (min others[0]! others[1]!, max others[0]! others[1]!)
        match faces.get? key with
        | some (ot, oj) =>
          T := T.link nt jj ot oj
          faces := faces.erase key
        | none => faces := faces.insert key (nt, jj)
  -- the cavity slots are reused only by later insertions (a neighbour's pointer to an old
  -- tetrahedron must stay unambiguous while the new ones are linked)
  return { T with last := (made.back?.map (·.1)).getD T.last, free := T.free ++ olds }

end Tets

/-- Morton (Z-order) key of a point quantized to a 2¹⁰ grid of the bounding box. -/
def morton (lo hi : P3) (p : P3) : Nat :=
  let qz := fun (a l h : Float) =>
    let t := if h > l then (a - l) / (h - l) else 0
    (t * 1023).toUInt64.toNat
  let (x, y, z) := (qz p.x lo.x hi.x, qz p.y lo.y hi.y, qz p.z lo.z hi.z)
  (List.range 10).foldl (fun acc b =>
    acc ||| (((x >>> b) &&& 1) <<< (3 * b)) ||| (((y >>> b) &&& 1) <<< (3 * b + 1)) |||
      (((z >>> b) &&& 1) <<< (3 * b + 2))) 0

/-- The tetrahedralization of `pts` inserting the points in `order` (finite points only). -/
def buildOrdered (pts : Array P3) (order : Array Nat) (limit : Nat := order.size) : Option Tets := Id.run do
  let n := pts.size
  if order.size < 4 then return none
  -- an initial non-degenerate tetrahedron
  let a := order[0]!
  let some b := order.find? (fun i => pts[i]! != pts[a]!) | return none
  let collinear := fun (c : Nat) =>
    let pa := pts[a]!; let pb := pts[b]!; let pc := pts[c]!
    orient2d (pa.x, pa.y) (pb.x, pb.y) (pc.x, pc.y) == 0 && orient2d (pa.x, pa.z) (pb.x, pb.z) (pc.x, pc.z) == 0 &&
      orient2d (pa.y, pa.z) (pb.y, pb.z) (pc.y, pc.z) == 0
  let some c := order.find? (fun i => !collinear i) | return none
  let some d := order.find? (fun i => orient3d pts[a]! pts[b]! pts[c]! pts[i]! != 0) | return none
  let (a, b) := if orient3d pts[a]! pts[b]! pts[c]! pts[d]! > 0 then (a, b) else (b, a)
  let inf := n
  let mut T : Tets := ⟨pts, inf, #[a, b, c, d], #[0, 0, 0, 0], #[true], #[], #[0], 0⟩
  -- the ghost behind face i: tet 0 with vertex i → ∞ and two others swapped (∞ is beyond)
  let base := #[a, b, c, d]
  for i in [0:4] do
    let vs := (Array.range 4).map fun j => if j == i then inf else base[j]!
    let (r1, r2) := ((i + 1) % 4, (i + 2) % 4)
    let vs := (vs.set! r1 vs[r2]!).set! r2 vs[r1]!
    let (T', g) := T.alloc vs
    T := T'.link 0 i g i
  -- ghost–ghost adjacency: faces through ∞, matched by their two finite vertices
  let mut faces : Std.HashMap (Nat × Nat) (Nat × Nat) := {}
  for g in [1:5] do
    for jj in [0:4] do
      if T.v g jj != inf then
        let others := (List.range 4).filter (fun r => r != jj && T.v g r != inf) |>.map (T.v g ·)
        let key := (min others[0]! others[1]!, max others[0]! others[1]!)
        match faces.get? key with
        | some (ot, oj) => T := T.link g jj ot oj; faces := faces.erase key
        | none => faces := faces.insert key (g, jj)
  let mut stampId := 1
  for i in order.extract 0 limit do
    if i == a || i == b || i == c || i == d then continue
    stampId := stampId + 1
    T := T.insert i stampId
  return some T

/-- The Delaunay tetrahedralization state of the points (ghosts included). -/
def build (pts : Array P3) : Option Tets := Id.run do
  let n := pts.size
  if n < 4 then return none
  let fin := fun (p : P3) => (q p.x).isSome && (q p.y).isSome && (q p.z).isSome
  let idx := (Array.range n).filter fun i => fin pts[i]!
  if idx.size < 4 then return none
  let lo : P3 := ⟨idx.foldl (fun m i => min m pts[i]!.x) pts[idx[0]!]!.x,
    idx.foldl (fun m i => min m pts[i]!.y) pts[idx[0]!]!.y, idx.foldl (fun m i => min m pts[i]!.z) pts[idx[0]!]!.z⟩
  let hi : P3 := ⟨idx.foldl (fun m i => max m pts[i]!.x) pts[idx[0]!]!.x,
    idx.foldl (fun m i => max m pts[i]!.y) pts[idx[0]!]!.y, idx.foldl (fun m i => max m pts[i]!.z) pts[idx[0]!]!.z⟩
  let keys := idx.map fun i => (morton lo hi pts[i]!, i)
  let order := (keys.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)).map (·.2)
  buildOrdered pts order

/-- Julia `delaunay` / TetGen `tetrahedralize` of a point cloud: the Delaunay tetrahedra as
0-based vertex quadruples, each positively oriented (`orient3d > 0`). -/
def delaunay3 (pts : Array P3) : Array (Nat × Nat × Nat × Nat) :=
  match build pts with
  | none => #[]
  | some T => (Array.range T.alive.size).filterMap fun t =>
      if T.alive[t]! && (T.ghostSlot t).isNone then some (T.v t 0, T.v t 1, T.v t 2, T.v t 3) else none

/-- Julia `chull` (Qhull) in 3-D: the triangles of the convex hull, 0-based, oriented
counter-clockwise seen from outside (coplanar hull points split the faces Delaunay-wise). -/
def convexHull3 (pts : Array P3) : Array (Nat × Nat × Nat) :=
  match build pts with
  | none => #[]
  | some T => (Array.range T.alive.size).filterMap fun t =>
      if !T.alive[t]! then none else
      match T.ghostSlot t with
      | none => none
      | some g =>
        -- ghost (… ∞ …) is positive with ∞ beyond: the finite face in slot order, flipped to
        -- face outward
        let f := (List.range 4).filter (· != g) |>.map (T.v t ·)
        if g % 2 == 1 then some (f[0]!, f[2]!, f[1]!) else some (f[0]!, f[1]!, f[2]!)

/-- The tetrahedralization as a `SimplexBundle` of homogeneous points `(1, x, y, z)` (1-based
vertex ids, as Julia's `SimplexTopology`). -/
def delaunay3Bundle (pts : Array P3) : SimplexBundle 4 (Grassmann.Chain Grassmann.ℝ4 1 Float) :=
  let hp := fun (p : P3) =>
    (Grassmann.Chain.ofFn fun i => #[1, p.x, p.y, p.z][i.1]! : Grassmann.Chain Grassmann.ℝ4 1 Float)
  SimplexBundle.ofPoints (pts.map hp) ((delaunay3 pts).map fun (a, b, c, d) => #v[a + 1, b + 1, c + 1, d + 1])

end Cartan.Delaunay3

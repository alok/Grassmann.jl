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

/-- `x = m · 2^e` exactly, for a finite `x` (`m = 0` for zeros). -/
@[inline] def dyadic (x : Float) : Int × Int :=
  let b := x.toBits
  let ex := ((b >>> 52) &&& 0x7FF).toNat
  let fr := (b &&& 0xFFFFFFFFFFFFF).toNat
  let (m, e) : Nat × Int := if ex == 0 then (fr, -1074) else (fr + 4503599627370496, (ex : Int) - 1075)
  (if b >>> 63 == 1 then -(m : Int) else m, e)

/-- The coordinates as integers `xᵢ · 2^(−E)`, for the smallest exponent `E` among the nonzero
ones: an exact, common positive scaling, so the sign of any homogeneous integer polynomial in
them is the sign at the original values. `none` if a coordinate is not finite. -/
def scaledInts (xs : Array Float) : Option (Array Int) :=
  if xs.any fun x => x.isNaN || x.isInf then none else
  let ds := xs.map dyadic
  let E := ds.foldl (fun E (m, e) => if m == 0 then E else min E e) 0
  some (ds.map fun (m, e) => if m == 0 then 0 else m * (2 : Int) ^ (e - E).toNat)

/-- The sign of an integer. -/
@[inline] def sgnZ (x : Int) : Int := if x > 0 then 1 else if x < 0 then -1 else 0

/-- Exact `orient3d`, on the inputs scaled to integers (no rational normalisation). -/
def orientExact (a b c d : P3) : Int :=
  match scaledInts #[a.x, a.y, a.z, b.x, b.y, b.z, c.x, c.y, c.z, d.x, d.y, d.z] with
  | none => 0
  | some v =>
    let adx := v[0]! - v[9]!; let ady := v[1]! - v[10]!; let adz := v[2]! - v[11]!
    let bdx := v[3]! - v[9]!; let bdy := v[4]! - v[10]!; let bdz := v[5]! - v[11]!
    let cdx := v[6]! - v[9]!; let cdy := v[7]! - v[10]!; let cdz := v[8]! - v[11]!
    sgnZ (adx * (bdy * cdz - bdz * cdy) + bdx * (cdy * adz - cdz * ady) + cdx * (ady * bdz - adz * bdy))

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

/-- Exact `insphere`, on the inputs scaled to integers. -/
def insphereExact (a b c d e : P3) : Int :=
  match scaledInts #[a.x, a.y, a.z, b.x, b.y, b.z, c.x, c.y, c.z, d.x, d.y, d.z, e.x, e.y, e.z] with
  | none => 0
  | some v =>
    let aex := v[0]! - v[12]!; let aey := v[1]! - v[13]!; let aez := v[2]! - v[14]!
    let bex := v[3]! - v[12]!; let bey := v[4]! - v[13]!; let bez := v[5]! - v[14]!
    let cex := v[6]! - v[12]!; let cey := v[7]! - v[13]!; let cez := v[8]! - v[14]!
    let dex := v[9]! - v[12]!; let dey := v[10]! - v[13]!; let dez := v[11]! - v[14]!
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
    sgnZ ((dlift * abc - clift * dab) + (blift * cda - alift * bcd))

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
  if T.v t 0 == T.inf then some 0 else if T.v t 1 == T.inf then some 1
  else if T.v t 2 == T.inf then some 2 else if T.v t 3 == T.inf then some 3 else none

/-- The point of a (finite) vertex id. -/
@[inline] def pt (T : Tets) (i : Nat) : P3 := T.pts[i]!

/-- Vertex `j` of `t` as a point, with slot `g` replaced by `p`. -/
@[inline] def ptOr (T : Tets) (t j g : Nat) (p : P3) : P3 := if j == g then p else T.pt (T.v t j)

/-- `orient3d` of `t` with its slot `g` replaced by `p`. -/
@[inline] def orientWith (T : Tets) (t g : Nat) (p : P3) : Int :=
  orient3d (T.ptOr t 0 g p) (T.ptOr t 1 g p) (T.ptOr t 2 g p) (T.ptOr t 3 g p)

/-- The three slots other than `g`, in increasing order. -/
@[inline] def others (g : Nat) : Nat × Nat × Nat :=
  if g == 0 then (1, 2, 3) else if g == 1 then (0, 2, 3) else if g == 2 then (0, 1, 3) else (0, 1, 2)

/-- Whether `p` conflicts with `t` (lies in its open circumball, or beyond its ghost face). -/
def conflict (T : Tets) (t : Nat) (p : P3) : Bool :=
  match T.ghostSlot t with
  | none => insphere (T.pt (T.v t 0)) (T.pt (T.v t 1)) (T.pt (T.v t 2)) (T.pt (T.v t 3)) p > 0
  | some g =>
    -- the face in tetrahedron order with ∞ replaced by p: positive when p is beyond it
    let o := T.orientWith t g p
    if o > 0 then true else if o < 0 then false else
      let (a, b, c) := others g
      incircleCoplanar (T.pt (T.v t a)) (T.pt (T.v t b)) (T.pt (T.v t c)) p

/-- `T.tv[k] := x` in place (the field is taken out first so the array stays unshared). -/
@[inline] def setTv (T : Tets) (k x : Nat) : Tets :=
  let a := T.tv
  let T := { T with tv := #[] }
  { T with tv := a.set! k x }

/-- `T.tn[k] := x` in place. -/
@[inline] def setTn (T : Tets) (k x : Nat) : Tets :=
  let a := T.tn
  let T := { T with tn := #[] }
  { T with tn := a.set! k x }

/-- `T.alive[k] := x` in place. -/
@[inline] def setAlive (T : Tets) (k : Nat) (x : Bool) : Tets :=
  let a := T.alive
  let T := { T with alive := #[] }
  { T with alive := a.set! k x }

/-- `T.stamp[k] := x` in place. -/
@[inline] def setStamp (T : Tets) (k x : Nat) : Tets :=
  let a := T.stamp
  let T := { T with stamp := #[] }
  { T with stamp := a.set! k x }

/-- A fresh slot for a tetrahedron. -/
def alloc (T : Tets) (vs : Array Nat) : Tets × Nat :=
  match T.free.back? with
  | some t =>
    let free := T.free
    let T := { T with free := #[] }
    let T := { T with free := free.pop }
    let T := ((T.setTv (4 * t) vs[0]!).setTv (4 * t + 1) vs[1]! |>.setTv (4 * t + 2) vs[2]!).setTv (4 * t + 3) vs[3]!
    (T.setAlive t true, t)
  | none =>
    let t := T.alive.size
    let (tv, tn, alive, stamp) := (T.tv, T.tn, T.alive, T.stamp)
    let T := { T with tv := #[], tn := #[], alive := #[], stamp := #[] }
    ({ T with tv := tv ++ vs, tn := tn ++ #[0, 0, 0, 0], alive := alive.push true, stamp := stamp.push 0 }, t)

/-- Make `t` and `u` neighbours across the face opposite vertex `i` of `t` and `j` of `u`. -/
@[inline] def link (T : Tets) (t i u j : Nat) : Tets :=
  (T.setTn (4 * t + i) u).setTn (4 * u + j) t

/-- A visibility walk from `T.last` to a tetrahedron that conflicts with `p` (a ghost when `p`
is outside the hull); a scan if the walk does not finish in `fuel` steps. -/
def locate (T : Tets) (p : P3) (fuel : Nat) : Nat := Id.run do
  let mut t := T.last
  let mut seed := 0
  for _ in [0:fuel] do
    match T.ghostSlot t with
    | some g =>
      -- a ghost reached through its hull face has p beyond that face; a start ghost may not,
      -- so step into the finite tetrahedron behind it
      if T.conflict t p then return t
      t := T.tn[4 * t + g]!
      continue
    | none => pure ()
    -- leave through a face that separates t from p (start at a rotating face)
    let mut moved := false
    for k in [0:4] do
      let i := (k + seed) % 4
      if !moved && T.orientWith t i p < 0 then
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
  let dup := fun (i : Nat) => T0.v s i != T0.inf && T0.pt (T0.v s i) == p
  if dup 0 || dup 1 || dup 2 || dup 3 then return T0
  let s := if T0.conflict s p then s else
    ((List.range T0.alive.size).find? fun u => T0.alive[u]! && T0.conflict u p).getD s
  if !(T0.conflict s p) then return T0
  let mut T := T0
  -- the conflict region, breadth first
  T := T.setStamp s stampId
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
        T := T.setStamp u stampId
        cavity := cavity.push u
      else
        bnd := bnd.push (t, i)
  -- new tetrahedra: the cavity tetrahedron behind each boundary face with its opposite vertex → p
  let mut made : Array (Nat × Nat × Nat) := #[]  -- (new tet, face slot i, outside neighbour)
  let olds := cavity
  let vsOf := bnd.map fun (t, i) =>
    #[if i == 0 then pi else T.v t 0, if i == 1 then pi else T.v t 1, if i == 2 then pi else T.v t 2,
      if i == 3 then pi else T.v t 3]
  let outs := bnd.map fun (t, i) => (T.tn[4 * t + i]!, t)
  for t in olds do
    T := T.setAlive t false
  -- unmatched faces through p: (smaller, larger other vertex, tetrahedron, slot); the list stays
  -- short (the cavity boundary's open edges), so a linear scan beats hashing
  let mut pend : Array (Nat × Nat × Nat × Nat) := #[]
  for b in [0:bnd.size] do
    let (_, i) := bnd[b]!
    let (T', nt) := T.alloc vsOf[b]!
    T := T'
    let (u, told) := outs[b]!
    -- u's pointer to the old cavity tetrahedron now points to nt
    let j := if T.tn[4 * u]! == told then 0 else if T.tn[4 * u + 1]! == told then 1
      else if T.tn[4 * u + 2]! == told then 2 else 3
    T := T.link nt i u j
    made := made.push (nt, i, u)
    -- the three faces through p: opposite each other vertex; key = the two vertices besides p
    for jj in [0:4] do
      if jj != i then
        let (r0, r1, r2) := others jj
        let (x, y) := if r0 == i then (r1, r2) else if r1 == i then (r0, r2) else (r0, r1)
        let (x, y) := (T.v nt x, T.v nt y)
        let (x, y) := (min x y, max x y)
        match pend.findIdx? (fun (a, c, _, _) => a == x && c == y) with
        | some q =>
          let (_, _, ot, oj) := pend[q]!
          T := T.link nt jj ot oj
          pend := (pend.set! q pend.back!).pop
        | none => pend := pend.push (x, y, nt, jj)
  -- the cavity slots are reused only by later insertions (a neighbour's pointer to an old
  -- tetrahedron must stay unambiguous while the new ones are linked)
  let free := T.free
  T := { T with free := #[] }
  return { T with last := (made.back?.map (·.1)).getD T.last, free := free ++ olds }

end Tets

/-- Morton (Z-order) key of a point quantized to a 2¹⁰ grid of the bounding box. -/
def morton (lo hi : P3) (p : P3) : Nat :=
  let qz := fun (a l h : Float) =>
    let t := if h > l then (a - l) / (h - l) else 0
    (t * 1023).toUInt64
  let (x, y, z) := (qz p.x lo.x hi.x, qz p.y lo.y hi.y, qz p.z lo.z hi.z)
  -- spread the 10 bits of `v` to every third position
  let spread := fun (v : UInt64) =>
    let v := (v ||| (v <<< 16)) &&& 0x030000FF
    let v := (v ||| (v <<< 8)) &&& 0x0300F00F
    let v := (v ||| (v <<< 4)) &&& 0x030C30C3
    (v ||| (v <<< 2)) &&& 0x09249249
  (spread x ||| (spread y <<< 1) ||| (spread z <<< 2)).toNat

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
  let fin := fun (p : P3) => !(p.x.isNaN || p.x.isInf || p.y.isNaN || p.y.isInf || p.z.isNaN || p.z.isInf)
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

/-- The circumcentre and circumradius of a tetrahedron (floating point; `NaN`/`inf` when flat). -/
def circumsphere (a b c d : P3) : P3 × Float :=
  let (bx, by_, bz) := (b.x - a.x, b.y - a.y, b.z - a.z)
  let (cx, cy, cz) := (c.x - a.x, c.y - a.y, c.z - a.z)
  let (dx, dy, dz) := (d.x - a.x, d.y - a.y, d.z - a.z)
  let (b2, c2, d2) := (bx * bx + by_ * by_ + bz * bz, cx * cx + cy * cy + cz * cz, dx * dx + dy * dy + dz * dz)
  let det := bx * (cy * dz - cz * dy) - by_ * (cx * dz - cz * dx) + bz * (cx * dy - cy * dx)
  let ux := (b2 * (cy * dz - cz * dy) - c2 * (by_ * dz - bz * dy) + d2 * (by_ * cz - bz * cy)) / (2 * det)
  let uy := -(b2 * (cx * dz - cz * dx) - c2 * (bx * dz - bz * dx) + d2 * (bx * cz - bz * cx)) / (2 * det)
  let uz := (b2 * (cx * dy - cy * dx) - c2 * (bx * dy - by_ * dx) + d2 * (bx * cy - by_ * cx)) / (2 * det)
  (⟨a.x + ux, a.y + uy, a.z + uz⟩, (ux * ux + uy * uy + uz * uz).sqrt)

/-- The radius–edge ratio (circumradius over shortest edge) of a tetrahedron: TetGen's `q`
quality measure, `√6/4 ≈ 0.612` for the regular tetrahedron. -/
def radiusEdge (a b c d : P3) : Float :=
  let dist := fun (p q : P3) => ((p.x - q.x) ^ 2 + (p.y - q.y) ^ 2 + (p.z - q.z) ^ 2).sqrt
  let e := min (min (min (dist a b) (dist a c)) (min (dist a d) (dist b c))) (min (dist b d) (dist c d))
  (circumsphere a b c d).2 / e

/-- Julia `∂` of a tetrahedral mesh: the faces used by exactly one tetrahedron, 0-based and
oriented counter-clockwise seen from outside (away from the tetrahedron that owns them). -/
def boundaryFaces (pts : Array P3) (ts : Array (Nat × Nat × Nat × Nat)) : Array (Nat × Nat × Nat) :=
  let key := fun (a b c : Nat) =>
    let s := #[a, b, c].qsort (· < ·)
    (s[0]!, s[1]!, s[2]!)
  let faces := fun ((a, b, c, d) : Nat × Nat × Nat × Nat) => #[(b, c, d, a), (a, c, d, b), (a, b, d, c), (a, b, c, d)]
  let count := ts.foldl (fun (m : Std.HashMap (Nat × Nat × Nat) Nat) t =>
    (faces t).foldl (fun m (a, b, c, _) => let k := key a b c; m.insert k (m.getD k 0 + 1)) m) {}
  ts.foldl (fun out t => (faces t).foldl (fun out (a, b, c, o) =>
    if count.getD (key a b c) 0 != 1 then out
    else if orient3d pts[a]! pts[b]! pts[c]! pts[o]! > 0 then out.push (a, b, c) else out.push (a, c, b)) out) #[]

/-- The tetrahedralization as a `SimplexBundle` of homogeneous points `(1, x, y, z)` (1-based
vertex ids, as Julia's `SimplexTopology`). -/
def delaunay3Bundle (pts : Array P3) : SimplexBundle 4 (Grassmann.Chain Grassmann.ℝ4 1 Float) :=
  let hp := fun (p : P3) =>
    (Grassmann.Chain.ofFn fun i => #[1, p.x, p.y, p.z][i.1]! : Grassmann.Chain Grassmann.ℝ4 1 Float)
  SimplexBundle.ofPoints (pts.map hp) ((delaunay3 pts).map fun (a, b, c, d) => #v[a + 1, b + 1, c + 1, d + 1])

/-- The convex hull as a boundary `SimplexBundle` on the same points as `delaunay3Bundle`
(Julia's boundary `e` of `tetrahedralize`), triangles 1-based and outward-oriented. -/
def hull3Bundle (pts : Array P3) : SimplexBundle 3 (Grassmann.Chain Grassmann.ℝ4 1 Float) :=
  let hp := fun (p : P3) =>
    (Grassmann.Chain.ofFn fun i => #[1, p.x, p.y, p.z][i.1]! : Grassmann.Chain Grassmann.ℝ4 1 Float)
  SimplexBundle.ofPoints (pts.map hp) ((convexHull3 pts).map fun (a, b, c) => #v[a + 1, b + 1, c + 1])

end Cartan.Delaunay3

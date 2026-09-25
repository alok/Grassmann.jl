import MeshTopology.Product

/-!
# QuotientTopology

Julia `QuotientTopology{N,L,M,O,LA}` (MeshTopology.jl `src/quotient.jl`): a structured grid of
sizes `s = (n₁,…,n_N)` whose boundary faces are glued to other faces (torus, Möbius strip,
Klein bottle, sphere, ball, cone, Hopf fibration, …).

## Representation

Julia stores the gluing as tables `p, q, r` indexed by *slot*: `r[f]` is the slot of face `f`
(`0` when open), `p[slot]` its target face and `q[slot]` the transversal map. In every Julia
constructor the nonzero `r` entries read `1, 2, …, O` in face order, so the tables are exactly a
face-indexed `Option Glue`: this is what we store (`toTable` rebuilds Julia's `p, q, r`).

* Faces are `Fin (2*N)`, 0-based: face `2a` is the low end (`i_a = 1`) and `2a+1` the high end
  (`i_a = n_a`) of the 0-based axis `a` (Julia faces `2a-1`/`2a` for the 1-based axis `a`).
* `Glue.maps : ProductTopology (N-1)` maps the transversal coordinates of the source face (all
  other axes, ascending) to those of the target face.
* `collapse` (Julia `c`) marks faces whose points are all one node (poles, centers); only the
  node identification `elementfuns` reads it.

The ghost-index resolver `ghost` (Julia `m[Val(K), i…]`, QT:400-561) is written once for every
`N`, over `Fin N` axes, instead of Julia's five hand-unrolled copies (one of which, for `N = 5`,
reads the wrong axis size: Q11).
-/

namespace MeshTopology

/-- A face identification: the target face and the map of transversal coordinates. -/
structure Glue (N : Nat) where
  /-- Target face, 0-based (Julia `p[slot] - 1`). -/
  target : Fin (2 * N)
  /-- Transversal map (Julia `q[slot]`); 0-dimensional for `N = 1`. -/
  maps : ProductTopology (N - 1)
  deriving BEq, Repr

/-- Julia `QuotientTopology{N}` (QT:27-36). -/
structure QuotientTopology (N : Nat) where
  /-- Grid sizes (Julia `s`). -/
  size : Vector Nat N
  /-- Per face: its identification, or `none` when the face is open (Julia `p, q, r`). -/
  glue : Vector (Option (Glue N)) (2 * N)
  /-- Collapsed faces (Julia `c`). -/
  collapse : Vector Bool (2 * N)
  deriving BEq, Repr

namespace QuotientTopology

variable {N : Nat}

/-! ## Faces and tables -/

/-- The 0-based axis of a 0-based face (Julia `_to_axis(f) = ceil(f/2)`, QT:187). -/
@[inline] def faceAxis (f : Fin (2 * N)) : Fin N := ⟨f.1 / 2, by omega⟩

/-- The low face of an axis. -/
@[inline] def lowFace (a : Fin N) : Fin (2 * N) := ⟨2 * a.1, by omega⟩

/-- The high face of an axis. -/
@[inline] def highFace (a : Fin N) : Fin (2 * N) := ⟨2 * a.1 + 1, by omega⟩

/-- Number of glued faces (Julia type parameter `O`). -/
def numGlued (m : QuotientTopology N) : Nat := m.glue.toList.countP (·.isSome)

/-- Julia `isopen(t)` (QT:183-184): no face is glued (`O == 0`). -/
def isOpen (m : QuotientTopology N) : Bool := m.glue.toList.all (·.isNone)

/-- Julia `iscompact(t)` (QT:185-186, Q2 fixed): every face is glued (`O == 2N`). -/
def isCompact (m : QuotientTopology N) : Bool := m.glue.toList.all (·.isSome)

/-- Julia's `(p, q, r)` tables: `p` and `q` per slot, `r` per face (1-based, `0` = open). -/
def toTable (m : QuotientTopology N) : Array Nat × Array (ProductTopology (N - 1)) × Array Nat :=
  m.glue.toList.foldl (fun (p, q, r) g =>
    match g with
    | none => (p, q, r.push 0)
    | some g => (p.push (g.target.1 + 1), q.push g.maps, r.push (p.size + 1))) (#[], #[], #[])

/-- Julia `QuotientTopology(p, q, r, s, c)` from tables satisfying the slot invariant (the
nonzero `r` entries are `1, 2, …` in face order); `none` otherwise. -/
def ofTable? (p : Array Nat) (q : Array (ProductTopology (N - 1))) (r : Array Nat)
    (s : Vector Nat N) (c : Vector Bool (2 * N)) : Option (QuotientTopology N) := do
  guard (r.size = 2 * N ∧ p.size = q.size)
  let (glue, used) ← r.toList.foldlM (fun (acc : Array (Option (Glue N)) × Nat) slot => do
    if slot == 0 then return (acc.1.push none, acc.2)
    guard (slot == acc.2 + 1)
    let t ← p[slot - 1]?
    let maps ← q[slot - 1]?
    if h : 0 < t ∧ t - 1 < 2 * N then
      return (acc.1.push (some ⟨⟨t - 1, h.2⟩, maps⟩), slot)
    else none) (#[], 0)
  guard (used = p.size)
  if h : glue.size = 2 * N then return ⟨s, ⟨glue, h⟩, c⟩ else none

/-! ## Named topologies (QT:47-85) -/

/-- The identity transversal map of face `f` (Julia `ProductTopology(sizes of the other axes)`). -/
def idMaps (s : Vector Nat N) (a : Fin N) : ProductTopology (N - 1) :=
  ProductTopology.ofSizes (s.eraseIdx a.1)

/-- The transversal map of axis `a` that is the identity except for `CrossRange` on the last
transversal axis (the half-turn of the periodic last axis). -/
def crossMaps (s : Vector Nat N) (a : Fin N) : ProductTopology (N - 1) :=
  let t := s.eraseIdx a.1
  ProductTopology.ofAxes (Vector.ofFn fun k : Fin (N - 1) =>
    if k.1 + 1 = N - 1 then .cross t[k] else .oneTo t[k])

/-- Build from a per-face table of `(target, maps)` (both 0-based). -/
def ofFaces (s : Vector Nat N) (g : Fin (2 * N) → Option (Fin (2 * N) × ProductTopology (N - 1)))
    (c : Fin (2 * N) → Bool := fun _ => false) : QuotientTopology N :=
  ⟨s, Vector.ofFn fun f => (g f).map fun (t, q) => ⟨t, q⟩, Vector.ofFn c⟩

/-- Julia `OpenTopology(n)` (QT:50): nothing glued. -/
def openTop (s : Vector Nat N) : QuotientTopology N := ofFaces s fun _ => none

/-- Julia `MirrorTopology(n)` (QT:54-58): face 1 is a mirror, the rest open. -/
def mirror (s : Vector Nat N) : QuotientTopology N :=
  ofFaces s fun f => if f.1 = 0 then some (f, idMaps s (faceAxis f)) else none

/-- Julia `ClampedTopology(n)` (QT:59-63): every face is a mirror. -/
def clamped (s : Vector Nat N) : QuotientTopology N :=
  ofFaces s fun f => some (f, idMaps s (faceAxis f))

/-- The opposite face of the same axis. -/
@[inline] def opposite (f : Fin (2 * N)) : Fin (2 * N) :=
  ⟨if f.1 % 2 = 0 then f.1 + 1 else f.1 - 1, by split <;> omega⟩

/-- Julia `TorusTopology(n)` (QT:64-68): every axis periodic. -/
def torus (s : Vector Nat N) : QuotientTopology N :=
  ofFaces s fun f => some (opposite f, idMaps s (faceAxis f))

/-- Julia `CylinderTopology(n1,n2)` (QT:51): axis 1 periodic. -/
def cylinder (s : Vector Nat 2) : QuotientTopology 2 :=
  ofFaces s fun f => if f.1 < 2 then some (opposite f, .ofSizes #v[s[1]]) else none

/-- Julia `MobiusTopology(n1,n2)` (QT:52): axis 1 periodic with the flip `j ↦ n2+1-j`. -/
def mobius (s : Vector Nat 2) : QuotientTopology 2 :=
  ofFaces s fun f =>
    if f.1 < 2 then some (opposite f, .single (.stepRange' s[1] (-1) 1)) else none

/-- Julia `WingTopology(n1,n2)` (QT:53): each end of axis 1 folded onto itself, reversed. -/
def wing (s : Vector Nat 2) : QuotientTopology 2 :=
  ofFaces s fun f => if f.1 < 2 then some (f, .single (.stepRange' s[1] (-1) 1)) else none

/-- Julia `HopfTopology(n1,n2)` (QT:69): axis 1 periodic with a half-turn in `j`; axis 2
periodic. -/
def hopf2 (s : Vector Nat 2) : QuotientTopology 2 :=
  ofFaces s fun f =>
    if f.1 < 2 then some (opposite f, .single (.cross s[1])) else some (opposite f, .ofSizes #v[s[0]])

/-- Julia `HopfTopology(n1,n2,n3)` (QT:70). -/
def hopf3 (s : Vector Nat 3) : QuotientTopology 3 :=
  ofFaces s fun f => some (opposite f, if f.1 < 4 then crossMaps s (faceAxis f) else idMaps s (faceAxis f))

/-- Julia `KleinTopology(n1,n2)` (QT:71): axis 1 periodic with a flip, axis 2 periodic. -/
def klein (s : Vector Nat 2) : QuotientTopology 2 :=
  ofFaces s fun f =>
    if f.1 < 2 then some (opposite f, .single (.stepRange' s[1] (-1) 1))
    else some (opposite f, .single (.stepRange' 1 1 s[0]))

/-- Julia `ConeTopology(n1,n2)` (QT:72): face 1 is an apex (self-glued by a half-turn), face 2
open, axis 2 periodic. -/
def cone (s : Vector Nat 2) : QuotientTopology 2 :=
  ofFaces s fun f =>
    match f.1 with
    | 0 => some (f, .single (.cross s[1]))
    | 1 => none
    | _ => some (opposite f, .ofSizes #v[s[0]])

/-- Julia `TubeTopology(n1,n2)` (QT:73): axis 2 periodic. -/
def tube2 (s : Vector Nat 2) : QuotientTopology 2 :=
  ofFaces s fun f => if f.1 < 2 then none else some (opposite f, .ofSizes #v[s[0]])

/-- Julia `TubeTopology(n1,n2,n3)` (QT:74): an axis-1 center (face 1, half-turn, collapsed),
face 2 a mirror, axis 2 open with collapsed ends, axis 3 periodic. -/
def tube3 (s : Vector Nat 3) : QuotientTopology 3 :=
  ofFaces s (fun f =>
    match f.1 with
    | 0 => some (f, crossMaps s 0)
    | 1 => some (f, idMaps s 0)
    | 2 | 3 => none
    | _ => some (opposite f, idMaps s 2))
    (fun f => f.1 = 0 || f.1 = 2 || f.1 = 3)

/-- Julia `BallTopology(n)` (QT:75-79; `PolarTopology`): for `N ≥ 2`, the low face of axis 1 is
the center (self-glued by the half-turn of the last axis, collapsed), faces of axes `2..N-1` are
self-glued with that half-turn, and the last axis is periodic. `N = 1` is the open interval. The
collapse flags follow Julia exactly (faces 3, 4 are collapsed only for `N = 3`). -/
def ball (s : Vector Nat N) : QuotientTopology N :=
  if N = 1 then openTop s else
  ofFaces s (fun f =>
    let a := faceAxis f
    if a.1 + 1 = N then some (opposite f, idMaps s a)
    else if f.1 = 1 then some (f, idMaps s a)
    else some (f, crossMaps s a))
    (fun f => f.1 = 0 || (N = 3 && (f.1 = 2 || f.1 = 3)))

/-- Julia `SphereTopology(n)` (QT:80-84): as `ball` but both faces of axis 1 are poles; only
the 2-sphere carries collapse flags (Julia Q10, replicated). `N = 1` is the circle. -/
def sphere (s : Vector Nat N) : QuotientTopology N :=
  if N = 1 then torus s else
  ofFaces s (fun f =>
    let a := faceAxis f
    if a.1 + 1 = N then some (opposite f, idMaps s a) else some (f, crossMaps s a))
    (fun f => N = 2 && f.1 < 2)

/-- Julia `GeographicTopology(n1,n2)` (QT:85): axis 1 periodic, axis-2 faces are poles glued by
a half-turn of axis 1 (not collapsed). -/
def geographic (s : Vector Nat 2) : QuotientTopology 2 :=
  ofFaces s fun f =>
    if f.1 < 2 then some (opposite f, .ofSizes #v[s[1]]) else some (f, .single (.cross s[0]))

/-! ### Julia's default sizes (QT:140-177) -/

/-- `HopfTopology()` = `HopfTopology(7,60,61)`. -/
def hopfDefault : QuotientTopology 3 := hopf3 #v[7, 60, 61]
/-- `TorusTopology()` = `TorusTopology(61,61)` (also `Open`, `Mirror`, `Clamped`). -/
def torusDefault : QuotientTopology 2 := torus #v[61, 61]
/-- `CylinderTopology(n=61, m=20)` (also `Wing`, `Mobius`). -/
def cylinderDefault (n : Nat := 61) (m : Nat := 20) : QuotientTopology 2 := cylinder #v[n, m]
/-- `KleinTopology(n=61, m=61)`. -/
def kleinDefault (n : Nat := 61) (m : Nat := 61) : QuotientTopology 2 := klein #v[n, m]
/-- `ConeTopology(n=31, m=2n+1)`. -/
def coneDefault (n : Nat := 31) (m : Nat := 2 * n + 1) : QuotientTopology 2 := cone #v[n, m]
/-- `GeographicTopology(n=61, m=n÷2)`. -/
def geographicDefault (n : Nat := 61) (m : Nat := n / 2) : QuotientTopology 2 :=
  geographic #v[n, m]
/-- `TubeTopology()` = `TubeTopology(20,61)`. -/
def tubeDefault : QuotientTopology 2 := tube2 #v[20, 61]
/-- `BallTopology()`: Julia builds `TubeTopology(20,61)` (Q8); fixed to `BallTopology(20,61)`. -/
def ballDefault : QuotientTopology 2 := ball #v[20, 61]
/-- `SphereTopology()`: Julia builds `TubeTopology(31,61)` (Q8); fixed to `SphereTopology(31,61)`. -/
def sphereDefault : QuotientTopology 2 := sphere #v[31, 61]

/-! ## Ghost-index resolution (QT:316-561) -/

/-- Julia `bounds(i, n, Val(K), Val(a))` (QT:418) for the 1-based axis `a`: strict interior
`1 < i < n` along the stepping axis `K` (and everywhere for `K = 0`), `0 < i ≤ n` across it. -/
@[inline] def inBounds (K a : Nat) (i : Int) (n : Nat) : Bool :=
  if K == 0 || K == a then 1 < i && i < (n : Int) else 0 < i && i ≤ (n : Int)

/-- The unique axis out of bounds, if exactly one is (Julia's `if isj && !isi … elseif …`
chains). One-dimensional topologies always use the strict interior (QT:403-416). -/
def soleOut (m : QuotientTopology N) (K : Nat) (idx : Vector Int N) : Option (Fin N) :=
  go 0 none
where
  /-- Scan axes `k..N-1`. -/
  go (k : Nat) (found : Option (Fin N)) : Option (Fin N) :=
    if h : k < N then
      if inBounds (if N = 1 then 0 else K) (k + 1) idx[k] m.size[k] then go (k + 1) found
      else match found with
        | none => go (k + 1) (some ⟨k, h⟩)
        | some _ => none
    else found
  termination_by N - k

/-- Julia `locate` (QT:337-350): the coordinate a ghost index `i` of an axis of size `n` takes
on the target axis (size `s2`) of the face gluing. `low`: the ghost lies beyond the low face
(`i < 2`); `targetLow`: the target face is a low face. Low → low reflects about `1`, low → high
wraps (`1 ↦ s2`, `0 ↦ s2-1`), high → high reflects about `n`, high → low wraps (`n ↦ 1`,
`n+1 ↦ 2`). -/
@[inline] def ghostCoord (low targetLow : Bool) (i n s2 : Int) : Int :=
  if low then (if targetLow then (i - 1).natAbs + 1 else s2 - (i - 1).natAbs)
  else (if targetLow then i + 1 - n else s2 + n - i)

/-- Julia `location`/`locate` (QT:337-361): resolve the ghost index `idx`, out of bounds on
axis `a` only, through the gluing of the face it lies beyond. With `q11 = true` the high face of
axis 5 of a 5-D topology uses `n₄` as its source size, as upstream does (Q11). -/
def resolveAt (m : QuotientTopology N) (a : Fin N) (idx : Vector Int N) (q11 : Bool := false) :
    Vector Int N :=
  let i := idx[a]
  let low := i < 2
  let f : Fin (2 * N) := if low then lowFace a else highFace a
  match m.glue[f] with
  | none => idx
  | some g =>
    let pr := g.target
    let a2 := faceAxis pr
    let s2 : Int := m.size[a2]
    let n : Int := if q11 && N = 5 && a.1 = 4 then m.size[3]! else m.size[a]
    let x : Int := ghostCoord low (pr.1 % 2 = 0) i n s2
    let t := g.maps.get (idx.eraseIdx a.1)
    (t.insertIdx a2.1 x (by have := a2.2; omega)).cast (by have := a.2; omega)

/-- Julia `m[Val(K), i₁,…,i_N]` (QT:420-561): the representative of the (possibly ghost) grid
index `idx` when stepping along axis `K` (`K = 0`: plain indexing). Exactly one axis may be out
of bounds (see `inBounds`); it is then mapped through its face's gluing. Corners, multi-axis
ghosts, open faces and interior points return `idx` unchanged. -/
def ghost (m : QuotientTopology N) (K : Nat) (idx : Vector Int N) (q11 : Bool := false) :
    Vector Int N :=
  match m.soleOut K idx with
  | none => idx
  | some a => m.resolveAt a idx q11

/-- Julia `m[i₁,…,i_N]` = `m[Val(0), i…]` (QT:400). -/
@[inline] def get (m : QuotientTopology N) (idx : Vector Int N) : Vector Int N := m.ghost 0 idx

/-- Julia `length(m)`: the number of grid points. -/
def length (m : QuotientTopology N) : Nat := gridLength m.size

/-- Julia `collect(m)` in column-major order: the representative of every grid point. -/
def toArray (m : QuotientTopology N) : Array (Vector Int N) :=
  (Array.range m.length).map fun k => m.get ((cartesianIndex m.size (k + 1)).map (Int.ofNat ·))

/-- The 1-based linear index of `m[Val(K), idx…]`, or `0` when the result lies outside the grid
(an open face). The allocation-light entry point for stencils. -/
def ghostLinear (m : QuotientTopology N) (K : Nat) (idx : Vector Int N) : Nat :=
  let r := m.ghost K idx
  if (List.finRange N).all fun k => 0 < r[k] && r[k] ≤ (m.size[k] : Int) then
    (linearIndex m.size r).toNat
  else 0

/-- Precomputed ±1 neighbors: for every axis `a` and point `p` (0-based linear), the 1-based
linear index of `m[Val(a+1), p ± e_a]`, or `0` beyond an open face. Julia recomputes the branchy
lookup at every stencil evaluation; with the table every neighbor is one array read. -/
structure NeighborTable (N : Nat) where
  /-- Grid sizes. -/
  size : Vector Nat N
  /-- Number of grid points. -/
  len : Nat
  /-- Entry `2 * (a * len + p) + d`, `d = 0` for the `-1` step and `1` for `+1`. -/
  table : Array Nat
  /-- The table has one entry per axis, point and direction. -/
  size_table : table.size = 2 * N * len

/-- Build the `NeighborTable` of `m`. -/
def neighborTable (m : QuotientTopology N) : NeighborTable N :=
  let len := m.length
  let tbl := (Array.range (N * len)).foldl (fun acc ap =>
      let a := ap / len
      let p := ap % len
      let idx := (cartesianIndex m.size (p + 1)).map (Int.ofNat ·)
      let step (d : Int) : Nat :=
        if h : a < N then m.ghostLinear (a + 1) (idx.set a (idx[a] + d)) else 0
      (acc.push (step (-1))).push (step 1)) (Array.mkEmpty (2 * N * len))
  if h : tbl.size = 2 * N * len then ⟨m.size, len, tbl, h⟩
  else ⟨m.size, len, Array.replicate (2 * N * len) 0, by simp⟩

/-- Neighbor of the 0-based point `p` along axis `a` (`up`: `+1`, else `-1`), 1-based (0 = none). -/
@[inline] def NeighborTable.get (t : NeighborTable N) (a : Fin N) (p : Fin t.len) (up : Bool) : Nat :=
  t.table[2 * (a.1 * t.len + p.1) + (if up then 1 else 0)]'(by
    have := t.size_table
    have : 2 * N * t.len = 2 * (N * t.len) := Nat.mul_assoc 2 N t.len
    have h1 : a.1 * t.len + p.1 < N * t.len := by
      have : a.1 * t.len + t.len ≤ N * t.len := by
        have := Nat.mul_le_mul_right t.len (Nat.succ_le_of_lt a.2)
        simpa [Nat.succ_mul] using this
      omega
    split <;> omega)

/-! ## Products (QT:195-314) -/

/-- Julia `m × n` of two quotient topologies (QT:223-283): targets of `n` shift by `2·dim m`, the
transversal maps are **rebuilt as identities** (flips and half-turns are lost, Q13, replicated)
and the collapse flags are dropped. Julia defines it for dimension pairs with sum ≤ 5; this is
the same construction for all dimensions. -/
def cross {M : Nat} (a : QuotientTopology M) (b : QuotientTopology N) : QuotientTopology (M + N) :=
  let s := a.size ++ b.size
  ofFaces s fun f =>
    if h : f.1 < 2 * M then
      (a.glue[f.1]'h).map fun g => (⟨g.target.1, by omega⟩, idMaps s (faceAxis f))
    else
      (b.glue[f.1 - 2 * M]'(by omega)).map fun g =>
        (⟨g.target.1 + 2 * M, by omega⟩, idMaps s (faceAxis f))

/-- Julia `m × n::Int` (QT:206-213): appends an open axis of size `n`; the transversal maps
gain a `OneTo(n)` axis; collapse flags are dropped. -/
def crossInt (a : QuotientTopology N) (n : Nat) : QuotientTopology (N + 1) :=
  let s := a.size.push n
  ofFaces s fun f =>
    if h : f.1 < 2 * N then
      (a.glue[f.1]'h).map fun g =>
        (⟨g.target.1, by omega⟩, ⟨(g.maps.crossAxis (.oneTo n)).axes.cast (by omega)⟩)
    else none

/-- Julia `n::Int × m` (QT:214-221): prepends an open axis. Upstream keeps the target faces
unshifted (Q12); the fix shifts them by one axis. -/
def intCross (n : Nat) (a : QuotientTopology N) : QuotientTopology (1 + N) :=
  let s := #v[n] ++ a.size
  ofFaces s fun f =>
    if h : 2 ≤ f.1 then
      (a.glue[f.1 - 2]'(by omega)).map fun g =>
        (⟨g.target.1 + 2, by omega⟩, ⟨(ProductTopology.axisCross (.oneTo n) g.maps).axes.cast (by omega)⟩)
    else none

/-- Julia `cross_sphere(m, n)` of two 1-D topologies (QT:285-290): both faces of axis 1 are
poles, self-glued by the half-turn of axis 2 and collapsed; axis 2 keeps `n`'s gluing. -/
def crossSphere (a b : QuotientTopology 1) : QuotientTopology 2 :=
  let s : Vector Nat 2 := #v[a.size[0], b.size[0]]
  ofFaces s (fun f =>
    match f.1 with
    | 0 | 1 => some (f, .single (.cross s[1]))
    | k => (b.glue[k - 2]!).map fun g => (⟨g.target.1 + 2, by omega⟩, .ofSizes #v[s[0]]))
    (fun f => f.1 < 2)

/-- Julia `cross_sector(m, n)` (QT:291-314): face 1 is a collapsed center (half-turn of the last
axis), face 2 a mirror, and `n`'s glued faces keep their targets with identity maps, except that
faces of `n`'s non-last axes take the half-turn of the last axis. Collapse flags follow Julia (the
faces of axis 2 are collapsed only when `dim n = 2`). Upstream drops two slots when `dim n = 4`
(Q32, fixed). -/
def crossSector (a : QuotientTopology 1) (b : QuotientTopology N) : QuotientTopology (1 + N) :=
  let s := #v[a.size[0]] ++ b.size
  ofFaces s (fun f =>
    let ax := faceAxis f
    match f.1 with
    | 0 => some (f, crossMaps s ax)
    | 1 => some (f, idMaps s ax)
    | k => (b.glue[k - 2]!).map fun g =>
        (⟨g.target.1 + 2, by omega⟩, if ax.1 = N then idMaps s ax else crossMaps s ax))
    (fun f => f.1 = 0 || (N = 2 && (f.1 = 2 || f.1 = 3)))

/-! ## Resizing (QT:363-393) -/

/-- Julia `resize(m, i)` (QT:363-378): sets the size of the last axis to `i` and resizes the
last axis of every transversal map that has one (faces not on the last axis). Upstream picks
those faces by comparing slot numbers (Q16) and drops the collapse flags (Q31); both are fixed.
`none` if a map has no `resize` method (`UnitRange`/`Vector` axes). -/
def resize? (m : QuotientTopology N) (i : Nat) : Option (QuotientTopology N) := do
  if N = 0 then return m
  let glue ← (List.finRange (2 * N)).foldlM (fun (acc : Vector (Option (Glue N)) (2 * N)) f =>
    match m.glue[f] with
    | none => some acc
    | some g =>
      if (faceAxis f).1 + 1 = N then some acc
      else (g.maps.resize? i).map fun q => acc.set f.1 (some ⟨g.target, q⟩)) m.glue
  return ⟨m.size.set! (N - 1) i, glue, m.collapse⟩

/-- Julia `resample(m, i)` (QT:380-393): new sizes `i`, and every transversal map resampled to
the sizes of its face's transversal axes. Upstream fails for every non-open topology (Q1, Q15)
and uses the wrong axis for general `O` (Q14); it also drops the collapse flags (Q31). -/
def resample? (m : QuotientTopology N) (s : Vector Nat N) : Option (QuotientTopology N) := do
  let glue ← (List.finRange (2 * N)).foldlM (fun (acc : Vector (Option (Glue N)) (2 * N)) f =>
    match m.glue[f] with
    | none => some acc
    | some g => (g.maps.resample? (s.eraseIdx (faceAxis f).1)).map fun q =>
        acc.set f.1 (some ⟨g.target, q⟩)) m.glue
  return ⟨s, glue, m.collapse⟩

/-- Julia `OpenTopology(m)` (QT:49): the open grid of the same size. -/
def toOpen (m : QuotientTopology N) : QuotientTopology N := openTop m.size

/-- Julia `QuotientTopology(n::ProductTopology)` / `OpenTopology(n::ProductTopology)` (QT:47-48,
Q29 fixed): the open grid of the product's size. -/
def ofProduct (p : ProductTopology N) : QuotientTopology N := openTop p.size

/-! ## Slicing (QT:563-752) -/

/-- The collapse flags of the faces of the given axes. -/
def collapseOf {K : Nat} (m : QuotientTopology N) (ax : Vector (Fin N) K) : Vector Bool (2 * K) :=
  Vector.ofFn fun f : Fin (2 * K) =>
    m.collapse[if f.1 % 2 = 0 then lowFace ax[f.1 / 2] else highFace ax[f.1 / 2]]

/-- Julia `subtopology(m, Val(A))` (QT:587-602): the 1-D topology of axis `A`, ignoring the
transversal maps (a glued face keeps only whether its target is a low or a high face). -/
def axisTopology (m : QuotientTopology N) (A : Fin N) : QuotientTopology 1 :=
  let side (f : Fin (2 * N)) : Option (Glue 1) :=
    (m.glue[f]).map fun g => ⟨⟨g.target.1 % 2, by omega⟩, .empty⟩
  if (m.glue[lowFace A]).isNone && (m.glue[highFace A]).isNone then openTop #v[m.size[A]]
  else ⟨#v[m.size[A]], #v[side (lowFace A), side (highFace A)], m.collapseOf #v[A]⟩

/-- The slice of `m` keeping the axes `ax` (ascending) with the other axes fixed at `vals`
(ascending axis order): Julia `m(i…, :, j…, :, …)` = `subtopology(m, …)` (QT:579-752).

A face identification survives only if it glues a kept axis to a kept axis *and* its
transversal map fixes the fixed coordinates. The result keeps the maps of the other kept axes.
Julia's one-colon case hard-codes two outcomes (Q25, replicated): a surviving high face alone
becomes `p = (2,)`, a surviving low face alone becomes `MirrorTopology(n)` with no collapse
flags. -/
def slice {K : Nat} (m : QuotientTopology N) (ax : Vector (Fin N) K) (vals : Array Int) :
    QuotientTopology K :=
  let R : Vector (Fin (2 * N)) (2 * K) := Vector.ofFn fun f =>
    if f.1 % 2 = 0 then lowFace ax[f.1 / 2] else highFace ax[f.1 / 2]
  let sizes : Vector Nat K := ax.map (m.size[·])
  if hK : K = N then
    -- all colons: `m` itself
    ⟨hK ▸ m.size, hK ▸ m.glue, hK ▸ m.collapse⟩
  else if m.isOpen then openTop sizes
  else
    let axN := ax.toList.map (·.1)
    -- position (1-based within R) of each surviving face identification, with its new maps
    let found : Vector (Option (Nat × ProductTopology (K - 1))) (2 * K) := Vector.ofFn fun f =>
      let j := f.1 / 2
      match m.glue[R[f]] with
      | none => none
      | some g =>
        match R.toList.findIdx? (· == g.target) with
        | none => none
        | some pos =>
          -- positions of the other kept axes in this face's transversal list
          let aj := axN[j]!
          let others : Vector Nat (K - 1) := Vector.ofFn fun i : Fin (K - 1) =>
            let o := axN[if i.1 < j then i.1 else i.1 + 1]!
            if o < aj then o else o - 1
          let fixedPos := (List.range (N - 1)).filter (fun k => !others.toList.contains k)
          let fixedMap := g.maps.selectIdx (Vector.ofFn fun i : Fin fixedPos.length => fixedPos[i])
          let image := fixedMap.get (Vector.ofFn fun i => vals[i.1]!)
          if image.toList == (List.range fixedPos.length).map (vals[·]!) then
            some (pos + 1, g.maps.selectIdx others)
          else none
    if hK1 : K = 1 then
      let p1 := (found[0]'(by omega)).map (·.1)
      let p2 := (found[1]'(by omega)).map (·.1)
      let c := m.collapseOf ax
      let q0 : ProductTopology (K - 1) := ⟨(#v[] : Vector AxisMap 0).cast (by omega)⟩
      match p1, p2 with
      | none, none => openTop sizes
      | none, some _ =>
        ⟨sizes, Vector.ofFn fun f => if f.1 = 1 then some ⟨⟨1, by omega⟩, q0⟩ else none, c⟩
      | some _, none => mirror sizes
      | some t1, some t2 =>
        ⟨sizes, Vector.ofFn fun f =>
          some ⟨⟨((if f.1 = 0 then t1 else t2) - 1) % 2, by omega⟩, q0⟩, c⟩
    else
      ⟨sizes, Vector.ofFn fun f : Fin (2 * K) => (found[f]).map fun (t, q) =>
        ⟨⟨(t - 1) % (2 * K), Nat.mod_lt _ (by have := f.2; omega)⟩, q⟩, m.collapseOf ax⟩

/-- `slice` addressed Julia-style: `colons` are the 1-based kept axes (ascending); `none` if they
are not valid. -/
def sliceAt? (m : QuotientTopology N) (colons : List Nat) (vals : Array Int) :
    Option ((K : Nat) × QuotientTopology K) := do
  let ax ← colons.mapM fun a => if h : 0 < a ∧ a - 1 < N then some (⟨a - 1, h.2⟩ : Fin N) else none
  return ⟨ax.length, m.slice (Vector.ofFn fun i => ax[i]) vals⟩

/-! ## Display -/

/-- Julia's type string of the `q` maps (`LA` parameter). -/
def mapsTypeString (m : QuotientTopology N) : String :=
  let arr (k : Nat) : String :=
    match k with
    | 1 => "Vector{Values{1, Int64}}"
    | 2 => "Matrix{Values{2, Int64}}"
    | k => s!"Array\{Values\{{k}, Int64}, {k}}"
  if N ≤ 1 then arr 0 else
  let qs := m.glue.toList.filterMap id
  match qs with
  | [] => arr (N - 1)
  | g :: rest =>
    if rest.all (fun h => h.maps.typeString == g.maps.typeString) then g.maps.typeString
    else s!"ProductTopology\{{N - 1}}"

/-- Julia `summary(m)`: `4×5 CompactTopology{2, 1, 4, ProductTopology{1, Base.OneTo{Int64}}}`
(`OpenTopology` when nothing is glued, `QuotientTopology{…, O, …}` otherwise). -/
def summary (m : QuotientTopology N) : String :=
  let O := m.numGlued
  let head :=
    if O = 0 then s!"OpenTopology\{{N}, {N - 1}, {2 * N}, "
    else if O = 2 * N then s!"CompactTopology\{{N}, {N - 1}, {2 * N}, "
    else s!"QuotientTopology\{{N}, {N - 1}, {2 * N}, {O}, "
  s!"{dimsString m.size.toList} {head}{m.mapsTypeString}}"

end QuotientTopology

end MeshTopology

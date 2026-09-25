import Cartan.Slice

/-!
# Evaluating grid fields: multilinear interpolation

Julia's `t(x)` for a field over a grid (Cartan.jl `src/grid.jl:98-456`, `linterp`, `bilinterp`,
`trilinterp`, …) interpolates the fibers multilinearly:

* each axis is bracketed by `searchpoints(p, t) = searchsortedfirst(p, t) - 1` (`t == p[1]` is in
  range, `t > p[end]` is not);
* in range, the corners are combined axis by axis, the first axis innermost and the last
  outermost: `bilinterp = linterp_y(linterp_x(f₁₁, f₂₁), linterp_x(f₁₂, f₂₂))`, with
  `linterp(x, x₁, x₂, f₁, f₂) = f₁ + (f₂ - f₁)*(x - x₁)/(x₂ - x₁)` (for Grassmann fibers the final
  division is Grassmann's `* (1/(x₂ - x₁))`);
* out of range on an open face the value is **zero**, not an extrapolation; through a glued face
  the coordinate is moved into range (`reposition`: shifted by the period when the partner is the
  opposite face, reflected when the face is glued to itself) and the evaluation repeats;
* a `NaN` coordinate gives `zero/0` (`NaN` fibers).

Julia reads the partner face positionally (`q.p[2a-1]`, `q.p[2a]`), which is the partner only
when the topology's slot table is the identity; for the tube and cone topologies it reads the
wrong entry or past the end (a `BoundsError`). Here the partner is the face's own gluing. Like
Julia, the transversal maps of a gluing (the Möbius flip, the sphere's half-turn) are not applied.
The fibers are combined on their flat encoding (`LinearFiber`), which is how Julia's `+`, `-` and
scalar `*`, `/` act on them.
-/

namespace Cartan

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase MeshTopology

namespace Interp

/-- Julia `searchsortedfirst(p, t) - 1` for an ascending vector: the number of entries `< t`
(binary search on `[lo, hi)`). -/
def countBelow (p : FloatArray) (t : Float) (lo hi : Nat) : Nat :=
  go lo hi (hi - lo + 1)
where
  /-- Bisection, fuelled by the interval width. -/
  go (lo hi : Nat) : Nat → Nat
    | 0 => lo
    | fuel + 1 =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if p.get! mid < t then go (mid + 1) hi fuel else go lo mid fuel
      else lo

/-- Walk the count `h` down while `p[h-1] ≥ t` (at most `k` steps). -/
def walkDown (p : FloatArray) (t : Float) : Nat → Nat → Nat
  | 0, h => h
  | k + 1, h => if h > 0 && p.get! (h - 1) ≥ t then walkDown p t k (h - 1) else h

/-- Walk the count `h` up while `p[h] < t` (at most `k` steps). -/
def walkUp (p : FloatArray) (t : Float) : Nat → Nat → Nat
  | 0, h => h
  | k + 1, h => if h < p.size && p.get! h < t then walkUp p t k (h + 1) else h

/-- `countBelow p t 0 p.size` for an ascending `p` (a range's points): the count guessed from the
end points (`(t - p₀)/(p_{n-1} - p₀)·(n-1)`, exact up to a step or two on a uniform grid),
verified (`p[h-1] < t ≤ p[h]`, which pins the count of an ascending array), else corrected by at
most four steps each way and verified again; the bisection when that fails (and outside or at
`NaN`). -/
def countBelowAsc (p : FloatArray) (t : Float) : Nat :=
  let n := p.size
  if n < 2 then countBelow p t 0 n else
  let a := p.get! 0
  let z := p.get! (n - 1)
  let m := (n - 1).toUInt64.toFloat
  let g := (t - a) / (z - a) * m
  if g ≥ 0 && g ≤ m then
    let h0 := g.floor.toUInt64.toNat + 1
    if (h0 == 0 || p.get! (h0 - 1) < t) && (h0 == n || p.get! h0 ≥ t) then h0 else
    let h := walkUp p t 4 (walkDown p t 4 h0)
    if (h == 0 || p.get! (h - 1) < t) && (h == n || p.get! h ≥ t) then h else countBelow p t 0 n
  else countBelow p t 0 n

/-- Julia `searchpoints(p, t)` (`grid.jl:102-106`): the bracket start `i` (1-based: `t ∈ (p[i], p[i+1]]`,
or `i = 1` when `t == p[1]`) and whether `t` lies below the range (`i = 0`). -/
def searchpoints (p : FloatArray) (t : Float) : Nat × Bool :=
  let i := countBelow p t 0 p.size
  if i == 0 && t == p.get! 0 then (1, false) else (i, i == 0)

/-- Julia `reposition_odd(pf, x, t)` (`grid.jl:98`): below the range, shift up by the period when
the partner is a high face (Julia's even `pf`), else reflect about the first point. -/
@[inline] def repositionLow (partnerHigh : Bool) (x : FloatArray) (t : Float) : Float :=
  if partnerHigh then x.get! (x.size - 1) - x.get! 0 + t else 2 * x.get! 0 - t

/-- Julia `reposition_even(pf, x, t)` (`grid.jl:99`): above the range, shift down by the period
when the partner is a low face (Julia's odd `pf`), else reflect about the last point. -/
@[inline] def repositionHigh (partnerLow : Bool) (x : FloatArray) (t : Float) : Float :=
  if partnerLow then x.get! 0 - x.get! (x.size - 1) + t else 2 * x.get! (x.size - 1) - t

/-- Julia `linterp(x, x₁, x₂, f₁, f₂)` on one float, `recip` selecting Grassmann's division
`* (1/(x₂ - x₁))` (see `TensorField.linterpComp`). -/
@[inline] def lin (recip : Bool) (x x1 x2 f1 f2 : Float) : Float :=
  if recip then f1 + ((f2 - f1) * (x - x1)) * (f64! 1 / (x2 - x1))
  else f1 + ((f2 - f1) * (x - x1)) / (x2 - x1)

/-- One separable pass of a tensor-product resampling. `src` has the column-major layout
`[inner][nOld][outer]` (`inner` floats per step of the middle axis, which has `nOld` points);
the result has `[inner][nNew][outer]`, entry `(q, j, o)` interpolating along the middle axis at
the new coordinate `xs[j]` between the old points `lo[j]` and `lo[j] + 1` (coordinates `old`).
Interpolating the axes one after the other, the first first, performs exactly the operations of
the corner nesting of `cellComp` (`linterp_y(linterp_x(f₁₁, f₂₁), linterp_x(f₁₂, f₂₂))`), since
the inner interpolations of neighbouring cells are shared rather than recomputed. -/
def resamplePass (recip : Bool) (inner nOld nNew outer : Nat) (lo : Array Nat)
    (old xs src : FloatArray) : FloatArray :=
  goO outer 0 (Flat.zeros (inner * nNew * outer))
where
  /-- The `inner` floats of one output step. -/
  goQ (b1 b2 d : Nat) (x x1 x2 : Float) : (k q : Nat) → FloatArray → FloatArray
    | 0, _, dst => dst
    | k + 1, q, dst =>
      goQ b1 b2 d x x1 x2 k (q + 1)
        (dst.set! (d + q) (lin recip x x1 x2 (src.get! (b1 + q)) (src.get! (b2 + q))))
  /-- The new points `j, …` of the middle axis in the outer block `o`. -/
  goJ (o : Nat) : (k j : Nat) → FloatArray → FloatArray
    | 0, _, dst => dst
    | k + 1, j, dst =>
      let l := lo[j]!
      let b1 := (o * nOld + l) * inner
      goJ o k (j + 1)
        (goQ b1 (b1 + inner) ((o * nNew + j) * inner) (xs.get! j) (old.get! l) (old.get! (l + 1))
          inner 0 dst)
  /-- The outer blocks `o, …`. -/
  goO : (k o : Nat) → FloatArray → FloatArray
    | 0, _, dst => dst
    | k + 1, o, dst => goO k (o + 1) (goJ o nNew 0 dst)

/-- A multilinear resampling done axis by axis (`resamplePass`), the first axis first, for fibers
of `w` floats on the flat data `src` over the old axes `old` (sizes `nOld`) onto the new axes
`new`, whose points `j` of axis `a` lie in the old cells starting at `lo[a][j]`. -/
def resampleFlat (recip : Bool) (w : Nat) (old new : Array FloatArray) (lo : Array (Array Nat))
    (src : FloatArray) : FloatArray :=
  let nOld := old.map (·.size)
  let nNew := new.map (·.size)
  let prod (xs : Array Nat) (i j : Nat) : Nat := (xs.extract i j).foldl (· * ·) 1
  (List.range old.size).foldl (fun acc a =>
    resamplePass recip (w * prod nNew 0 a) nOld[a]! nNew[a]! (prod nOld (a + 1) old.size) lo[a]!
      old[a]! new[a]! acc) src

end Interp

namespace TensorField

variable {N : Nat} {P G F : Type} [FlatFiber F] [LinearFiber F]

/-- Julia `linterp(x, x₁, x₂, f₁, f₂) = f₁ + (f₂ - f₁)*(x - x₁)/(x₂ - x₁)` on one component of the
flat encoding (Grassmann fibers divide as `* (1/(x₂ - x₁))`). -/
@[inline] def linterpComp (x x1 x2 f1 f2 : Float) : Float :=
  if LinearFiber.recipDiv F then f1 + ((f2 - f1) * (x - x1)) * ((1 : Float) / (x2 - x1))
  else f1 + ((f2 - f1) * (x - x1)) / (x2 - x1)

/-- Component `c` of the multilinear combination of the corners of the cell at `idx` (0-based
lower corner) over the axes `0 … a-1`, the last of them outermost (Julia's `linterp`/`bilinterp`/
`trilinterp` nesting). `lin` is the linear index of the corner reached so far; `st` the axis
strides. -/
def cellComp {b : GridBundle N P G} (t : TensorField b F) (x : Vector Float N) (idx st : Vector Nat N)
    (c : Nat) : (a lin : Nat) → Float
  | 0, lin => t.data.get! (lin * FlatFiber.width F + c)
  | a + 1, lin =>
    if h : a < N then
      let ax := b.space.coords[a]
      let i := idx[a]
      let s := st[a]
      let f1 := cellComp t x idx st c a (lin + i * s)
      let f2 := cellComp t x idx st c a (lin + (i + 1) * s)
      linterpComp (F := F) x[a] (ax.get! i) (ax.get! (i + 1)) f1 f2
    else 0

/-- The fiber whose flat encoding is `w` copies of `x` (the zero and `NaN` fibers). -/
@[inline] def fill (x : Float) : F := FlatFiber.ofComps fun _ => x

/-- Julia `t(x)` for a grid field (`linterp`, `bilinterp`, `trilinterp`, `quadlinterp`,
`quintlinterp`; `grid.jl:108-456`), for coordinates `x` (axis 1 first): multilinear interpolation
of the fibers, zero outside an open face, repositioned through glued faces. -/
def eval {b : GridBundle N P G} (t : TensorField b F) (x : Vector Float N) : F :=
  let st : Vector Nat N := Vector.ofFn fun a => MeshTopology.axisStride b.size a.1
  go st (N + 64) x
where
  /-- One evaluation; `fuel` bounds the repositionings (one per period or reflection). -/
  go (st : Vector Nat N) : Nat → Vector Float N → F
    | 0, _ => fill 0
    | fuel + 1, x =>
      if x.any Float.isNaN then fill ((0 : Float) / 0)
      else
        -- per axis: the bracket (Julia `searchpoints`) and whether the coordinate is below (1),
        -- above (2) or inside (0) the axis
        let br : Vector Nat N := Vector.ofFn fun a => (Interp.searchpoints (b.space.coords[a]) x[a]).1
        let status : Vector Nat N := Vector.ofFn fun a =>
          let i := br[a]
          if i == 0 then 1 else if i == (b.space.coords[a]).size then 2 else 0
        if status.all (· == 0) then
          let idx : Vector Nat N := br.map (· - 1)
          FlatFiber.ofComps fun c => cellComp t x idx st c N 0
        else
          -- an out-of-range axis through an open face gives zero; otherwise reposition
          let glued (a : Fin N) : Option (Glue N) :=
            if status[a] == 1 then b.top.glue[QuotientTopology.lowFace a]
            else b.top.glue[QuotientTopology.highFace a]
          if (List.finRange N).any fun a => status[a] != 0 && (glued a).isNone then fill 0
          else
            let x' : Vector Float N := Vector.ofFn fun a =>
              if status[a] == 0 then x[a]
              else match glued a with
                | none => x[a]
                | some g =>
                  let partnerHigh := g.target.1 % 2 == 1
                  if status[a] == 1 then Interp.repositionLow partnerHigh (b.space.coords[a]) x[a]
                  else Interp.repositionHigh (!partnerHigh) (b.space.coords[a]) x[a]
            go st fuel x'

/-- The in-range bracket of `x` in the points `c` of the axis `a` (0-based lower corner), or `none`
outside (or at `NaN`), as `eval` decides it (`searchpoints`); an increasing range is searched from
a guess (`countBelowAsc`, the same count). -/
@[inline] def bracket (a : Axis) (c : FloatArray) (x : Float) : Option Nat :=
  let asc := a.isRange && c.size ≥ 2 && c.get! 0 < c.get! 1
  let k := if asc then Interp.countBelowAsc c x else Interp.countBelow c x 0 c.size
  let i := if k == 0 && x == c.get! 0 then 1 else k
  if i == 0 || i == c.size then none else some (i - 1)

/-- Julia `t(x)` for a 1-D field: inside the grid the linear interpolation of the bracketing
fibers (the operations of `eval`, without its vectors), else `eval` (zero outside an open end,
repositioned through a glued one, `NaN` fibers at `NaN`). -/
@[specialize] def eval1 {b : GridBundle 1 P G} (t : TensorField b F) (x : Float) : F :=
  let c0 := b.space.coords[0]
  match bracket b.space.axes[0] c0 x with
  | some i =>
    let w := FlatFiber.width F
    let x1 := c0.get! i
    let x2 := c0.get! (i + 1)
    FlatFiber.ofComps fun c =>
      linterpComp (F := F) x x1 x2 (t.data.get! (i * w + c)) (t.data.get! ((i + 1) * w + c))
  | none => t.eval #v[x]

/-- Component `c` of the bilinear interpolation of the cell `(i, j)` of a 2-D grid (axes `c0`,
`c1`, `n0 = c0.size` points on the first, fibers of `w` floats in `d`):
`linterp_y(linterp_x(f₁₁, f₂₁), linterp_x(f₁₂, f₂₂))`, the operations of `cellComp`. -/
@[inline] def bilinComp (r : Bool) (c0 c1 d : FloatArray) (w n0 i j c : Nat) (x y : Float) : Float :=
  let o1 := (j * n0 + i) * w + c
  let o2 := o1 + n0 * w
  let x1 := c0.get! i
  let x2 := c0.get! (i + 1)
  let f1 := Interp.lin r x x1 x2 (d.get! o1) (d.get! (o1 + w))
  let f2 := Interp.lin r x x1 x2 (d.get! o2) (d.get! (o2 + w))
  Interp.lin r y (c1.get! j) (c1.get! (j + 1)) f1 f2

/-- Component `c` of the trilinear interpolation of the cell `(i, j, k)` of a 3-D grid (strides
`n0` and `n01 = n0·n1` points): `linterp_z` of two bilinear interpolations, as `cellComp`. -/
@[inline] def trilinComp (r : Bool) (c0 c1 c2 d : FloatArray) (w n0 n01 i j k c : Nat)
    (x y z : Float) : Float :=
  let o := (k * n01 + j * n0 + i) * w + c
  let sy := n0 * w
  let sz := n01 * w
  let x1 := c0.get! i
  let x2 := c0.get! (i + 1)
  let y1 := c1.get! j
  let y2 := c1.get! (j + 1)
  let b1 := Interp.lin r y y1 y2 (Interp.lin r x x1 x2 (d.get! o) (d.get! (o + w)))
    (Interp.lin r x x1 x2 (d.get! (o + sy)) (d.get! (o + sy + w)))
  let b2 := Interp.lin r y y1 y2 (Interp.lin r x x1 x2 (d.get! (o + sz)) (d.get! (o + sz + w)))
    (Interp.lin r x x1 x2 (d.get! (o + sz + sy)) (d.get! (o + sz + sy + w)))
  Interp.lin r z (c2.get! k) (c2.get! (k + 1)) b1 b2

/-- Julia `t(x, y)` for a 2-D field: inside the grid the bilinear interpolation of the cell
(`linterp_y(linterp_x(f₁₁, f₂₁), linterp_x(f₁₂, f₂₂))`, the operations of `eval`), built
component by component without an intermediate array (`FlatFiber.ofComps`), else `eval`. -/
@[specialize] def eval2 {b : GridBundle 2 P G} (t : TensorField b F) (x y : Float) : F :=
  let c0 := b.space.coords[0]
  let c1 := b.space.coords[1]
  match bracket b.space.axes[0] c0 x, bracket b.space.axes[1] c1 y with
  | some i, some j =>
    FlatFiber.ofComps fun c =>
      bilinComp (LinearFiber.recipDiv F) c0 c1 t.data (FlatFiber.width F) c0.size i j c x y
  | _, _ => t.eval #v[x, y]

/-- Julia `t(x, y, z)` for a 3-D field: inside the grid the trilinear interpolation of the cell
(the operations of `eval`), else `eval`. -/
@[specialize] def eval3 {b : GridBundle 3 P G} (t : TensorField b F) (x y z : Float) : F :=
  let c0 := b.space.coords[0]
  let c1 := b.space.coords[1]
  let c2 := b.space.coords[2]
  match bracket b.space.axes[0] c0 x, bracket b.space.axes[1] c1 y, bracket b.space.axes[2] c2 z with
  | some i, some j, some k =>
    FlatFiber.ofComps fun c =>
      trilinComp (LinearFiber.recipDiv F) c0 c1 c2 t.data (FlatFiber.width F) c0.size
        (c0.size * c1.size) i j k c x y z
  | _, _, _ => t.eval #v[x, y, z]

end TensorField

/-! ## Prepared evaluators

`t(x, y)` evaluated at many points (a streamplot's Euler steps, a raster, `eval_a`) repeats the
per-field work of `eval2`: reading the axes out of the base and, for a range axis, the division
behind the bracket guess. `Grid2Eval`/`Grid3Eval` do that once; `eval` is then `eval2`/`eval3`
bit for bit (the same bracket, the same operations), and `withComps` hands the components of the
value to a continuation without building the fiber. -/

/-- An axis prepared for repeated bracketing (Julia `searchpoints`): its points, and for an
increasing range the slope `s = (n − 1)/(p_{n−1} − p₀)` of the guess `(t − p₀)·s`, which is then
verified (so the bracket is `bracket`'s, whatever the rounding of the guess). -/
structure AxisSearch where
  /-- The points. -/
  p : FloatArray
  /-- An increasing range: guess, then verify. -/
  asc : Bool
  /-- `p₀`. -/
  p0 : Float
  /-- `(n − 1)/(p_{n−1} − p₀)`. -/
  s : Float
  /-- `n − 1` as a float. -/
  m : Float

namespace AxisSearch

/-- Prepare the axis `a` with the points `c`. -/
def ofAxis (a : Axis) (c : FloatArray) : AxisSearch :=
  let n := c.size
  let asc := a.isRange && n ≥ 2 && c.get! 0 < c.get! 1
  let m := (n - 1).toUInt64.toFloat
  ⟨c, asc, c.get! 0, m / (c.get! (n - 1) - c.get! 0), m⟩

/-- The number of points `< t` (`Interp.countBelow` over all points), from the guess on a range. -/
@[inline] def count (a : AxisSearch) (t : Float) : Nat :=
  let p := a.p
  let n := p.size
  if a.asc then
    let g := (t - a.p0) * a.s
    if g ≥ 0 && g ≤ a.m then
      let h0 := g.floor.toUInt64.toNat + 1
      if (h0 == 0 || p.get! (h0 - 1) < t) && (h0 == n || p.get! h0 ≥ t) then h0 else
      let h := Interp.walkUp p t 4 (Interp.walkDown p t 4 h0)
      if (h == 0 || p.get! (h - 1) < t) && (h == n || p.get! h ≥ t) then h
      else Interp.countBelow p t 0 n
    else Interp.countBelow p t 0 n
  else Interp.countBelow p t 0 n

/-- The 0-based lower corner of the cell containing `t` (`TensorField.bracket`), or `p.size` when
`t` is outside the axis (or `NaN`). -/
@[inline] def cell (a : AxisSearch) (t : Float) : Nat :=
  let k := a.count t
  let i := if k == 0 && t == a.p.get! 0 then 1 else k
  if i == 0 || i == a.p.size then a.p.size else i - 1

end AxisSearch

section Prepared

variable {P G F : Type} [FlatFiber F] [LinearFiber F]

/-- A 2-D grid field prepared for evaluation at many points. -/
structure Grid2Eval (F : Type) where
  /-- Axis 1. -/
  ax : AxisSearch
  /-- Axis 2. -/
  ay : AxisSearch
  /-- The flat fibers. -/
  d : FloatArray
  /-- Floats per fiber. -/
  w : Nat
  /-- Grassmann division by a real (`* (1/s)`, `LinearFiber.recipDiv`). -/
  r : Bool
  /-- The evaluation outside the grid (`TensorField.eval`: zero or repositioned). -/
  slow : Float → Float → F

/-- Prepare a 2-D grid field for evaluation (Julia `t(x, y)` at many points). -/
def TensorField.grid2Eval {b : GridBundle 2 P G} (t : TensorField b F) : Grid2Eval F :=
  ⟨.ofAxis b.space.axes[0] b.space.coords[0], .ofAxis b.space.axes[1] b.space.coords[1], t.data,
   FlatFiber.width F, LinearFiber.recipDiv F, fun x y => t.eval #v[x, y]⟩

namespace Grid2Eval

/-- Component `c` of the value in the cell `(i, j)` (`TensorField.bilinComp`). -/
@[inline] def comp (g : Grid2Eval F) (i j c : Nat) (x y : Float) : Float :=
  TensorField.bilinComp g.r g.ax.p g.ay.p g.d g.w g.ax.p.size i j c x y

/-- Julia `t(x, y)`: `TensorField.eval2` bit for bit. -/
@[inline] def eval (g : Grid2Eval F) (x y : Float) : F :=
  let i := g.ax.cell x
  let j := g.ay.cell y
  if i < g.ax.p.size && j < g.ay.p.size then FlatFiber.ofComps fun c => g.comp i j c x y
  else g.slow x y

/-- The components of `t(x, y)` handed to `k` (component `c` for `c < width F`; no fiber is
built inside the grid; outside, the components of `eval`'s value). -/
@[inline] def withComps {β : Type} (g : Grid2Eval F) (x y : Float) (k : (Nat → Float) → β) : β :=
  let i := g.ax.cell x
  let j := g.ay.cell y
  if i < g.ax.p.size && j < g.ay.p.size then k fun c => g.comp i j c x y
  else
    let v := FlatFiber.write (Flat.zeros g.w) 0 (g.slow x y)
    k fun c => v.get! c

end Grid2Eval

/-- A 3-D grid field prepared for evaluation at many points. -/
structure Grid3Eval (F : Type) where
  /-- Axis 1. -/
  ax : AxisSearch
  /-- Axis 2. -/
  ay : AxisSearch
  /-- Axis 3. -/
  az : AxisSearch
  /-- The flat fibers. -/
  d : FloatArray
  /-- Floats per fiber. -/
  w : Nat
  /-- Grassmann division by a real. -/
  r : Bool
  /-- The evaluation outside the grid (`TensorField.eval`). -/
  slow : Float → Float → Float → F

/-- Prepare a 3-D grid field for evaluation (Julia `t(x, y, z)` at many points). -/
def TensorField.grid3Eval {b : GridBundle 3 P G} (t : TensorField b F) : Grid3Eval F :=
  ⟨.ofAxis b.space.axes[0] b.space.coords[0], .ofAxis b.space.axes[1] b.space.coords[1],
   .ofAxis b.space.axes[2] b.space.coords[2], t.data, FlatFiber.width F, LinearFiber.recipDiv F,
   fun x y z => t.eval #v[x, y, z]⟩

namespace Grid3Eval

/-- Component `c` of the value in the cell `(i, j, k)` (`TensorField.trilinComp`). -/
@[inline] def comp (g : Grid3Eval F) (i j k c : Nat) (x y z : Float) : Float :=
  let n0 := g.ax.p.size
  TensorField.trilinComp g.r g.ax.p g.ay.p g.az.p g.d g.w n0 (n0 * g.ay.p.size) i j k c x y z

/-- Julia `t(x, y, z)`: `TensorField.eval3` bit for bit. -/
@[inline] def eval (g : Grid3Eval F) (x y z : Float) : F :=
  let i := g.ax.cell x
  let j := g.ay.cell y
  let k := g.az.cell z
  if i < g.ax.p.size && j < g.ay.p.size && k < g.az.p.size then
    FlatFiber.ofComps fun c => g.comp i j k c x y z
  else g.slow x y z

/-- The components of `t(x, y, z)` handed to `k` (see `Grid2Eval.withComps`). -/
@[inline] def withComps {β : Type} (g : Grid3Eval F) (x y z : Float) (k : (Nat → Float) → β) : β :=
  let i := g.ax.cell x
  let j := g.ay.cell y
  let l := g.az.cell z
  if i < g.ax.p.size && j < g.ay.p.size && l < g.az.p.size then k fun c => g.comp i j l c x y z
  else
    let v := FlatFiber.write (Flat.zeros g.w) 0 (g.slow x y z)
    k fun c => v.get! c

end Grid3Eval

end Prepared

namespace TensorField

variable {N : Nat} {P G F : Type} [FlatFiber F] [LinearFiber F]

/-- Julia `t(p)` at an affine point. -/
@[inline] def evalAt {b : GridBundle N P G} (t : TensorField b F) (p : AffinePoint N) : F :=
  t.eval (Vector.ofFn fun a => p.get! a)

/-- The brackets of the new points of every axis in the old one (1-based lower corner as
`Interp.searchpoints`; `0` = outside the old axis). -/
def resampleBrackets [Inhabited G] (b : GridBundle N P G) (n : Vector Nat N) : Vector (Array Nat) N :=
  let s := (b.resample n).space
  Vector.ofFn fun a =>
    let old := b.space.coords[a]
    (s.coords[a]).foldl (fun acc y =>
      let i := (Interp.searchpoints old y).1
      acc.push (if i == 0 || i == old.size then 0 else i)) #[]

/-- `resample` point by point: the cell's corners interpolated, or `eval` (zero or repositioned
through a glued face) outside the old grid. -/
def resamplePointwise [Inhabited G] {b : GridBundle N P G} (t : TensorField b F) (n : Vector Nat N)
    (brk : Vector (Array Nat) N) : TensorField (b.resample n) F :=
  let s := (b.resample n).space
  let st : Vector Nat N := Vector.ofFn fun a => MeshTopology.axisStride b.size a.1
  let ns := s.size
  ofFn _ fun k =>
    let j : Vector Nat N := Vector.ofFn fun a => k / MeshTopology.axisStride ns a.1 % ns[a]
    let x : Vector Float N := Vector.ofFn fun a => (s.coords[a]).get! j[a]
    let i : Vector Nat N := Vector.ofFn fun a => brk[a][j[a]]!
    if i.all (· != 0) then
      let idx := i.map (· - 1)
      FlatFiber.ofComps fun c => cellComp t x idx st c N 0
    else t.eval x

/-- Julia `resample(t, n)` (`Cartan.jl:220-224`): the field interpolated onto the resampled grid
(`GridBundle.resample`). Julia's 1-D method is ambiguous and throws (B4); this is the intended
evaluation at the new points. When every new point lies inside the old grid (the usual case: the
same span, more or fewer points) the axes are interpolated one after the other
(`Interp.resampleFlat`, the same operations as the corner nesting); otherwise point by point. -/
def resample [Inhabited G] {b : GridBundle N P G} (t : TensorField b F) (n : Vector Nat N) :
    TensorField (b.resample n) F :=
  let brk := resampleBrackets b n
  if brk.toArray.all (·.all (· != 0)) then
    let data := Interp.resampleFlat (LinearFiber.recipDiv F) (FlatFiber.width F)
      b.space.coords.toArray (b.resample n).space.coords.toArray (brk.toArray.map (·.map (· - 1)))
      t.data
    if h : data.size = FlatFiber.width F * card (b.resample n) then ⟨data, h, none⟩
    else resamplePointwise t n brk
  else resamplePointwise t n brk

/-- Julia `leaf(m::RectangleMap, t::AbstractFloat, j = 2)` (`grid.jl:149-157`; `m(t)`): the leaf at
the coordinate `x` of axis `j` (0-based, default the last), interpolated linearly between the two
bracketing leaves (`linterp` on the fiber arrays), as a field over the other axis (Julia
`TensorField(x, …)`: an open interval with real points). Coordinates outside the axis give the
bracket at its end, where Julia throws. -/
def leafInterp {b : GridBundle 2 P G} (t : TensorField b F) (x : Float) (j : Fin 2 := 1) :
    TensorField (GridBundle.ofAxis (b.space.axis (otherAxis2 j))) F :=
  let p := b.space.coords[j]
  let (i, _) := Interp.searchpoints p x
  let i := if i == 0 then 1 else if i ≥ p.size then p.size - 1 else i
  let w := FlatFiber.width F
  let n0 := b.size[0]
  -- the linear index of point `k` of the leaf at the 0-based index `l` of axis `j`
  let lin (l k : Nat) : Nat := if j.1 = 1 then k + n0 * l else l + n0 * k
  ofFn _ fun k =>
    FlatFiber.ofComps fun c =>
      linterpComp (F := F) x (p.get! (i - 1)) (p.get! i)
        (t.data.get! (lin (i - 1) k * w + c)) (t.data.get! (lin i k * w + c))

/-- Julia `orbit(f, x, n)` (`Cartan.jl:516-525`): the iterates `x, f(x), f(f(x)), …` of a field map,
one per entry of `n`, stacked along a new last axis `n` of the base (Julia's field over
`base(x) ⊕ n`; the lazily extensible `SequenceArray` storage is not modelled). -/
def orbit {b : GridBundle N P G} (f : TensorField b F → TensorField b F) (x : TensorField b F)
    (n : Axis) : TensorField (b.pushAxis n) F :=
  let its := go n.length x #[]
  let c := card b
  ofFn _ fun k => (its[k / c]?.getD x).get (k % c)
where
  /-- The first `k` iterates starting from `y`. -/
  go : Nat → TensorField b F → Array (TensorField b F) → Array (TensorField b F)
    | 0, _, acc => acc
    | k + 1, y, acc => go k (f y) (acc.push y)

end TensorField

end Cartan

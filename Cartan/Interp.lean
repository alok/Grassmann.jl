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
@[inline] def fill (x : Float) : F := FlatFiber.read (buildFlat (F := Float) (FlatFiber.width F) fun _ => x) 0

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
          FlatFiber.read (buildFlat (F := Float) (FlatFiber.width F) fun c => cellComp t x idx st c N 0) 0
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

/-- Julia `t(x)` for a 1-D field. -/
@[inline] def eval1 {b : GridBundle 1 P G} (t : TensorField b F) (x : Float) : F := t.eval #v[x]
/-- Julia `t(x, y)` for a 2-D field. -/
@[inline] def eval2 {b : GridBundle 2 P G} (t : TensorField b F) (x y : Float) : F := t.eval #v[x, y]
/-- Julia `t(x, y, z)` for a 3-D field. -/
@[inline] def eval3 {b : GridBundle 3 P G} (t : TensorField b F) (x y z : Float) : F := t.eval #v[x, y, z]

/-- Julia `t(p)` at an affine point. -/
@[inline] def evalAt {b : GridBundle N P G} (t : TensorField b F) (p : AffinePoint N) : F :=
  t.eval (Vector.ofFn fun a => p.get! a)

/-- Julia `resample(t, n)` (`Cartan.jl:220-224`): the field interpolated onto the resampled grid
(`GridBundle.resample`). Julia's 1-D method is ambiguous and throws (B4); this is the intended
evaluation at the new points. -/
def resample [Inhabited G] {b : GridBundle N P G} (t : TensorField b F) (n : Vector Nat N) :
    TensorField (b.resample n) F :=
  let s := (b.resample n).space
  let st : Vector Nat N := Vector.ofFn fun a => MeshTopology.axisStride b.size a.1
  -- the new points form a product: bracket every new coordinate once per axis (`0` = outside)
  let brk : Vector (Array Nat) N := Vector.ofFn fun a =>
    let old := b.space.coords[a]
    (s.coords[a]).foldl (fun acc y =>
      let i := (Interp.searchpoints old y).1
      acc.push (if i == 0 || i == old.size then 0 else i)) #[]
  let ns := s.size
  ofFn _ fun k =>
    let j : Vector Nat N := Vector.ofFn fun a => k / MeshTopology.axisStride ns a.1 % ns[a]
    let x : Vector Float N := Vector.ofFn fun a => (s.coords[a]).get! j[a]
    let i : Vector Nat N := Vector.ofFn fun a => brk[a][j[a]]!
    if i.all (· != 0) then
      let idx := i.map (· - 1)
      FlatFiber.read (buildFlat (F := Float) (FlatFiber.width F) fun c => cellComp t x idx st c N 0) 0
    else t.eval x

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
    FlatFiber.read (buildFlat (F := Float) w fun c =>
      linterpComp (F := F) x (p.get! (i - 1)) (p.get! i)
        (t.data.get! (lin (i - 1) k * w + c)) (t.data.get! (lin i k * w + c))) 0

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

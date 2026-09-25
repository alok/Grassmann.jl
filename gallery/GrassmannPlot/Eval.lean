import GrassmannPlot.Convert

/-!
# Fast field evaluation for plotting

Makie calls the interpolated field `p ↦ Point(m(Chain(p...)))` at every Euler step of a
streamplot, and the tangent-space streamplot pushes every line point through the embedding
`M(p)`. `Cartan.TensorField.eval` is the general multilinear interpolation (any dimension, any
gluing), which builds index vectors and a fiber value per call. For points inside the grid of a
2-D or 3-D field these functions compute the first three components of the same interpolation
directly from the flat fibers: Cartan's nesting (`linterp` over the first axis innermost,
`src/grid.jl:108-456`), the same operations in the same order, so the results are bit-identical
(`Cartan.TensorField.cellComp`). Points outside the grid, or with a `NaN` coordinate, fall back to
`eval` (zero through an open face, repositioned through a glued one).
-/

namespace GrassmannPlot

open LeanPlot Cartan

/-- `1.0`, a module-level constant (docs/PERF.md). -/
def fOne : Float := 1

/-- Julia `linterp(x, x₁, x₂, f₁, f₂)` on one component (`Cartan.TensorField.linterpComp`):
Grassmann fibers divide as `* (1/(x₂ - x₁))`. -/
@[inline] def linterp (recip : Bool) (x x1 x2 f1 f2 : Float) : Float :=
  if recip then f1 + ((f2 - f1) * (x - x1)) * (fOne / (x2 - x1)) else f1 + ((f2 - f1) * (x - x1)) / (x2 - x1)

/-- The number of entries `< t` of the ascending `p` in `[lo, hi)` (Julia `searchsortedfirst - 1`),
by bisection; tail-recursive, fuelled by the interval width. -/
def countBelow (p : FloatArray) (t : Float) (lo hi : Nat) : Nat → Nat
  | 0 => lo
  | fuel + 1 =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if p.get! mid < t then countBelow p t (mid + 1) hi fuel else countBelow p t lo mid fuel
    else lo

/-- The 0-based lower corner of the cell of an ascending axis containing `t` (Julia
`searchpoints`, `grid.jl:102-106`: `t == p₀` belongs to the first cell, `t > p_last` and `NaN` are
outside), or `p.size` when `t` is outside `[p₀, p_last]`. No allocation. -/
@[inline] def cellIndex (p : FloatArray) (t : Float) : Nat :=
  let n := p.size
  let i := countBelow p t 0 n (n + 1)
  if i == 0 then (if t == p.get! 0 then 0 else n)
  else if i < n then i - 1 else n

/-- The bilinear combination of one component (`linterp` over `y` of two `linterp`s over `x`). -/
@[inline] def bilin (r : Bool) (x x1 x2 y y1 y2 f11 f21 f12 f22 : Float) : Float :=
  linterp r y y1 y2 (linterp r x x1 x2 f11 f21) (linterp r x x1 x2 f12 f22)

/-- The trilinear combination of one component. -/
@[inline] def trilin (r : Bool) (x x1 x2 y y1 y2 z z1 z2 f111 f211 f121 f221 f112 f212 f122 f222 : Float) : Float :=
  linterp r z z1 z2 (bilin r x x1 x2 y y1 y2 f111 f211 f121 f221) (bilin r x x1 x2 y y1 y2 f112 f212 f122 f222)

/-- A 2-D grid field prepared for repeated evaluation: its axes, flat fibers, fiber width, the
fiber's division rule, and the general evaluation for points outside the grid. -/
structure Grid2Eval where
  /-- Axis 1. -/
  xs : FloatArray
  /-- Axis 2. -/
  ys : FloatArray
  /-- The flat fibers. -/
  d : FloatArray
  /-- Floats per fiber. -/
  w : Nat
  /-- Grassmann division by a real (`* (1/s)`). -/
  r : Bool
  /-- The general evaluation (`TensorField.eval2`), first three components. -/
  slow : Float → Float → Vec3

/-- The component `c` at the cell `(i, j)`. -/
@[inline] def Grid2Eval.comp (g : Grid2Eval) (i j c : Nat) (x y : Float) : Float :=
  let nx := g.xs.size
  let o11 := (i + nx * j) * g.w + c
  let o12 := o11 + nx * g.w
  bilin g.r x (g.xs.get! i) (g.xs.get! (i + 1)) y (g.ys.get! j) (g.ys.get! (j + 1))
    (g.d.get! o11) (g.d.get! (o11 + g.w)) (g.d.get! o12) (g.d.get! (o12 + g.w))

/-- Julia `t(x, y)`, first three components (bit-identical with `TensorField.eval2`). -/
@[inline] def Grid2Eval.eval (g : Grid2Eval) (x y : Float) : Vec3 :=
  let i := cellIndex g.xs x
  let j := cellIndex g.ys y
  if i < g.xs.size && j < g.ys.size then
    ⟨g.comp i j 0 x y, if g.w > 1 then g.comp i j 1 x y else 0, if g.w > 2 then g.comp i j 2 x y else 0⟩
  else g.slow x y

/-- A 3-D grid field prepared for repeated evaluation (see `Grid2Eval`). -/
structure Grid3Eval where
  /-- Axis 1. -/
  xs : FloatArray
  /-- Axis 2. -/
  ys : FloatArray
  /-- Axis 3. -/
  zs : FloatArray
  /-- The flat fibers. -/
  d : FloatArray
  /-- Floats per fiber. -/
  w : Nat
  /-- Grassmann division by a real. -/
  r : Bool
  /-- The general evaluation (`TensorField.eval3`). -/
  slow : Float → Float → Float → Vec3

/-- The component `c` at the cell `(i, j, k)`. -/
@[inline] def Grid3Eval.comp (g : Grid3Eval) (i j k c : Nat) (x y z : Float) : Float :=
  let nx := g.xs.size
  let sy := nx * g.w
  let sz := nx * g.ys.size * g.w
  let o := (i + nx * (j + g.ys.size * k)) * g.w + c
  let w := g.w
  trilin g.r x (g.xs.get! i) (g.xs.get! (i + 1)) y (g.ys.get! j) (g.ys.get! (j + 1)) z (g.zs.get! k) (g.zs.get! (k + 1))
    (g.d.get! o) (g.d.get! (o + w)) (g.d.get! (o + sy)) (g.d.get! (o + sy + w))
    (g.d.get! (o + sz)) (g.d.get! (o + sz + w)) (g.d.get! (o + sz + sy)) (g.d.get! (o + sz + sy + w))

/-- Julia `t(x, y, z)`, first three components (bit-identical with `TensorField.eval3`). -/
@[inline] def Grid3Eval.eval (g : Grid3Eval) (x y z : Float) : Vec3 :=
  let i := cellIndex g.xs x
  let j := cellIndex g.ys y
  let k := cellIndex g.zs z
  if i < g.xs.size && j < g.ys.size && k < g.zs.size then
    ⟨g.comp i j k 0 x y z, if g.w > 1 then g.comp i j k 1 x y z else 0, if g.w > 2 then g.comp i j k 2 x y z else 0⟩
  else g.slow x y z

section

variable {P G F : Type} [FlatFiber F] [LinearFiber F]

/-- The first three components of a fiber value. -/
@[inline] def vecOf (x : F) : Vec3 :=
  let buf := FlatFiber.push (FloatArray.emptyWithCapacity (FlatFiber.width F)) x
  ⟨buf.get! 0, buf.get! 1, buf.get! 2⟩

/-- Prepare a 2-D grid field for evaluation. -/
def grid2Eval {b : GridBundle 2 P G} (t : TensorField b F) : Grid2Eval :=
  ⟨b.space.coords[0], b.space.coords[1], t.data, FlatFiber.width F, LinearFiber.recipDiv F,
   fun x y => vecOf (t.eval2 x y)⟩

/-- Prepare a 3-D grid field for evaluation. -/
def grid3Eval {b : GridBundle 3 P G} (t : TensorField b F) : Grid3Eval :=
  ⟨b.space.coords[0], b.space.coords[1], b.space.coords[2], t.data, FlatFiber.width F, LinearFiber.recipDiv F,
   fun x y z => vecOf (t.eval3 x y z)⟩

/-- Julia `t(x, y)` of a 2-D grid field, first three components (one-off use; build a `Grid2Eval`
for repeated evaluation). -/
@[inline] def evalVec2 {b : GridBundle 2 P G} (t : TensorField b F) (x y : Float) : Vec3 := (grid2Eval t).eval x y

/-- Julia `t(x, y, z)` of a 3-D grid field, first three components. -/
@[inline] def evalVec3 {b : GridBundle 3 P G} (t : TensorField b F) (x y z : Float) : Vec3 := (grid3Eval t).eval x y z

end

end GrassmannPlot

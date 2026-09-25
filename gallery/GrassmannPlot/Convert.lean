import GrassmannPlot.Canvas

/-!
# From fields to plot data

Makie receives Cartan data through three conversions (`ext/MakieExt.jl`):

* `Makie.Point.(vec(fiber(t)))`: a fiber value becomes a point of its coordinates (a `Chain`'s
  coefficients, an affine point's coordinates, a complex number's `(re, im)`: `vectorize`);
* `Real.(points(t))`, `Real.(fiber(t))`: the graph `(x, y)` of a real function of a real
  variable (`RealFunction`);
* the `speed` colouring of curves (`lines(t::AbstractCurve, f = speed)`, `MakieExt.jl:171-176`).

Fibers are flat (`Cartan.FlatFiber`: `width F` floats per point, which *are* the coordinates in
Julia's order), so every conversion is a strided copy of the field's `FloatArray`; nothing is
decoded per point. `speed` is Cartan's `speed(f::IntervalMap)` (`src/diffgeo.jl:544`): the norm of
the five-point central difference `centraldiff_slow` (`src/grid.jl:788-799`) of the fibers,
divided by the same difference of the points.
-/

namespace GrassmannPlot

open LeanPlot Cartan

/-- `x.1`, `x.2`, `x.3` of the fibers `data` (width `w`, `n` points) as points; coordinates past
`w` are `0` (Julia `Makie.Point.(vec(fiber(t)))`; a 4-D point has no Makie plot, only its first
three coordinates are kept). Tail-recursive over the flat data. -/
def pointsOf (data : FloatArray) (w n : Nat) : Pts3 :=
  go 0 0 (FloatArray.emptyWithCapacity n) (FloatArray.emptyWithCapacity n) (FloatArray.emptyWithCapacity n)
where
  /-- The strided copy: point `i` starts at `off = i*w`. -/
  go (i off : Nat) (xs ys zs : FloatArray) : Pts3 :=
    if i < n then
      let x := if w > 0 then data.get! off else 0
      let y := if w > 1 then data.get! (off + 1) else 0
      let z := if w > 2 then data.get! (off + 2) else 0
      go (i + 1) (off + w) (xs.push x) (ys.push y) (zs.push z)
    else Pts3.ofArrays xs ys zs
  termination_by n - i

/-- The graph points `(xs[i], ys[i])` (z = 0) of a real function (Julia
`Makie.lines(Real.(points(t)), Real.(fiber(t)))`). -/
def graphOf (xs ys : FloatArray) : Pts3 :=
  let n := min xs.size ys.size
  Pts3.ofArrays ⟨xs.data.extract 0 n⟩ ⟨ys.data.extract 0 n⟩ (FloatArray.mk (Array.replicate n 0))

/-- The plot dimension of fibers of width `w` (1: a real function, plotted as a graph in 2-D). -/
@[inline] def dimOfWidth (w : Nat) : Nat := if w ≤ 2 then 2 else 3

/-! ## Fields -/

namespace Field

variable {M : Type} [FrameBundle M] {m : M} {F : Type} [FlatFiber F]

/-- The fibers as points (Julia `Makie.Point.(vec(fiber(t)))`). -/
@[inline] def fiberPoints (t : TensorField m F) : Pts3 := pointsOf t.data (FlatFiber.width F) (card m)

/-- The fibers of a real field, flat (Julia `Real.(vec(fiber(t)))`). -/
@[inline] def values (t : TensorField m Float) : FloatArray := t.data

/-- The points of the base as plot points (Julia `Makie.Point.(vec(points(t)))`). -/
def basePoints {P G : Type} [Coordinates M P G] [FlatFiber P] (_ : TensorField m F) : Pts3 :=
  pointsOf (FrameBundle.pointsFlat (P := P) (G := G) m) (FlatFiber.width P) (card m)

end Field

/-! ## `speed`: the colouring of curves -/

/-- `18.0` and the other stencil weights, as module-level constants (docs/PERF.md: no
`Float.ofScientific` in the loop). -/
def w18 : Float := 18
/-- Stencil weight `9`. -/
def w9 : Float := 9
/-- Stencil weight `2`. -/
def w2 : Float := 2
/-- Stencil weight `11`. -/
def w11 : Float := 11
/-- Stencil weight `6`. -/
def w6 : Float := 6
/-- Stencil weight `3`. -/
def w3 : Float := 3
/-- Stencil weight `8`. -/
def w8 : Float := 8
/-- `1.0`. -/
def fOneC : Float := 1

/-- Component `c` of the flat vector `k` (width `w`). -/
@[inline] def ga (a : FloatArray) (w c k : Nat) : Float := a.get! (k * w + c)

/-- Cartan `centraldiff_slow_calc(f::GridBundle{…,<:OpenTopology}, l, Val(1), i)`
(`src/grid.jl:788-799`) for component `c` of the flat vectors `a` (width `w`, `l ≥ 4` points)
at the 0-based index `i`: the one-sided five-point stencils at the ends and
`f[i-2] + 8(f[i+1] - f[i-1]) - f[i+2]` inside, evaluated in Julia's order. -/
@[inline] def stencil (a : FloatArray) (w c i l : Nat) : Float :=
  if 2 ≤ i && i + 2 < l then
    ga a w c (i - 2) + w8 * (ga a w c (i + 1) - ga a w c (i - 1)) - ga a w c (i + 2)
  else if i == 0 then w18 * ga a w c 1 - w9 * ga a w c 2 + w2 * ga a w c 3 - w11 * ga a w c 0
  else if i + 1 == l then w11 * ga a w c i - w18 * ga a w c (i - 1) + w9 * ga a w c (i - 2) - w2 * ga a w c (i - 3)
  else if i == 1 then w6 * ga a w c 2 - ga a w c 3 - w3 * ga a w c 1 - w2 * ga a w c 0
  else w3 * ga a w c i - w6 * ga a w c (i - 1) + ga a w c (i - 2) + w2 * ga a w c (i + 1)

/-- The derivative components `stencil(f)/stencil(x)` at point `i` (Julia
`centraldifffiber(f, centraldiffpoints(f))`, `src/grid.jl:707-713`): a Grassmann fiber divides by
the real `d` as `x * (1/d)` (`LinearFiber.recipDiv`), numbers as `x / d`. -/
@[inline] def derivAt (x a : FloatArray) (w i l : Nat) (recip : Bool) (c : Nat) : Float :=
  let d := stencil x 1 0 i l
  let s := stencil a w c i l
  if recip then s * (fOneC / d) else s / d

/-- `√(Σ_c (stencil(f)_c / stencil(x))²)` at point `i`: the norm of the central-difference tangent
of a fiber whose norm is the Euclidean norm of its flat encoding (`FiberNorm.flat`: Grassmann
elements), summed left to right without building the fiber. -/
def flatSpeedAt (x a : FloatArray) (w i l : Nat) (recip : Bool) : Float :=
  if 2 ≤ i && i + 2 < l then
    -- interior: `f[i-2] + 8(f[i+1] - f[i-1]) - f[i+2]` at fixed offsets
    let d := x.get! (i - 2) + w8 * (x.get! (i + 1) - x.get! (i - 1)) - x.get! (i + 2)
    let rd := fOneC / d
    let rec inner (o k : Nat) (acc : Float) : Float :=
      match k with
      | 0 => acc
      | k + 1 =>
        let s := a.get! (o - 2 * w) + w8 * (a.get! (o + w) - a.get! (o - w)) - a.get! (o + 2 * w)
        let v := if recip then s * rd else s / d
        inner (o + 1) k (acc + v * v)
    Float.sqrt (inner (i * w) w 0)
  else
    let d := stencil x 1 0 i l
    let rd := fOneC / d
    let rec go (c : Nat) (acc : Float) : Float :=
      if c < w then
        let s := stencil a w c i l
        let v := if recip then s * rd else s / d
        go (c + 1) (acc + v * v)
      else acc
    termination_by w - c
    Float.sqrt (go 0 0)

/-- Julia `speed(f::IntervalMap)` (`src/diffgeo.jl:544-546`) of a curve over an open 1-D grid:
`abs` (the fiber norm, `FiberNorm`) of the central-difference tangent. `none` below 4 points,
where Julia's stencil reads out of bounds (a `BoundsError`). Grassmann fibers take the
allocation-free `flatSpeedAt`. -/
def speed {G F : Type} [FlatFiber F] [LinearFiber F] [FiberNorm F] {b : GridBundle 1 Float G}
    (t : TensorField b F) : Option (TensorField b Float) :=
  let l := card b
  if l < 4 then none else
  let x := b.space.coords[0]
  let w := FlatFiber.width F
  let recip := LinearFiber.recipDiv F
  if FiberNorm.flat F then
    some <| TensorField.ofFn b fun i => flatSpeedAt x t.data w i l recip
  else
    some <| TensorField.ofFn b fun i =>
      let buf := buildFlat (F := Float) w (derivAt x t.data w i l recip)
      fnorm (FlatFiber.read buf 0 : F)

/-! ## Grid surfaces -/

/-- The quads of an `nx × ny` column-major grid of points split into triangles `(a, b, c)`,
`(a, c, d)`: GeometryBasics `decompose(GLTriangleFace, Tesselation(Rect(0,0,1,1), (nx, ny)))`,
the faces of Cartan's `_mesh(m::GridBundle{2})` (`ext/GeometryBasicsExt.jl:49-57`). -/
def gridTriMesh (nx ny : Nat) (pos : Pts3) : TriMesh :=
  (Recipes.Algo.Surface.quadsToTriMesh pos (Recipes.Algo.Surface.gridQuads nx ny)).getD default

/-- The wireframe of an `nx × ny` grid of points: each quad's four edges as segment pairs
(Makie `wireframe(GeometryBasics.Mesh(M))` draws the `LineFace` decomposition of every quad). -/
def gridWireframe (nx ny : Nat) (pos : Pts3) : Pts3 :=
  go 0 FloatArray.empty FloatArray.empty FloatArray.empty
where
  /-- Quad `k` (column-major over the cells). -/
  go (k : Nat) (xs ys zs : FloatArray) : Pts3 :=
    let nq := (nx - 1) * (ny - 1)
    if k < nq then
      let i := k % (nx - 1)
      let j := k / (nx - 1)
      let a := i + nx * j
      let b := a + 1
      let c := a + 1 + nx
      let d := a + nx
      let push2 (u v : Nat) (xs ys zs : FloatArray) : FloatArray × FloatArray × FloatArray :=
        ((xs.push (pos.xs.get! u)).push (pos.xs.get! v), (ys.push (pos.ys.get! u)).push (pos.ys.get! v),
         (zs.push (pos.zs.get! u)).push (pos.zs.get! v))
      let (xs, ys, zs) := push2 a b xs ys zs
      let (xs, ys, zs) := push2 b c xs ys zs
      let (xs, ys, zs) := push2 c d xs ys zs
      let (xs, ys, zs) := push2 d a xs ys zs
      go (k + 1) xs ys zs
    else Pts3.ofArrays xs ys zs
  termination_by (nx - 1) * (ny - 1) - k

/-- The axis vector of a grid (`points(t).v[a+1]`). -/
@[inline] def axisCoords {N : Nat} {P G : Type} (b : GridBundle N P G) (a : Fin N) : FloatArray :=
  b.space.coords[a]

end GrassmannPlot

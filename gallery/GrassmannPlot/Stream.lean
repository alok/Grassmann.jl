import GrassmannPlot.Arrows

/-!
# `streamplot` of vector fields

Cartan's methods (`ext/MakieExt.jl:522-558`):

* `streamplot(m::VectorField over RealSpace)`: Makie's `streamplot` of the interpolated field
  `p ↦ Point(m(Chain(p...)))` (multilinear interpolation of the grid, `Cartan.TensorField.eval`)
  over the box spanned by the axes (`points(m).v...` when every axis is a range, `to_interval`
  of each axis otherwise: the same box). A 3-D field gets Cartan's default `gridsize = (11,11,11)`
  (`streamargs`, `Cartan.jl:935-945`); a 2-D field Makie's `(32, 32)`. Colours: Makie's default,
  `norm` of the field value;
* `streamplot(M::VectorField, m::VectorField{…,2})`: streamlines of a 2-D parameter field
  pushed through the embedding `M` (`makietransform`, `transform_func = p ↦ Point(M(p))`). For a
  surface embedded in 3-D, the 3-D streamplot of `p ↦ (m(p)₁, m(p)₂, 0)` over the parameter box ×
  `[-1e-15, 1e-15]` with `gridsize = (32, 32, 1)` and cone size
  `0.2·√(area(M)/∏w)·min(w)/min(gs₁, gs₂)`; only the positions are transformed, the cones keep
  their parameter-space directions (as in Julia). For a plane `M` the 2-D streamplot, drawn through
  `M` with the axis limits set to the extrema of `M`.

The streamline tracing is LeanPlot's exact port of Makie's `streamplot_impl`
(`Recipes.Algo.Stream`). `area(M)` is Cartan's `surfacearea` (a `Cartan.Diffgeo` integral not in
the core port); it only sizes the arrowheads, and is taken here as the area of the triangulated
surface.
-/

namespace GrassmannPlot

open LeanPlot Cartan MeshTopology
open LeanPlot.Recipes.Algo

/-! ## Drawing a streamplot result -/

/-- Makie's 3-D streamplot arrowheads (`basic_recipes/streamplot.jl:106-111, 257-282`): a
`meshscatter` of `Cone(Point3f(0), Point3f(0, 0, 1), 0.5)` tessellated with `quality = 16`,
scaled by `size` and rotated from `+z` onto each arrow direction; one colour value per vertex. -/
def streamCones (pos dir : Pts3) (vals : FloatArray) (size : Float) (k : Nat := 16) : TriMesh × FloatArray :=
  Id.run do
    let mut xs : FloatArray := .empty
    let mut ys : FloatArray := .empty
    let mut zs : FloatArray := .empty
    let mut cv : FloatArray := .empty
    let mut tri : Array UInt32 := #[]
    let kf := k.toUInt64.toFloat
    for i in [0:pos.size] do
      let p := pos.get! i
      let d := (dir.get! i).normalize
      let a : Vec3 := if d.x.abs < 0.9 then ⟨1, 0, 0⟩ else ⟨0, 1, 0⟩
      let u := (Vec3.cross d a).normalize
      let v := Vec3.cross d u
      let base := xs.size.toUInt32
      let apex := p + Vec3.smul size d
      xs := (xs.push apex.x).push p.x; ys := (ys.push apex.y).push p.y; zs := (zs.push apex.z).push p.z
      for j in [0:k] do
        let θ := 2 * Num.pi * j.toUInt64.toFloat / kf
        let q := p + Vec3.smul (size * 0.5 * Float.cos θ) u + Vec3.smul (size * 0.5 * Float.sin θ) v
        xs := xs.push q.x; ys := ys.push q.y; zs := zs.push q.z
      for _ in [0:k + 2] do cv := cv.push (vals.get! i)
      for j in [0:k] do
        let r0 := base + 2 + j.toUInt32
        let r1 := base + 2 + ((j + 1) % k).toUInt32
        tri := ((tri.push r0).push r1).push base
        tri := ((tri.push r1).push r0).push (base + 1)
    return ((TriMesh.mk? (Pts3.ofArrays xs ys zs) tri).getD default, cv)

/-- Draw a streamplot result: coloured streamlines and arrowheads (`:utriangle` markers in 2-D,
cones of size `arrowSize` in 3-D), lines and arrowheads each with their own automatic colour
range unless `colorrange` is set (Makie's two child plots). -/
def drawStream (c : Canvas) (r : Stream.Result) (arrowSize : Float) (a : Attrs) : Canvas :=
  let m := a.mapping
  let lineCol : ColorSpec := a.color.getD (.values r.lineColors m)
  let arrowCol : ColorSpec := a.color.getD (.values r.arrowColors m)
  if r.dim == 3 || c.is3 then
    let (cm, cv) := streamCones r.arrowPos r.arrowDir r.arrowColors arrowSize
    let arrowCol := match a.color with | some col => col | none => .values cv m
    let c := c.drawLines r.linePoints (some lineCol) a
    c.drawMesh cm (some arrowCol) true a
  else
    c.map2 fun ax =>
      let ax := ax.add (.lines (.xy r.linePoints2) { color := lineCol, width := a.lw }) a.label
      ax.add (.scatter (.xy r.arrowPos2) { shape := .utriangle, size := 15, color := arrowCol
                                           alongDirections := some (.xy r.arrowDir2, -Num.pi / 2) })

/-! ## Fields as vector functions -/

section Fields

variable {P G F : Type} [FlatFiber F] [LinearFiber F]

/-- The first three components of a fiber value (Julia `Makie.Point(x)`). -/
@[inline] def fiberVec (x : F) : Vec3 :=
  let buf := FlatFiber.push (FloatArray.emptyWithCapacity (FlatFiber.width F)) x
  ⟨buf.get! 0, buf.get! 1, buf.get! 2⟩

/-- Julia `p ↦ Point(m(Chain(p...)))` for a field over a 2-D grid (multilinear interpolation). -/
@[inline] def field2 {b : GridBundle 2 P G} (t : TensorField b F) (p : Vec2) : Vec2 :=
  let v := fiberVec (t.eval2 p.x p.y)
  ⟨v.x, v.y⟩

/-- Julia `p ↦ Point(m(Chain(p...)))` for a field over a 3-D grid. -/
@[inline] def field3 {b : GridBundle 3 P G} (t : TensorField b F) (p : Vec3) : Vec3 :=
  fiberVec (t.eval3 p.x p.y p.z)

/-- The box `[first, last]` of an axis (Makie's `Rect` from the extrema of the range, or
`to_interval`). -/
@[inline] def axisBox (a : Cartan.Axis) : Float × Float :=
  let lo := JuliaBase.F64.min a.first a.last
  (lo, JuliaBase.F64.max a.first a.last - lo)

/-- Makie `streamplot` options from the attributes and the default `gridsize`. -/
def streamOptions (a : Attrs) (gs : Array Nat) : Stream.Options :=
  { gridsize := a.gridsize.getD gs, stepsize := a.stepsize, maxsteps := a.maxsteps, density := a.density }

/-- Julia `streamplot(m::VectorField{…,2,RealSpace{2}})` (`MakieExt.jl:527-533`). -/
def stream2 {b : GridBundle 2 P G} (t : TensorField b F) (a : Attrs) : Stream.Result :=
  let (x0, w) := axisBox (b.space.axis 0)
  let (y0, h) := axisBox (b.space.axis 1)
  Stream.streamplot2 (field2 t) x0 y0 w h (streamOptions a #[32, 32])

/-- Julia `streamplot(m::VectorField{…,3,RealSpace{3}})` with Cartan's default
`gridsize = (11, 11, 11)` (`streamargs`, `Cartan.jl:936-945`). -/
def stream3 {b : GridBundle 3 P G} (t : TensorField b F) (a : Attrs) : Stream.Result × Float :=
  let (x0, wx) := axisBox (b.space.axis 0)
  let (y0, wy) := axisBox (b.space.axis 1)
  let (z0, wz) := axisBox (b.space.axis 2)
  let o := streamOptions a #[11, 11, 11]
  let res := Stream.streamplot3 (field3 t) ⟨x0, y0, z0⟩ ⟨wx, wy, wz⟩ o
  (res, Stream.arrowSize3 ⟨wx, wy, wz⟩ (Stream.resolution o.gridsize 3))

/-- Julia `streamplot(m::VectorField over a 2-D grid)`. -/
instance instStreamGrid2 {b : GridBundle 2 P G} : MakiePlot .streamplot (TensorField b F) where
  plot c t a := drawStream c (stream2 t a) 15 a
  dim _ := 2

/-- Julia `streamplot(m::VectorField over a 3-D grid)`. -/
instance instStreamGrid3 {b : GridBundle 3 P G} : MakiePlot .streamplot (TensorField b F) where
  plot c t a := let (r, s) := stream3 t a; drawStream c r s a
  dim _ := 3

end Fields

/-! ## Tangent-space streamplots `streamplot(M, m)` -/

section Tangent

variable {P G E F : Type} [Inhabited G] [FlatFiber E] [LinearFiber E] [FlatFiber F] [LinearFiber F]

/-- The area of the triangulated surface of the fiber points of a field over a 2-D grid (the
arrowhead scale; Cartan's `surfacearea` integrates `|det dγ|` instead). -/
def meshArea {b : GridBundle 2 P G} (M : TensorField b E) : Float :=
  let pos := Field.fiberPoints M
  let m := gridTriMesh b.size[0] b.size[1] pos
  (List.range m.numTriangles).foldl (init := 0) fun s k =>
    let (p, q, r) := m.triangle k
    s + 0.5 * (Vec3.cross (q - p) (r - p)).norm

/-- Julia `streamplot(M::VectorField, m::VectorField{…,2,RealSpace{2}})` (`MakieExt.jl:536-557`). -/
instance instStreamTangent {bM bm : GridBundle 2 P G} : MakiePlot .streamplot (TensorField bM E × TensorField bm F) where
  plot c Mm a :=
    let M := Mm.1
    let m := Mm.2
    let embed (p : Vec3) : Vec3 := fiberVec (M.eval2 p.x p.y)
    if FlatFiber.width E != 2 then
      let (x0, wx) := axisBox (bm.space.axis 0)
      let (y0, wy) := axisBox (bm.space.axis 1)
      let gs : Array Nat := match a.gridsize with | some g => g.push 1 | none => #[32, 32, 1]
      let o := streamOptions { a with gridsize := some gs } gs
      let f (p : Vec3) : Vec3 := let v := field2 m ⟨p.x, p.y⟩; ⟨v.x, v.y, 0⟩
      let res := Stream.streamplot3 f ⟨x0, y0, -1e-15⟩ ⟨wx, wy, 2e-15⟩ o
      let scale := 0.2 * Float.sqrt (meshArea M / (wx * wy))
      let size := scale * JuliaBase.F64.min wx wy / (JuliaBase.F64.min (gs.getD 0 32).toUInt64.toFloat (gs.getD 1 32).toUInt64.toFloat)
      drawStream c (res.mapPoints embed) size a
    else
      let pts := Field.fiberPoints M
      let res := stream2 m a
      let c := drawStream c (res.mapPoints fun p => let v := embed p; ⟨v.x, v.y, 0⟩) 15 a
      match Num.extremaFinite pts.xs, Num.extremaFinite pts.ys with
      | some (x0, x1), some (y0, y1) => c.map2 (·.limits x0 x1 y0 y1)
      | _, _ => c
  dim _ := if FlatFiber.width E != 2 then 3 else 2

end Tangent

end GrassmannPlot

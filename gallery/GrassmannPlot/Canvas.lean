import LeanPlot
import Cartan

/-!
# Canvases: Makie's current axis, and the keyword arguments of Cartan's plot methods

Cartan's Makie extension (`Cartan.jl ext/MakieExt.jl`) adds methods to Makie's plotting
functions: a non-mutating call such as `lines(t)` creates a figure with an axis chosen from the
data (an `Axis` for 2-D points, an `LScene` for 3-D ones) and a mutating call `lines!(t)` adds to
the current axis. Here the current axis is a value, `Canvas` (a LeanPlot `Axis2` or `Axis3`;
LeanPlot draws Makie's `LScene` as an `Axis3`), and every Cartan method is a function
`Canvas → field → Attrs → Canvas`.

`Attrs` collects the Makie keyword arguments these methods read (with Makie's defaults) and the
keywords Cartan strips before forwarding (`gridsize`, `arcgridsize`, `poly`, `lengthscale`:
`Cartan.jl:956-982`).

The `draw*` functions put one LeanPlot mark on the canvas: 2-D data in an `Axis3` lies in the
plane `z = 0`, 3-D data in an `Axis2` is projected onto `xy` (LeanPlot's rule, `Scene/Mark.lean`).
-/

namespace GrassmannPlot

open LeanPlot

/-- The Makie keyword arguments read by Cartan's plot methods (`ext/MakieExt.jl`), with Makie's
defaults. A `none` colour means the method's own colouring: `speed` for curves (`lines`,
`linesegments`, `MakieExt.jl:171-176`), the field values for `mesh(M, f)`, the palette otherwise. -/
structure Attrs where
  /-- Makie `color`: a solid colour, per-element colours, or values through `colormap`. -/
  color : Option ColorSpec := none
  /-- Makie `colormap` (`:viridis`). -/
  colormap : Colormap := Colormap.viridis
  /-- Makie `colorrange` (`automatic`: the extrema of the values). -/
  colorrange : Option (Float × Float) := none
  /-- Makie `colorscale`. -/
  colorscale : Scale := .identity
  /-- Makie `lowclip`, `highclip`. -/
  lowclip : Option RGBA := none
  /-- Makie `highclip`. -/
  highclip : Option RGBA := none
  /-- Makie `linewidth` (`none`: the recipe default, 1.5; contour 1). -/
  linewidth : Option Float := none
  /-- Makie `linestyle`. -/
  linestyle : LineStyle := .solid
  /-- Makie `marker`. -/
  marker : MarkerShape := .circle
  /-- Makie `markersize` (a scalar). -/
  markersize : Float := 9
  /-- Makie `markersize` (one per marker). -/
  markersizes : Option FloatArray := none
  /-- Makie `strokecolor`. -/
  strokecolor : RGBA := RGBA.black
  /-- Makie `strokewidth`. -/
  strokewidth : Float := 0
  /-- Makie `label` (legend entry). -/
  label : Option String := none
  /-- Makie `shading` (`none`: the method's default). -/
  shading : Option Bool := none
  /-- Makie `lengthscale` of `arrows2d`/`arrows3d`. -/
  lengthscale : Float := 1
  /-- Makie `align` of arrows: `0` tail, `0.5` centre, `1` tip. -/
  align : Float := 0
  /-- Makie `normalize` of arrows. -/
  normalize : Bool := false
  /-- Makie `shaftcolor` of `arrows3d` (`none`: `color`). -/
  shaftcolor : Option ColorSpec := none
  /-- Makie `tipcolor` of `arrows3d` (`none`: `color`). -/
  tipcolor : Option ColorSpec := none
  /-- Makie `levels` of `contour`/`contourf`/`contour3d` (`none`: 5 automatic levels;
  `contourf`: 10). -/
  levels : Option Recipes.Algo.Levels.LevelSpec := none
  /-- Makie `stepsize`, `maxsteps`, `density` of `streamplot`, and `gridsize` for it. -/
  stepsize : Float := 0.01
  /-- Makie `maxsteps` of `streamplot`. -/
  maxsteps : Nat := 500
  /-- Makie `density` of `streamplot`. -/
  density : Float := 1
  /-- Cartan `gridsize`: resample the field before plotting (`gridargs`, `Cartan.jl:956`); for
  `streamplot` the streamline cell grid (Makie's own keyword). -/
  gridsize : Option (Array Nat) := none
  /-- Cartan `poly`: draw planes as polygons instead of meshes (`planes`, `planesbundle`). -/
  poly : Bool := false
  /-- Makie `gap` of `voxels` (data units subtracted from the voxel size). -/
  gap : Float := 0
  /-- Makie `fontsize` of `text`. -/
  fontsize : Float := 14
  deriving Inhabited

namespace Attrs

/-- The line width, or the recipe default `d`. -/
@[inline] def lw (a : Attrs) (d : Float := 1.5) : Float := a.linewidth.getD d

/-- The colour mapping of values in `a` (Makie `colormap`, `colorrange`, `colorscale`,
`lowclip`, `highclip`). -/
def mapping (a : Attrs) : ColorMapping :=
  { colormap := a.colormap, colorrange := a.colorrange, colorscale := a.colorscale
    lowclip := a.lowclip, highclip := a.highclip }

/-- Values coloured through `a`'s colormap. -/
@[inline] def mapped (a : Attrs) (vs : FloatArray) : ColorSpec := .values vs a.mapping

/-- The explicit colour, else values coloured through the colormap, else nothing (the
palette). -/
def colorOr (a : Attrs) (vs : Option FloatArray) : Option ColorSpec :=
  match a.color, vs with
  | some c, _ => some c
  | none, some v => some (a.mapped v)
  | none, none => none

end Attrs

/-! ## Canvases -/

/-- Makie's current axis: a 2-D `Axis` or a 3-D scene (`LScene`/`Axis3`, drawn as a LeanPlot
`Axis3`). -/
inductive Canvas where
  /-- A 2-D axis. -/
  | ax2 (a : Axis2)
  /-- A 3-D axis. -/
  | ax3 (a : Axis3)
  deriving Inhabited

namespace Canvas

/-- The axis Makie creates for data of dimension `dim` (Makie's automatic axis: `Axis` for 2-D
points, `LScene` for 3-D). -/
def fresh (dim : Nat) : Canvas := if dim ≥ 3 then .ax3 Axis3.new else .ax2 Axis2.new

/-- A 3-D canvas. -/
def is3 : Canvas → Bool
  | ax2 _ => false
  | ax3 _ => true

/-- The figure with this canvas as its only block (Makie's `Figure` of a non-mutating plot). -/
def figure (c : Canvas) (size : Nat × Nat := (600, 450)) : Figure :=
  match c with
  | ax2 a => Figure.new size |>.axis 1 1 a
  | ax3 a => Figure.new size |>.axis3 1 1 a

/-- Place the canvas in cell `(r, col)` of a figure. -/
def placeIn (c : Canvas) (f : Figure) (r col : Nat) : Figure :=
  match c with
  | ax2 a => f.axis r col a
  | ax3 a => f.axis3 r col a

/-- Update a 2-D canvas (a 3-D one is unchanged). -/
def map2 (c : Canvas) (f : Axis2 → Axis2) : Canvas :=
  match c with
  | ax2 a => ax2 (f a)
  | ax3 a => ax3 a

/-- Update a 3-D canvas (a 2-D one is unchanged). -/
def map3 (c : Canvas) (f : Axis3 → Axis3) : Canvas :=
  match c with
  | ax2 a => ax2 a
  | ax3 a => ax3 (f a)

/-- The plot items drawn so far. -/
def items : Canvas → Array PlotItem
  | ax2 a => a.items
  | ax3 a => a.items

/-! ## Marks -/

/-- `lines!` of points (NaN points break the line). `color = none` takes the next palette
colour. -/
def drawLines (c : Canvas) (p : Pts3) (color : Option ColorSpec) (a : Attrs) : Canvas :=
  match c with
  | ax2 ax => ax2 (ax.linesPts p.xy color (a.lw) a.linestyle a.label)
  | ax3 ax => ax3 (ax.linesPts p color (a.lw) a.linestyle a.label)

/-- `linesegments!` of point pairs `p[2k] → p[2k+1]`. -/
def drawSegments (c : Canvas) (p : Pts3) (color : Option ColorSpec) (a : Attrs) : Canvas :=
  match c with
  | ax2 ax => ax2 (ax.linesegments p.xy color (a.lw) a.linestyle a.label)
  | ax3 ax =>
    let (col, ax) := ax.cycleSegments color
    ax3 (ax.add (.segments (.xyz p) { color := col, width := a.lw, style := a.linestyle }) a.label)

/-- `scatter!` of points. -/
def drawScatter (c : Canvas) (p : Pts3) (color : Option ColorSpec) (a : Attrs) : Canvas :=
  let spec (col : ColorSpec) : MarkerSpec :=
    { shape := a.marker, size := a.markersize, sizes := a.markersizes, color := col
      strokeColor := a.strokecolor, strokeWidth := a.strokewidth }
  match c with
  | ax2 ax =>
    let (col, ax) := ax.cycleScatter color
    ax2 (ax.add (.scatter (.xy p.xy) (spec col)) a.label)
  | ax3 ax =>
    let (col, ax) := ax.cycleScatter color
    ax3 (ax.add (.scatter (.xyz p) (spec col)) a.label)

/-- `text!` of strings at points (Makie's default alignment `(:left, :bottom)`). -/
def drawText (c : Canvas) (p : Pts3) (ss : Array String) (fontsize : Float := 14)
    (color : RGBA := RGBA.black) : Canvas :=
  let s : TextSpec := { size := fontsize, color }
  match c with
  | ax2 ax => ax2 (ax.add (.text (.xy p.xy) ss s))
  | ax3 ax => ax3 (ax.add (.text (.xyz p) ss s))

/-- `mesh!` of triangles; `shading` is used in 3-D only (LeanPlot's rule). -/
def drawMesh (c : Canvas) (m : TriMesh) (color : Option ColorSpec) (shading : Bool) (a : Attrs) : Canvas :=
  match c with
  | ax2 ax => ax2 (ax.mesh m color a.label)
  | ax3 ax => ax3 (ax.mesh m color shading a.label)

/-- `arrows2d!` (in 3-D: LeanPlot's projected arrows) from origins along directions. -/
def drawArrows (c : Canvas) (o d : Pts3) (color : ColorSpec) (a : Attrs) : Canvas :=
  let s : ArrowSpec := { color, lengthscale := a.lengthscale, normalize := a.normalize, align := a.align }
  match c with
  | ax2 ax => ax2 (ax.add (.arrows (.xy o.xy) (.xy d.xy) s) a.label)
  | ax3 ax => ax3 (ax.add (.arrows (.xyz o) (.xyz d) s) a.label)

/-- `heatmap!` of cell centres (or edges) and values (2-D canvases; a 3-D canvas draws nothing,
as Makie's `heatmap` needs a 2-D axis). -/
def drawHeatmap {nx ny : Nat} (c : Canvas) (xs ys : FloatArray) (z : Grid2 nx ny) (a : Attrs) : Canvas :=
  c.map2 fun ax => ax.add (.heatmap { xs := Recipes.Algo.Heatmap.cellEdges xs nx |>.getD (Recipes.cellEdges xs nx)
                                      ys := Recipes.Algo.Heatmap.cellEdges ys ny |>.getD (Recipes.cellEdges ys ny)
                                      z := ⟨nx, ny, z⟩, mapping := a.mapping }) a.label

end Canvas

end GrassmannPlot

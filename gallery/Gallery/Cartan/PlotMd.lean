import Gallery.Cartan.Common
import Gallery.Grassmann.Figures

/-!
# Cartan.jl `docs/src/plot.md`: the Makie gallery on TensorFields

Each figure is the documented Julia block drawn with `GrassmannPlot`, next to the render of
Cartan's own Makie methods (`oracle/gallery/cartan-plot-*.jl`). Omitted blocks and why:

* `contour_himmelblau` (labelled isolines, a `ReversibleScale` colour scale) and
  `heatmap_logscale` (an `asinh` axis scale): LeanPlot has no contour labels and no custom
  scales yet;
* `contour_curvilinear` and `contourf`: broken upstream (`Mesh(::GridBundle{PointMatrix})` has no
  method; `FieldError: Array has no field v`), so Julia has no render to compare with;
* `contour_volume_and_contour3d`, `contour_isorange_alpha`, `volume_*`: volume renderings
  (blank in CairoMakie; LeanPlot has no `volume` mark yet), and `voxels_cube_with_holes` (a 100³
  chunk);
* `surface_mesh_polar(_noshading)`: the docs reuse the 2-D `xy` field of the mesh section, so
  both are `cartan-plot-mesh-polar2d` again.

Julia's `sind`/`cosd` (`base/special/trig.jl:1308-1377`) and `sinc` (`:1086-1092`) are written
out below on JuliaBase's kernels (`JuliaBase.Math.sinKernelDD`, `cosKernelDD`, `F64.sinpi`); they
belong in `JuliaBase` (DESIGN.md §2.9) and move there with the next JuliaBase change.
-/

namespace Gallery.CartanPlotMd

open Lean LeanPlot Cartan Grassmann DirectSum JuliaBase GrassmannPlot
open Gallery.CartanCommon
open LeanPlot.Recipes.Algo

/-! ## Julia `sind`, `cosd`, `sinc` -/

/-- Julia `deg2rad_ext(x::Float64)` (`trig.jl:1308-1320`): `x·π/180` in double-double. -/
def deg2radExt (x : Float) : Float × Float :=
  let m := f64! 0.017453292519943295
  let mHi := f64! 0.01745329238474369
  let mLo := f64! 1.3519960527851425e-10
  let u := f64! 134217729.0 * x
  let xHi := u - (u - x)
  let xLo := x - xHi
  let yHi := m * x
  let yLo := xHi * mLo + (xLo * mHi + ((xHi * mHi - yHi) + xLo * mLo))
  (yHi, yLo)

/-- `sin_kernel` of a double-double. -/
@[inline] def sinK (y : Float × Float) : Float := JuliaBase.Math.sinKernelDD y.1 y.2
/-- `cos_kernel` of a double-double. -/
@[inline] def cosK (y : Float × Float) : Float := JuliaBase.Math.cosKernelDD y.1 y.2

/-- Julia `sind(x)` for an integer number of degrees (`trig.jl:1325-1354`). -/
def sind (x : Int) : Float :=
  let r := x.tmod 360
  let rx := Cartan.Axis.intToFloat r
  let arx := rx.abs
  if rx == 0 then rx
  else if arx < 45 then sinK (deg2radExt rx)
  else if arx ≤ 135 then
    let c := cosK (deg2radExt (90 - arx)); if rx < 0 then -c.abs else c.abs
  else if arx == 180 then (if rx < 0 then -0.0 else 0.0)
  else if arx < 225 then sinK (deg2radExt ((180 - arx) * (if rx < 0 then -1 else 1)))
  else if arx ≤ 315 then
    let c := cosK (deg2radExt (270 - arx)); -(if rx < 0 then -c.abs else c.abs)
  else sinK (deg2radExt (rx - (if rx < 0 then -360 else 360)))

/-- Julia `cosd(x)` for an integer number of degrees (`trig.jl:1356-1377`). -/
def cosd (x : Int) : Float :=
  let rx := (Cartan.Axis.intToFloat (x.tmod 360)).abs
  if rx ≤ 45 then cosK (deg2radExt rx)
  else if rx < 135 then sinK (deg2radExt (90 - rx))
  else if rx ≤ 225 then -cosK (deg2radExt (180 - rx))
  else if rx < 315 then sinK (deg2radExt (rx - 270))
  else cosK (deg2radExt (360 - rx))

/-- Julia `sinc(x::Float64)` (`trig.jl:1086-1092`): `sinpi(x)/(π x)`, `1` at `0`. -/
def sinc (x : Float) : Float :=
  if x.abs < f64! 0.001 then
    let x2 := x * x
    1 + x2 * (f64! -1.6449340668482264 + x2 * f64! 0.8117424252833536)
  else F64.sinpi x / (piF * x)

/-! ## Helpers -/

/-- A 2-D grid of product-space points. -/
def grid2 (a b : Cartan.Axis) : GridBundle 2 (AffinePoint 2) := GridBundle.ofSpace (.ofAxes #v[a, b])

/-- A 3-D grid of product-space points. -/
def grid3 (a b c : Cartan.Axis) : GridBundle 3 (AffinePoint 3) := GridBundle.ofSpace (.ofAxes #v[a, b, c])

/-- The Cartan plot documentation. -/
def plotDoc : String := "https://cartan.crucialflow.com/dev/plot"

/-- A plot.md entry. -/
def entry (name title source : String) (build : Option Json → IO Outcome) : Entry :=
  { name, title, source, group := "Cartan (plot.md)", upstream := plotDoc, build }

/-- The checks when a dump is present. -/
def withDump (j? : Option Json) (f : Json → Array Check) : Array Check :=
  match j? with | some j => f j | none => #[]

/-- A solid colour by name. -/
def named (s : String) : RGBA := (RGBA.parse? s).getD RGBA.black

/-! ## arrows -/

/-- Julia `xy = TensorField(OpenParameter(xs,ys),Chain.(us,vs))` of `plot.md:15-28`. -/
def arrowsField :=
  TensorField.tabulate2 (grid2 (.linRange 0 twoPiF 20) (.linRange 0 (3 * piF) 20)) fun x y =>
    (Chain.ofFn fun i => if i.1 = 0 then F64.sin x * F64.cos y else -F64.cos x * F64.sin y : Chain ℝ2 1 Float)

/-- Julia `ps = OpenParameter(-5:2:5,-5:2:5,-5:2:5)`. -/
def arrowsBase := grid3 (.ints (-5) 2 6) (.ints (-5) 2 6) (.ints (-5) 2 6)

/-- Julia `ns = map(p -> 0.1 * Chain(p[2], p[3], p[1]), ps)`. -/
def arrowsNs := TensorField.tabulate3 arrowsBase fun x y z =>
  (Chain.ofFn fun i => f64! 0.1 * (if i.1 = 0 then y else if i.1 = 1 then z else x) : Chain ℝ3 1 Float)

/-- The arrow checks: origins, directions, colour values. -/
def arrowChecks (c : Canvas) (o d : Pts3) (j : Json) (colors : Option FloatArray := none) : Array Check :=
  ptsChecks "origins" o (jget j "origins") ++ ptsChecks "directions" d (jget j "directions") ++
  (match colors with
   | some v => summaryChecks "colour values" v (jget (jget j "color") "values")
   | none => #[]) ++
  #[eqCheck "plot items" (decide (c.items.size > 0)) true]

/-! ## contour -/

/-- Julia `xyz = TensorField(OpenParameter(xs,ys),zs)` with `zs = cos(x)·sin(y)` on
`LinRange(0,10,100) × LinRange(0,15,100)` (`plot.md:52-65, 319-327`). -/
def cosSin := TensorField.tabulate2 (grid2 (.linRange 0 10 100) (.linRange 0 15 100)) fun x y => F64.cos x * F64.sin y

/-- Julia `zs = [sqrt(x^2+y^2) …]` on `LinRange(-0.5, 0.5, 100)²` (`plot.md:104-118`). -/
def cone := TensorField.tabulate2 (grid2 (.linRange (f64! -0.5) (f64! 0.5) 100) (.linRange (f64! -0.5) (f64! 0.5) 100))
  fun x y => Float.sqrt (x * x + y * y)

/-- The `contour3d` axis of `plot.md:104-125`: `Axis3(aspect = (0.5,0.5,1), perspectiveness = 0.75)`. -/
def coneAxis : Canvas := .ax3 (Axis3.new (perspectiveness := f64! 0.75) (aspect := .ratio (f64! 0.5) (f64! 0.5) 1))

/-- The line points of every plot item compared with Julia's `contours` list. -/
def contourChecks (c : Canvas) (j : Json) : Array Check :=
  let js := jarr (jget j "contours")
  (Array.range js.size).foldl (init := #[eqCheck "contour plots" c.items.size js.size]) fun acc k =>
    acc ++ momentsChecks s!"contour {k + 1}" (itemPoints c k) js[k]!

/-- `a:s:b` as an array (Julia's range elements). -/
def rangeValues (a s b : Float) : FloatArray := (JuliaBase.colon a s b).toFloatArray

/-! ## heatmap, linesegments, mesh, scatter -/

/-- Julia `ProductSpace([1,2,4,7,11],[6,7,9,12,16])` with the values `reshape(1:25, 5, 5)`. -/
def centersField :=
  TensorField.ofFn (grid2 (.explicit ⟨#[1, 2, 4, 7, 11]⟩) (.explicit ⟨#[6, 7, 9, 12, 16]⟩)) fun i => (i + 1).toUInt64.toFloat

/-- Julia `zs = [sin(x*y) …]` on `range(0, 2π, length=100)²` (`plot.md:190-201`). -/
def sinXY := TensorField.tabulate2 (grid2 (.range 0 twoPiF 100) (.range 0 twoPiF 100)) fun x y => F64.sin (x * y)

/-- Julia `ys = sin(TensorField(1:0.2:10))`. -/
def sinSegments := TensorField.ofAxisFn (Cartan.Axis.colon 1 (f64! 0.2) 10) F64.sin

/-- Julia `rs = 1:10; thetas = 0:10:360` as a product grid. -/
def polarBase := grid2 (.ints 1 1 10) (.ints 0 10 37)

/-- `(r, θ)` of a polar grid point as integers. -/
@[inline] def polarRT (x y : Float) : Int × Int := (Float.toInt64 x |>.toInt, Float.toInt64 y |>.toInt)

/-- Julia `Chain.(xs, ys, zs)` with `xs = r·cosd θ`, `ys = r·sind θ`, `zs = sin(r)·cosd θ`. -/
def polar3 := TensorField.tabulate2 polarBase fun x y =>
  let (_, θ) := polarRT x y
  (Chain.ofFn fun i => if i.1 = 0 then x * cosd θ else if i.1 = 1 then x * sind θ else F64.sin x * cosd θ : Chain ℝ3 1 Float)

/-- Julia `Chain.(xs, ys)`. -/
def polar2 := TensorField.tabulate2 polarBase fun x y =>
  let (_, θ) := polarRT x y
  (Chain.ofFn fun i => if i.1 = 0 then x * cosd θ else x * sind θ : Chain ℝ2 1 Float)

/-- Julia `zs = sin.(rs) .* cosd.(thetas')` as a field. -/
def polarZ := TensorField.tabulate2 polarBase fun x y => let (_, θ) := polarRT x y; F64.sin x * cosd θ

/-- The mesh checks of `plot.md:242-256`. -/
def meshChecks (c : Canvas) (j : Json) : Array Check :=
  let faces := match c.items[0]? with
    | some it => match it.mark with | .mesh m => m.mesh.numTriangles | _ => 0
    | none => 0
  ptsChecks "vertices" (itemPoints c 0) (jget j "vertices") ++
  summaryChecks "colour values (binary32)" (itemColorValues c 0) (jget (jget j "color") "values") 1e-7 ++
  #[eqCheck "triangles" faces (jnat (jget j "faces"))]

/-- Julia `xs = range(0, 10, length = 30)`. -/
def scatterAxis : Cartan.Axis := .range 0 10 30

/-! ## streamplot -/

/-- Julia `fun.(OpenParameter(-1.5:0.1:1.5,-1.5:0.1:1.5))` of the FitzHugh-Nagumo model
`(e, s, y, b) = (0.1, 0, 1.5, 0.8)` (`plot.md:294-310`). -/
def fhn := TensorField.tabulate2 (grid2 (.colon (f64! -1.5) (f64! 0.1) (f64! 1.5)) (.colon (f64! -1.5) (f64! 0.1) (f64! 1.5)))
  fun x y => (Chain.ofFn fun i =>
    if i.1 = 0 then (x - y - x * x * x + 0) / f64! 0.1 else f64! 1.5 * x - y + f64! 0.8 : Chain ℝ2 1 Float)

/-- Julia `color = (p) -> RGBAf(p..., 0.0, 1)`: the colour of every line point and arrow from the
field value `(u, v)` (the streamlines traced twice, with `u` and `v` as colour values). -/
def colorFunctionStream : Stream.Result × ByteArray × ByteArray :=
  let o (g : Vec3 → Float) : Stream.Options := { gridsize := #[32, 32], colorFn := some g }
  let ru := Stream.streamplot2 (field2 fhn) (f64! -1.5) (f64! -1.5) 3 3 (o (·.x))
  let rv := Stream.streamplot2 (field2 fhn) (f64! -1.5) (f64! -1.5) 3 3 (o (·.y))
  let rgba (u v : FloatArray) : ByteArray :=
    (Array.range u.size).foldl (init := ByteArray.empty) fun acc i =>
      RGBA.pushRGBA8 acc ⟨Num.clamp (u.get! i) 0 1, Num.clamp (v.get! i) 0 1, 0, 1⟩
  (ru, rgba ru.lineColors rv.lineColors, rgba ru.arrowColors rv.arrowColors)

/-! ## wireframe, voxels -/

/-- Julia `z = [sinc(√(X^2 + Y^2) / π) …]` on `collect(-8:0.5:8)²` (`plot.md:409-415`). -/
def sincField :=
  let ax : Cartan.Axis := .explicit (rangeValues (-8) (f64! 0.5) 8)
  TensorField.tabulate2 (grid2 ax ax) fun x y => sinc (Float.sqrt (x * x + y * y) / piF)

/-- Julia `TensorField(OpenParameter(n,n,n), reshape(collect(1:n³), n, n, n))`. -/
def chunk (n : Nat) : TensorField (Parameter.baseN (N := 3) (fun _ => 0) (fun _ => 1) #v[n, n, n]) Float :=
  TensorField.ofFn _ fun i => (i + 1).toUInt64.toFloat

/-! ## Entries -/

/-- The plot.md figures. -/
def entries : List Entry := [
  entry "cartan-plot-arrows2d" "arrows2d of a vector field on a black axis, coloured by strength"
    "`xy = TensorField(OpenParameter(xs,ys),Chain.(us,vs)); arrows2d!(xy, lengthscale = 0.2, color = strength)` (`plot.md:15-28`)"
    fun j? => do
      let strength := arrowsField.norm.data
      let c := (Canvas.fresh 2).map2 (·.mapStyle fun s => { s with backgroundcolor := RGBA.black })
      let c := c.arrows2d arrowsField { color := some (.values strength {}), lengthscale := f64! 0.2 }
      return { fig := c.figure (800, 800)
               checks := withDump j? (arrowChecks c (gridBasePoints arrowsField) (Field.fiberPoints arrowsField) · (some strength)) },
  entry "cartan-plot-arrows3d" "arrows3d with grey shafts and black tips"
    "`ps = OpenParameter(-5:2:5,-5:2:5,-5:2:5); ns = map(p -> 0.1 * Chain(p[2], p[3], p[1]), ps); arrows3d(TensorField(ps, ns), shaftcolor = :gray, tipcolor = :black, align = :center)` (`plot.md:31-38`)"
    fun j? => do
      let c := GrassmannPlot.arrows3d arrowsNs { shaftcolor := some (.solid (named "gray")), tipcolor := some (.solid RGBA.black), align := 0.5 }
      return { fig := c.figure, checks := withDump j? (arrowChecks c (gridBasePoints arrowsNs) (Field.fiberPoints arrowsNs)) },
  entry "cartan-plot-arrows3d-lengths" "arrows3d coloured by length"
    "`lengths = vec(norm.(ns)); arrows3d(TensorField(ps, ns), color = lengths, lengthscale = 1.5, align = :center)` (`plot.md:40-46`)"
    fun j? => do
      let lengths := arrowsNs.norm.data
      let c := GrassmannPlot.arrows3d arrowsNs { color := some (.values lengths {}), lengthscale := 1.5, align := 0.5 }
      return { fig := c.figure, checks := withDump j? (arrowChecks c (gridBasePoints arrowsNs) (Field.fiberPoints arrowsNs) · (some lengths)) },
  entry "cartan-plot-contour" "contour of cos(x)·sin(y): 5 automatic levels, then levels -1:0.1:1"
    "`xyz = TensorField(OpenParameter(xs,ys),zs); contour!(xyz); contour!(xyz,levels=-1:0.1:1)` (`plot.md:52-65`)"
    fun j? => do
      let c := (Canvas.fresh 2).contour cosSin |>.contour cosSin { levels := some (.values (rangeValues (-1) (f64! 0.1) 1)) }
      return { fig := c.figure, checks := withDump j? (contourChecks c) },
  entry "cartan-plot-contour3d" "contour3d of the cone ±√(x²+y²)"
    "`contour3d!(-xyz, linewidth=2, color=:blue2); contour3d!(+xyz, linewidth=2, color=:red2)` (`plot.md:104-118`)"
    fun j? => do
      let c := coneAxis.contour3d (cone.map (-·)) { linewidth := some 2, color := some (.solid (named "blue2")) }
        |>.contour3d cone { linewidth := some 2, color := some (.solid (named "red2")) }
      return { fig := c.figure, checks := withDump j? (contourChecks c) },
  entry "cartan-plot-contour3d-levels" "contour3d of the cone with explicit levels"
    "`contour3d!(-xyz, levels=-(.025:0.05:.475), …); contour3d!(+xyz, levels=.025:0.05:.475, …)` (`plot.md:119-125`)"
    fun j? => do
      let lv := rangeValues (f64! 0.025) (f64! 0.05) (f64! 0.475)
      let c := coneAxis.contour3d (cone.map (-·)) { linewidth := some 2, color := some (.solid (named "blue2")), levels := some (.values ⟨lv.data.map (-·)⟩) }
        |>.contour3d cone { linewidth := some 2, color := some (.solid (named "red2")), levels := some (.values lv) }
      return { fig := c.figure, checks := withDump j? (contourChecks c) },
  entry "cartan-plot-heatmap-centers" "heatmap over irregular cell centres, centres marked"
    "`xy = ProductSpace([1,2,4,7,11],[6,7,9,12,16]); heatmap!(TensorField(xy,reshape(1:25, 5, 5))); scatter!(TensorField(xy,collect(xy)), color=:white, strokecolor=:black, strokewidth=1)` (`plot.md:176-188`)"
    fun j? => do
      let c := (Canvas.fresh 2).heatmap centersField
        |>.scatter (TensorField.identity centersField.base) { color := some (.solid RGBA.white), strokecolor := RGBA.black, strokewidth := 1 }
      let b := centersField.base
      return { fig := c.figure
               checks := withDump j? fun j =>
                 #[closeCheck "x edges" (Recipes.cellEdges b.space.coords[0] 5) (jfloats (jget j "x")) 1e-12,
                   closeCheck "y edges" (Recipes.cellEdges b.space.coords[1] 5) (jfloats (jget j "y")) 1e-12] ++
                 summaryChecks "values" centersField.data (jget j "z") ++ ptsChecks "centres" (itemPoints c 1) (jget j "scatter") },
  entry "cartan-plot-heatmap-colorbar" "heatmap of sin(x·y) with a colorbar"
    "`xyz = TensorField(OpenParameter(xs,ys),zs); fig, ax, hm = heatmap(xyz); Colorbar(fig[:, end+1], hm)` (`plot.md:190-201`)"
    fun j? => do
      let c := GrassmannPlot.heatmap sinXY
      let b := sinXY.base
      return { fig := c.placeIn (Figure.new (600, 450)) 1 1 |>.colorbar 1 2 (1, 1)
               checks := withDump j? fun j =>
                 summaryChecks "x edges" (Recipes.cellEdges b.space.coords[0] 100) (jget j "x") 1e-12 ++
                 summaryChecks "y edges" (Recipes.cellEdges b.space.coords[1] 100) (jget j "y") 1e-12 ++
                 summaryChecks "values (binary32)" sinXY.data (jget j "z") 1e-7 },
  entry "cartan-plot-linesegments" "linesegments of sin, shifted: speed colours, then an explicit colour range"
    "`ys = sin(TensorField(1:0.2:10)); linesegments!(ys); linesegments!(ys - 1, linewidth = 5); linesegments!(ys - 2, linewidth = 5, color = LinRange(1, 5, length(xs)))` (`plot.md:224-236`)"
    fun j? => do
      let lin := (Cartan.Axis.linRange 1 5 46).toFloatArray
      let c := (Canvas.fresh 2).linesegments sinSegments
        |>.linesegments (sinSegments.map (· - 1)) { linewidth := some 5 }
        |>.linesegments (sinSegments.map (· - 2)) { linewidth := some 5, color := some (.values lin {}) }
      return { fig := c.figure
               checks := withDump j? fun j =>
                 let ps := jarr (jget j "plots")
                 (Array.range 3).foldl (init := #[]) fun acc k =>
                   acc ++ ptsChecks s!"plot {k + 1}" (itemPoints c k) (jget ps[k]! "points") ++
                     summaryChecks s!"plot {k + 1} colours (binary32)" (itemColorValues c k) (jget (jget ps[k]! "color") "values") 1e-7 },
  entry "cartan-plot-mesh-polar3d" "mesh of a polar surface coloured by its height"
    "`xyz = TensorField(ProductSpace(rs,thetas),Chain.(xs,ys,zs)); mesh(xyz,TensorField(xyz,zs))` (`plot.md:242-252`)"
    fun j? => do
      let c := GrassmannPlot.mesh (polar3, polarZ)
      return { fig := c.figure, checks := withDump j? (meshChecks c) },
  entry "cartan-plot-mesh-polar2d" "the same mesh with 2-D positions"
    "`xy = TensorField(ProductSpace(rs,thetas),Chain.(xs,ys)); mesh(xy,TensorField(xy,zs))` (`plot.md:253-256`)"
    fun j? => do
      let c := GrassmannPlot.mesh (polar2, polarZ)
      return { fig := c.figure, checks := withDump j? (meshChecks c) },
  entry "cartan-plot-scatter" "scatter of a real function"
    "`xs = range(0, 10, length = 30); xy = TensorField(xs, 0.5 .* sin.(xs)); scatter(xy)` (`plot.md:266-272`)"
    fun j? => do
      let t := TensorField.ofAxisFn scatterAxis fun x => f64! 0.5 * F64.sin x
      let c := GrassmannPlot.scatter t
      return { fig := c.figure, checks := withDump j? fun j => ptsChecks "points" (itemPoints c 0) (jget j "points") },
  entry "cartan-plot-scatter-colored" "scatter of a plane curve with colours and marker sizes"
    "`pts = TensorField(xs,Chain.(xs, ys)); scatter(pts, color = 1:30, markersize = range(5, 30, length = 30), colormap = :thermal)` (`plot.md:273-280`)"
    fun j? => do
      let t := TensorField.ofAxisFn scatterAxis fun x =>
        (Chain.ofFn fun i => if i.1 = 0 then x else f64! 0.5 * F64.sin x : Chain ℝ2 1 Float)
      let cols := (Cartan.Axis.oneTo 30).toFloatArray
      let sizes := (Cartan.Axis.range 5 30 30).toFloatArray
      let c := GrassmannPlot.scatter t { color := some (.values cols { colormap := Colormap.named "thermal" }), markersizes := some sizes }
      return { fig := c.figure
               checks := withDump j? fun j =>
                 ptsChecks "points" (itemPoints c 0) (jget j "points") ++
                 summaryChecks "colour values" (itemColorValues c 0) (jget (jget j "color") "values") ++
                 summaryChecks "marker sizes (binary32)" sizes (jget j "markersize") 1e-7 },
  entry "cartan-plot-streamplot-point2" "streamplot of the plain function (y, 4x)"
    "`v(x::Point2{T}) where T = Point2f(x[2], 4*x[1]); streamplot(v, -2..2, -2..2)` (`plot.md:290-293`)"
    fun j? => do
      let r := Stream.streamplot2 (fun p => ⟨p.y, 4 * p.x⟩) (-2) (-2) 4 4 { gridsize := #[32, 32], fieldF32 := true }
      return { fig := (drawStream (Canvas.fresh 2) r 15 {}).figure, checks := withDump j? (GrassmannFigs.streamChecks r) },
  entry "cartan-plot-streamplot-fhn" "FitzHugh-Nagumo vector field, magma colours"
    "`xy = OpenParameter(-1.5:0.1:1.5,-1.5:0.1:1.5); streamplot(fun.(xy), colormap = :magma)` (`plot.md:294-310`)"
    fun j? => do
      let r := stream2 fhn {}
      return { fig := (drawStream (Canvas.fresh 2) r 15 { colormap := Colormap.named "magma" }).figure
               checks := withDump j? (GrassmannFigs.streamChecks r) },
  entry "cartan-plot-streamplot-colorfunction" "FitzHugh-Nagumo streamlines coloured by RGBAf(u, v, 0, 1)"
    "`streamplot(fun.(xy), color=(p)-> RGBAf(p..., 0.0, 1))` (`plot.md:311-313`)"
    fun j? => do
      let (r, lineRGBA, arrowRGBA) := colorFunctionStream
      let c := (Canvas.fresh 2).map2 fun ax =>
        let ax := ax.add (.lines (.xy r.linePoints2) { color := .perElement lineRGBA })
        ax.add (.scatter (.xy r.arrowPos2) { shape := .utriangle, size := 15, color := .perElement arrowRGBA
                                             alongDirections := some (.xy r.arrowDir2, -Num.pi / 2) })
      let rv := Stream.streamplot2 (field2 fhn) (f64! -1.5) (f64! -1.5) 3 3 { gridsize := #[32, 32], colorFn := some (·.y) }
      return { fig := c.figure
               checks := withDump j? fun j =>
                 GrassmannFigs.streamChecks r j ++
                 summaryChecks "red channel (u)" r.lineColors (jget j "line_red") 1e-6 ++
                 summaryChecks "green channel (v)" rv.lineColors (jget j "line_green") 1e-6 },
  entry "cartan-plot-surface" "surface of cos(x)·sin(y)"
    "`xyz = TensorField(OpenParameter(xs,ys),zs); surface(xyz, axis=(type=Axis3,))` (`plot.md:319-327`)"
    fun j? => do
      let c := GrassmannPlot.surface cosSin
      let b := cosSin.base
      return { fig := c.figure
               checks := withDump j? fun j =>
                 summaryChecks "x" b.space.coords[0] (jget j "x") ++ summaryChecks "y" b.space.coords[1] (jget j "y") ++
                 summaryChecks "z (binary32)" cosSin.data (jget j "z") 1e-7 ++
                 summaryChecks "colour values" (itemColorValues c 0) (jget (jget j "color") "values") 1e-6 },
  entry "cartan-plot-wireframe-sinc" "wireframe of the graph of sinc(r/π)"
    "`xyz = TensorField(ProductSpace(x,y),z); wireframe(graph(xyz), axis=(type=Axis3,), color=:black)` (`plot.md:409-415`)"
    fun j? => do
      let c := GrassmannPlot.wireframe sincField.graph { color := some (.solid RGBA.black) }
      return { fig := c.figure, checks := withDump j? fun j => segmentChecks (itemPoints c 0) j },
  entry "cartan-plot-voxels-chunk3" "voxels of a 3×3×3 chunk with gaps"
    "`chunk = TensorField(OpenParameter(3,3,3),reshape(collect(1:27), 3, 3, 3)); voxels(chunk, gap = 0.33)` (`plot.md:389-393`)"
    fun j? => do
      let t := chunk 3
      let c := GrassmannPlot.voxels t { gap := f64! 0.33 }
      return { fig := c.figure, checks := withDump j? fun j => summaryChecks "values" t.data (jget j "values") },
  entry "cartan-plot-voxels-chunk8" "voxels of an 8³ chunk: log colour scale, clip colours"
    "`voxels(chunk, colorrange = (65, 448), colorscale = log10, lowclip = :red, highclip = :orange, colormap = [:blue, :green])` (`plot.md:394-403`)"
    fun j? => do
      let t := chunk 8
      let a : Attrs := { colorrange := some (65, 448), colorscale := .log10, lowclip := some (named "red"),
                         highclip := some (named "orange"), colormap := Colormap.ofColors #[named "blue", named "green"] }
      let c := GrassmannPlot.voxels t a
      return { fig := c.figure, checks := withDump j? fun j => summaryChecks "values" t.data (jget j "values") }]

end Gallery.CartanPlotMd

import Gallery.Cartan.PlotMd

/-!
# Cartan's own plot recipes: `scaledarrows`, `arrowsbundle`

`scaledarrows` and `arrowsbundle` (`ext/MakieExt.jl:290-299, 371-385`) scale the arrows by the
sample spacing of the base points: `lengthscale = spacing(M)/(Σ|t|/n)/3` (`/2` for the bundle).
The documented sessions use them with the frames of Cartan's differential geometry
(`unitframe`, `bishopunitframe`, `unitnormal`: fiber.md C1, C19, C23); these figures use analytic
fields instead, with the same code paths:

| figure | Julia |
|---|---|
| `cartan-scaledarrows-grid` | `scaledarrows(xy, gridsize = (10,10))` of the plot.md arrows field (the one-argument form, resampled) |
| `cartan-scaledarrows-helix` | `lines(M); scaledarrows!(M, T)` of a helix and its unit tangents (3-D arrows) |
| `cartan-arrowsbundle-helix` | `arrowsbundle!(M, T)`: the points and the arrows of `±T` |
| `cartan-scaledarrows-frame` | `scaledarrows!(S, F)` of a two-column tangent frame (Julia `TensorOperator` fibers, here the column fields) |
| `cartan-linegraph-polar`, `…-gridsize` | `linegraph!(xyz)` and `linegraph!(xyz, gridsize = (5, 7))` of the plot.md polar surface |

`planes`, `scaledplanes` (the non-mutating forms return `nothing` and draw every parallelogram
in a figure of its own) and `planesbundle` (B4: undefined `M`) fail in Cartan 0.4.16; their
intended forms are in `GrassmannPlot.Arrows` but have no Julia render to compare with.
-/

namespace Gallery.CartanRecipes

open Lean LeanPlot Cartan Grassmann DirectSum JuliaBase GrassmannPlot
open Gallery.CartanCommon Gallery.CartanPlotMd

/-- Julia `t = TensorField(0:step:4pi); M = Chain.(cos(t), sin(t), t/4)` (the division keeps the
range lazy, as Julia does). -/
def helixM (step : Float) : TensorField (GridBundle.ofAxis (Cartan.Axis.colon 0 step fourPiF)) (Chain ℝ3 1 Float) :=
  let t := TensorField.ofAxis (Cartan.Axis.colon 0 step fourPiF)
  let q := t / (4 : Float)
  TensorField.chainOf ℝ3 1 fun j =>
    if j.1 = 0 then t.map F64.cos else if j.1 = 1 then t.map F64.sin else q

/-- Julia `T = Chain(-sin(x), cos(x), 0.25)/sqrt(1.0625)`: the unit tangents of the helix (a
Grassmann division by a real, `* (1/s)`). -/
def helixT (step : Float) :=
  let t := TensorField.ofAxis (Cartan.Axis.colon 0 step fourPiF)
  let r := (1 : Float) / Float.sqrt (f64! 1.0625)
  t.map fun x => (Chain.ofFn fun i =>
    (if i.1 = 0 then -F64.sin x else if i.1 = 1 then F64.cos x else f64! 0.25) * r : Chain ℝ3 1 Float)

/-- Julia `S = (x -> Chain(x[1], x[2], x[1]*x[2]/4)).(TensorField(ProductSpace(0:0.25:2, 0:0.25:2)))`. -/
def frameBase := grid2 (.colon 0 (f64! 0.25) 2) (.colon 0 (f64! 0.25) 2)

/-- The surface `z = xy/4`. -/
def frameS := TensorField.tabulate2 frameBase fun x y =>
  (Chain.ofFn fun i => if i.1 = 0 then x else if i.1 = 1 then y else x * y / 4 : Chain ℝ3 1 Float)

/-- Its tangent frame, as the two column fields `(1, 0, y/4)` and `(0, 1, x/4)`. -/
def frameCols : Array (TensorField frameBase (Chain ℝ3 1 Float)) :=
  #[TensorField.tabulate2 frameBase fun _ y => Chain.ofFn fun i => if i.1 = 0 then 1 else if i.1 = 1 then 0 else y / 4,
    TensorField.tabulate2 frameBase fun x _ => Chain.ofFn fun i => if i.1 = 0 then 0 else if i.1 = 1 then 1 else x / 4]

/-- The lines of a canvas: their point counts, colour values and points, concatenated. -/
def linesData (c : Canvas) : List Nat × FloatArray × Pts3 :=
  let ks := (List.range c.items.size).filter fun k => match c.items[k]!.mark with | .lines .. => true | _ => false
  let pts := ks.map (itemPoints c)
  let cat (f : Pts3 → FloatArray) : FloatArray := ⟨(pts.map fun p => (f p).data).toArray.flatten⟩
  (pts.map (·.size), ⟨(ks.map fun k => (itemColorValues c k).data).toArray.flatten⟩,
   Pts3.ofArrays (cat (·.xs)) (cat (·.ys)) (cat (·.zs)))

/-- The checks of a `linegraph` figure. -/
def linegraphChecks (c : Canvas) (j : Json) : Array Check :=
  let (ns, speed, pts) := linesData c
  #[eqCheck "lines" ns.length (jnat (jget j "lines")),
    eqCheck "points per line" ns ((jarr (jget j "points")).map jnat).toList] ++
  summaryChecks "speed colours (binary32)" speed (jget j "speed") 1e-6 ++ ptsChecks "points" pts (jget j "coords") 1e-7

/-- A lengthscale check. -/
def lengthscaleCheck (lean julia : Float) : Check :=
  let d := (lean - julia).abs / julia.abs
  { label := "lengthscale", ok := d ≤ 1e-12, detail := s!"Lean {lean}, Julia {julia} (rel |Δ| = {sci d})" }

/-- The figures. -/
def entries : List Entry := [
  entry "cartan-scaledarrows-grid" "scaledarrows of a vector field resampled to 10×10"
    "`xy = TensorField(OpenParameter(xs,ys),Chain.(us,vs)); scaledarrows(xy, gridsize = (10,10))` (`MakieExt.jl:371-379`, the field of `plot.md:15-28`)"
    fun j? => do
      let a : Attrs := { gridsize := some #[10, 10] }
      let c := GrassmannPlot.scaledarrows arrowsField a
      let ⟨_, M, t⟩ := gridArgs2 (TensorField.identity arrowsField.base) arrowsField a
      return { fig := c.figure
               checks := withDump j? fun j =>
                 #[lengthscaleCheck (scaledLengthscale M t) (jfloat (jget j "lengthscale"))] ++
                 ptsChecks "origins" (Field.fiberPoints M) (jget j "origins") ++
                 ptsChecks "directions" (Field.fiberPoints t) (jget j "directions") },
  entry "cartan-scaledarrows-helix" "a helix coloured by speed with its unit tangents, scaled by the sample spacing"
    "`t = TensorField(0:0.1:4pi); M = Chain.(cos(t), sin(t), t/4); lines(M); scaledarrows!(M, T)` (`MakieExt.jl:371-379`)"
    fun j? => do
      let M := helixM (f64! 0.1)
      let T := helixT (f64! 0.1)
      let c := GrassmannPlot.lines M |>.scaledarrows (M, T)
      return { fig := c.figure (600, 500)
               checks := withDump j? fun j =>
                 #[lengthscaleCheck (scaledLengthscale M T) (jfloat (jget j "lengthscale")),
                   lengthscaleCheck (spacingOf M) (jfloat (jget j "spacing"))] ++
                 ptsChecks "origins" (Field.fiberPoints M) (jget j "origins") ++
                 ptsChecks "directions" (Field.fiberPoints T) (jget j "directions") },
  entry "cartan-arrowsbundle-helix" "arrowsbundle: the helix points with the arrows of ±T"
    "`t = TensorField(0:0.2:4pi); M = Chain.(cos(t), sin(t), t/4); arrowsbundle!(M, T)` (`MakieExt.jl:290-299`)"
    fun j? => do
      let M := helixM (f64! 0.2)
      let T := helixT (f64! 0.2)
      let c := (Canvas.fresh 3).plot .arrowsbundle (M, T)
      let ls := spacingOf M / meanNorm T / 2
      return { fig := c.figure (600, 500)
               checks := withDump j? fun j =>
                 let jl := (jarr (jget j "lengthscales")).map jfloat
                 #[eqCheck "arrow plots" 2 (jnat (jget j "narrows"))] ++
                 jl.map (lengthscaleCheck ls) ++
                 ptsChecks "points" (Field.fiberPoints M) (jget j "points") ++
                 ptsChecks "directions of +T" (Field.fiberPoints T) ((jarr (jget j "directions"))[0]!) ++
                 ptsChecks "directions of -T" (negPoints (Field.fiberPoints T)) ((jarr (jget j "directions"))[1]!) },
  entry "cartan-scaledarrows-frame" "scaledarrows of a two-column tangent frame on z = xy/4"
    "`S = (x -> Chain(x[1], x[2], x[1]*x[2]/4)).(p); F = TensorField(base(p), TensorOperator.(Chain.(c1, c2))); scaledarrows!(S, F)` (`MakieExt.jl:380-384`)"
    fun j? => do
      let c := (Canvas.fresh 3).scaledarrows (frameS, frameCols)
      let ls := spacingOf frameS / frameCols.foldl (fun m t => F64.max m (meanNorm t)) 0 / 3
      return { fig := c.figure (600, 500)
               checks := withDump j? fun j =>
                 let dirs := jarr (jget j "directions")
                 #[eqCheck "arrow plots" 2 (jnat (jget j "narrows"))] ++
                 ((jarr (jget j "lengthscales")).map jfloat).map (lengthscaleCheck ls) ++
                 ptsChecks "origins" (Field.fiberPoints frameS) (jget j "origins") ++
                 ptsChecks "column 1" (Field.fiberPoints frameCols[0]!) dirs[0]! ++
                 ptsChecks "column 2" (Field.fiberPoints frameCols[1]!) dirs[1]! },
  entry "cartan-linegraph-polar" "linegraph of the polar surface: every grid line coloured by its speed"
    "`fig = Figure(); Axis3(fig[1,1]); linegraph!(xyz)` (`MakieExt.jl:627-660`, the surface of `plot.md:242-252`)"
    fun j? => do
      let c := (Canvas.fresh 3).linegraph polar3
      return { fig := c.figure (600, 500), checks := withDump j? (linegraphChecks c) },
  entry "cartan-linegraph-polar-gridsize" "linegraph with gridsize = (5, 7): interpolated leaves"
    "`linegraph!(xyz, gridsize = (5, 7))` (`MakieExt.jl:631-638`, `Cartan.jl:737-803`)"
    fun j? => do
      let c := (Canvas.fresh 3).linegraph polar3 { gridsize := some #[5, 7] }
      return { fig := c.figure (600, 500), checks := withDump j? (linegraphChecks c) }]

end Gallery.CartanRecipes

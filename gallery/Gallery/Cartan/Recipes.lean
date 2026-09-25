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
                 ptsChecks "directions of -T" (negPoints (Field.fiberPoints T)) ((jarr (jget j "directions"))[1]!) }]

end Gallery.CartanRecipes

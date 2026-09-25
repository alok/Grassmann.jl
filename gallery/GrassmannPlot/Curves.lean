import GrassmannPlot.Makie

/-!
# Curves, graphs, point sets and meshes as points (`lines`, `linesegments`, `linegraph`,
`scatter`, `text`)

Cartan's methods for fields over 1-D grids and for simplex meshes (`ext/MakieExt.jl`):

| Julia | here |
|---|---|
| `lines(t::RealFunction, f = speed)` (`:173`) | the graph `(x, y)`, coloured by `speed` |
| `lines(t::PlaneCurve / SpaceCurve, f = speed)` (`:171-172`) | the fiber points, coloured by `speed` |
| `lines(t::ComplexMap{…,1}, f = speed)` (`:175-176`) | `(re, im)` (a complex fiber is a 2-D point) |
| `lines(t, f::TensorField)` | coloured by `f` (a pair `(t, f)`) |
| `lines(t::RectangleMap / HyperrectangleMap)` (`:162-163`) | `lines(boundarycomponents(t))` |
| `lines(p::SimplexBundle)` (`:618-619`) | the homogeneous points as one polyline |
| `linesegments(…)` | the same forms, drawn as segments |
| `linegraph(t::RealFunction)` (`:189-190`) | `lines(x, y)` in the palette colour |
| `linegraph(t::GradedField{…,1})` (`:191-206`) | one line per component |
| `linegraph(M::TensorField{…,2,GridBundle})` (`:627-797`) | the grid lines of `variation!`/`_alteration`, each coloured by its `speed` |
| `scatter(t::RealFunction)`, `scatter(t::TensorField)` (`:604-607`) | the graph, or the fiber points |
| `scatter(p::SimplexBundle / FaceBundle)`, `text(…)` (`:608-616`) | vertices / centroids, labelled by id |

`speed` is `GrassmannPlot.speed` (Cartan `speed`, `src/diffgeo.jl:544`); below four points Julia's
stencil throws and the curve is drawn in the palette colour instead.
-/

namespace GrassmannPlot

open LeanPlot Cartan MeshTopology

/-! ## 1-D grid fields -/

section Interval

variable {G F : Type} [FlatFiber F] {b : GridBundle 1 Float G}

/-- The plotted points of a field over a 1-D grid: the graph `(x, y)` of a real function
(`Real.(points(t)), Real.(fiber(t))`), the fiber points otherwise (`vec(fiber(t))`). -/
def curvePoints (t : TensorField b F) : Pts3 :=
  if FlatFiber.width F == 1 then graphOf b.space.coords[0] t.data else Field.fiberPoints t

/-- The `speed` colour values of a curve (`none` below four points). -/
def speedValues [LinearFiber F] [FiberNorm F] (t : TensorField b F) : Option FloatArray :=
  (speed t).map (·.data)

/-- The axis dimension of a field over a 1-D grid (a real function is drawn in 2-D). -/
@[inline] def curveDim (_ : TensorField b F) : Nat := dimOfWidth (FlatFiber.width F)

/-- Julia `lines(t::IntervalMap, f = speed)` (`MakieExt.jl:171-176`). -/
instance instLinesInterval [LinearFiber F] [FiberNorm F] : MakiePlot .lines (TensorField b F) where
  plot c t a := c.drawLines (curvePoints t) (a.colorOr (speedValues t)) a
  dim := curveDim

/-- Julia `lines(t, f::TensorField)`: coloured by the values of `f`. -/
instance instLinesIntervalBy : MakiePlot .lines (TensorField b F × TensorField b Float) where
  plot c tf a := c.drawLines (curvePoints tf.1) (a.colorOr (some tf.2.data)) a
  dim tf := curveDim tf.1

/-- Julia `linesegments(t::IntervalMap, f = speed)` (`MakieExt.jl:160-178`). -/
instance instSegmentsInterval [LinearFiber F] [FiberNorm F] : MakiePlot .linesegments (TensorField b F) where
  plot c t a := c.drawSegments (curvePoints t) (a.colorOr (speedValues t)) a
  dim := curveDim

/-- Julia `linesegments(t, f::TensorField)`. -/
instance instSegmentsIntervalBy : MakiePlot .linesegments (TensorField b F × TensorField b Float) where
  plot c tf a := c.drawSegments (curvePoints tf.1) (a.colorOr (some tf.2.data)) a
  dim tf := curveDim tf.1

/-- Julia `scatter(p::RealFunction) = scatter(points(p), fiber(p))` and
`scatter(p::TensorField) = scatter(vec(fiber(p)))` (`MakieExt.jl:604-607`). -/
instance instScatterInterval : MakiePlot .scatter (TensorField b F) where
  plot c t a := c.drawScatter (curvePoints t) a.color a
  dim := curveDim

/-- Julia `linegraph(t::RealFunction)` (`MakieExt.jl:189-190`) and
`linegraph(t::GradedField{G,B,F,1})` (`:191-206`): one line `(x, y_i)` per component, each in
the next palette colour. -/
instance instLinegraphInterval : MakiePlot .linegraph (TensorField b F) where
  plot c t a :=
    let x := b.space.coords[0]
    let w := FlatFiber.width F
    (List.range w).foldl (init := c) fun c k =>
      let y := buildFlat (F := Float) (card b) fun i => t.data.get! (i * w + k)
      c.drawLines (graphOf x y) a.color a
  dim _ := 2

end Interval

/-! ## Grid fields of dimension 2 and 3: boundary components -/

section Grid

variable {P G F : Type} [Inhabited G] [FlatFiber F] [LinearFiber F] [FiberNorm F]

/-- Julia `lines(t::RectangleMap) = lines(boundarycomponents(t))` (`MakieExt.jl:162`): the
four boundary curves, each coloured by its `speed`. -/
instance instLinesRect {b : GridBundle 2 P G} : MakiePlot .lines (TensorField b F) where
  plot c t a := c.plot .lines t.boundaryComponents a
  dim _ := dimOfWidth (FlatFiber.width F)

/-- Julia `lines(t::HyperrectangleMap) = lines(boundarycomponents(t))` (`MakieExt.jl:163`): the
six boundary faces, each drawn as its four boundary curves. -/
instance instLinesCube {b : GridBundle 3 P G} : MakiePlot .lines (TensorField b F) where
  plot c t a := c.plot .lines t.boundaryComponentsN a
  dim _ := dimOfWidth (FlatFiber.width F)

/-- Julia `linesegments(t::RectangleMap)`. -/
instance instSegmentsRect {b : GridBundle 2 P G} : MakiePlot .linesegments (TensorField b F) where
  plot c t a := c.plot .linesegments t.boundaryComponents a
  dim _ := dimOfWidth (FlatFiber.width F)

/-- Julia `linesegments(t::HyperrectangleMap)`. -/
instance instSegmentsCube {b : GridBundle 3 P G} : MakiePlot .linesegments (TensorField b F) where
  plot c t a := c.plot .linesegments t.boundaryComponentsN a
  dim _ := dimOfWidth (FlatFiber.width F)

end Grid

/-! ## Scatter of any field (`scatter(p::TensorField) = scatter(vec(fiber(p)))`) -/

/-- The points Makie makes of `vec(fiber(p))`: a real vector is plotted against its index
`1 … n`, point fibers as points. -/
def fiberScatterPoints {M F : Type} [FrameBundle M] {m : M} [FlatFiber F] (t : TensorField m F) : Pts3 :=
  if FlatFiber.width F == 1 then
    graphOf (buildFlat (F := Float) (card m) fun i => (i + 1).toUInt64.toFloat) t.data
  else Field.fiberPoints t

/-- Julia `scatter(p::TensorField) = scatter(vec(fiber(p)))` (`MakieExt.jl:606`) for fields over
any base (the 1-D grid method takes precedence). -/
instance (priority := low) instScatterField {M F : Type} [FrameBundle M] {m : M} [FlatFiber F] :
    MakiePlot .scatter (TensorField m F) where
  plot c t a := c.drawScatter (fiberScatterPoints t) a.color a
  dim _ := dimOfWidth (FlatFiber.width F)

/-! ## Simplex meshes -/

section Simplex

variable {n : Nat} {P G : Type} [FlatFiber P] [Inhabited G]

/-- Julia `submesh(m)` of a simplex bundle's points (`element.jl:380`): the coordinates after the
homogeneous `1`, as points. -/
def submeshPoints (m : SimplexBundle n P G) : Pts3 :=
  let w := FlatFiber.width P
  let flat := FrameBundle.pointsFlat (P := P) (G := G) m
  pointsOf (buildFlat (F := Float) (card m * (w - 1)) fun k =>
    flat.get! (k / (w - 1) * w + 1 + k % (w - 1))) (w - 1) (card m)

/-- Julia `lines(p::SimplexBundle) = lines(Vector(points(p)))` (`MakieExt.jl:618`): the
homogeneous points (leading `1` included) as one polyline. -/
instance instLinesSimplex : MakiePlot .lines (SimplexBundle n P G) where
  plot c m a := c.drawLines (pointsOf (FrameBundle.pointsFlat (P := P) (G := G) m) (FlatFiber.width P) (card m)) a.color a
  dim _ := dimOfWidth (FlatFiber.width P)

/-- Julia `scatter(p::SimplexBundle) = scatter(submesh(p))` (`MakieExt.jl:608`). -/
instance instScatterSimplex : MakiePlot .scatter (SimplexBundle n P G) where
  plot c m a := c.drawScatter (submeshPoints m) a.color a
  dim _ := dimOfWidth (FlatFiber.width P - 1)

/-- Julia `text(p::SimplexBundle; text = string.(vertices(p)))` (`MakieExt.jl:613`): each vertex
labelled by its (1-based) mesh id. -/
instance instTextSimplex : MakiePlot .text (SimplexBundle n P G) where
  plot c m _ := c.drawText (submeshPoints m) ((Array.range (card m)).map fun i => toString (m.image i))
  dim _ := dimOfWidth (FlatFiber.width P - 1)

variable [LinearFiber P]

/-- The element centroids of a face bundle without the homogeneous `1` (Julia
`submesh(fiber(means(p)))`). -/
def centroidPoints (m : FaceBundle n P G) : Pts3 :=
  let w := FlatFiber.width P
  let flat := FrameBundle.pointsFlat (P := P) (G := G) m
  pointsOf (buildFlat (F := Float) (card m * (w - 1)) fun k =>
    flat.get! (k / (w - 1) * w + 1 + k % (w - 1))) (w - 1) (card m)

/-- Julia `scatter(p::FaceBundle) = scatter(submesh(fiber(means(p))))` (`MakieExt.jl:610`). -/
instance instScatterFace : MakiePlot .scatter (FaceBundle n P G) where
  plot c m a := c.drawScatter (centroidPoints m) a.color a
  dim _ := dimOfWidth (FlatFiber.width P - 1)

/-- Julia `text(p::FaceBundle; text = string.(subelements(p)))` (`MakieExt.jl:615`): each
element labelled by its (1-based) element id at its centroid. -/
instance instTextFace : MakiePlot .text (FaceBundle n P G) where
  plot c m _ := c.drawText (centroidPoints m) ((Array.range (card m)).map fun e => toString (m.top.getFacet (e + 1)))
  dim _ := dimOfWidth (FlatFiber.width P - 1)

end Simplex

end GrassmannPlot

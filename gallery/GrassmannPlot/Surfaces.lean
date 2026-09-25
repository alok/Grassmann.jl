import GrassmannPlot.Curves

/-!
# Surfaces, meshes and scalar fields over grids (`mesh`, `wireframe`, `surface`, `contour`,
`contourf`, `contour3d`, `heatmap`, `linegraph` of 2-D and 3-D grid fields)

Cartan's methods (`ext/MakieExt.jl`, `ext/GeometryBasicsExt.jl`):

| Julia | here |
|---|---|
| `mesh(M::TensorField{…,<:Chain,2,<:GridBundle})` (`:826-831`) | the quad mesh of the fiber points (`GridBundle(fiber(M))`), triangles `(a,b,c), (a,c,d)`; shading iff the points are not 2-D |
| `mesh(M, f::TensorField)` (`:844-849`) | coloured by `f` |
| `mesh(M::TensorField{…,<:Chain,3,<:GridBundle})` (`:832-837`) | `mesh(boundarycomponents(M))` |
| `mesh(M::TensorField{…,<:Real,2,<:GridBundle})` (`:838-843`, broken upstream: B22) | the intended mesh of the base coloured by the values |
| `mesh(M::GridBundle)` (`:819`) | the quad mesh of the grid points |
| `mesh(M::SimplexBundle)`, `mesh(t::ScalarMap)` (`:854-874`) | the triangles of the mesh (coloured by the values) |
| `wireframe(M::TensorField{…,<:Chain,2,<:GridBundle})`, `wireframe(M::GridBundle)` (`:814-825`) | every quad's four edges |
| `wireframe(t::SurfaceGrid) = wireframe(graph(t))` (`:494-498`) | the same for the graph points |
| `wireframe(t::SimplexBundle) = linesegments(edges(t))` (`:810`) | the mesh edges |
| `surface(t::SurfaceGrid)` (`:454`) | Makie `surface(xs, ys, Z; color = Z)` |
| `surface(t::ComplexMap{…,2})` (`:456`) | `surface(xs, ys, abs.(z); color = angle.(z), colormap = :twilight)` |
| `surface(M::ScalarMap)` (`:876-885`) | the mesh lifted by the values |
| `contour`, `contourf`, `contour3d`, `heatmap` of a `SurfaceGrid` (`:480-482`) | Makie's recipe on `(xs, ys, Z)`; one plot per component for `Chain` fibers (`:484-491`); `abs` (contours) or `angle` with `:twilight` (heatmap) of complex fibers (`:468-478`) |
| `linegraph(M::TensorField{…,<:Chain,2,<:GridBundle}, f = speed)` (`:627-660`) | the grid lines of `variation!` then `_alteration`, each coloured by its own `speed`; with `gridsize = (n₁, n₂)` the resampled leaves (`leaf(v, x::AbstractFloat)`) |
| `linegraph(t::SurfaceGrid) = linegraph(graph(t))` (`:184`) | the same for the graph |
| `linegraph(v::TensorField{…,<:Chain,3,<:GridBundle})` (`:712-747`) | every axis-parallel line (the first one twice, as in Julia) |

Normals: Cartan passes `normal(m)` (a central difference of the embedding) to
`GeometryBasics.Mesh`; LeanPlot shades with the vertex normals of the triangles instead (the
images differ only in the shading; the plotted data are identical).
-/

namespace GrassmannPlot

open LeanPlot Cartan MeshTopology
open LeanPlot.Recipes.Algo

/-! ## Grid data -/

section GridData

variable {N : Nat} {P G F : Type} [FlatFiber F]

/-- The values of a real field over a 2-D grid as a Makie matrix `Z[i, j]` (`i ↔ x`). -/
def grid2 {b : GridBundle 2 P G} (vals : FloatArray) : Grid2 b.size[0] b.size[1] :=
  (Grid2.ofFloatArray? b.size[0] b.size[1] vals).getD default

/-- Component `k` of the fibers (width `w`) as a flat real array (Julia `getindex.(fiber(t), k+1)`). -/
def componentValues {M : Type} [FrameBundle M] {m : M} (t : TensorField m F) (k : Nat) : FloatArray :=
  let w := FlatFiber.width F
  buildFlat (F := Float) (card m) fun i => t.data.get! (i * w + k)

/-- The graph points `(x, y, f(x, y))` of a real field over a 2-D grid (Julia `graph(t)`). -/
def graphPoints2 {b : GridBundle 2 P G} (vals : FloatArray) : Pts3 :=
  let xs := b.space.coords[0]
  let ys := b.space.coords[1]
  let n0 := xs.size
  let n := card b
  Pts3.ofArrays (buildFlat (F := Float) n fun k => xs.get! (k % n0))
    (buildFlat (F := Float) n fun k => ys.get! (k / n0)) (vals.data.extract 0 n |> FloatArray.mk)

/-- The points of a 2-D grid (the fibers of the identity field). -/
def gridPoints2 (b : GridBundle 2 P G) : Pts3 :=
  let xs := b.space.coords[0]
  let ys := b.space.coords[1]
  let n0 := xs.size
  let n := card b
  Pts3.ofArrays (buildFlat (F := Float) n fun k => xs.get! (k % n0))
    (buildFlat (F := Float) n fun k => ys.get! (k / n0)) (FloatArray.mk (Array.replicate n 0))

/-- The plotted positions of a field over a 2-D grid: the fiber points, or the graph of a real
field. -/
def surfacePoints {b : GridBundle 2 P G} (t : TensorField b F) : Pts3 :=
  if FlatFiber.width F == 1 then graphPoints2 (b := b) t.data else Field.fiberPoints t

/-- The dimension of the plotted positions. -/
def surfaceDim {b : GridBundle 2 P G} (_ : TensorField b F) : Nat :=
  if FlatFiber.width F == 1 then 3 else dimOfWidth (FlatFiber.width F)

end GridData

/-! ## `mesh` -/

section Mesh

variable {P G F : Type} [Inhabited G] [FlatFiber F]

/-- Draw the quad mesh of a grid of positions (`GeometryBasics.Mesh(GridBundle(points))` with
`shading = mdims ≠ 2`, `MakieExt.jl:819`). -/
def drawGridMesh (c : Canvas) (nx ny : Nat) (pos : Pts3) (dim : Nat) (color : Option ColorSpec) (a : Attrs) : Canvas :=
  c.drawMesh (gridTriMesh nx ny pos) color (a.shading.getD (dim != 2)) a

/-- The mesh positions of a field over a 2-D grid: the fiber points (Julia
`GridBundle(fiber(M))`), or the grid points for a real field (the intended `mesh(base(M))` of
`MakieExt.jl:838-843`). -/
def meshPoints {b : GridBundle 2 P G} (t : TensorField b F) : Pts3 × Nat :=
  if FlatFiber.width F == 1 then (gridPoints2 b, 2) else (Field.fiberPoints t, dimOfWidth (FlatFiber.width F))

/-- Julia `mesh(M::TensorField{…,2,GridBundle})` (`MakieExt.jl:826-843`). -/
instance instMeshGrid {b : GridBundle 2 P G} : MakiePlot .mesh (TensorField b F) where
  plot c t a :=
    let (pos, d) := meshPoints t
    let col := if FlatFiber.width F == 1 then a.colorOr (some t.data) else a.color
    drawGridMesh c b.size[0] b.size[1] pos d col a
  dim t := (meshPoints t).2

/-- Julia `mesh(M::TensorField{…,<:Chain,2,<:GridBundle}, f::TensorField)` (`MakieExt.jl:844-849`):
coloured by `vec(fiber(Real(f)))`. -/
instance instMeshGridBy {b : GridBundle 2 P G} : MakiePlot .mesh (TensorField b F × TensorField b Float) where
  plot c tf a :=
    let (pos, d) := meshPoints tf.1
    drawGridMesh c b.size[0] b.size[1] pos d (a.colorOr (some tf.2.data)) a
  dim tf := (meshPoints tf.1).2

/-- Julia `mesh(M::TensorField{…,<:Chain,3,<:GridBundle}) = mesh(boundarycomponents(M))`
(`MakieExt.jl:832-837`). -/
instance instMeshCube {b : GridBundle 3 P G} : MakiePlot .mesh (TensorField b F) where
  plot c t a := c.plot .mesh t.boundaryComponentsN a
  dim _ := 3

/-- Julia `mesh(M::GridBundle)` (`MakieExt.jl:819`): the quad mesh of the grid's points. -/
instance instMeshGridBundle : MakiePlot .mesh (GridBundle 2 P G) where
  plot c b a := drawGridMesh c b.size[0] b.size[1] (gridPoints2 b) 2 a.color a
  dim _ := 2

variable {P : Type} [FlatFiber P]

/-- The full point cloud of a simplex mesh without the homogeneous `1` (Julia `submesh`). -/
def cloudPoints {n : Nat} (m : SimplexBundle n P G) : Pts3 :=
  let w := FlatFiber.width P
  let np := m.cloud.points.size / w
  pointsOf (buildFlat (F := Float) (np * (w - 1)) fun k =>
    m.cloud.points.get! (k / (w - 1) * w + 1 + k % (w - 1))) (w - 1) np

/-- The triangles of a simplex mesh as 0-based indices into its full point cloud (Julia
`array(immersion(M))`). -/
def simplexTriangles (m : SimplexBundle 3 P G) : Array UInt32 :=
  m.top.topology.foldl (init := #[]) fun acc e =>
    ((acc.push (e[0] - 1).toUInt32).push (e[1] - 1).toUInt32).push (e[2] - 1).toUInt32

/-- The triangle mesh of a simplex bundle. -/
def simplexMesh (m : SimplexBundle 3 P G) (pos : Pts3 := cloudPoints m) : TriMesh :=
  (TriMesh.mk? pos (simplexTriangles m)).getD default

/-- Julia `mesh(M::SimplexBundle) = mesh(submesh(M), array(immersion(M)))` (`MakieExt.jl:856-864`,
triangle meshes). -/
instance instMeshSimplex : MakiePlot .mesh (SimplexBundle 3 P G) where
  plot c m a := c.drawMesh (simplexMesh m) a.color (a.shading.getD (FlatFiber.width P - 1 != 2)) a
  dim _ := dimOfWidth (FlatFiber.width P - 1)

/-- The value of a simplex field at every point of the full cloud (Julia's nodal values; points
outside the field's vertices get `NaN`). -/
def cloudValues {b : SimplexBundle 3 P G} (t : TensorField b Float) : FloatArray :=
  let np := b.cloud.points.size / FlatFiber.width P
  buildFlat (F := Float) np fun v =>
    let j := b.top.vinv.get v
    if j == 0 then (0 : Float) / 0 else t.data.get! (j - 1)

/-- Julia `mesh(t::ScalarMap) = mesh(base(t); color = Real.(fiber(t)))` (`MakieExt.jl:854`). -/
instance instMeshScalarMap {b : SimplexBundle 3 P G} : MakiePlot .mesh (TensorField b Float) where
  plot c t a := c.drawMesh (simplexMesh b) (a.colorOr (some (cloudValues t)))
    (a.shading.getD (FlatFiber.width P - 1 != 2)) a
  dim _ := dimOfWidth (FlatFiber.width P - 1)

/-- Julia `surface(M::ScalarMap, f = identity)` (`MakieExt.jl:876-880`): the mesh with the values
as an extra coordinate, coloured by the values. -/
instance instSurfaceScalarMap {b : SimplexBundle 3 P G} : MakiePlot .surface (TensorField b Float) where
  plot c t a :=
    let base := cloudPoints b
    let vals := cloudValues t
    let pos := if FlatFiber.width P - 1 ≥ 3 then base else Pts3.ofArrays base.xs base.ys vals
    c.drawMesh (simplexMesh b pos) (a.colorOr (some vals)) (a.shading.getD true) a
  dim _ := 3

end Mesh

/-! ## `wireframe` -/

section Wireframe

variable {P G F : Type} [Inhabited G] [FlatFiber F]

/-- Julia `wireframe(M::TensorField{…,<:Chain,2,<:GridBundle})` and
`wireframe(t::SurfaceGrid) = wireframe(graph(t))` (`MakieExt.jl:494-498, 822-823`): the edges of
every quad of the plotted positions. -/
instance instWireframeGrid {b : GridBundle 2 P G} : MakiePlot .wireframe (TensorField b F) where
  plot c t a := c.drawSegments (gridWireframe b.size[0] b.size[1] (surfacePoints t)) a.color a
  dim := surfaceDim

/-- Julia `wireframe(M::TensorField{…,<:Chain,3,<:GridBundle}) = wireframe(boundarycomponents(M))`. -/
instance instWireframeCube {b : GridBundle 3 P G} : MakiePlot .wireframe (TensorField b F) where
  plot c t a := c.plot .wireframe t.boundaryComponentsN a
  dim _ := 3

/-- Julia `wireframe(M::GridBundle)` (`MakieExt.jl:814`). -/
instance instWireframeGridBundle : MakiePlot .wireframe (GridBundle 2 P G) where
  plot c b a := c.drawSegments (gridWireframe b.size[0] b.size[1] (gridPoints2 b)) a.color a
  dim _ := 2

variable {n : Nat} {P : Type} [FlatFiber P]

/-- Julia `wireframe(t::SimplexBundle) = linesegments(edges(t))` (`MakieExt.jl:810`, `:799-806`):
the segments between the (Euclidean) end points of every mesh edge. -/
instance instWireframeSimplex : MakiePlot .wireframe (SimplexBundle n P G) where
  plot c m a :=
    let pos := cloudPoints m
    let es := m.top.edges.topology
    let pt (v : Nat) : Vec3 := pos.get! (v - 1)
    let (xs, ys, zs) := es.foldl (init := (FloatArray.empty, FloatArray.empty, FloatArray.empty))
      fun (xs, ys, zs) e =>
        let p := pt e[0]
        let q := pt e[1]
        ((xs.push p.x).push q.x, (ys.push p.y).push q.y, (zs.push p.z).push q.z)
    c.drawSegments (Pts3.ofArrays xs ys zs) a.color a
  dim _ := dimOfWidth (FlatFiber.width P - 1)

end Wireframe

/-! ## `surface`, `contour`, `contourf`, `contour3d`, `heatmap` -/

section Scalar

variable {P G : Type} [Inhabited G]

/-- Makie `surface(xs, ys, Z; color)` (`surface2mesh`: `Z` in binary32, shaded). -/
def drawSurface {b : GridBundle 2 P G} (c : Canvas) (z : FloatArray) (color : FloatArray) (a : Attrs) : Canvas :=
  let sm := Surface.surfaceMesh b.space.coords[0] b.space.coords[1] (grid2 (b := b) z)
  c.drawMesh sm.mesh (some (a.color.getD (a.mapped color))) (a.shading.getD true) a

/-- Julia `surface(t::SurfaceGrid; color = fiber(Real(t)))` (`MakieExt.jl:454`). -/
instance instSurfaceGrid {b : GridBundle 2 P G} : MakiePlot .surface (TensorField b Float) where
  plot c t a := drawSurface (b := b) c t.data (Surface.surfaceMesh b.space.coords[0] b.space.coords[1] (grid2 (b := b) t.data)).values a
  dim _ := 3

/-- Julia `surface(t::SurfaceGrid, f::Function)` (`MakieExt.jl:455`) with the colour field given:
coloured by `abs.(f)`. -/
instance instSurfaceGridBy {b : GridBundle 2 P G} : MakiePlot .surface (TensorField b Float × TensorField b Float) where
  plot c tf a := drawSurface (b := b) c tf.1.data (FloatArray.mk (tf.2.data.data.map Float.abs)) a
  dim _ := 3

/-- Julia `surface(t::ComplexMap{…,2})` (`MakieExt.jl:456`): height `abs.(z)`, colour `angle.(z)`
through `:twilight`. -/
instance instSurfaceComplex {b : GridBundle 2 P G} : MakiePlot .surface (TensorField b (JuliaBase.Complex Float)) where
  plot c t a :=
    let z := t.fiberArray
    let abs := FloatArray.mk (z.map JuliaBase.ComplexF64.abs)
    let ang := FloatArray.mk (z.map JuliaBase.ComplexF64.angle)
    drawSurface (b := b) c abs ang { a with colormap := Colormap.named "twilight" }
  dim _ := 3

/-- Makie `contour!(xs, ys, Z)` / `contour3d!` data: the traced lines (binary32), the level of
every point, and the colour range (`computed_colorrange`, the data range). -/
def contourData {b : GridBundle 2 P G} (z : FloatArray) (a : Attrs) :
    Contour.Lines × (Float × Float) :=
  let g := grid2 (b := b) z
  let ls := Contour.makieContour (.rect b.space.coords[0] b.space.coords[1]) g (a.levels.getD (.count 5))
  let (lo, hi) := (Num.extremaFinite (Contour.roundGrid g).z).getD (0, 1)
  (ls, Contour.colorRange lo hi)

/-- The level value of every point of flattened contour lines (separators included). -/
def pointLevels (ls : Contour.Lines) (segs : Array (Nat × Nat)) : FloatArray :=
  segs.foldl (init := FloatArray.empty) fun acc (lvl, cnt) =>
    (List.range cnt).foldl (fun acc _ => acc.push (ls.levels.get! lvl)) acc

/-- Draw Makie's `contour` of one scalar grid (`linewidth = 1`, each line in its level's colour). -/
def drawContour {b : GridBundle 2 P G} (c : Canvas) (z : FloatArray) (lift3 : Bool) (a : Attrs) : Canvas :=
  let (ls, cr) := contourData (b := b) z a
  let (pts, segs) :=
    if lift3 then ls.flatten3d
    else let (p, s) := ls.flatten; (Pts3.ofArrays p.xs p.ys (FloatArray.mk (Array.replicate p.size 0)), s)
  let col := a.color.getD (.values (pointLevels ls segs) { a.mapping with colorrange := some (a.colorrange.getD cr) })
  c.drawLines pts (some col) { a with linewidth := some (a.lw 1) }

/-- The real grids plotted by the contour family for a field over a 2-D grid: the values, one
per `Chain` component (`MakieExt.jl:484-491`), `abs` of a complex fiber (`:468-473`). -/
class ScalarGrids (F : Type) [FlatFiber F] where
  /-- The real value arrays, one per plot. -/
  grids : {M : Type} → [FrameBundle M] → {m : M} → TensorField m F → Array FloatArray

instance : ScalarGrids Float := ⟨fun t => #[t.data]⟩

instance {V : DirectSum.TensorBundle} {Gr : Nat} : ScalarGrids (Grassmann.Chain V Gr Float) :=
  ⟨fun t => (Array.range (FlatFiber.width (Grassmann.Chain V Gr Float))).map (componentValues t)⟩

instance : ScalarGrids (JuliaBase.Complex Float) :=
  ⟨fun t => #[FloatArray.mk (t.fiberArray.map JuliaBase.ComplexF64.abs)]⟩

variable {F : Type} [FlatFiber F] [ScalarGrids F]

/-- Julia `contour(t::TensorField{…,2,RealSpace{2}})` (`MakieExt.jl:480-491`). -/
instance instContourGrid {b : GridBundle 2 P G} : MakiePlot .contour (TensorField b F) where
  plot c t a := (ScalarGrids.grids t).foldl (fun c z => drawContour (b := b) c z false a) c
  dim _ := 2

/-- Julia `contour3d(t::TensorField{…,2,RealSpace{2}})`: the isolines lifted to their levels. -/
instance instContour3dGrid {b : GridBundle 2 P G} : MakiePlot .contour3d (TensorField b F) where
  plot c t a := (ScalarGrids.grids t).foldl (fun c z => drawContour (b := b) c z true a) c
  dim _ := 3

/-- Draw Makie's `contourf` of one scalar grid (`levels = 10` bands, the banded colormap). -/
def drawContourf {b : GridBundle 2 P G} (c : Canvas) (z : FloatArray) (a : Attrs) : Canvas :=
  let cf := Isoband.makieContourf b.space.coords[0] b.space.coords[1] (grid2 (b := b) z) (a.levels.getD (.count 10))
  let bc := Isoband.bandColoring a.colormap cf.levels
  let cols := (Isoband.polygonColors bc cf).foldl RGBA.pushRGBA8 ByteArray.empty
  let join (outer : Pts2) (holes : Array Pts2) : Pts2 :=
    holes.foldl (init := outer) fun acc h =>
      Pts2.ofArrays ⟨(acc.xs.push Num.nan).data ++ h.xs.data⟩ ⟨(acc.ys.push Num.nan).data ++ h.ys.data⟩
  let rings := cf.polys.map fun p => join p.outer p.holes
  c.map2 fun ax => ax.add (.poly rings { color := a.color.getD (.perElement cols) }) a.label

/-- Julia `contourf(t::TensorField{…,2,RealSpace{2}})`. -/
instance instContourfGrid {b : GridBundle 2 P G} : MakiePlot .contourf (TensorField b F) where
  plot c t a := (ScalarGrids.grids t).foldl (fun c z => drawContourf (b := b) c z a) c
  dim _ := 2

/-- The real grids of `heatmap`: the values, one per component, or `angle` of a complex fiber
(`MakieExt.jl:475-478`, with `colormap = :twilight`). -/
class HeatGrids (F : Type) [FlatFiber F] where
  /-- The value arrays and the colormap override. -/
  grids : {M : Type} → [FrameBundle M] → {m : M} → TensorField m F → Array FloatArray × Option Colormap

instance : HeatGrids Float := ⟨fun t => (#[t.data], none)⟩

instance {V : DirectSum.TensorBundle} {Gr : Nat} : HeatGrids (Grassmann.Chain V Gr Float) :=
  ⟨fun t => ((Array.range (FlatFiber.width (Grassmann.Chain V Gr Float))).map (componentValues t), none)⟩

instance : HeatGrids (JuliaBase.Complex Float) :=
  ⟨fun t => (#[FloatArray.mk (t.fiberArray.map JuliaBase.ComplexF64.angle)], some (Colormap.named "twilight"))⟩

/-- Julia `heatmap(t::TensorField{…,2,RealSpace{2}}) = heatmap(points(t).v..., Real.(fiber(t)))`
(`MakieExt.jl:480-491`): the axis vectors are cell centres (Makie's `edges` rule). -/
instance instHeatmapGrid {F : Type} [FlatFiber F] [HeatGrids F] {b : GridBundle 2 P G} :
    MakiePlot .heatmap (TensorField b F) where
  plot c t a :=
    let (zs, cm) := HeatGrids.grids t
    let a := match cm with | some m => { a with colormap := m } | none => a
    zs.foldl (fun c z => c.drawHeatmap b.space.coords[0] b.space.coords[1] (grid2 (b := b) z) a) c
  dim _ := 2

end Scalar

/-! ## `linegraph` of grid fields -/

section Linegraph

variable {P G F : Type} [Inhabited G] [FlatFiber F] [LinearFiber F] [FiberNorm F]

/-- `lines!` of one leaf coloured by its `speed` (Julia `lines(leaf, speed)`). -/
def drawLeaf {Gl : Type} {bl : GridBundle 1 Float Gl} (c : Canvas) (l : TensorField bl F) (a : Attrs) : Canvas :=
  c.drawLines (curvePoints l) (a.colorOr (speedValues l)) a

/-- Julia `linegraph(M::TensorField{…,<:Chain,2,<:GridBundle}, f = speed)` (`MakieExt.jl:627-660`)
without `gridsize`: `variation!` draws the leaves `M[:, j]` for every `j`, `_alteration` then the
leaves `M[i, :]` for every `i`. -/
def linegraphGrid {b : GridBundle 2 P G} (c : Canvas) (t : TensorField b F) (a : Attrs) : Canvas :=
  let c := (List.range b.size[1]).foldl (fun c j => drawLeaf c (t.leaf j 1) a) c
  (List.range b.size[0]).foldl (fun c i => drawLeaf c (t.leaf i 0) a) c

/-- `linegraph` with `gridsize = (n₁, n₂)` (`MakieExt.jl:631-638`, `Cartan.jl:737-751, 794-803`):
`variation!(M, lines, lines!, n₁)` draws the leaf at the first index, the leaves at the interior
points of the last axis resampled to `n₁` points (interpolated between grid leaves), and the leaf
at the last index; `_alteration(…, n₂)` then draws the leaves at all `n₂` resampled points of the
first axis. -/
def linegraphGridResampled {b : GridBundle 2 P G} (c : Canvas) (t : TensorField b F) (n1 n2 : Nat)
    (a : Attrs) : Canvas :=
  let x := (b.space.axis 1).resample n1
  let c := drawLeaf c (t.leaf 0 1) a
  let c := (List.range (x.length - 2)).foldl (fun c i => drawLeaf c (t.leafInterp (x.get (i + 1)) 1) a) c
  let c := drawLeaf c (t.leaf (b.size[1] - 1) 1) a
  let y := (b.space.axis 0).resample n2
  (List.range y.length).foldl (fun c i => drawLeaf c (t.leafInterp (y.get i) 0) a) c

/-- Julia `linegraph(M::TensorField{…,<:Chain,2,<:GridBundle})`. -/
instance instLinegraphGrid {b : GridBundle 2 P G} : MakiePlot .linegraph (TensorField b F) where
  plot c t a :=
    match a.gridsize with
    | some gs => linegraphGridResampled c t (gs.getD 0 2) (gs.getD 1 2) { a with gridsize := none }
    | none => linegraphGrid c t a
  dim _ := dimOfWidth (FlatFiber.width F)

/-- Julia `linegraph(v::TensorField{…,<:Chain,3,<:GridBundle}, f = speed)` (`MakieExt.jl:712-747`):
the first line `leaf2(v,1,1,1)`, then every line along axis `k` for all positions of the two
other axes (`c = ((2,3),(1,3),(1,2))`), so the first line is drawn twice as in Julia. -/
instance instLinegraphCube {b : GridBundle 3 P G} : MakiePlot .linegraph (TensorField b F) where
  plot c t a :=
    let others : Fin 3 → Fin 3 × Fin 3 := fun k => if k.1 = 0 then (1, 2) else if k.1 = 1 then (0, 2) else (0, 1)
    let line (k : Fin 3) (i j : Nat) : Canvas → Canvas := fun c =>
      let (p, q) := others k
      let fixed : Vector Nat 3 := (Vector.replicate 3 0).set p i |>.set q j
      drawLeaf c (t.sliceLine k fixed) a
    let c := line 0 0 0 c
    (List.finRange 3).foldl (init := c) fun c k =>
      let (p, q) := others k
      (List.range b.size[p]).foldl (init := c) fun c i =>
        (List.range b.size[q]).foldl (init := c) fun c j => line k i j c
  dim _ := 3

end Linegraph

end GrassmannPlot

import FlowGeometry.Mesh

/-!
# Plot data

FlowGeometry.jl's Makie and UnicodePlots extensions (`ext/MakieExt.jl:19-42`,
`ext/UnicodePlotsExt.jl:19-40`) draw profiles and airfoils as lines; the gallery
(`docs/port-notes/plot-inventory.md` §6.6, W1-W4) also draws the wing surface and the Rakich mesh.
This module produces exactly the data those recipes plot, as packed coordinate arrays, so that a
plotting backend (the `gallery/` sub-package with LeanPlot) needs nothing else:

| Julia | here |
|---|---|
| `lines(N::Profile)` = `lines(profile(N))` | `Profile.series` |
| `lines(N::Airfoil)` = `lines(complex(N))` | `Airfoil.outlineSeries`, `Joukowski.outlineSeries` |
| `lines(N::DoubleArc)`: upper, mean line, lower | `Airfoil.doubleArcSeries` |
| UnicodePlots `lineplot(N::Airfoil)`: outline and camber `N.c` | `Airfoil.outlineSeries`, `Airfoil.camberSeries` |
| `mesh(wing(N))` | `wingGrid` |
| `wireframe(pt); linesegments!(pe)` of `initrakich()` | `Mesh.edgeSegments` |
-/

namespace FlowGeometry

open Cartan JuliaBase MeshTopology

/-- A polyline: `xs[i], ys[i]`. -/
structure Series where
  /-- abscissae -/
  xs : FloatArray
  /-- ordinates -/
  ys : FloatArray
  deriving Inhabited

/-- Julia `lines(profile(N))` (`ext/MakieExt.jl:19`): the samples over `interval(N)`. -/
def Profile.series (p : Profile) : Series := ⟨axisValues p.baseAxis, p.fieldData⟩

/-- Julia `lines(complex(N))` (`ext/MakieExt.jl:29`): the closed outline `(Re z, Im z)`, `2P-1`
points from the leading edge around and back. -/
def Airfoil.outlineSeries (a : Airfoil) : Series :=
  let z := a.outlineData
  ⟨reParts z, imParts z⟩

/-- The camber line that UnicodePlots overlays on an airfoil (`ext/UnicodePlotsExt.jl:23`,
`lineplot!(p, N.c)`): the camber profile's samples (`FlatPlate` for a `SymmetricArc`). -/
def Airfoil.camberSeries (a : Airfoil) : Series :=
  match a with
  | .symmetric s => ⟨axisValues s.baseAxis, floatsOfFn s.samples fun _ => 0⟩
  | _ => a.camber.series

/-- Julia `lines(N::DoubleArc)` (`ext/MakieExt.jl:31-36`): the upper surface, the mean line
`(Re U, (Im U + Im L)/2)` when both surfaces have as many samples, and the lower surface. -/
def Airfoil.doubleArcSeries (a : Airfoil) : Array Series :=
  let (u, l) := a.surfaces 1 0
  let (ux, uy, lx, ly) := (reParts u, imParts u, reParts l, imParts l)
  if uy.size == ly.size then
    #[⟨ux, uy⟩, ⟨ux, floatsOfFn uy.size fun i => (uy.get! i + ly.get! i) / 2⟩, ⟨lx, ly⟩]
  else #[⟨ux, uy⟩, ⟨lx, ly⟩]

/-- Julia `lines(complex(j))` of a Joukowski airfoil. -/
def Joukowski.outlineSeries (j : Joukowski) : Series :=
  let z := j.complexData
  ⟨reParts z, imParts z⟩

/-- The wing surface as three `np × (2np-1)` coordinate grids, column-major (Julia
`mesh(wing(N))`): `(rows, cols, x, y, z)`. -/
def wingGrid (a : Airfoil) (taper : Float := f64! 0.7) (σ : Float := f64! 0.5) :
    Nat × Nat × FloatArray × FloatArray × FloatArray :=
  let w := (wing a taper σ).data
  let n := w.size / 3
  let np := a.upperSamples
  (np, 2 * np - 1, floatsOfFn n fun k => w.get! (3 * k), floatsOfFn n fun k => w.get! (3 * k + 1),
    floatsOfFn n fun k => w.get! (3 * k + 2))

/-- The edges of a triangle or edge mesh over homogeneous `ℝ3` points as line segments
`(x₀, y₀, x₁, y₁)` (Julia `wireframe(pt)` / `linesegments!(pe)` of `initrakich()`); each triangle
contributes its three edges. -/
def Mesh.edgeSegments {n : Nat} (b : SimplexBundle n (Grassmann.Chain DirectSum.ℝ3 1 Float)) : FloatArray :=
  let pts := b.cloud.points
  let els := b.top.topology
  els.foldl (fun acc f =>
    let m := if n == 2 then 1 else n
    (List.range m).foldl (fun acc k =>
      let a := f[k]!
      let c := f[(k + 1) % n]!
      (((acc.push (pts.get! (3 * (a - 1) + 1))).push (pts.get! (3 * (a - 1) + 2))).push
        (pts.get! (3 * (c - 1) + 1))).push (pts.get! (3 * (c - 1) + 2))) acc) .empty

end FlowGeometry

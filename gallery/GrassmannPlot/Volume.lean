import GrassmannPlot.Stream

/-!
# Volume grids: `voxels`

Cartan's `voxels(t::VolumeGrid)` (`ext/MakieExt.jl:443-448`) is Makie's
`voxels(x₀..x₁, y₀..y₁, z₀..z₁, Real.(fiber(resample(t))))`: the values of the grid (resampled
onto a uniform grid of the same size) in a box spanned by the end points of the axes. The voxel
ids, colormap and cube placement are LeanPlot's port of Makie's recipe and CairoMakie's drawing
(`Recipes.Algo.Voxels`); each non-air voxel is drawn as a shaded cube of size `step - gap`.

`volume` and `contour` of a volume grid (Makie's ray-marched renderings) have no LeanPlot mark
yet (docs/parity-gaps.json, LeanPlot `volume`).
-/

namespace GrassmannPlot

open LeanPlot Cartan
open LeanPlot.Recipes.Algo

/-- The cubes of the voxels (`Voxels.voxelCubes`) as one triangle mesh with a colour per vertex. -/
def voxelMesh (chunk : Voxels.Chunk) (o : Voxels.Options) (cm : Colormap) : TriMesh × ByteArray := Id.run do
  let (pos, cols) := Voxels.voxelCubes chunk o cm
  let sz := Voxels.voxelSize chunk o
  let cube := Voxels.cubeMarker
  let mut xs : FloatArray := .empty
  let mut ys : FloatArray := .empty
  let mut zs : FloatArray := .empty
  let mut rgba : ByteArray := .empty
  let mut tri : Array UInt32 := #[]
  for i in [0:pos.size] do
    let p := pos.get! i
    let base := xs.size.toUInt32
    for k in [0:cube.mesh.pos.size] do
      let v := cube.mesh.pos.get! k
      xs := xs.push (p.x + sz.x * v.x); ys := ys.push (p.y + sz.y * v.y); zs := zs.push (p.z + sz.z * v.z)
      rgba := RGBA.pushRGBA8 rgba (cols.getD i RGBA.transparent)
    tri := tri ++ cube.mesh.tri.map (· + base)
  return ((TriMesh.mk? (Pts3.ofArrays xs ys zs) tri).getD default, rgba)

/-- Julia `voxels(t::VolumeGrid)` (`MakieExt.jl:443-448`). -/
instance instVoxelsGrid {P G : Type} [Inhabited G] {b : GridBundle 3 P G} : MakiePlot .voxels (TensorField b Float) where
  plot c t a :=
    let r := t.resample b.size
    let ends (i : Fin 3) : Float × Float := ((b.space.axis i).first, (b.space.axis i).last)
    let chunk := Voxels.Chunk.withExtent b.size[0] b.size[1] b.size[2] r.data (ends 0) (ends 1) (ends 2)
    let o : Voxels.Options := { colorrange := a.colorrange, scale := a.colorscale, gap := a.gap
                                lowclip := a.lowclip, highclip := a.highclip }
    let (m, rgba) := voxelMesh chunk o a.colormap
    c.drawMesh m (some (a.color.getD (.perElement rgba))) (a.shading.getD true) a
  dim _ := 3

end GrassmannPlot

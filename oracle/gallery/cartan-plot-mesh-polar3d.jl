# Cartan.jl docs/src/plot.md:242-252 (Makie's mesh example on a TensorField):
#   rs = 1:10; thetas = 0:10:360
#   xs = rs .* cosd.(thetas'); ys = rs .* sind.(thetas'); zs = sin.(rs) .* cosd.(thetas')
#   xyz = TensorField(ProductSpace(rs,thetas),Chain.(xs,ys,zs))
#   mesh(xyz,TensorField(xyz,zs))
# `mesh(M, f)` is the quad mesh of `GridBundle(fiber(M))` coloured by `f` (ext/MakieExt.jl:844);
# an Axis3 replaces the LScene so the Lean render is comparable.
include("cartan_common.jl")
rs = 1:10
thetas = 0:10:360
xs = rs .* cosd.(thetas')
ys = rs .* sind.(thetas')
zs = sin.(rs) .* cosd.(thetas')
xyz = TensorField(ProductSpace(rs,thetas),Chain.(xs,ys,zs))
fig, ax, pl = mesh(xyz,TensorField(xyz,zs); axis = (type = Axis3,))
m = pl[1][]
dumpdata("cartan-plot-mesh-polar3d", Dict("vertices" => pts_summary(Makie.GeometryBasics.coordinates(m)),
    "faces" => length(Makie.GeometryBasics.faces(m)), "color" => color_summary(pl.color[]), "shading" => string(pl.shading[])))
savefig("cartan-plot-mesh-polar3d", fig)

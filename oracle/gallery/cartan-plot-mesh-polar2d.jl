# Cartan.jl docs/src/plot.md:253-256 (Makie's mesh example on a TensorField, 2-D positions):
#   xy = TensorField(ProductSpace(rs,thetas),Chain.(xs,ys))
#   mesh(xy,TensorField(xy,zs))
include("cartan_common.jl")
rs = 1:10
thetas = 0:10:360
xs = rs .* cosd.(thetas')
ys = rs .* sind.(thetas')
zs = sin.(rs) .* cosd.(thetas')
xy = TensorField(ProductSpace(rs,thetas),Chain.(xs,ys))
fig, ax, pl = mesh(xy,TensorField(xy,zs))
m = pl[1][]
dumpdata("cartan-plot-mesh-polar2d", Dict("vertices" => pts_summary(Makie.GeometryBasics.coordinates(m)),
    "faces" => length(Makie.GeometryBasics.faces(m)), "color" => color_summary(pl.color[]), "shading" => string(pl.shading[])))
savefig("cartan-plot-mesh-polar2d", fig)

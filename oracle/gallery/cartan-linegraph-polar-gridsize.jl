# Cartan `linegraph!(M; gridsize = (5, 7))` (ext/MakieExt.jl:631-638) of the plot.md polar
# surface: `variation!` draws 5 leaves at the last axis resampled to 5 points (interior leaves
# interpolated), `_alteration` 7 leaves at the first axis resampled to 7 points.
include("cartan_common.jl")
rs = 1:10
thetas = 0:10:360
xs = rs .* cosd.(thetas')
ys = rs .* sind.(thetas')
zs = sin.(rs) .* cosd.(thetas')
xyz = TensorField(ProductSpace(rs,thetas),Chain.(xs,ys,zs))
fig = Figure(size = (600, 500))
ax = Axis3(fig[1, 1])
linegraph!(xyz, gridsize = (5, 7))
ls = [p for p in ax.scene.plots if p isa Lines]
dumpdata("cartan-linegraph-polar-gridsize", Dict("lines" => length(ls), "points" => [length(p[1][]) for p in ls],
    "speed" => summary_of(reduce(vcat, [Float64.(p.color[]) for p in ls]), 7),
    "coords" => pts_summary(reduce(vcat, [p[1][] for p in ls]); k = 7)))
savefig("cartan-linegraph-polar-gridsize", fig)

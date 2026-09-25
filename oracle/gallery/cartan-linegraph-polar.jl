# Cartan `linegraph!(M)` (ext/MakieExt.jl:627-660) of the plot.md:242-252 polar surface:
# `variation!` draws the 37 leaves M[:, j], `_alteration` the 10 leaves M[i, :], each coloured by
# its own `speed`. `linegraph!` on an Axis3 (the non-mutating form opens an LScene).
include("cartan_common.jl")
rs = 1:10
thetas = 0:10:360
xs = rs .* cosd.(thetas')
ys = rs .* sind.(thetas')
zs = sin.(rs) .* cosd.(thetas')
xyz = TensorField(ProductSpace(rs,thetas),Chain.(xs,ys,zs))
fig = Figure(size = (600, 500))
ax = Axis3(fig[1, 1])
linegraph!(xyz)
ls = [p for p in ax.scene.plots if p isa Lines]
dumpdata("cartan-linegraph-polar", Dict("lines" => length(ls), "points" => [length(p[1][]) for p in ls],
    "speed" => summary_of(reduce(vcat, [Float64.(p.color[]) for p in ls]), 13),
    "coords" => pts_summary(reduce(vcat, [p[1][] for p in ls]); k = 13)))
savefig("cartan-linegraph-polar", fig)

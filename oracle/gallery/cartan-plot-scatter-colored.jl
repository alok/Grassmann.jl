# Cartan.jl docs/src/plot.md:273-280 (Makie's scatter example with colours and sizes):
#   pts = TensorField(xs,Chain.(xs, ys))
#   scatter(pts, color = 1:30, markersize = range(5, 30, length = 30), colormap = :thermal)
include("cartan_common.jl")
xs = range(0, 10, length = 30)
ys = 0.5 .* sin.(xs)
pts = TensorField(xs,Chain.(xs, ys))
fig, ax, pl = scatter(pts, color = 1:30, markersize = range(5, 30, length = 30), colormap = :thermal)
dumpdata("cartan-plot-scatter-colored", Dict("points" => pts_summary(pl[1][]), "color" => color_summary(pl.color[]),
    "markersize" => summary_of([Float64(first(m)) for m in pl.markersize[]], 1)))
savefig("cartan-plot-scatter-colored", fig)

# Cartan.jl docs/src/plot.md:190-201 (Makie's heatmap example with a colorbar):
#   xs = range(0, 2π, length=100); ys = range(0, 2π, length=100)
#   zs = [sin(x*y) for x in xs, y in ys]
#   xyz = TensorField(OpenParameter(xs,ys),zs)
#   fig, ax, hm = heatmap(xyz)
#   Colorbar(fig[:, end+1], hm)
include("cartan_common.jl")
xs = range(0, 2π, length=100)
ys = range(0, 2π, length=100)
zs = [sin(x*y) for x in xs, y in ys]
xyz = TensorField(OpenParameter(xs,ys),zs)
fig, ax, hm = heatmap(xyz)
Colorbar(fig[:, end+1], hm)
dumpdata("cartan-plot-heatmap-colorbar", Dict("x" => summary_of(collect(hm[1][]), 1), "y" => summary_of(collect(hm[2][]), 1),
    "z" => summary_of(vec(hm[3][]), 7)))
savefig("cartan-plot-heatmap-colorbar", fig)

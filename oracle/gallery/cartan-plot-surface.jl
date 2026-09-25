# Cartan.jl docs/src/plot.md:319-327 (Makie's surface example on a TensorField):
#   xs = LinRange(0, 10, 100); ys = LinRange(0, 15, 100)
#   zs = [cos(x) * sin(y) for x in xs, y in ys]
#   xyz = TensorField(OpenParameter(xs,ys),zs)
#   surface(xyz, axis=(type=Axis3,))
include("cartan_common.jl")
xs = LinRange(0, 10, 100)
ys = LinRange(0, 15, 100)
zs = [cos(x) * sin(y) for x in xs, y in ys]
xyz = TensorField(OpenParameter(xs,ys),zs)
fig, ax, pl = surface(xyz, axis=(type=Axis3,))
dumpdata("cartan-plot-surface", Dict("x" => summary_of(collect(pl[1][]), 1), "y" => summary_of(collect(pl[2][]), 1),
    "z" => summary_of(vec(pl[3][]), 7), "color" => color_summary(pl.color[]; k = 7)))
savefig("cartan-plot-surface", fig)

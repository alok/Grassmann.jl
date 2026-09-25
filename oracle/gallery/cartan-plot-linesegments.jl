# Cartan.jl docs/src/plot.md:224-236 (Makie's linesegments example on a TensorField):
#   f = Figure(); Axis(f[1, 1])
#   xs = TensorField(1:0.2:10); ys = sin(xs)
#   linesegments!(ys)
#   linesegments!(ys - 1, linewidth = 5)
#   linesegments!(ys - 2, linewidth = 5, color = LinRange(1, 5, length(xs)))
# Cartan's `linesegments` of a real function colours it by `speed` (ext/MakieExt.jl:173).
include("cartan_common.jl")
f = Figure()
Axis(f[1, 1])
xs = TensorField(1:0.2:10)
ys = sin(xs)
p1 = linesegments!(ys)
p2 = linesegments!(ys - 1, linewidth = 5)
p3 = linesegments!(ys - 2, linewidth = 5, color = LinRange(1, 5, length(xs)))
dumpdata("cartan-plot-linesegments", Dict("plots" => [Dict("points" => pts_summary(p[1][]), "color" => color_summary(p.color[]),
    "linewidth" => p.linewidth[]) for p in (p1, p2, p3)]))
savefig("cartan-plot-linesegments", f)

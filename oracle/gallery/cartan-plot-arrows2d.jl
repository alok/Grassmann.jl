# Cartan.jl docs/src/plot.md:15-28 (Makie's arrows example on a TensorField):
#   f = Figure(size = (800, 800))
#   Axis(f[1, 1], backgroundcolor = "black")
#   xs = LinRange(0, 2pi, 20); ys = LinRange(0, 3pi, 20)
#   us = [sin(x) * cos(y) for x in xs, y in ys]; vs = [-cos(x) * sin(y) for x in xs, y in ys]
#   xy = TensorField(OpenParameter(xs,ys),Chain.(us,vs))
#   strength = vec(fiber(norm(xy)))
#   arrows2d!(xy, lengthscale = 0.2, color = strength)
include("cartan_common.jl")
f = Figure(size = (800, 800))
Axis(f[1, 1], backgroundcolor = "black")
xs = LinRange(0, 2pi, 20)
ys = LinRange(0, 3pi, 20)
us = [sin(x) * cos(y) for x in xs, y in ys]
vs = [-cos(x) * sin(y) for x in xs, y in ys]
xy = TensorField(OpenParameter(xs,ys),Chain.(us,vs))
strength = vec(fiber(norm(xy)))
pl = arrows2d!(xy, lengthscale = 0.2, color = strength)
dumpdata("cartan-plot-arrows2d", Dict("origins" => pts_summary(pl[1][]), "directions" => pts_summary(pl[2][]),
    "color" => color_summary(pl.color[]), "lengthscale" => pl.lengthscale[]))
savefig("cartan-plot-arrows2d", f)

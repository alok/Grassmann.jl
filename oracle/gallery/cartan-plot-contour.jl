# Cartan.jl docs/src/plot.md:52-65 (Makie's contour example on a TensorField):
#   f = Figure(); Axis(f[1, 1])
#   xs = LinRange(0, 10, 100); ys = LinRange(0, 15, 100)
#   zs = [cos(x) * sin(y) for x in xs, y in ys]
#   xyz = TensorField(OpenParameter(xs,ys),zs)
#   contour!(xyz); contour!(xyz,levels=-1:0.1:1)
include("cartan_common.jl")
f = Figure()
ax = Axis(f[1, 1])
xs = LinRange(0, 10, 100)
ys = LinRange(0, 15, 100)
zs = [cos(x) * sin(y) for x in xs, y in ys]
xyz = TensorField(OpenParameter(xs,ys),zs)
p1 = contour!(xyz)
p2 = contour!(xyz,levels=-1:0.1:1)
lines_of(p) = first(c for c in p.plots if c isa Lines)[1][]
dumpdata("cartan-plot-contour", Dict("contours" => [lines_moments(lines_of(p)) for p in (p1, p2)]))
savefig("cartan-plot-contour", f)

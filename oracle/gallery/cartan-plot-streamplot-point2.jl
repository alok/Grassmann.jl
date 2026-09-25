# Cartan.jl docs/src/plot.md:290-293 (Makie's streamplot example, a plain function):
#   v(x::Point2{T}) where T = Point2f(x[2], 4*x[1])
#   streamplot(v, -2..2, -2..2)
include("cartan_common.jl")
v(x::Point2{T}) where T = Point2f(x[2], 4*x[1])
dump_stream("cartan-plot-streamplot-point2", v, Rect2d(-2, -2, 4, 4), (32, 32))
fig, ax, pl = streamplot(v, -2..2, -2..2)
savefig("cartan-plot-streamplot-point2", fig)

# Cartan.jl docs/src/plot.md:311-313 (the FitzHugh-Nagumo streamplot with a colour function):
#   streamplot(fun.(xy), color=(p)-> RGBAf(p..., 0.0, 1))
# The colour of a line point is `RGBAf(u, v, 0, 1)` of the field value `(u, v)` (Makie's
# `streamplot_impl` colour callback); the dump records the red and green channels.
include("cartan_common.jl")
struct FitzhughNagumo{T}
    e::T
    s::T
    y::T
    b::T
end
P = FitzhughNagumo(0.1, 0.0, 1.5, 0.8)
fun(x) = fun(x, P)
fun(x, P::FitzhughNagumo) = Chain(
    (x[1]-x[2]-x[1]^3+P.s)/P.e,
    P.y*x[1]-x[2] + P.b)
xy = OpenParameter(-1.5:0.1:1.5,-1.5:0.1:1.5)
tf = fun.(xy)
colorfn = (p)-> RGBAf(p..., 0.0, 1)
name = "cartan-plot-streamplot-colorfunction"
dump_stream(name, p -> Makie.Point(tf(Chain(p.data...))), Rect2d(-1.5, -1.5, 3.0, 3.0), (32, 32))
ap, ad, lp, ac, lc = Makie.streamplot_impl(Point, p -> Makie.Point(tf(Chain(p.data...))), Rect2d(-1.5, -1.5, 3.0, 3.0), (32, 32), 0.01, 500, 1.0, colorfn)
d = JSON.parsefile(joinpath(JULIA_DATA, name * ".json"))
d["line_red"] = summary_of([Float64(c.r) for c in lc], 4); d["line_green"] = summary_of([Float64(c.g) for c in lc], 4)
dumpdata(name, d)
fig, ax, pl = streamplot(tf, color = colorfn)
savefig(name, fig)

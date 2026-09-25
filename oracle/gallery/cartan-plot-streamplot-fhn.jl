# Cartan.jl docs/src/plot.md:294-310 (Makie's FitzHugh-Nagumo streamplot on a TensorField):
#   struct FitzhughNagumo{T}; e::T; s::T; y::T; b::T; end
#   P = FitzhughNagumo(0.1, 0.0, 1.5, 0.8)
#   fun(x) = fun(x, P)
#   fun(x, P::FitzhughNagumo) = Chain((x[1]-x[2]-x[1]^3+P.s)/P.e, P.y*x[1]-x[2] + P.b)
#   xy = OpenParameter(-1.5:0.1:1.5,-1.5:0.1:1.5)
#   fig, ax, pl = streamplot(fun.(xy), colormap = :magma)
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
field_stream("cartan-plot-streamplot-fhn", fun.(xy), (32, 32); colormap = :magma)

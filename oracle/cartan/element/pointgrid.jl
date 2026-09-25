# Goldens for fields over grids of explicit points (Cartan.jl src/Cartan.jl:109-115, 159; C2, C6):
# `TensorField(fiber(s))` of a surface `s`, a map over it, and `TensorField(a, b)` with a 2-D `a`.
#
#   julia --startup-file=no --project=oracle oracle/cartan/element/pointgrid.jl
#
# Writes oracle/golden/cartan/element/pointgrid.json.
include(joinpath(@__DIR__, "common.jl"))
using Grassmann, Cartan

flat(xs) = reduce(vcat, [x isa Real ? [Float64(x)] : collect(Float64, value(x)) for x in vec(collect(xs))];
    init = Float64[])

# a bumped sheet: Chain(x, y, x y + sin 2y) over 5 × 7 points
s = (p -> Chain(p[1], p[2], p[1] * p[2] + sin(2p[2]))).(TensorField(ProductSpace(0:0.25:1, 0:0.5:3)))
g = TensorField(fiber(s))
h = (x -> x[1] + x[2] * x[3]).(g)
r = TensorField(s, (p -> p[1] - p[2]).(TensorField(ProductSpace(0:0.25:1, 0:0.5:3))))
out = Dict{String,Any}(
    "size" => collect(size(g)),
    "points" => hxs(flat(points(g))),
    "h" => hxs(flat(fiber(h))),
    "r_points" => hxs(flat(points(r))),
    "r_fiber" => hxs(flat(fiber(r))))
save("pointgrid", out)

# Goldens for Cartan's fields of leaves (Cartan.jl src/Cartan.jl:663-681): Variation(t),
# alteration(t) and modification(t) of a 2-D field: the leaves along the last, first and second
# axis, as a field over that axis.
#
#   julia --startup-file=no --project=oracle oracle/cartan/element/variation.jl
#
# Writes oracle/golden/cartan/element/variation.json: per field of leaves its base points and, per
# leaf, the leaf's base points and fibers.
include(joinpath(@__DIR__, "common.jl"))
using Grassmann, Cartan

leaves(v) = Dict("base" => hxs(collect(Float64, points(v))),
    "leaves" => [Dict("base" => hxs(collect(Float64, points(l))), "fiber" => hxs(collect(Float64, fiber(l))))
        for l in fiber(v)])

aa = (x -> x[1] + 10x[2] + x[1] * x[2]).(TensorField(ProductSpace(0:1.0:3, 0:0.5:1)))
out = Dict{String,Any}()
out["variation"] = @safe leaves(Variation(aa))
out["alteration"] = @safe leaves(alteration(aa))
out["modification"] = @safe leaves(modification(aa))
save("variation", out)

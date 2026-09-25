# Goldens for operator-, couple- and phasor-valued fields (Cartan.jl src/Cartan.jl:136-142,
# 401-449): EndomorphismField, DiagonalField, OutermorphismField, ComplexMap, PhasorField.
#
#   julia --startup-file=no --project=oracle oracle/cartan/element/operators.jl
#
# Writes oracle/golden/cartan/element/operators.json. The fields live over TensorField(0:0.25:1).
# Flat layouts (the Lean FlatFiber encodings of Cartan/Operator.lean): an operator is its
# column-major matrix, an outermorphism its compound blocks Λ¹…Λᵏ, a Couple (blade, re, im) with
# the blade mask as a float, a Phasor (amplitude, blade, 0, θ), a complex Chain (re, im) per entry.
include(joinpath(@__DIR__, "common.jl"))
using Grassmann, Cartan, LinearAlgebra

xs = collect(0:0.25:1)
t = TensorField(0:0.25:1)
V = Submanifold(ℝ^2); B = V(1, 2)

opmat(T) = reduce(vcat, [collect(value(c)) for c in value(value(T))])   # column-major entries
blockflat(O) = reduce(vcat, [opmat(TensorOperator(O[g])) for g in 1:length(O.v)])

E = (x -> TensorOperator(Chain(Chain(1 + x, x^2), Chain(-x, 2.0)))).(t)
D = (x -> DiagonalOperator(Chain(1 + x, 2x))).(t)
O = (x -> outermorphism(TensorOperator(Chain(Chain(1 + x, x^2), Chain(-x, 2.0))))).(t)
C = TensorField(t, [Couple{V,B}(cos(x), sin(x)) for x in xs])
P = polarize(C)
Z = TensorField(t, [complex(x, 2x) for x in xs])
E3 = TensorField(t, [TensorOperator(Chain(Chain(0.0, 1.0), Chain(-1.0, x))) for x in xs])

out = Dict{String,Any}(
    "meta" => Dict("julia" => string(VERSION), "cartan" => string(pkgversion(Cartan)),
        "grassmann" => string(pkgversion(Grassmann))),
    "xs" => hxs(xs),
    "E" => hxs(reduce(vcat, map(opmat, fiber(E)))),
    "detE" => hxs([value(x)[1] for x in fiber(det(E))]),
    "trE" => hxs(fiber(tr(E))),
    "transposeE" => hxs(reduce(vcat, map(opmat, fiber(transpose(E))))),
    "invE" => hxs(reduce(vcat, map(opmat, fiber(inv(E))))),
    "diagE" => hxs(reduce(vcat, [collect(value(value(d))) for d in fiber(DiagonalOperator(E))])),
    "eigE" => hxc(reduce(vcat, [complex.(collect(value(c))) for c in fiber(eigvals(E))])),
    "eigE3" => hxc(reduce(vcat, [complex.(collect(value(c))) for c in fiber(eigvals(E3))])),
    "D" => hxs(reduce(vcat, [collect(value(value(d))) for d in fiber(D)])),
    "detD" => hxs([value(x)[1] for x in fiber(det(D))]),
    "trD" => hxs(fiber(tr(D))),
    "O" => hxs(reduce(vcat, map(blockflat, fiber(O)))),
    "detO" => hxs([value(x)[1] for x in fiber(det(O))]),
    "trO" => hxs(fiber(tr(O))),
    "C" => hxs(reduce(vcat, [[Float64(UInt(B)), realvalue(z), imagvalue(z)] for z in fiber(C)])),
    "polarize" => hxs(reduce(vcat, [[amplitude(p), Float64(UInt(B)), 0.0, value(angle(p))] for p in fiber(P)])),
    "complexify" => hxs(reduce(vcat, [[realvalue(z), imagvalue(z)] for z in fiber(complexify(P))])),
    "vectorize" => hxs(reduce(vcat, [collect(value(c)) for c in fiber(vectorize(C))])),
    "radius" => hxs(fiber(radius(C))),
    "angle" => hxs(value.(fiber(angle(C)))),
    "realvalue" => hxs(fiber(realvalue(C))),
    "imagvalue" => hxs(fiber(imagvalue(C))),
    "amplitude" => hxs(fiber(amplitude(P))),
    "vectorizeZ" => hxs(reduce(vcat, [collect(value(c)) for c in fiber(vectorize(Z))])),
    "show" => Dict("E2" => sprint(show, fiber(E)[2]), "C2" => sprint(show, fiber(C)[2]),
        "P2" => sprint(show, fiber(P)[2]), "O2" => sprint(show, fiber(O)[2]),
        "D2" => sprint(show, fiber(D)[2])),
)
save("operators", out)

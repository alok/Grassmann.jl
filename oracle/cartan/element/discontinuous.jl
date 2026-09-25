# Goldens for discontinuous simplex bundles and Crouzeix-Raviart interpolation (Cartan.jl
# src/element.jl:561-588, src/Cartan.jl:601-605, MeshTopology's DiscontinuousTopology).
#
#   julia --startup-file=no --project=oracle oracle/cartan/element/discontinuous.jl
#
# Writes oracle/golden/cartan/element/discontinuous.json. The shim is fem.jl's (MeshTopology's
# missing imports, defect B1).
include(joinpath(@__DIR__, "common.jl"))
using Grassmann, Cartan, LinearAlgebra, SparseArrays
import MeshTopology
using MeshTopology: topology, vertices, totalnodes, subelements
@eval MeshTopology begin
    const Grassmann = Main.Grassmann; const Leibniz = Main.Grassmann.Leibniz
    const ∂ = Main.Grassmann.∂; const Submanifold = Main.Grassmann.Submanifold
    const Variables = Main.Grassmann.Variables
    fiber(x) = Main.Cartan.fiber(x); means(a...) = Main.Cartan.means(a...)
end
@eval MeshTopology fibertype(x::AbstractArray) = eltype(x)
@eval MeshTopology fibertype(x::$(Cartan.TensorField)) = $(Cartan.fibertype)(x)

ints(xs) = [collect(Int, x) for x in xs]
function mkmesh(pts, els)
    d = length(pts[1])
    V = Cartan.varmanifold(d + 1)
    p = PointCloud([Chain{V,1}(1.0, x...) for x in pts])
    p(SimplexTopology([Values(e...) for e in els], length(pts)))
end

"A structured `a × b` triangulation of the unit square (node k = i + (a+1) j, 0-based)."
function gridmesh(a, b)
    pts = [[i / a, j / b] for j in 0:b for i in 0:a]
    node(i, j) = 1 + i + (a + 1) * j
    els = Vector{Vector{Int}}()
    for j in 0:b-1, i in 0:a-1
        push!(els, [node(i, j), node(i + 1, j), node(i + 1, j + 1)])
        push!(els, [node(i, j), node(i + 1, j + 1), node(i, j + 1)])
    end
    mkmesh(pts, els)
end

function case(pt)
    out = Dict{String,Any}()
    ed = edges(pt)
    ei = Cartan.edgesindices(pt, FaceBundle(ed))
    ne = length(topology(immersion(ed)))
    out["edges"] = ints(topology(immersion(ed)))
    out["edgesindices"] = ints(topology(immersion(ei)))
    vals = [sin(Float64(k)) + k / 10 for k in 1:ne]
    out["crvalues"] = hxs(vals)
    out["interpCR"] = @safe begin
        r = Cartan.interpCR(pt, TensorField(ei, vals))
        dt = immersion(r)
        Dict("fiber" => hxs(fiber(r)), "elements" => ints(topology(dt)),
            "vertices" => collect(Int, vertices(dt)), "nodes" => totalnodes(dt))
    end
    np = length(Cartan.fullpoints(pt))
    t = TensorField(pt, [Float64(k)^2 / 7 for k in 1:np])
    out["discontinuous"] = @safe begin
        r = Cartan.discontinuous(t)
        Dict("fiber" => hxs(collect(fiber(r))), "vertices" => collect(Int, vertices(immersion(r))),
            "elements" => ints(topology(immersion(r))),
            "points" => hxs(reduce(vcat, [collect(Float64, value(point(r.dom[i]))) for i in 1:length(fiber(r))])))
    end
    out
end

square = mkmesh([[0.0, 0.0], [1.0, 0.0], [1.0, 1.0], [0.0, 1.0], [0.5, 0.5]],
    [[1, 2, 5], [2, 3, 5], [3, 4, 5], [4, 1, 5]])
out = Dict("square" => case(square), "grid" => case(gridmesh(3, 2)))
save("discontinuous", out)

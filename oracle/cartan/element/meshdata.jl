# Goldens for Cartan's mesh-data constructors (Cartan.jl src/element.jl:56-123, 325-398):
# initpointsdata, initmeshdata, totalmeshdata (MATLAB pdetool-style P, E, T matrices),
# array and submesh.
#
#   julia --startup-file=no --project=oracle oracle/cartan/element/meshdata.jl
#
# Writes oracle/golden/cartan/element/meshdata.json. Topologies are dumped as their element
# lists (1-based), vertices, subelements and node counts.
include(joinpath(@__DIR__, "common.jl"))
using Grassmann, Cartan, LinearAlgebra, SparseArrays
import MeshTopology
using MeshTopology: topology, vertices, subelements, totalnodes, fullvertices, fulltopology
# MeshTopology 0.1.0 references names it never imports (defect B1; see fem.jl): the shim supplies
# the intended bindings so `edgetopology` (totalmeshdata) runs.
@eval MeshTopology begin
    const Grassmann = Main.Grassmann; const Leibniz = Main.Grassmann.Leibniz
    const ∂ = Main.Grassmann.∂; const Submanifold = Main.Grassmann.Submanifold
    const Variables = Main.Grassmann.Variables
    fiber(x) = Main.Cartan.fiber(x); means(a...) = Main.Cartan.means(a...)
end
# `totalmeshdata` bumps `global top_id`, which moved to MeshTopology (declared, never assigned, in
# Cartan 0.4.16): give Cartan its own counter (the id only keys caches).
@eval Cartan top_id = 1000

ints(xs) = [collect(Int, x) for x in xs]
idx(v) = collect(Int, v)
flatpts(p) = reduce(vcat, [collect(Float64, value(x)) for x in p]; init = Float64[])
function topo(t)
    Dict("elements" => ints(topology(t)), "full" => ints(fulltopology(t)),
        "vertices" => idx(vertices(t)), "sub" => idx(subelements(t)),
        "fullvertices" => idx(fullvertices(t)), "nodes" => totalnodes(t))
end
bundle(b) = Dict("points" => hxs(flatpts(Cartan.fullpoints(b))), "top" => topo(immersion(b)))
mat(A) = [hxs(A[i, :]) for i in 1:size(A, 1)]

# the unit square split into four triangles around its centre; the edge rows 3-4 and the
# triangle row 4 are pdetool's parameters/subdomains (dropped by `list(1, n)`)
P = [0.0 1.0 1.0 0.0 0.5; 0.0 0.0 1.0 1.0 0.5]
E = [1 2 3 4; 2 3 4 1; 0 0 0 0; 1 1 1 1]
T = [1 2 3 4; 2 3 4 1; 5 5 5 5; 1 1 1 1]

out = Dict{String,Any}()
out["P"] = mat(P); out["E"] = ints(eachcol(E)); out["T"] = ints(eachcol(T))
out["initpointsdata"] = @safe bundle(Cartan.initpointsdata(P, E))
out["initmeshdata"] = @safe begin
    t, e = Cartan.initmeshdata(P, E, T)
    Dict("t" => bundle(t), "e" => bundle(e), "submesh_t" => mat(Cartan.submesh(t)),
        "submesh_e" => mat(Cartan.submesh(e)), "array_t" => mat(Cartan.array(t)),
        "array_top" => [collect(Int, Cartan.array(immersion(t))[i, :]) for i in 1:size(Cartan.array(immersion(t)), 1)])
end
out["totalmeshdata"] = @safe begin
    t, e = Cartan.totalmeshdata(P, E, T)
    Dict("t" => bundle(t), "e" => bundle(e))
end
# a 3-D point set (a tetrahedron's corners and centroid), boundary triangles, tetrahedra
P3 = [0.0 1.0 0.0 0.0 0.25; 0.0 0.0 1.0 0.0 0.25; 0.0 0.0 0.0 1.0 0.25]
E3 = [1 1 1 2; 2 2 3 3; 3 4 4 4]
T3 = [1 1 1 2; 2 2 3 3; 3 4 4 4; 5 5 5 5]
out["initmeshdata3"] = @safe begin
    t, e = Cartan.initmeshdata(P3, E3, T3)
    Dict("t" => bundle(t), "e" => bundle(e), "submesh_t" => mat(Cartan.submesh(t)))
end
save("meshdata", out)

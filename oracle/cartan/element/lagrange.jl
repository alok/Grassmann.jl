# Goldens for Cartan's LagrangeBundle (Cartan.jl src/element.jl:677-786): the node coordinates of
# degree-M Lagrange elements (edge, face and centre nodes) on triangle and tetrahedron meshes.
#
#   julia --startup-file=no --project=oracle oracle/cartan/element/lagrange.jl
#
# Writes oracle/golden/cartan/element/lagrange.json. `LagrangeBundle!` of `LagrangeEdges` reads
# the undefined `pt` (`cornertopology(pt)`, element.jl:686, 694) and MeshTopology 0.1.0 cannot build
# a `LagrangeEdges` topology (`edgesindices` returns a vector), so edges have no golden: the port
# checks them against `printlagrange`'s layout (node x+2 at ci + x(cj-ci)/M).
include(joinpath(@__DIR__, "common.jl"))
using Grassmann, Cartan, LinearAlgebra, SparseArrays
import MeshTopology
using MeshTopology: topology, totalnodes, cornertopology, columns, nodes
@eval MeshTopology begin
    const Grassmann = Main.Grassmann; const Leibniz = Main.Grassmann.Leibniz
    const ∂ = Main.Grassmann.∂; const Submanifold = Main.Grassmann.Submanifold
    const Variables = Main.Grassmann.Variables
    fiber(x) = Main.Cartan.fiber(x); means(a...) = Main.Cartan.means(a...)
end
# the generated `getlagrange3/4` run their generators in the world of their definition, before the
# shim: re-evaluate MeshTopology's lagrange.jl so they see the supplied `Grassmann` binding
Base.include(MeshTopology, joinpath(dirname(pathof(MeshTopology)), "lagrange.jl"))
ints(xs) = [collect(Int, x) for x in xs]
function mkmesh(pts, els)
    d = length(pts[1])
    V = Cartan.varmanifold(d + 1)
    p = PointCloud([Chain{V,1}(1.0, x...) for x in pts])
    p(SimplexTopology([Values(e...) for e in els], length(pts)))
end
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
flat(p) = reduce(vcat, [collect(Float64, value(x)) for x in p]; init = Float64[])

function lagrange(mesh, T)
    @safe begin
        lt = T(immersion(mesh))
        b = Cartan.LagrangeBundle(PointCloud(0, copy(points(fullcoordinates(mesh)))), lt)
        Dict("points" => hxs(flat(Cartan.fullpoints(b))), "topology" => ints(topology(immersion(b))),
            "nodes" => totalnodes(immersion(b)))
    end
end

grid = gridmesh(3, 2)
# the unit cube in Kuhn's six tetrahedra
cube = mkmesh([[0.0, 0, 0], [1.0, 0, 0], [0.0, 1, 0], [1.0, 1, 0], [0.0, 0, 1], [1.0, 0, 1], [0.0, 1, 1], [1.0, 1, 1]],
    [[1, 2, 4, 8], [1, 4, 3, 8], [1, 3, 7, 8], [1, 7, 5, 8], [1, 5, 6, 8], [1, 6, 2, 8]])
out = Dict{String,Any}()
for M in 2:4
    out["tri$M"] = lagrange(grid, MeshTopology.LagrangeTriangles{M})
    out["tet$M"] = lagrange(cube, MeshTopology.LagrangeTetrahedra{M})
end
save("lagrange", out)

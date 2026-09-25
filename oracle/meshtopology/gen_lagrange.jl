# lagrange.json: LagrangeEdges / LagrangeTriangles / LagrangeTetrahedra (lagrange.jl) and
# `refinement` (element.jl:409-465).

"Counts and node lists of a Lagrange topology."
function linfoj(M, L)
    d = Dict{String,Any}("summary" => summary(L), "totalnodes" => M.totalnodes(L), "nodes" => M.nodes(L),
        "elements" => J(collect(L)), "vertices" => J(collect(M.vertices(L))), "vkind" => kind(M.vertices(L)),
        "fullvertices" => J(collect(M.fullvertices(L))), "elementcount" => M.elements(L),
        "totalelements" => M.totalelements(L), "iscover" => M.iscover(L),
        "totalcornernodes" => M.totalcornernodes(L), "totaledgesnodes" => M.totaledgesnodes(L),
        "cornernodes" => M.cornernodes(L), "edgesnodes" => M.edgesnodes(L), "totaledges" => M.totaledges(L))
    if !(L isa M.LagrangeEdges)
        d["totalcenternodes"] = M.totalcenternodes(L)
        d["centernodes"] = M.centernodes(L)
        d["totalfacets"] = M.totalfacets(L)
    end
    if L isa M.LagrangeTetrahedra
        d["totalfacetsnodes"] = M.totalfacetsnodes(L)
        d["facetsnodes"] = M.facetsnodes(L)
    end
    d
end

lagr = Any[]
for (name, elems) in meshes
    N = length(elems[1])
    2 ≤ N ≤ 4 || continue
    nt = length(elems)
    ks = sort(randperm(nt)[1:max(1, nt ÷ 2)])
    for m in 1:5
        ctor = M -> (N == 2 ? M.LagrangeEdges{m} : N == 3 ? M.LagrangeTriangles{m} : M.LagrangeTetrahedra{m})
        f = M -> ctor(M)(M.SimplexTopology(0, elems))
        d = Dict{String,Any}("mesh" => name, "N" => N, "M" => m, "ks" => ks)
        d["info"] = both(M -> linfoj(M, f(M)))
        d["display"] = both(M -> sprint(show, MIME"text/plain"(), f(M)))
        d["refinement"] = both(M -> infoj(M, M.refinement(f(M))))
        d["subtopology"] = both(M -> M.subtopology(f(M)))
        d["subset"] = both(M -> linfoj(M, f(M)[ks]))
        d["subset_getelement"] = both(M -> (s = f(M)[ks]; [M.getelement(s, k) for k in 1:length(s)]))
        d["subset_subimmersion"] = both(M -> linfoj(M, M.subimmersion(f(M)[ks])))
        d["subset_fullimmersion"] = both(M -> linfoj(M, M.fullimmersion(f(M)[ks])))
        d["subset_refine"] = both(M -> linfoj(M, M.refine(f(M)[ks])))
        d["refine"] = both(M -> linfoj(M, M.refine(f(M))))
        push!(lagr, d)
    end
end
refinetables = Dict(string(n) => J(F.refinetriangle(Values(ntuple(identity, n)...))) for n in (3, 6, 10, 15))

writejson("lagrange.json", Dict("cases" => lagr, "refinetriangle" => refinetables))

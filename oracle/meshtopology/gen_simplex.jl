# simplex.json: SimplexTopology and DiscontinuousTopology (MT:210-625, element.jl).

facesj(r) = Any[J(collect(r[1])), J(r[2])]

"Element-level quantities (element.jl) of `f(M)`, where `f` builds a SimplexTopology."
function elementops(f, N)
    d = Dict{String,Any}()
    d["columns"] = both(M -> collect(M.columns(f(M))))
    d["reducedcolumns"] = both(M -> collect(M.reducedcolumns(f(M))))
    d["incidence"] = both(M -> M.incidence(f(M)))
    d["degrees"] = both(M -> M.degrees(f(M)))
    d["weights"] = both(M -> M.weights(f(M)))
    d["degrees_B"] = both(M -> (t = f(M); M.degrees(t, M.incidence(t))))
    d["interp"] = both(M -> M.interp(f(M)))
    d["pretni"] = both(M -> M.pretni(f(M)))
    if N ≥ 2
        d["sparse"] = both(M -> M.sparse(f(M)))
        d["adjacency"] = both(M -> M.adjacency(f(M)))
        d["antiadjacency"] = both(M -> M.antiadjacency(f(M)))
        d["edges"] = both(M -> infoj(M, M.edges(f(M))))
        d["edgesindices"] = both(M -> infoj(M, M.edgesindices(f(M))))
        d["neighbors"] = both(M -> M.neighbors(f(M)))
        d["facetsigns"] = both(M -> M.facetsigns(f(M)))
        d["facets"] = both(M -> infoj(M, M.facets(f(M))))
        d["facets_h"] = both(M -> (t = f(M); facesj(M.facets(t, ones(Int, M.elements(t))))))
        d["facets_h2"] = both(M -> (t = f(M); facesj(M.facets(t, collect(1:M.elements(t))))))
        d["facetsinterior"] = both(M -> facesj(M.facetsinterior(f(M))))
        d["faces"] = [both(M -> infoj(M, M.faces(f(M), k))) for k in 1:N]
        d["faces_h"] = [both(M -> (t = f(M); facesj(M.faces(t, ones(Int, M.elements(t)), Val(k))))) for k in 1:N-1]
        d["skeleton"] = both(M -> [facesj(x) for x in M.skeleton(f(M))])
    end
    N ≥ 3 && (d["facetsindices"] = both(M -> Any[infoj(M, x) for x in M._facetsindices(f(M))]))
    return d
end

simplexj = Any[]
for (name, elems) in meshes
    N = length(elems[1])
    f = M -> M.SimplexTopology(0, elems)
    d = Dict{String,Any}("name" => name, "N" => N, "mesh" => J(elems))
    d["info"] = both(M -> infoj(M, f(M)))
    merge!(d, elementops(f, N))
    if 2 ≤ N ≤ 5
        d["edgesigns"] = [J(F.edgesigns(e)) for e in elems]
        d["localfacets"] = [both(M -> M.facets(e)) for e in elems]
    end
    nt = length(elems)
    ks = sort(randperm(nt)[1:max(1, nt ÷ 2)])
    vs = sort(unique(vcat(collect.(elems)...)))
    vs = vs[sort(randperm(length(vs))[1:max(2, (3 * length(vs)) ÷ 4)])]
    d["ks"] = ks
    d["vs"] = vs
    sub = M -> f(M)[ks]
    d["subset"] = both(M -> infoj(M, sub(M)))
    d["subset_ops"] = elementops(sub, N)
    d["subset_subtopology"] = both(M -> M.subtopology(sub(M)))
    d["subset_subimmersion"] = both(M -> infoj(M, M.subimmersion(sub(M))))
    d["subset_complement"] = both(M -> infoj(M, M.AbstractTensors.complement(sub(M))))
    d["subset_fullimmersion"] = both(M -> infoj(M, M.fullimmersion(sub(M))))
    d["subset_getelement"] = both(M -> (s = sub(M); [M.getelement(s, k) for k in 1:length(s)]))
    d["subset_getimage"] = both(M -> (s = sub(M); [M.getimage(s, k) for k in 1:M.nodes(s)]))
    d["subset_refine"] = both(M -> infoj(M, M.refine(sub(M))))
    d["subsubset"] = both(M -> infoj(M, sub(M)[[length(ks)]]))
    d["subset_byvertices"] = both(M -> infoj(M, sub(M)(vs)))
    byv = M -> f(M)(vs)
    d["byvertices"] = both(M -> infoj(M, byv(M)))
    d["byvertices_subtopology"] = both(M -> M.subtopology(byv(M)))
    d["byvertices_subimmersion"] = both(M -> infoj(M, M.subimmersion(byv(M))))
    d["byvertices_complement"] = both(M -> infoj(M, M.AbstractTensors.complement(byv(M))))
    d["untotal"] = both(M -> infoj(M, M.untotal(f(M), M.totalnodes(f(M)) + 2)))
    d["refine"] = both(M -> infoj(M, M.refine(f(M))))
    d["fullimmersion"] = both(M -> infoj(M, M.fullimmersion(f(M))))
    d["subimmersion"] = both(M -> infoj(M, M.subimmersion(f(M))))
    d["subtopology"] = both(M -> M.subtopology(f(M)))
    d["getimage"] = both(M -> (t = f(M); [M.getimage(t, k) for k in 1:M.nodes(t)]))
    # discontinuous
    dis = M -> M.discontinuous(f(M))
    d["discontinuous"] = both(M -> dinfoj(M, dis(M)))
    d["discontinuousvertices"] = both(M -> M.discontinuousvertices(dis(M)))
    d["disconnect"] = both(M -> dinfoj(M, M.disconnect(f(M))))
    d["d_fullimmersion"] = both(M -> dinfoj(M, M.fullimmersion(dis(M))))
    d["d_subset"] = both(M -> dinfoj(M, dis(M)[ks]))
    d["d_subset_fullimmersion"] = both(M -> dinfoj(M, M.fullimmersion(dis(M)[ks])))
    d["d_subset_subimmersion"] = both(M -> dinfoj(M, M.subimmersion(dis(M)[ks])))
    d["d_subset_subtopology"] = both(M -> M.subtopology(dis(M)[ks]))
    d["d_subset_getimage"] = both(M -> (s = dis(M)[ks]; [M.getimage(s, k) for k in 1:M.nodes(s)]))
    d["d_subset_disconnect"] = both(M -> dinfoj(M, M.disconnect(dis(M)[ks])))
    d["d_subset_refine"] = both(M -> dinfoj(M, M.refine(dis(M)[ks])))
    d["d_byvertices"] = both(M -> dinfoj(M, dis(M)(vs)))
    d["d_neighbors"] = both(M -> M.neighbors(dis(M)))
    d["d_interp"] = both(M -> M.interp(dis(M), collect(10:10:10nt)))
    if N == 3
        d["d_edges"] = both(M -> infoj(M, M.edges(dis(M))))
        bnd = M -> (t = f(M); (top, c) = M.facets(t, ones(Int, M.elements(t)));
            M.SimplexTopology(0, collect(top)[findall(!iszero, c)], M.totalnodes(t)))
        d["boundary"] = both(M -> infoj(M, bnd(M)))
        d["interior"] = both(M -> M.interior(bnd(M)))
        d["discontinuousboundary"] = both(M -> collect(M.discontinuousboundary(dis(M), bnd(M))))
    end
    push!(simplexj, d)
end

misc2 = Dict{String,Any}(
    "interior" => [Dict("fixed" => fx, "neq" => n, "out" => J(F.interior(fx, n))) for (fx, n) in (([1, 5, 3], 6), (Int[], 3), ([2, 2, 4], 4))],
    "invmap" => [Dict("t" => [4, 7, 9], "n" => n, "out" => F.invmap(Values(4, 7, 9), n)) for n in (4, 7, 9, 5)],
    "findmissing" => [Dict("n" => collect(n), "out" => F.findmissing(Values(n...))) for n in ((1, 2), (2, 3), (1, 3), (3, 1))],
    "neighbor" => [Dict("k" => k, "ab" => ab, "out" => F.neighbor(k, ab...)) for (k, ab) in ((1, [[1, 2, 3], [2, 3]]), (2, [[2], [2, 5]]), (3, [[1, 3, 5], [3, 5, 7], [5, 3]]))],
    "facetsign" => [Dict("i" => i, "ni" => ni, "out" => F.facetsign(i, ni)) for (i, ni) in ((1, 2), (2, 1), (3, 3), (0, 1))],
    "verticesinv" => [Dict("n" => n, "ind" => ind, "out" => J(F.verticesinv(n, ind))) for (n, ind) in ((5, [3, 1]), (4, [4, 2, 3]), (3, Int[]))],
    "vertices" => [Dict("t" => J(t), "out" => J(collect(F.vertices(t))), "kind" => kind(F.vertices(t)))
        for t in (Values{3,Int}[Values(2, 1, 3)], Values{2,Int}[Values(5, 2), Values(2, 7)], Values{2,Int}[Values(1, 4), Values(2, 3)], Values{1,Int}[Values(3), Values(1)])],
)
assem = zeros(4, 4)
F.assemblelocal!(assem, [1.0 2.0; 3.0 4.0], 0.5, Values(2, 4))
F.assemblelocal!(assem, [1.0 -1.0 0.0; -1.0 2.0 1.0; 0.0 1.0 3.0], Values(1, 2, 4))
misc2["assemblelocal"] = J(assem)

writejson("simplex.json", Dict("meshes" => simplexj, "misc" => misc2))

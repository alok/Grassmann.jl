# Julia twin of Bench/MeshTopology.lean (`meshtopology` suite), on the `Fixed` module of
# oracle/meshtopology/load.jl (same code paths as upstream for everything timed here).
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "harness.jl"))
using .BenchHarness
isdefined(Main, :F) || include(joinpath(@__DIR__, "..", "meshtopology", "load.jl"))
import StaticVectors
using SparseArrays: nnz

"All one-step stencil lookups `m[Val(a), i ± e_a]`, precomputed (not timed)."
function mt_queries(m)
    N = length(m.s)
    out = Tuple{Int,NTuple{N,Int}}[]
    for I in CartesianIndices(Tuple(m.s)), a in 1:N, d in (-1, 1)
        q = collect(Tuple(I)); q[a] += d
        push!(out, (a, Tuple(q)))
    end
    out
end
function mt_sweep(m, qs::Vector{Tuple{Int,NTuple{2,Int}}})
    acc = 0
    @inbounds for (a, q) in qs
        r = a == 1 ? m[Val(1), q...] : m[Val(2), q...]
        acc += r[1]
    end
    acc
end
function mt_sweep(m, qs::Vector{Tuple{Int,NTuple{3,Int}}})
    acc = 0
    @inbounds for (a, q) in qs
        r = a == 1 ? m[Val(1), q...] : a == 2 ? m[Val(2), q...] : m[Val(3), q...]
        acc += r[1]
    end
    acc
end
function mt_gridtris(nx, ny)
    t = StaticVectors.Values{3,Int}[]
    for j in 1:ny-1, i in 1:nx-1
        a = i + (j - 1) * nx
        push!(t, StaticVectors.Values(a, a + 1, a + nx + 1), StaticVectors.Values(a, a + nx + 1, a + nx))
    end
    t
end

function mt_topology_cases(ctx, tag, dims, m)
    qs = mt_queries(m)
    bench!(ctx, "ghost_$tag"; ops = length(qs), param = dims) do i
        mt_sweep(blackbox(i, m), qs)
    end
    bench!(ctx, "elementfuns_$tag"; param = dims) do i
        F.elementfuns(blackbox(i, m))
    end
end

function suite_meshtopology(ctx)
    M = F
    n = sized(ctx, 61, 9)
    d2 = "$(n)×$(n)"
    mt_topology_cases(ctx, "torus", d2, M.TorusTopology(n, n))
    mt_topology_cases(ctx, "sphere", d2, M.SphereTopology(n, n))
    mt_topology_cases(ctx, "mobius", d2, M.MobiusTopology(n, n))
    h = ctx.cfg.smoke ? (4, 5, 5) : (7, 60, 61)
    mt_topology_cases(ctx, "hopf", join(h, "×"), M.HopfTopology(h...))
    sph = M.SphereTopology(n, n)
    bench!(ctx, "bilinear_sphere"; param = d2) do i
        M.nodes(M.BilinearTopology(blackbox(i, sph)))
    end
    g = sized(ctx, 200, 12)
    els = mt_gridtris(g, g)
    p = "$(length(els)) triangles"
    bench!(ctx, "simplex_topology"; param = p) do i
        M.elements(M.SimplexTopology(0, blackbox(i, els)))
    end
    st = M.SimplexTopology(0, els)
    es = M.edges(st)
    bench!(ctx, "edges"; param = p) do i
        M.totalelements(M.edges(blackbox(i, st)))
    end
    bench!(ctx, "edgesindices"; param = p) do i
        M.totalelements(M.edgesindices(blackbox(i, st), es))
    end
    bench!(ctx, "neighbors"; param = p) do i
        length(M.neighbors(blackbox(i, st)))
    end
    bench!(ctx, "incidence"; param = p) do i
        nnz(M.incidence(blackbox(i, st)))
    end
    bench!(ctx, "degrees"; param = p) do i
        length(M.degrees(blackbox(i, st)))
    end
    bench!(ctx, "facets_ones"; param = p) do i
        r = M.facets(blackbox(i, st), ones(Int, length(els)))
        length(last(r))
    end
    bench!(ctx, "lagrange3_nodes"; param = p) do i
        t = blackbox(i, st)
        length(collect(M.LagrangeTriangles{3}(0, t, es, M.edgesindices(t, es))))
    end
end

register!("meshtopology", suite_meshtopology)
(abspath(PROGRAM_FILE) == @__FILE__) && main_suites(["meshtopology" => suite_meshtopology])

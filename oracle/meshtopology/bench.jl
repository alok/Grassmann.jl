# Julia side of the MeshTopology benchmarks (compare Tests/MeshTopology/Bench.lean).
#
#   julia --startup-file=no --project=<juliaenv> oracle/meshtopology/bench.jl
#
# Uses the fixed module of load.jl (same code paths as upstream for everything timed here).
# Reports the best of 7 runs after a warm-up, like the Lean harness.

include(joinpath(@__DIR__, "load.jl"))
import StaticVectors: Values
const M = F

function best(f, reps = 7)
    f()
    t = Inf
    local r
    for _ in 1:reps
        t0 = time_ns()
        r = f()
        t = min(t, time_ns() - t0)
    end
    t, r
end
fmt(ns) = ns < 1e4 ? "$(round(Int, ns)) ns" : ns < 1e7 ? "$(round(ns / 1e3; digits = 1)) µs" : "$(round(ns / 1e6; digits = 1)) ms"
report(name, ns, count = 1) = println(name, ": ", fmt(ns), count > 1 ? " ($(round(ns / count; digits = 1)) ns each)" : "")

"All one-step stencil lookups `m[Val(a), i ± e_a]`, precomputed (not timed)."
function queries(m)
    N = length(m.s)
    out = Tuple{Int,NTuple{N,Int}}[]
    for I in CartesianIndices(Tuple(m.s)), a in 1:N, d in (-1, 1)
        q = collect(Tuple(I)); q[a] += d
        push!(out, (a, Tuple(q)))
    end
    out
end
function sweep(m, qs::Vector{Tuple{Int,NTuple{2,Int}}})
    acc = 0
    @inbounds for (a, q) in qs
        r = a == 1 ? m[Val(1), q...] : m[Val(2), q...]
        acc += r[1]
    end
    acc
end
function sweep(m, qs::Vector{Tuple{Int,NTuple{3,Int}}})
    acc = 0
    @inbounds for (a, q) in qs
        r = a == 1 ? m[Val(1), q...] : a == 2 ? m[Val(2), q...] : m[Val(3), q...]
        acc += r[1]
    end
    acc
end

for (name, m) in (("Torus(61,61)", M.TorusTopology(61, 61)), ("Sphere(61,61)", M.SphereTopology(61, 61)),
                  ("Mobius(61,61)", M.MobiusTopology(61, 61)), ("Hopf(7,60,61)", M.HopfTopology(7, 60, 61)))
    qs = queries(m)
    t, _ = best(() -> sweep(m, qs))
    report("ghost sweep $name", t, length(qs))
    t, _ = best(() -> M.elementfuns(m))
    report("elementfuns $name", t)
end
t, _ = best(() -> M.BilinearTopology(M.SphereTopology(61, 61)))
report("BilinearTopology Sphere(61,61)", t)

function gridtris(nx, ny)
    t = Values{3,Int}[]
    for j in 1:ny-1, i in 1:nx-1
        a = i + (j - 1) * nx
        push!(t, Values(a, a + 1, a + nx + 1), Values(a, a + nx + 1, a + nx))
    end
    t
end
els = gridtris(200, 200)
t, st = best(() -> M.SimplexTopology(0, els))
report("SimplexTopology $(length(els)) triangles", t)
t, es = best(() -> M.edges(st))
report("edges", t)
t, _ = best(() -> M.edgesindices(st, es))
report("edgesindices", t)
t, _ = best(() -> M.neighbors(st))
report("neighbors", t)
t, _ = best(() -> M.incidence(st))
report("incidence", t)
t, _ = best(() -> M.degrees(st))
report("degrees", t)
t, _ = best(() -> M.facets(st, ones(Int, length(els))), 2)
report("facets(t, ones)", t)
t, _ = best(() -> collect(M.LagrangeTriangles{3}(0, st, es, M.edgesindices(st, es))))
report("LagrangeTriangles{3} node lists (incl. edgesindices)", t)
println("threads: ", Threads.nthreads())

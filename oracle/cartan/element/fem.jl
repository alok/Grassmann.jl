# Goldens for Cartan's finite-element layer (Cartan.jl src/element.jl): simplex geometry,
# P1 gradients, lumped loads, transfers, evaluation, 1-D meshes and refinement.
#
#   julia --startup-file=no --project=oracle oracle/cartan/element/fem.jl
#
# Writes oracle/golden/cartan/element/fem.json. MeshTopology 0.1.0 references names it never
# imports (`fibertype`, `means`, `Grassmann`, …; docs/port-notes/cartan-element-spectral-plot.md
# §7, defect B1), so `assembleload`, `interp`, `gradient` and `∂` throw upstream; the shim below
# supplies the intended bindings so the goldens record the intended values.
include(joinpath(@__DIR__, "common.jl"))
using Grassmann, Cartan, LinearAlgebra, SparseArrays
import MeshTopology
@eval MeshTopology begin
    const Grassmann = Main.Grassmann; const Leibniz = Main.Grassmann.Leibniz
    const ∂ = Main.Grassmann.∂; const Submanifold = Main.Grassmann.Submanifold
    const Variables = Main.Grassmann.Variables
    fiber(x) = Main.Cartan.fiber(x); means(a...) = Main.Cartan.means(a...)
end
@eval MeshTopology fibertype(x::AbstractArray) = eltype(x)
@eval MeshTopology fibertype(x::$(Cartan.TensorField)) = $(Cartan.fibertype)(x)

deep(x::Real) = [Float64(x)]
deep(x::Chain) = reduce(vcat, [deep(c) for c in value(x)]; init = Float64[])
deep(x::Union{Values,Tuple,AbstractVector}) = reduce(vcat, [deep(c) for c in x]; init = Float64[])
flatc(xs) = reduce(vcat, [deep(x) for x in xs]; init = Float64[])
opflat(T) = reduce(vcat, [collect(value(c)) for c in value(value(T))])
ints(xs) = [collect(Int, x) for x in xs]

"The mesh with homogeneous points `(1, x…)` and 1-based elements."
function mkmesh(pts, els)
    d = length(pts[1])
    V = Cartan.varmanifold(d + 1)
    p = PointCloud([Chain{V,1}(1.0, x...) for x in pts])
    p(SimplexTopology([Values(e...) for e in els], length(pts)))
end

"A structured `a × b` triangulation of the unit square (node k = i + (a+1) j, 0-based), interior
nodes jittered by ±`jit`·h from the stream `seed`; `flip` reverses every other triangle."
function gridmesh(a, b; jit = 0.0, seed = UInt64(1), flip = false)
    np = (a + 1) * (b + 1)
    r = randfloats(2np, seed, -1.0, 1.0)
    pts = Vector{Tuple{Float64,Float64}}()
    for j in 0:b, i in 0:a
        k = i + (a + 1) * j
        x = i / a; y = j / b
        if 0 < i < a && 0 < j < b
            x += jit * r[2k+1] / a; y += jit * r[2k+2] / b
        end
        push!(pts, (x, y))
    end
    els = Vector{NTuple{3,Int}}()
    for j in 0:b-1, i in 0:a-1
        k = i + (a + 1) * j + 1
        t1 = (k, k + 1, k + a + 2); t2 = (k, k + a + 2, k + a + 1)
        push!(els, t1)
        push!(els, flip && isodd(i + j) ? (t2[1], t2[3], t2[2]) : t2)
    end
    pts, els
end

"Kuhn's 6-tetrahedron split of the unit cube."
function cubemesh()
    pts = [(x, y, z) for z in (0.0, 1.0) for y in (0.0, 1.0) for x in (0.0, 1.0)]
    # node (x,y,z) ↦ 1 + x + 2y + 4z
    els = [(1, 2, 4, 8), (1, 2, 6, 8), (1, 3, 4, 8), (1, 3, 7, 8), (1, 5, 6, 8), (1, 5, 7, 8)]
    pts, els
end

function femcase(pts, els; ufun = nothing)
    t = mkmesh(pts, els)
    d = length(pts[1])
    n = length(els[1])
    np = length(pts)
    ne = length(els)
    out = Dict{String,Any}("d" => d, "n" => n, "points" => hxs(reduce(vcat, [collect(x) for x in pts])),
        "elements" => ints(els))
    m = volumes(t)
    out["volumes"] = @safe(hxs(fiber(m)))
    out["gradienthat"] = @safe(hxs(reduce(vcat, [opflat(g) for g in fiber(gradienthat(t))])))
    out["degrees"] = @safe(collect(fiber(degrees(t))))
    out["weights"] = @safe(hxs(fiber(weights(t))))
    out["load1"] = @safe(hxs(assembleload(t)))
    out["loadx"] = @safe(hxs(assembleload(t, x -> x[2])))
    out["loadxy"] = @safe(hxs(assembleload(t, x -> d ≥ 2 ? x[2] * x[3] + 1 : x[2] * x[2] + 1)))
    fe = randfloats(ne, UInt64(0xface), -1.0, 1.0)
    out["interp"] = @safe(hxs(fiber(interp(TensorField(FaceBundle(t), fe)))))
    un = randfloats(np, UInt64(0x40de), -1.0, 1.0)
    out["pretni"] = @safe(hxs(fiber(Cartan.pretni(TensorField(t, un)))))
    out["means"] = @safe(hxs(flatc(fiber(means(t)))))
    out["barycenters"] = @safe(hxs(flatc(fiber(barycenters(t)))))
    out["centroids"] = @safe(hxs(flatc(fiber(centroids(t)))))
    out["curls"] = @safe(hxs(flatc(fiber(curls(t)))))
    out["grad2"] = @safe(hxs(flatc(fiber(Cartan.gradient_2(TensorField(t, un))))))
    out["grad"] = @safe(hxs(flatc(fiber(Cartan.gradient(TensorField(t, un))))))
    lin = [2x[1] - (d ≥ 2 ? x[2] : 0.0) + 3 for x in pts]
    out["gradlin"] = @safe(hxs(flatc(fiber(Cartan.gradient(TensorField(t, lin))))))
    out["wedge"] = @safe(hxs(flatc(fiber(Grassmann.:∧(t)))))
    out["detsimplex"] = @safe(hxs(flatc(fiber(Grassmann.detsimplex(t)))))
    if d + 1 == n
        # evaluation at points (inside, on edges, outside)
        q = randfloats(12d, UInt64(0x9ad), -0.1, 1.1)
        qs = [Tuple(q[(k-1)*d+1:k*d]) for k in 1:12]
        V = Cartan.varmanifold(d + 1)
        out["query"] = @safe(hxs(q))
        out["findfirst"] = @safe([findfirst(Chain{V,1}(1.0, x...), t) for x in qs])
        out["sinterp"] = @safe(hxs(reduce(vcat, [deep(TensorField(t, un)(Chain{V,1}(1.0, x...))) for x in qs])))
    end
    out
end

out = Dict{String,Any}("meta" => Dict("julia" => string(VERSION), "cartan" => string(pkgversion(Cartan))))
out["two"] = femcase([(0.0, 0.0), (1.0, 0.0), (0.0, 1.0), (1.0, 1.0)], [(1, 2, 3), (2, 4, 3)])
let (p, e) = gridmesh(3, 2; jit = 0.15, seed = UInt64(0x1d))
    out["grid"] = @safe(femcase(p, e))
end
let (p, e) = gridmesh(3, 2; jit = 0.15, seed = UInt64(0x1d), flip = true)
    out["gridflip"] = @safe(femcase(p, e))
end
out["tet"] = femcase([(0.0, 0.0, 0.0), (1.0, 0.0, 0.0), (0.0, 1.0, 0.0), (0.0, 0.0, 1.0)], [(1, 2, 3, 4)])
let (p, e) = cubemesh()
    out["cube"] = @safe(femcase(p, e))
end
out["surf"] = femcase([(0.0, 0.0, 0.0), (2.0, 0.0, 0.0), (0.0, 0.0, 2.0), (1.0, 1.5, 0.5)],
    [(1, 2, 3), (2, 4, 3)])
# 1-D: initmesh of a range and of random sorted points
let r = 0:0.25:1
    t, e = Cartan.initmesh(r)
    c = femcase([(x,) for x in r], [(i, i + 1) for i in 1:length(r)-1])
    c["bnd_vertices"] = collect(vertices(e))
    c["bnd_elements"] = ints(immersion(e))
    # refinemesh! of elements 2 and 4. Upstream `refinemesh!` resizes `vertices(t)`, which is a
    # `OneTo` for every mesh `initmesh` builds (MethodError: no method matching resize!); the
    # golden records the intended result (port notes §4.5): midpoints of the refined elements
    # inserted, points sorted, consecutive elements, boundary vertices [1, np].
    rr = @safe begin
        g, pt, pe = r, t, e
        Cartan.refinemesh!(g, pt, pe, [2, 4])
        nothing
    end
    c["refine_upstream"] = rr === nothing ? "ok" : rr
    xr = sort(vcat(collect(r), [(r[i] + r[i+1]) / 2 for i in (2, 4)]))
    c["refined_points"] = hxs(xr)
    c["refined_elements"] = [[i, i + 1] for i in 1:length(xr)-1]
    c["refined_bnd"] = [1, length(xr)]
    c["refined_volumes"] = hxs(fiber(volumes(mkmesh([(x,) for x in xr], [(i, i + 1) for i in 1:length(xr)-1]))))
    out["line"] = @safe(c)
end
let x = sort(randfloats(7, UInt64(0x11e), 0.0, 1.0))
    out["line_rand"] = @safe(femcase([(v,) for v in x], [(i, i + 1) for i in 1:6]))
end
# rms/select/maximum of a face field
let t = mkmesh([(0.0, 0.0), (1.0, 0.0), (0.0, 1.0), (1.0, 1.0)], [(1, 2, 3), (2, 4, 3)])
    η = TensorField(FaceBundle(t), [0.1, 2.0])
    out["misc"] = Dict("rms34" => hx(rms(TensorField(FaceBundle(t), [3.0, 4.0]))),
        "select" => Cartan.select(η), "select05" => Cartan.select(η, 0.05),
        "laplacian" => Matrix(Grassmann.Δ(immersion(mkmesh([(0.0, 0.0), (1.0, 0.0), (0.0, 1.0)], [(1, 2, 3)])))))
end
save("fem", out)

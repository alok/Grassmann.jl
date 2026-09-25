# quotient.json and cross.json: QuotientTopology (MT quotient.jl, grid.jl).

"Every lookup `m[Val(K), idx...]` for `idx ∈ (0:n+1)^N`, column-major."
function ghostgrid(m, K)
    N = length(m.s)
    R = CartesianIndices(Tuple(0:n+1 for n in m.s))
    Any[J(N == 1 ? m[Val(K), I[1]] : m[Val(K), Tuple(I)...]) for I in vec(R)]
end

"Random lookups with indices in `-2:n+3` (two ghost layers and beyond)."
function ghostsamples(f, count)
    s = collect(f(F).s)
    N = length(s)
    out = Any[]
    for _ in 1:count
        K = rand(0:N)
        idx = [rand(-2:n+3) for n in s]
        push!(out, Dict("K" => K, "idx" => idx,
            "out" => both(M -> (m = f(M); N == 1 ? m[Val(K), idx[1]] : m[Val(K), idx...]))))
    end
    out
end

"All slices with `k` colons (`samples` random fixed coordinates per colon pattern when > 0)."
function slices(f, k, samples = 0)
    s = collect(f(F).s)
    N = length(s)
    out = Any[]
    for pat in Iterators.filter(p -> length(p) == k, [findall(b -> (c >> (b - 1)) & 1 == 1, 1:N) for c in 1:2^N-1])
        fixedaxes = setdiff(1:N, pat)
        R = vec(CartesianIndices(Tuple(1:s[a] for a in fixedaxes)))
        samples > 0 && length(R) > samples && (R = R[sort(randperm(length(R))[1:samples])])
        for I in R
            args = Any[Colon() for _ in 1:N]
            for (t, a) in enumerate(fixedaxes)
                args[a] = I[t]
            end
            fixed = Int[I[t] for t in 1:length(fixedaxes)]
            push!(out, Dict("colons" => pat, "fixed" => fixed, "out" => both(M -> qtj(f(M)(args...)))))
        end
    end
    out
end

function bilinearj(M, m)
    b = M.BilinearTopology(m)
    Dict("q" => J(b.q), "t" => J(b.t), "iq" => J(b.iq), "it" => J(b.it), "split" => J(b.s),
         "v" => J(b.v), "i" => G(b.i), "nodes" => M.nodes(b))
end

function qcase(name, f; ghosts = true, samples = 150, slicecfg = nothing)
    m = f(F)
    N = length(m.s)
    d = Dict{String,Any}("name" => name, "N" => N)
    d["table"] = both(M -> qtj(f(M)))
    d["summary"] = both(M -> summary(f(M)))
    d["isopen"] = both(M -> M.isopen(f(M)))
    d["iscompact"] = both(M -> M.iscompact(f(M)))
    if ghosts && N ≤ 3
        d["ghosts"] = [Dict("K" => K, "grid" => both(M -> ghostgrid(f(M), K))) for K in 0:N]
    end
    d["ghostsamples"] = ghostsamples(f, samples)
    d["elementfuns"] = both(M -> G(M.elementfuns(f(M))))
    d["vertices"] = both(M -> G(M.vertices(f(M))))
    d["verticesinv"] = both(M -> collect(M.verticesinv(f(M))))
    d["duplicates"] = both(M -> collect(M.duplicates(f(M))))
    d["duplicatemap"] = both(M -> M.duplicatemap(f(M)))
    d["uniquemap"] = both(M -> M.uniquemap(f(M)))
    d["linearelements"] = both(M -> G(M.linearelements(f(M))))
    N == 2 && (d["bilinear"] = both(M -> bilinearj(M, f(M))))
    d["subtopology_val"] = [both(M -> qtj(M.subtopology(f(M), Val(a)))) for a in 1:N]
    cfg = something(slicecfg, N ≤ 3 ? [(k, 0) for k in 1:N] : [(k, 6) for k in 1:N])
    d["slices"] = vcat([slices(f, k, smp) for (k, smp) in cfg]...)
    d["resize"] = both(M -> qtj(M.resize(f(M), 7)))
    d["resample"] = both(M -> qtj(M.resample(f(M), Tuple(m.s .+ 1))))
    d["open"] = both(M -> qtj(M.OpenTopology(f(M))))
    return d
end

const FAM1 = (:Open, :Mirror, :Clamped, :Torus, :Ball, :Sphere)
const FAM2 = (:Open, :Cylinder, :Mobius, :Wing, :Mirror, :Clamped, :Torus, :Hopf, :Klein, :Cone, :Tube,
              :Ball, :Sphere, :Geographic)
const FAM3 = (:Open, :Mirror, :Clamped, :Torus, :Hopf, :Tube, :Ball, :Sphere)
const FAM4 = (:Open, :Mirror, :Clamped, :Torus, :Ball, :Sphere)
const FAM5 = (:Open, :Mirror, :Clamped, :Torus, :Ball, :Sphere)
top(M, fam) = getfield(M, Symbol(fam, :Topology))

quot = Any[]
for n in (4, 5, 7), fam in FAM1
    push!(quot, qcase("$(fam)($n)", M -> top(M, fam)(n)))
end
for s in ((3, 3), (4, 5), (5, 7), (6, 4), (4, 6), (7, 7)), fam in FAM2
    push!(quot, qcase("$(fam)$s", M -> top(M, fam)(s...)))
end
for s in ((3, 4, 5), (4, 4, 5), (5, 3, 4)), fam in FAM3
    push!(quot, qcase("$(fam)$s", M -> top(M, fam)(s...)))
end
for s in ((3, 4, 5, 4),), fam in FAM4
    push!(quot, qcase("$(fam)$s", M -> top(M, fam)(s...); samples = 400))
end
for s in ((3, 3, 4, 3, 5),), fam in FAM5
    push!(quot, qcase("$(fam)$s", M -> top(M, fam)(s...); samples = 400))
end

defaults = Any[]
for (name, f) in (("Hopf()", M -> M.HopfTopology()), ("Open()", M -> M.OpenTopology()),
        ("Mirror()", M -> M.MirrorTopology()), ("Clamped()", M -> M.ClampedTopology()),
        ("Torus()", M -> M.TorusTopology()), ("Cylinder()", M -> M.CylinderTopology()),
        ("Wing()", M -> M.WingTopology()), ("Mobius()", M -> M.MobiusTopology()),
        ("Klein()", M -> M.KleinTopology()), ("Cone()", M -> M.ConeTopology()),
        ("Cone(5)", M -> M.ConeTopology(5)), ("Geographic()", M -> M.GeographicTopology()),
        ("Geographic(9)", M -> M.GeographicTopology(9)), ("Tube()", M -> M.TubeTopology()),
        ("Ball()", M -> M.BallTopology()), ("Sphere()", M -> M.SphereTopology()),
        ("Polar(4,5)", M -> M.PolarTopology(4, 5)), ("Revolved(4,5)", M -> M.RevolvedTopology(4, 5)),
        ("Torus((3,4))", M -> M.TorusTopology((3, 4))), ("Cylinder(9)", M -> M.CylinderTopology(9)))
    push!(defaults, Dict("name" => name, "table" => both(M -> qtj(f(M))), "summary" => both(M -> summary(f(M)))))
end

writejson("quotient.json", Dict("cases" => quot, "defaults" => defaults))

# ---------------------------------------------------------------- products of topologies
T(M, s...) = M.TorusTopology(s...)
crosses = [
    ("Open(3)×Open(4)", M -> M.cross(M.OpenTopology(3), M.OpenTopology(4))),
    ("Open(3,4)×Open(5)", M -> M.cross(M.OpenTopology(3, 4), M.OpenTopology(5))),
    ("Open(3)×Open(4,5)", M -> M.cross(M.OpenTopology(3), M.OpenTopology(4, 5))),
    ("Open(2,3)×Open(4,5)", M -> M.cross(M.OpenTopology(2, 3), M.OpenTopology(4, 5))),
    ("Open(3)×Open(2,3,4)", M -> M.cross(M.OpenTopology(3), M.OpenTopology(2, 3, 4))),
    ("Open(2,3,4)×Open(3)", M -> M.cross(M.OpenTopology(2, 3, 4), M.OpenTopology(3))),
    ("Open(3,4)×6", M -> M.cross(M.OpenTopology(3, 4), 6)),
    ("Open(3)×6", M -> M.cross(M.OpenTopology(3), 6)),
    ("6×Open(3,4)", M -> M.cross(6, M.OpenTopology(3, 4))),
    ("6×Open(3)", M -> M.cross(6, M.OpenTopology(3))),
    ("Torus(4)×5", M -> M.cross(T(M, 4), 5)),
    ("Mirror(4)×5", M -> M.cross(M.MirrorTopology(4), 5)),
    ("Torus(3,4)×5", M -> M.cross(T(M, 3, 4), 5)),
    ("Mobius(4,5)×3", M -> M.cross(M.MobiusTopology(4, 5), 3)),
    ("Sphere(4,5)×3", M -> M.cross(M.SphereTopology(4, 5), 3)),
    ("Hopf(3,4,5)×3", M -> M.cross(M.HopfTopology(3, 4, 5), 3)),
    ("5×Torus(4)", M -> M.cross(5, T(M, 4))),
    ("5×Mirror(4)", M -> M.cross(5, M.MirrorTopology(4))),
    ("5×Torus(3,4)", M -> M.cross(5, T(M, 3, 4))),
    ("5×Mobius(4,5)", M -> M.cross(5, M.MobiusTopology(4, 5))),
    ("Torus(4)×Torus(5)", M -> M.cross(T(M, 4), T(M, 5))),
    ("Torus(4)×Open(5)", M -> M.cross(T(M, 4), M.OpenTopology(5))),
    ("Mirror(4)×Torus(5)", M -> M.cross(M.MirrorTopology(4), T(M, 5))),
    ("Clamped(4)×Mirror(5)", M -> M.cross(M.ClampedTopology(4), M.MirrorTopology(5))),
    ("Torus(3)×Torus(4,5)", M -> M.cross(T(M, 3), T(M, 4, 5))),
    ("Mirror(3)×Mobius(4,5)", M -> M.cross(M.MirrorTopology(3), M.MobiusTopology(4, 5))),
    ("Torus(4,5)×Torus(3)", M -> M.cross(T(M, 4, 5), T(M, 3))),
    ("Mobius(4,5)×Torus(3)", M -> M.cross(M.MobiusTopology(4, 5), T(M, 3))),
    ("Sphere(4,5)×Mirror(3)", M -> M.cross(M.SphereTopology(4, 5), M.MirrorTopology(3))),
    ("Torus(3)×Torus(3,4,5)", M -> M.cross(T(M, 3), T(M, 3, 4, 5))),
    ("Torus(3,4,5)×Torus(3)", M -> M.cross(T(M, 3, 4, 5), T(M, 3))),
    ("Torus(3)×Torus(2,3,4,5)", M -> M.cross(T(M, 3), T(M, 2, 3, 4, 5))),
    ("Torus(2,3,4,5)×Torus(3)", M -> M.cross(T(M, 2, 3, 4, 5), T(M, 3))),
    ("Torus(3,4)×Torus(5,6)", M -> M.cross(T(M, 3, 4), T(M, 5, 6))),
    ("Klein(4,5)×Mirror(3,4)", M -> M.cross(M.KleinTopology(4, 5), M.MirrorTopology(3, 4))),
    ("Torus(3,4)×Torus(3,4,5)", M -> M.cross(T(M, 3, 4), T(M, 3, 4, 5))),
    ("Torus(3,4,5)×Torus(3,4)", M -> M.cross(T(M, 3, 4, 5), T(M, 3, 4))),
    ("cross_sphere(Torus(4),Torus(5))", M -> M.cross_sphere(T(M, 4), T(M, 5))),
    ("cross_sphere(Torus(4),Mirror(5))", M -> M.cross_sphere(T(M, 4), M.MirrorTopology(5))),
    ("cross_sector(Torus(4),Torus(5))", M -> M.cross_sector(T(M, 4), T(M, 5))),
    ("cross_sector(Torus(4),Mirror(5))", M -> M.cross_sector(T(M, 4), M.MirrorTopology(5))),
    ("cross_sector(Torus(4),Torus(3,5))", M -> M.cross_sector(T(M, 4), T(M, 3, 5))),
    ("cross_sector(Torus(4),Mirror(3,5))", M -> M.cross_sector(T(M, 4), M.MirrorTopology(3, 5))),
    ("cross_sector(Torus(4),Torus(3,4,5))", M -> M.cross_sector(T(M, 4), T(M, 3, 4, 5))),
    ("cross_sector(Torus(4),Torus(3,3,4,5))", M -> M.cross_sector(T(M, 4), T(M, 3, 3, 4, 5))),
]
crossj = Any[]
for (name, f) in crosses
    N = length(f(F).s)
    d = Dict{String,Any}("name" => name, "table" => both(M -> qtj(f(M))), "summary" => both(M -> summary(f(M))))
    N ≤ 3 && (d["ghosts"] = [Dict("K" => K, "grid" => both(M -> ghostgrid(f(M), K))) for K in 0:N])
    N ≥ 4 && (d["ghostsamples"] = ghostsamples(f, 200))
    push!(crossj, d)
end
writejson("cross.json", Dict("cases" => crossj))

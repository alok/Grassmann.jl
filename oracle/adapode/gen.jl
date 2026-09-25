# Golden generator for the Adapode ODE port (docs/port-notes/adapode.md §9).
#
#   julia --startup-file=no --project=<env with Grassmann 0.8.46, Cartan 0.4.16, MeshTopology 0.1.0, JSON> \
#       oracle/adapode/gen.jl [section …]
#
# Writes oracle/golden/adapode/<section>.json for the sections tables, fixed, adaptive, chaos, flow,
# geodesic, leapfrog, runtests (all of them without arguments; each lives in sections/<name>.jl).
# Adapode.jl master is loaded by `include` with the patches of load.jl (the adaptive integrators
# need them to record their times, defect B1). Floats are IEEE bit patterns "0x…" (every
# comparison is bit-exact unless a case says otherwise); states are flattened point by point in
# Grassmann's storage order (the Lean `OdeState` layout). Long trajectories are summarized by
# `digest`: word-wise FNV-1a over the bit patterns of all times, then all state coefficients
# (Tests/Adapode computes the same).
#
# The work of each section is inside functions: Julia compiles a top-level block that contains
# loops as one thunk, and inference of one large block of Grassmann types does not terminate.
include(joinpath(@__DIR__, "load.jl"))
using JSON

const OUT = joinpath(@__DIR__, "..", "golden", "adapode")
mkpath(OUT)
save(name, data) = (open(io -> JSON.print(io, data), joinpath(OUT, name * ".json"), "w");
    println(stderr, "wrote ", name, " (", filesize(joinpath(OUT, name * ".json")), " bytes)"); flush(stderr))

hx(x::Real) = "0x" * string(reinterpret(UInt64, Float64(x)), base = 16, pad = 16)
hxs(xs) = [hx(x) for x in xs]
coeffs(x::Real) = [Float64(x)]
coeffs(x::AbstractVector{<:Real}) = collect(Float64, x)
coeffs(x) = collect(Float64, value(x))
function flatstates(F)   # (`reduce(vcat, …; init)` is quadratic)
    out = Float64[]
    for x in F
        append!(out, coeffs(x))
    end
    out
end
function digest(xs::Vector{Float64})
    h = 0xcbf29ce484222325
    for x in xs
        h = (h ⊻ reinterpret(UInt64, x)) * 0x100000001b3
    end
    "0x" * string(h, base = 16, pad = 16)
end
errstr(e) = (s = sprint(showerror, e); string(nameof(typeof(e)), ": ", first(s, 200)))
progress(xs...) = (println(stderr, xs...); flush(stderr))

const meta = Dict("julia" => string(VERSION), "adapode" => "master 91e8516 (include)", "cartan" => string(pkgversion(Cartan)),
    "grassmann" => string(pkgversion(Grassmann)), "patches" => "load.jl: B1 (adaptive times), B1b (adaptive ABM bootstrap times)")

# the test problems (Tests/Adapode/Problems.lean)
const V3 = Submanifold(3)
lorenz(x) = Chain(10.0(x[2] - x[1]), x[1] * (28.0 - x[3]) - x[2], x[1] * x[2] - (8 / 3) * x[3])
osc(x) = Chain(x[2], -x[1] - 0.1x[2])
nonauto(x) = Chain(x[1] * cos(point(x)) + point(x))
const Bspin = Multivector{V3}(Values(0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.5, 0.0))
spin(x) = Bspin * fiber(x)
const probs = [("lorenz", lorenz, Chain(10.0, 10.0, 10.0)), ("osc", osc, Chain(1.0, 0.0)), ("nonauto", nonauto, Chain(1.0)),
    ("spin", spin, Multivector{V3}(Values(1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)))]
const x0 = Chain(10.0, 10.0, 10.0)

for sec in ("tables", "fixed", "adaptive", "chaos", "flow", "geodesic", "leapfrog", "runtests")
    if isempty(ARGS) || sec in ARGS
        progress("== ", sec)
        include(joinpath(@__DIR__, "sections", sec * ".jl"))
    end
end
progress("done")

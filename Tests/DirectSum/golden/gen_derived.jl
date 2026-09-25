# Oracle generator for the derived blade-operation suite (Tests/DirectSum/Derived.lean).
#
#   julia --startup-file=no --project=oracle Tests/DirectSum/golden/gen_derived.jl Tests/DirectSum/golden/derived.jsonl
#
# Complements oracle/golden/blades/dump_all.jsonl (grassmann-parity.md §9) with what that dump
# does not cover:
#   P1'  the derived binary operators of §2.3 on every blade pair: a<b (⨼), a⨽b, a<<b, a>>b,
#        a∗b, a⊛b, a⟇b (veedot), antidot(a,b);
#   P4   tangent spaces including pairs whose ∂ bits overlap (the dump skips them): * ∧ ∨ ⋅;
#   P5   larger N (6 … 24, Euclidean and alternating signature), random blade pairs: * ∧ ∨ ⋅, ⋆a, ~a
#        (exercises Julia's cache_limit / sparse_limit regimes, values must not depend on them);
#   P6   signbit(V), signbit(V,G) and the blade predicates/projections iseven isodd even odd real imag.
#
# Every space runs in a fresh Julia process (defect 4: the regressive/interior cache key omits
# diffvars/diffmode), spawned by this script; the parent concatenates the per-space outputs.
# Output: JSON lines, an {"info": …} record per space followed by its records (dump schema:
# each op is {"s": string, "t": [[bits, coef]…], "T": type name} or {"err": message}).
using Grassmann, DirectSum, Leibniz, LinearAlgebra, JSON, Random
const Gm = Grassmann

fmtc(c) = (c isa Real && !(c isa Grassmann.TensorAlgebra)) ? (isinteger(c) ? Int(c) : Float64(c)) : string(c)
function terms(x)
    x isa Zero && return Any[]
    x isa Submanifold && return Any[Any[Int(UInt(x)), 1]]
    x isa Single && return Any[Any[Int(UInt(basis(x))), fmtc(value(x))]]
    (x isa Number && !(x isa Grassmann.TensorAlgebra)) && return Any[Any[0, fmtc(x)]]
    V = Manifold(x); N = mdims(V)
    if x isa Chain
        ib = Leibniz.indexbasis(N, grade(x)); vals = value(x)
    else
        m = Multivector(x); ib = Leibniz.indexbasis(N); vals = value(m)
    end
    Any[Any[Int(ib[i]), fmtc(vals[i])] for i in 1:length(vals)
        if !((vals[i] isa Real && !(vals[i] isa Grassmann.TensorAlgebra)) && iszero(vals[i]))]
end
function rec(f)
    try
        r = f()
        r isa Bool && return Dict("b" => r)
        return Dict("s" => string(r), "t" => terms(r), "T" => string(nameof(typeof(r))))
    catch e
        return Dict("err" => first(sprint(showerror, e), 120))
    end
end

E2 = Signature("++")
alt(n) = Signature(join(isodd(i) ? '-' : '+' for i in 1:n))
const SPACES = Any[
    ("E3", () -> Signature("+++")), ("M4", () -> Signature("-+++")), ("I4", () -> 4),
    ("C3", () -> Signature("∞∅+")), ("C4neg", () -> Signature("∞∅+-")), ("P4orig", () -> Signature("∅+++")),
    ("D3", () -> DiagonalForm((1, 2, -3))), ("D3deg", () -> DiagonalForm((1, 1, 0))),
    ("dual3", () -> Signature("+-+")'), ("mixed2", () -> E2 ⊕ E2'),
    ("tan21", () -> tangent(E2)), ("tan22", () -> tangent(E2, 2, 2)), ("tanM", () -> tangent(Signature("-+"), 2, 1)),
    ("MT3", () -> Gm.MetricTensor([1 0.5 0; 0.5 1 0.5; 0 0.5 1])),
]
const LARGE = [6, 8, 12, 13, 20, 21, 23, 24]
const NSAMPLE = parse(Int, get(ENV, "NSAMPLE", "150"))

function info(nm, V0, V)
    S0 = V0 isa Int ? Signature(V0) : V0
    d = Dict("space" => nm, "show" => string(V), "N" => mdims(V), "opts" => DirectSum.options(S0),
        "metricbits" => (S0 isa Signature ? Int(DirectSum.metric(S0)) : -1),
        "diag" => (S0 isa DiagonalForm ? collect(S0[:]) : nothing),
        "diffvars" => diffvars(V), "diffmode" => diffmode(V), "dyadmode" => dyadmode(V), "grade" => grade(V))
    Dict("info" => d)
end

# kept out of `info`: Julia's inference concretely evaluates the @pure `signbit(V)` of a
# constant space even on an untaken branch, i.e. 2^N parities for the large spaces
function basisinfo!(rec, V)
    d = rec["info"]
    b = Λ(V).b
    d["basis"] = [Int(UInt(x)) for x in b]
    d["names"] = string.(b)
    d["signbit"] = try collect(signbit(V)) catch e; nothing end
    d["signbitG"] = try [collect(signbit(V, G)) for G in 0:mdims(V)] catch e; nothing end
    rec
end

binops = Any[("lt", (x, y) -> x < y), ("lcontr", (x, y) -> x ⨼ y), ("rcontr", (x, y) -> x ⨽ y),
    ("lshift", (x, y) -> x << y), ("rshift", (x, y) -> x >> y), ("star", (x, y) -> x ∗ y),
    ("cdast", (x, y) -> x ⊛ y), ("veedot", (x, y) -> x ⟇ y), ("antidot", (x, y) -> Gm.antidot(x, y))]
prodops = Any[("mul", (x, y) -> x * y), ("wedge", (x, y) -> x ∧ y), ("vee", (x, y) -> x ∨ y),
    ("dot", (x, y) -> contraction(x, y))]
unops = Any[("iseven", iseven), ("isodd", isodd), ("even", even), ("odd", odd), ("real", real), ("imag", imag)]

function small(io, nm, V0)
    V = Submanifold(V0)
    println(io, JSON.json(basisinfo!(info(nm, V0, V), V)))
    b = Λ(V).b
    dm = diffvars(V) ≠ 0 ? (dyadmode(V) < 0 ? |(Leibniz.diffmask(V)...) : Leibniz.diffmask(V)) : UInt(0)
    for x in b
        u = Dict{String,Any}("space" => nm, "a" => Int(UInt(x)))
        for (op, f) in unops
            u[op] = rec(() -> f(x))
        end
        println(io, JSON.json(Dict("space" => nm, "u" => u)))
        for y in b
            d = Dict{String,Any}("space" => nm, "a" => Int(UInt(x)), "b" => Int(UInt(y)))
            if iszero(UInt(x) & UInt(y) & dm)
                for (op, f) in binops
                    d[op] = rec(() -> f(x, y))
                end
            else
                # P4: overlapping ∂ bits (only the products; the derived ops add nothing new)
                d["overlap"] = true
                for (op, f) in prodops
                    d[op] = rec(() -> f(x, y))
                end
            end
            println(io, JSON.json(d))
        end
    end
end

function large(io, N, altsig)
    nm = (altsig ? "A" : "E") * string(N)
    V0 = altsig ? alt(N) : Signature(N)
    V = Submanifold(V0)
    println(io, JSON.json(info(nm, V0, V)))
    rng = MersenneTwister(1000 * N + altsig)
    full = UInt(1) << N - 1
    for _ in 1:NSAMPLE
        a = rand(rng, UInt) & full
        c = rand(rng, UInt) & full
        # bias towards sparse and overlapping pairs as well as random ones
        r = rand(rng, 1:3)
        c = r == 1 ? c : r == 2 ? (a & c) | (UInt(1) << rand(rng, 0:N-1)) : (a ⊻ (UInt(1) << rand(rng, 0:N-1)))
        x = Submanifold{V}(a); y = Submanifold{V}(c)
        d = Dict{String,Any}("space" => nm, "a" => Int(a), "b" => Int(c), "large" => true)
        for (op, f) in prodops
            d[op] = rec(() -> f(x, y))
        end
        d["hr"] = rec(() -> ⋆(x)); d["rev"] = rec(() -> reverse(x))
        println(io, JSON.json(d))
    end
end

if length(ARGS) == 2 && ARGS[1] == "--space"
    nm = ARGS[2]
    if startswith(nm, "E") && all(isdigit, nm[2:end])
        large(stdout, parse(Int, nm[2:end]), false)
    elseif startswith(nm, "A") && all(isdigit, nm[2:end])
        large(stdout, parse(Int, nm[2:end]), true)
    else
        small(stdout, nm, Dict(SPACES)[nm]())
    end
else
    out = ARGS[1]
    names = vcat(first.(SPACES), ["E$N" for N in LARGE], ["A$N" for N in LARGE])
    me = @__FILE__
    proj = Base.active_project()
    open(out, "w") do io
        for nm in names
            t0 = time()
            txt = read(`$(Base.julia_cmd()) --startup-file=no --project=$proj $me --space $nm`, String)
            write(io, txt)
            println(stderr, nm, " done in ", round(time() - t0, digits = 1), "s")
        end
    end
end

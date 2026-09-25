# Julia twin of Bench/Harness.lean: the same measurement algorithm, result schema and CLI, so
# that every Lean case key `suite/case` is compared with a Julia case measured identically.
#
#   julia --startup-file=no --project=<env> oracle/bench/<suite>.jl [--smoke] [--json out.json]
#         [--filter substr]... [--samples n] [--sample-ms n] [--quiet]
#
# Algorithm (see the Lean module docstring):
#   1. warm-up: one call (compiles), then a second timed call whose checksum is the reported check
#      (skipped when the first call, compilation excluded, took longer than the case cap);
#   2. calibration: k grows ×4 until a batch of k calls takes ≥ sample_ns/10, then k is scaled so
#      that a batch lasts about sample_ns (default 20 ms);
#   3. `samples` batches (default 7, fewer when a single call is slow: the case is capped near
#      case_ns), each giving ns per operation = batch time / (k · ops); min and median reported.
#
# Every body call goes through a call-site `@noinline`, so its work cannot be hoisted out of the
# batch loop; `blackbox(i, x)` hides literal inputs from constant propagation. `GC.gc()` runs
# before each case (untimed).
module BenchHarness

export Ctx, bench!, benchwith!, blackbox, checkval, splitmix64, randfloats, randwords, main_suites, sized,
    register!, REGISTRY

mutable struct Config
    smoke::Bool
    sample_ns::Int
    samples::Int
    case_ns::Int
    filters::Vector{String}
    json::Union{Nothing,String}
    quiet::Bool
end
Config() = Config(false, 20_000_000, 7, 1_500_000_000, String[], nothing, false)

struct Result
    suite::String
    name::String
    param::String
    ops::Int
    iters::Int
    samples::Int
    min_ns::Float64
    median_ns::Float64
    max_ns::Float64
    check::Float64
end
key(r::Result) = r.suite * "/" * r.name

mutable struct Ctx
    cfg::Config
    suite::String
    results::Vector{Result}
end

"`full` normally, `small` under `--smoke` (Lean `Bench.size`)."
sized(ctx::Ctx, full, small) = ctx.cfg.smoke ? small : full

# ------------------------------------------------------------------ sinks
"Scalar summary of a result, as Lean's `Checksum`: numbers are themselves, collections and
strings their length, tuples the sum of their parts."
checkval(x::Real) = Float64(x)
checkval(x::AbstractString) = Float64(length(x))
checkval(x::AbstractArray) = Float64(length(x))
checkval(x::AbstractDict) = Float64(length(x))
checkval(x::AbstractSet) = Float64(length(x))
checkval(x::Tuple) = isempty(x) ? 0.0 : sum(checkval, x)
checkval(::Nothing) = 0.0
checkval(::Any) = NaN   # not comparable (written as null)

"An opaque identity for literal inputs (no constant propagation through it)."
@noinline blackbox(salt, x) = Base.compilerbarrier(:const, x)

const SINK = Ref(0.0)

# ------------------------------------------------------------------ deterministic inputs
"SplitMix64 step (Tests/Util/Random.lean): returns (value, next state)."
function splitmix64(s::UInt64)
    s += 0x9e3779b97f4a7c15
    z = s
    z = (z ⊻ (z >> 30)) * 0xbf58476d1ce4e5b9
    z = (z ⊻ (z >> 27)) * 0x94d049bb133111eb
    (z ⊻ (z >> 31), s)
end

"`n` floats uniform in `[lo, hi)` from SplitMix64 seeded with `seed` (53-bit mantissas), the
same sequence as `Bench.randFloats` in Lean."
function randfloats(n::Integer, seed::UInt64, lo::Float64 = 0.0, hi::Float64 = 1.0)
    out = Vector{Float64}(undef, n)
    s = seed
    for i in 1:n
        z, s = splitmix64(s)
        u = Float64(z >> 11) * 0x1.0p-53
        out[i] = lo + (hi - lo) * u
    end
    out
end

"`n` raw SplitMix64 outputs (Lean `Bench.randWords`)."
function randwords(n::Integer, seed::UInt64)
    out = Vector{UInt64}(undef, n)
    s = seed
    for i in 1:n
        out[i], s = splitmix64(s)
    end
    out
end

# ------------------------------------------------------------------ timing
function runbatch(body::F, k::Int, i::Int) where {F}
    acc = 0.0
    for j in i:i+k-1
        r = @noinline body(j)
        acc += checkval(r)
    end
    acc
end

function timebatch(body::F, k::Int, i::Int) where {F}
    t0 = time_ns()
    c = runbatch(body, k, i)
    SINK[] = c
    t1 = time_ns()
    (Int(t1 - t0), c)
end

function median(xs::Vector{Float64})
    s = sort(xs)
    n = length(s)
    isodd(n) ? s[(n+1)÷2] : (s[n÷2] + s[n÷2+1]) / 2
end

function fmtns(ns)
    r(x) = string(round(x; sigdigits = 6))
    ns < 1e3 ? r(ns) * " ns" : ns < 1e6 ? r(ns / 1e3) * " µs" : ns < 1e9 ? r(ns / 1e6) * " ms" : r(ns / 1e9) * " s"
end

selected(cfg::Config, key) = isempty(cfg.filters) || any(f -> occursin(f, key), cfg.filters)

function measure!(ctx::Ctx, name, param, ops, body::F) where {F}
    cfg = ctx.cfg
    ops = max(ops, 1)
    GC.gc()
    # first call compiles; a second (timed) call follows unless the first call's run time,
    # compilation excluded, already exceeds the case cap
    st = @timed body(0)
    t1 = round(Int, (st.time - st.compile_time) * 1e9)
    tw, check = t1 > cfg.case_ns ? (t1, checkval(st.value)) : timebatch(body, 1, 0)
    k = 1; t = tw; i = 1
    if tw < cfg.sample_ns ÷ 10
        for _ in 1:40
            tk, _ = timebatch(body, k, i)
            i += k; t = tk
            (tk ≥ cfg.sample_ns ÷ 10 || k ≥ (1 << 40)) && break
            k *= 4
        end
    end
    percall = max(t, 1) / k
    kk = max(1, ceil(Int, cfg.sample_ns / percall))
    batch = percall * kk
    nsamp = cfg.smoke ? 1 : max(1, min(cfg.samples, floor(Int, cfg.case_ns / max(batch, 1))))
    per = Float64[]
    for _ in 1:nsamp
        ts, _ = timebatch(body, kk, i)
        i += kk
        push!(per, ts / (kk * ops))
    end
    r = Result(ctx.suite, name, param, ops, kk, nsamp, minimum(per), median(per), maximum(per), check)
    push!(ctx.results, r)
    println("  ", rpad(key(r), 44), " ", rpad(param, 16), " median ", rpad(fmtns(r.median_ns), 12),
            " min ", rpad(fmtns(r.min_ns), 12), " ($(kk)×$(nsamp))")
    flush(stdout)
    nothing
end

"Benchmark a case: `body(i)` is one call (`ops` operations) at iteration index `i`."
function bench!(body::F, ctx::Ctx, name::AbstractString; ops::Integer = 1, param::AbstractString = "") where {F}
    selected(ctx.cfg, ctx.suite * "/" * name) || return nothing
    measure!(ctx, name, param, Int(ops), body)
end

"Benchmark with an untimed setup that runs only when the case is selected: `body(input, i)`."
function benchwith!(body::F, setup::S, ctx::Ctx, name::AbstractString; ops::Integer = 1,
                    param::AbstractString = "") where {F,S}
    selected(ctx.cfg, ctx.suite * "/" * name) || return nothing
    inp = setup()
    measure!(ctx, name, param, Int(ops), let inp = inp; i -> body(inp, i); end)
end

# ------------------------------------------------------------------ output and CLI
jnum(x::Float64) = isfinite(x) ? repr(x) : "null"
jstr(s) = "\"" * escape_string(s) * "\""

function tojson(cfg::Config, rs::Vector{Result})
    io = IOBuffer()
    print(io, "{\"lang\": \"julia\", \"smoke\": ", cfg.smoke, ", \"sample_ns\": ", cfg.sample_ns,
          ", \"samples\": ", cfg.samples, ", \"julia\": ", jstr(string(VERSION)),
          ", \"threads\": ", Threads.nthreads(), ",\n \"results\": [\n  ")
    for (j, r) in enumerate(rs)
        j > 1 && print(io, ",\n  ")
        print(io, "{\"key\": ", jstr(key(r)), ", \"suite\": ", jstr(r.suite), ", \"case\": ", jstr(r.name),
              ", \"param\": ", jstr(r.param), ", \"ops\": ", r.ops, ", \"iters\": ", r.iters,
              ", \"samples\": ", r.samples, ", \"min_ns\": ", jnum(r.min_ns), ", \"median_ns\": ",
              jnum(r.median_ns), ", \"max_ns\": ", jnum(r.max_ns), ", \"check\": ", jnum(r.check), "}")
    end
    print(io, "\n]}\n")
    String(take!(io))
end

function parseargs(args)
    cfg = Config()
    names = String[]
    k = 1
    while k <= length(args)
        a = args[k]
        if a == "--smoke"
            cfg.smoke = true; cfg.sample_ns = 1_000_000
        elseif a == "--quiet"
            cfg.quiet = true
        elseif a == "--json"
            cfg.json = args[k+1]; k += 1
        elseif a == "--filter"
            push!(cfg.filters, args[k+1]); k += 1
        elseif a == "--samples"
            cfg.samples = max(1, parse(Int, args[k+1])); k += 1
        elseif a == "--sample-ms"
            cfg.sample_ns = max(1, parse(Int, args[k+1])) * 1_000_000; k += 1
        elseif startswith(a, "-")
            error("unknown option $a")
        else
            push!(names, a)
        end
        k += 1
    end
    cfg, names
end

"Suites registered by the files `oracle/bench/run.jl` includes."
const REGISTRY = Pair{String,Any}[]
"Register a suite (called at the top level of every suite file)."
register!(name::AbstractString, f) = (filter!(p -> first(p) != name, REGISTRY); push!(REGISTRY, String(name) => f); nothing)

"Run `suites` (name => function of a `Ctx`) with the command line `args`; writes `--json`."
function main_suites(suites::Vector{<:Pair}, args = ARGS)
    cfg, names = parseargs(args)
    chosen = isempty(names) ? suites : filter(s -> any(n -> lowercase(n) == lowercase(first(s)), names), suites)
    results = Result[]
    for (name, f) in chosen
        cfg.quiet || println("== ", name)
        f(Ctx(cfg, name, results))
    end
    if cfg.json !== nothing
        write(cfg.json, tojson(cfg, results))
        println("wrote $(length(results)) results to $(cfg.json)")
    end
    results
end

end # module

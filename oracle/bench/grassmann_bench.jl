# Julia side of the Grassmann product benchmarks (docs/PERF.md; Lean side: Bench/Grassmann.lean).
#
#   julia --startup-file=no --project=oracle oracle/bench/grassmann_bench.jl [smoke]
#
# For each space (ℝ3, STA, PGA3, CGA3) and operation: ns per call over N calls on a ring of
# K = 1024 random Float64 operands (inputs vary per call, so nothing is loop-invariant), each
# result's coefficients summed into an accumulator (so every output is computed). After a
# warm-up run, the best of 7 timed runs (`@elapsed`; BenchmarkTools is not in the oracle env).
# The Lean benchmark runs the identical loop.

using Grassmann, Random

const K = 1024

total(x) = sum(value(x))
total(x::Values) = sum(x)

function bench1(f, xs, N)
    mask = K - 1
    acc = 0.0
    @inbounds for i in 0:N-1
        acc += total(f(xs[(i & mask) + 1]))
    end
    acc
end

function bench2(f, xs, ys, N)
    mask = K - 1
    acc = 0.0
    @inbounds for i in 0:N-1
        acc += total(f(xs[(i & mask) + 1], ys[((i * 7 + 3) & mask) + 1]))
    end
    acc
end

# Every result goes to a global sink: an unused pure loop would be removed by Julia's effect
# analysis (a bare `@elapsed(run(N))` of `sum(value(~m))` measures nothing).
const SINK = Ref(0.0)

function iterate(f, x, N)
    for _ in 1:N
        x = f(x)
    end
    total(x)
end

function timed(name, run, N)
    SINK[] += run(N ÷ 10)                 # warm-up (compiles the specialized loop)
    best = Inf
    for _ in 1:7
        t0 = time_ns()
        SINK[] += run(N)
        best = min(best, (time_ns() - t0) / N)
    end
    println(rpad(name, 28), lpad(string(round(best, digits = 2)), 9), " ns/op   (checksum ",
            round(run(1000), sigdigits = 6), ")")
end

rnd(rng, n) = Values{n,Float64}(Tuple(2 .* rand(rng, n) .- 1))

function bench_space(label, V, N)
    rng = MersenneTwister(42)
    n = mdims(V)
    h = 2^(n - 1)
    M = [Multivector{V}(rnd(rng, 2^n)) for _ in 1:K]
    S = [Spinor{V}(rnd(rng, h)) for _ in 1:K]
    c1 = binomial(n, 1); c2 = binomial(n, 2)
    U = [Chain{V,1}(rnd(rng, c1)) for _ in 1:K]
    C = [Chain{V,2}(rnd(rng, c2)) for _ in 1:K]
    println("== $label  $(V)")
    mvN = n ≥ 5 ? N ÷ 10 : N
    timed("sum of an operand", k -> bench1(identity, M, k), N)
    timed("copy of an operand", k -> bench1(m -> Values(Base.setindex(Tuple(value(m)), value(m)[2], 1)), M, k), N)
    timed("Multivector*Multivector", k -> bench2(*, M, M, k), mvN)
    timed("Spinor*Spinor", k -> bench2(*, S, S, k), N)
    timed("R*v*~R", k -> bench2((R, v) -> R * v * ~R, S, U, k), N)
    timed("v ⊘ R", k -> bench2((R, v) -> v ⊘ R, S, U, k), N)
    timed("R >>> v", k -> bench2((R, v) -> R >>> v, S, U, k), N)
    timed("Chain1∧Chain1", k -> bench2(∧, U, U, k), N)
    timed("Chain2*Chain1", k -> bench2(*, C, U, k), N)
    timed("reverse Multivector", k -> bench1(~, M, k), N)
    timed("reverse in place (m := ~m)", k -> iterate(~, M[1], k), N)
    timed("hodge Multivector", k -> bench1(⋆, M, k), N)
    timed("hodge Chain1", k -> bench1(⋆, U, k), N)
end

smoke = "smoke" in ARGS
N = smoke ? 10_000 : 10_000_000
println("Julia $(VERSION), Grassmann $(pkgversion(Grassmann)), threads=$(Threads.nthreads())")
bench_space("ℝ3", S"+++", N)
bench_space("STA", S"-+++", N)
bench_space("PGA3", D"0,1,1,1", N)
bench_space("CGA3", S"∞∅+++", N)

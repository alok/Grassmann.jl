# Julia twin of Bench/Dynamic.lean (`dynamic` suite): Grassmann.jl elements with Float64
# coefficients stored in a `Vector{Any}`, so every operation dispatches on the runtime type, as
# the Lean dynamic layer `TA` dispatches on its kind. Spaces: ℝ3 (`Submanifold(3)`), PGA3
# (`D"0,1,1,1"`) and CGA3 (`S"∞∅+++"`). Same operands (randfloats/randwords streams), same sweep
# (k, 7k + 3), same checksum (the sum of every result's stored coefficients).
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "harness.jl"))
using .BenchHarness
using Grassmann

const dyn_V = Submanifold(3)
const dyn_ring = 1024

"`dyn_ring` containers of kind `kind` (`:multi` or `:chain`, grade 1) of the space `V`."
function dyn_containers(V, kind::Symbol, seed::UInt64)
    n = mdims(V)
    w = kind === :multi ? 2^n : n
    xs = randfloats(dyn_ring * w, seed, -1.0, 1.0)
    out = Vector{Any}(undef, dyn_ring)
    for k in 0:dyn_ring-1
        v = xs[k*w+1:k*w+w]
        out[k+1] = kind === :multi ? Multivector{V}(v...) : Chain{V,1}(v...)
    end
    out
end

dyn_containers(kind::Symbol, seed::UInt64) = dyn_containers(dyn_V, kind, seed)

function dyn_singles(seed::UInt64)
    xs = randfloats(dyn_ring, seed, -1.0, 1.0)
    bs = randwords(dyn_ring, seed + 1)
    out = Vector{Any}(undef, dyn_ring)
    for k in 1:dyn_ring
        # the blade mask 1 + (w mod 7), as in Lean
        out[k] = xs[k] * Grassmann.getbasis(dyn_V, UInt(1 + bs[k] % 7))
    end
    out
end

dyn_sum(x::Grassmann.Zero) = 0.0
dyn_sum(x::Submanifold) = 1.0
dyn_sum(x::Grassmann.Single) = Float64(Grassmann.value(x))
dyn_sum(x) = Float64(sum(Grassmann.value(x)))

@noinline function dyn_sweep2(f::F, xs::Vector{Any}, ys::Vector{Any}, n::Int) where {F}
    acc = 0.0
    for k in 0:n-1
        acc += dyn_sum(f(xs[(k & 1023) + 1], ys[((7k + 3) & 1023) + 1]))
    end
    acc
end

@noinline function dyn_sweep1(f::F, xs::Vector{Any}, n::Int) where {F}
    acc = 0.0
    for k in 0:n-1
        acc += dyn_sum(f(xs[(k & 1023) + 1]))
    end
    acc
end

"The container cases of one space (Lean `dyn_cases%`): keys `<case>_<label>`, seeds `16·seed + j`."
function dyn_space(ctx, label, V, seed)
    sd(j) = UInt64(seed * 16 + j)
    ms = dyn_containers(V, :multi, sd(1))
    ns = dyn_containers(V, :multi, sd(2))
    cs = dyn_containers(V, :chain, sd(3))
    ds = dyn_containers(V, :chain, sd(4))
    n = dyn_ring
    bench!(i -> dyn_sweep2(*, blackbox(i, ms), ns, n), ctx, "mul_multi_$label"; ops = n)
    bench!(i -> dyn_sweep2(*, blackbox(i, cs), ds, n), ctx, "mul_chain1_$label"; ops = n)
    bench!(i -> dyn_sweep2(∧, blackbox(i, cs), ds, n), ctx, "wedge_chain1_$label"; ops = n)
    bench!(i -> dyn_sweep2(+, blackbox(i, ms), ns, n), ctx, "add_multi_$label"; ops = n)
    bench!(i -> dyn_sweep1(~, blackbox(i, ms), n), ctx, "reverse_multi_$label"; ops = n)
end

function suite_dynamic(ctx)
    ms = dyn_containers(:multi, UInt64(101))
    ns = dyn_containers(:multi, UInt64(102))
    cs = dyn_containers(:chain, UInt64(103))
    ds = dyn_containers(:chain, UInt64(104))
    ss = dyn_singles(UInt64(105))
    ts = dyn_singles(UInt64(107))
    n = dyn_ring
    bench!(i -> dyn_sweep2(*, blackbox(i, ms), ns, n), ctx, "mul_multi_R3"; ops = n)
    bench!(i -> dyn_sweep2(*, blackbox(i, cs), ds, n), ctx, "mul_chain1_R3"; ops = n)
    bench!(i -> dyn_sweep2(∧, blackbox(i, cs), ds, n), ctx, "wedge_chain1_R3"; ops = n)
    bench!(i -> dyn_sweep2(*, blackbox(i, ss), ts, n), ctx, "mul_single_R3"; ops = n)
    bench!(i -> dyn_sweep2(+, blackbox(i, ms), ns, n), ctx, "add_multi_R3"; ops = n)
    bench!(i -> dyn_sweep1(~, blackbox(i, ms), n), ctx, "reverse_multi_R3"; ops = n)
    dyn_space(ctx, "PGA3", D"0,1,1,1", 11)
    dyn_space(ctx, "CGA3", S"∞∅+++", 12)
end

register!("dynamic", suite_dynamic)
(abspath(PROGRAM_FILE) == @__FILE__) && main_suites(["dynamic" => suite_dynamic])

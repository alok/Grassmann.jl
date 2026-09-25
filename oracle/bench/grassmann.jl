# Julia twin of Bench/Grassmann.lean (`grassmann` suite): the typed operations of Grassmann.jl
# 0.8.46 on rings of K = 1024 operands built from the harness's SplitMix64 floats in [-1, 1)
# (element i takes the floats (i-1)d+1 : i·d, the Lean storage order), each body call applying
# the operation to the whole ring (binary operations pair xs[i] with ys[(7i + 3) mod K]) and
# summing every coefficient of every result, K operations per call. Keys, inputs and checksums
# match the Lean suite (Bench/Grassmann/Products.lean).
#
#   julia --startup-file=no --project=oracle oracle/bench/grassmann.jl [--smoke] [--json out.json] [--filter s]
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "harness.jl"))
using .BenchHarness
using Grassmann, LinearAlgebra

const GK = 1024

"The sum of every coefficient of a result (Lean `total`, summed in storage order)."
gtotal(x::Real) = Float64(x)
gtotal(x::Values) = sum(x)
gtotal(x) = gtotal(value(x))

"`Σ f(xs[i], ys[(7i + 3) & (K-1)])` over the ring."
function gl2(f::F, xs, ys) where {F}
    acc = 0.0
    m = GK - 1
    @inbounds for i in 0:GK-1
        acc += gtotal(f(xs[(i & m) + 1], ys[((7i + 3) & m) + 1]))
    end
    acc
end

"`Σ f(xs[i])` over the ring."
function gl1(f::F, xs) where {F}
    acc = 0.0
    @inbounds for i in 1:GK
        acc += gtotal(f(xs[i]))
    end
    acc
end

"`f` applied `k` times to `x` (each result the operand of the next call)."
function giterate(f::F, x, k) where {F}
    for _ in 1:k
        x = f(x)
    end
    gtotal(x)
end

"`K` elements of `d` coefficients from SplitMix64 seeded with `seed` (Lean `ringOf`)."
function gring(mk::F, d::Int, seed) where {F}
    xs = randfloats(d * GK, UInt64(seed), -1.0, 1.0)
    [mk(Values{d,Float64}(ntuple(j -> xs[(i-1)*d+j], d))) for i in 1:GK]
end

gcase2(ctx, name, f::F, xs, ys) where {F} = bench!(i -> gl2(f, blackbox(i, xs), ys), ctx, name; ops = GK, param = "K=$GK")
gcase1(ctx, name, f::F, xs) where {F} = bench!(i -> gl1(f, blackbox(i, xs)), ctx, name; ops = GK, param = "K=$GK")

"Which case groups a space runs (Lean `Bench.Grassmann.CaseSet`)."
Base.@kwdef struct GCaseSet
    inner::Bool = true
    norms::Bool = true
    inverses::Bool = false
    spinorInverses::Bool = false
    linear::Bool = true
    unary::Bool = true
    floors::Bool = true
end

function gspace(ctx, label, V, seed, cs::GCaseSet = GCaseSet())
    n = mdims(V)
    k(s) = "$label/$s"
    sd(j) = seed * 16 + j
    M = gring(v -> Multivector{V}(v), 2^n, sd(1))
    N = gring(v -> Multivector{V}(v), 2^n, sd(2))
    S = gring(v -> Spinor{V}(v), 2^(n-1), sd(3))
    T = gring(v -> Spinor{V}(v), 2^(n-1), sd(4))
    U = gring(v -> Chain{V,1}(v), n, sd(5))
    W = gring(v -> Chain{V,1}(v), n, sd(6))
    C = gring(v -> Chain{V,2}(v), binomial(n, 2), sd(7))
    H = gring(v -> Chain{V,n-1}(v), n, sd(8))
    J = gring(v -> Chain{V,n-1}(v), n, sd(9))
    if cs.floors
        gcase1(ctx, k("sum of an operand"), identity, M)
        gcase1(ctx, k("copy of an operand"), m -> Values(Base.setindex(Tuple(value(m)), value(m)[2], 1)), M)
    end
    # products and sandwiches
    gcase2(ctx, k("Multivector*Multivector"), *, M, N)
    gcase2(ctx, k("Spinor*Spinor"), *, S, T)
    gcase2(ctx, k("Chain1*Chain1"), *, U, W)
    gcase2(ctx, k("Chain1∧Chain1"), ∧, U, W)
    gcase2(ctx, k("Chain2*Chain1"), *, C, U)
    gcase2(ctx, k("Multivector∧Multivector"), ∧, M, N)
    gcase2(ctx, k("R*v*~R"), (R, v) -> R * v * ~R, S, U)
    gcase2(ctx, k("v ⊘ R"), (R, v) -> v ⊘ R, S, U)
    gcase2(ctx, k("R >>> v"), (R, v) -> R >>> v, S, U)
    if cs.inner
        gcase2(ctx, k("Chain1⋅Chain1"), ⋅, U, W)
        gcase2(ctx, k("Chain2⋅Chain1"), ⋅, C, U)
        gcase2(ctx, k("Chain1⨼Chain2"), ⨼, U, C)
        gcase2(ctx, k("Multivector⋅Multivector"), ⋅, M, N)
        gcase2(ctx, k("Chain(n-1)∨Chain(n-1)"), ∨, H, J)
        gcase2(ctx, k("Multivector∨Multivector"), ∨, M, N)
        gcase2(ctx, k("Chain1×Chain1"), ×, U, W)
        gcase2(ctx, k("Multivector⊛Multivector"), ⊛, M, N)
    end
    if cs.norms
        gcase1(ctx, k("abs2 Multivector"), abs2, M)
        gcase1(ctx, k("abs2 Spinor"), abs2, S)
        gcase1(ctx, k("abs2 Chain1"), abs2, U)
        gcase1(ctx, k("norm Multivector"), norm, M)
    end
    if cs.inverses
        gcase1(ctx, k("inv Chain1"), inv, U)
        gcase2(ctx, k("Chain1/Chain1"), /, U, W)
        gcase2(ctx, k("Chain1\\Chain1"), \, U, W)
    end
    if cs.spinorInverses
        gcase1(ctx, k("inv Spinor"), inv, S)
        gcase2(ctx, k("Spinor/Spinor"), /, S, T)
    end
    if cs.linear
        gcase2(ctx, k("Multivector+Multivector"), +, M, N)
        gcase2(ctx, k("Chain1+Chain1"), +, U, W)
        gcase2(ctx, k("Spinor-Spinor"), -, S, T)
        gcase1(ctx, k("2.5*Multivector"), a -> 2.5 * a, M)
        gcase2(ctx, k("2.5*Chain1+1.5*Chain1"), (a, b) -> 2.5 * a + 1.5 * b, U, W)
        gcase2(ctx, k("Chain1+Multivector"), +, U, N)
        gcase2(ctx, k("Chain1+Chain2"), +, U, C)
    end
    gcase1(ctx, k("reverse Multivector"), ~, M)
    bench!(i -> giterate(~, M[(i % GK) + 1], GK), ctx, k("reverse in place (m := ~m)"); ops = GK, param = "K=$GK")
    gcase1(ctx, k("hodge Multivector"), ⋆, M)
    gcase1(ctx, k("hodge Chain1"), ⋆, U)
    if cs.unary
        gcase1(ctx, k("involute Multivector"), involute, M)
        gcase1(ctx, k("clifford Multivector"), clifford, M)
        gcase1(ctx, k("complementright Multivector"), complementright, M)
        gcase1(ctx, k("grade 2 of Multivector"), a -> a(2), M)
        gcase1(ctx, k("even Multivector"), even, M)
    end
    nothing
end

function suite_grassmann(ctx)
    gspace(ctx, "ℝ2", S"++", 1, GCaseSet(inverses = true, spinorInverses = true))
    gspace(ctx, "ℝ3", S"+++", 2, GCaseSet(inverses = true, spinorInverses = true))
    gspace(ctx, "ℝ4", S"++++", 3, GCaseSet(inverses = true))
    gspace(ctx, "STA", S"-+++", 4)
    gspace(ctx, "PGA2", D"0,1,1", 5, GCaseSet(inverses = true))
    gspace(ctx, "PGA3", D"0,1,1,1", 6, GCaseSet(inverses = true))
    gspace(ctx, "CGA2", S"∞∅++", 7)
    gspace(ctx, "CGA3", S"∞∅+++", 8)
    gspace(ctx, "ℝ5", S"+++++", 9, GCaseSet(inverses = true))
end

register!("grassmann", suite_grassmann)
(abspath(PROGRAM_FILE) == @__FILE__) && main_suites(["grassmann" => suite_grassmann])

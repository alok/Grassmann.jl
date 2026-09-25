# Julia twin of Bench/Wilkinson.lean (`wilkinson` suite): expression parsing, SyntaxTree's
# exprval, and Wilkinson's errval (Stieltjes bound on the 3000-point log grid + Simpson score).
# Wilkinson itself does not load without PyPlot/Conda, so its kernels (src/Wilkinson.jl:17-88)
# are copied verbatim as in oracle/wilkinson/gen.jl; SyntaxTree comes by package id.
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "harness.jl"))
using .BenchHarness
const wk_ST = Base.require(Base.PkgId(Base.UUID("a4af3ec5-f8ac-5fed-a759-c2e80b4d74cb"), "SyntaxTree"))

function wk_floatset(T::DataType, N; scale = x -> x)
    l = scale(eps(T))
    u = scale(prevfloat(T(Inf)))
    return l:(u-l)/(N-1):u
end
wk_geonorm(x) = 1 / (1 - x)
function wk_Ω(p::Array{<:Number,1})
    n = length(p) - 1
    for k ∈ 1:length(p)
        p[k] == Inf && (n = k - 1; break)
    end
    return n
end
wk_genabs(expr, T::DataType) = wk_ST.genlatest(wk_ST.abs(wk_ST.sub(T, expr)), [:x])
function wk_stieltjes(set::AbstractRange, expr, T::DataType, T2::DataType = T; logi = log, expi = exp,
                      t = wk_genabs(expr, T))
    sc = collect(set)
    esc = expi.(sc)
    p = t.(esc)
    return Float64.((logi.(abs.(p)) - sc) .+ logi(wk_ST.callcount(expr) * eps(T2)))
end
function wk_simpson(set::AbstractRange, p::Array{<:Number,1}, n::Int = wk_Ω(p))
    s = 4sum(p[1:2:n-1]) + 2sum(p[2:2:n-1]) + sum(p[[1, n]])
    r = -(collect(set)[[n, 1]]...)
    return s / (3n * r)
end
"Wilkinson's `errval(expr, T, N)`: generates the absolute-value function (`genlatest`) per call."
wk_errval(expr, T = Float64, N = 3000) =
    (set = wk_floatset(T, N; scale = log); wk_geonorm(wk_simpson(set, wk_stieltjes(set, expr, T))))
"The same numerics with the function generated once, outside the timing (no code generation)."
wk_errval_pre(expr, t, T = Float64, N = 3000) =
    (set = wk_floatset(T, N; scale = log); wk_geonorm(wk_simpson(set, wk_stieltjes(set, expr, T; t = t))))

const WK_EXPRS = ["x^9 - 2", "(x - 2)^9", "2x^2 - 1//2", "x^2 + 3x + 2", "(x + 1) * (x + 2)",
    "2 + x * (3 + x)", "1.0 - 3.0x + x^3", "((x - 1) * x + 1) * x + 5", "(x - 1) * (x - 2) * (x - 3)",
    "x^9 - 18x^8 + 144x^7 - 672x^6 + 2016x^5 - 4032x^4 + 5376x^3 - 4608x^2 + 2304x - 512",
    "((((((((x - 18) * x + 144) * x - 672) * x + 2016) * x - 4032) * x + 5376) * x - 4608) * x + 2304) * x - 512"]
const WK_ERRVAL = [("factored9", "(x - 2)^9"),
    ("expanded9", "x^9 - 18x^8 + 144x^7 - 672x^6 + 2016x^5 - 4032x^4 + 5376x^3 - 4608x^2 + 2304x - 512"),
    ("horner9", "((((((((x - 18) * x + 144) * x - 672) * x + 2016) * x - 4032) * x + 5376) * x - 4608) * x + 2304) * x - 512")]

function wk_parseall(ss::Vector{String})
    acc = 0
    for s in ss
        acc += wk_ST.callcount(Meta.parse(s))
    end
    acc
end
function wk_exprvalall(es::Vector{Any})
    acc = 0.0
    for e in es
        acc += wk_ST.exprval(e)[1]
    end
    acc
end

function suite_wilkinson(ctx)
    ss = copy(WK_EXPRS)
    n = length(ss)
    bench!(i -> wk_parseall(blackbox(i, ss)), ctx, "parse"; ops = n, param = "$n exprs")
    es = Any[Meta.parse(s) for s in ss]
    bench!(i -> wk_exprvalall(blackbox(i, es)), ctx, "exprval"; ops = n, param = "$n exprs")
    for (name, s) in WK_ERRVAL
        e = Meta.parse(s)
        bench!(i -> wk_errval(blackbox(i, e)), ctx, "errval_$name"; param = "N=3000")
        t = wk_genabs(e, Float64)
        bench!(i -> wk_errval_pre(blackbox(i, e), t), ctx, "errval_$(name)_nocodegen"; param = "N=3000")
    end
end

register!("wilkinson", suite_wilkinson)
(abspath(PROGRAM_FILE) == @__FILE__) && main_suites(["wilkinson" => suite_wilkinson])

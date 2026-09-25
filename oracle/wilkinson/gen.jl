# Golden generator for the Lean port of Wilkinson.jl (0.1.1) and the parts of
# SyntaxTree.jl (1.0.1) it uses.
#
#   julia --startup-file=no --project=<env with Wilkinson, JSON> oracle/wilkinson/gen.jl
#
# Wilkinson itself does not load without a working PyPlot/Conda, so its numeric
# kernels (src/Wilkinson.jl:17-103, src/polynomial.jl:4-69) are copied verbatim
# below; SyntaxTree and Reduce (the REDUCE CAS) are loaded through their package
# ids. Writes oracle/golden/wilkinson/{exprval,reduce,ranges,kernels,stieltjes,
# comparison}.json. Floats are hex bit patterns or `repr` strings (bit-exact),
# expressions are Julia `string(expr)` plus a JSON tree
# ({"sym"}, {"int"}, {"f64"}, {"call", "args"}). Deterministic (MersenneTwister(0x5EED)).

using JSON, Random, Printf
const SyntaxTree = Base.require(Base.PkgId(Base.UUID("a4af3ec5-f8ac-5fed-a759-c2e80b4d74cb"), "SyntaxTree"))
const Reduce = Base.require(Base.PkgId(Base.UUID("93e0c654-6965-5f22-aba9-9c1ae6b3c259"), "Reduce"))
const Algebra = Reduce.Algebra
import .SyntaxTree: callcount

const OUT = joinpath(@__DIR__, "..", "golden", "wilkinson")
mkpath(OUT)
const META = Dict("julia" => string(VERSION), "SyntaxTree" => "1.0.1", "Reduce" => string(pkgversion(Reduce)),
                  "Wilkinson" => "0.1.1 (kernels copied)", "seed" => "0x5EED")
wjson(name, obj) = open(io -> JSON.print(io, obj), joinpath(OUT, name), "w")

hex(x::Float64) = string(reinterpret(UInt64, x), base = 16, pad = 16)
hex(x::Float32) = string(reinterpret(UInt32, x), base = 16, pad = 8)
fs(x::AbstractFloat) = repr(Float64(x))
fs(x::Integer) = string(x)
tree(e::Symbol) = Dict("sym" => string(e))
tree(e::Integer) = Dict("int" => string(e))
tree(e::AbstractFloat) = Dict("f64" => repr(Float64(e)))
function tree(e::Expr)
    # integers beyond Int64 parse as `Core.@int128_str`/`Core.@big_str` macro calls
    e.head == :macrocall && return Dict("bigint" => e.args[end])
    e.head == :call || error("unexpected head $(e.head) in $e")
    Dict("call" => string(e.args[1]), "args" => [tree(a) for a in e.args[2:end]])
end
exrec(e) = Dict("str" => string(e), "tree" => tree(e))
# exact BigFloat as sign, 256-bit mantissa (hex) and exponent: x = ±m·2^e
function bigrec(x::BigFloat)
    iszero(x) && return Dict("zero" => true, "neg" => signbit(x))
    isinf(x) && return Dict("inf" => true, "neg" => signbit(x))
    isnan(x) && return Dict("nan" => true)
    p = precision(x)
    e = exponent(x) - (p - 1)
    m = BigInt(abs(x) * big(2.0)^(-e))
    Dict("neg" => signbit(x), "m" => string(m, base = 16), "e" => e)
end

const rng = MersenneTwister(0x5EED)

# ------------------------------------------------------------------ exprval
# random polynomial ASTs in the shapes Wilkinson meets: expanded sums, Horner
# nests, products of linear factors, with integer, float and `//` literals
function randlit(r)
    u = rand(r)
    u < 0.45 && return rand(r, 1:12) * rand(r, [1, 1, -1])
    u < 0.6 && return round(rand(r) * 20 - 10, digits = rand(r, 1:3))
    u < 0.75 && return rand(r, [1, 1, 2])
    u < 0.85 && return Expr(:call, ://, rand(r, 1:9), rand(r, 2:9))
    return round(rand(r) * 3, digits = 2) + 0.25
end
pos(r) = (l = randlit(r); l isa Number && l < 0 ? -l : l)
function randterm(r, k)
    c = pos(r)
    k == 0 && return c
    xk = k == 1 ? :x : Expr(:call, :^, :x, k)
    rand(r) < 0.2 ? xk : Expr(:call, :*, c, xk)
end
function randexpanded(r, n)
    ks = sort(unique(rand(r, 0:n, rand(r, 1:n+1))), rev = true)
    e = randterm(r, ks[1])
    for k in ks[2:end]
        e = Expr(:call, rand(r, [:+, :-]), e, randterm(r, k))
    end
    e
end
function randhorner(r, n)
    e = :x
    for _ in 1:n
        e = Expr(:call, rand(r, [:+, :-]), Expr(:call, :*, e, :x), pos(r))
    end
    e
end
randfactors(r, n) = Expr(:call, :*, [Expr(:call, rand(r, [:-, :+]), :x, pos(r)) for _ in 1:n]...)
function randexpr(r)
    u = rand(r)
    u < 0.35 && return randexpanded(r, rand(r, 1:9))
    u < 0.6 && return randhorner(r, rand(r, 1:8))
    u < 0.8 && return randfactors(r, rand(r, 1:5))
    return Expr(:call, :^, Expr(:call, :-, :x, rand(r, 1:5)), rand(r, 2:9))
end

const FIXED = [:(x^9 - 2), :((x - 2)^9), :(2x^2 - 1//2), :(x^2 + 3x + 2), :((x + 1) * (x + 2)),
               :(2 + x * (3 + x)), :(1.0 - 3.0x + x^3), :(((x - 1) * x + 1) * x + 5),
               :(x^2), :(2x), :(x), :(1 * x + 1), :(x^2 + 1 * x + 1), :(-x + 2), :(x ^ -2 + 1),
               :((x - 1) * (x - 2) * (x - 3)), :(x / 3 + 1 / 2)]
exprvalrec(e) = begin
    v = SyntaxTree.exprval(e)
    a = SyntaxTree.expravg(e)
    Dict("expr" => exrec(e), "callcount" => callcount(e),
         "expravg" => [a[1], fs(a[2]), a[3], fs(a[4])],
         "exprval" => [fs(v[1]), v[2], fs(v[3]), fs(v[4]), fs(v[5])],
         "sub64" => string(SyntaxTree.sub(Float64, e)), "sub32" => string(SyntaxTree.sub(Float32, e)),
         "abs" => string(SyntaxTree.abs(e)), "alg" => string(SyntaxTree.alg(e)))
end
wjson("exprval.json", Dict("meta" => META,
    # a bare literal has callcount 0, and exprval then takes sqrt of a negative (DomainError)
    "cases" => [exprvalrec(e) for e in vcat(FIXED, filter(e -> e isa Expr, [randexpr(rng) for _ in 1:600]))]))
println("exprval done")

# ------------------------------------------------------------------ REDUCE forms
Reduce.Rational(false)
# REDUCE forms whose integers exceed Int64: Int128 literals (evaluated in Float64
# after promotion) and BigInt literals (which pull the evaluation into BigFloat)
WIDE = [Reduce.rcall(:((x - 0.7236182478592211) * (x - 0.12345678901234567)), :expand),
        Reduce.rcall(:((x - 0.7236182478592211) * (x - 0.12345678901234567) * (x - 0.9876543210987654)), :expand),
        Reduce.rcall(:((x - 0.7236182478592211) * (x - 0.12345678901234567) * (x - 0.9876543210987654)), :horner)]
randint(r, n) = Expr(:call, :+, [Expr(:call, :*, c, Expr(:call, :^, :x, k)) for (k, c) in
                  zip(0:n, rand(r, -6:6, n + 1)) if c != 0]..., 0)
function randpoly(r)
    u = rand(r)
    if u < 0.3
        return randint(r, rand(r, 0:7))
    elseif u < 0.6
        fs_ = Any[Expr(:call, :-, Expr(:call, :*, rand(r, 1:4), :x), rand(r, -5:5)) for _ in 1:rand(r, 1:4)]
        rand(r) < 0.3 && push!(fs_, Expr(:call, :+, Expr(:call, :^, :x, 2), rand(r, 1:5)))
        rand(r) < 0.3 && push!(fs_, :x)
        return Expr(:call, :*, rand(r, [1, 1, 1, -1, 2, -2, 3, -3]), fs_...)
    elseif u < 0.75
        return Expr(:call, :*, rand(r, [1, -1, 2]), Expr(:call, :^, Expr(:call, :-, :x, rand(r, -3:3)), rand(r, 2:5)),
                    Expr(:call, :-, :x, rand(r, -4:4)))
    elseif u < 0.9
        return Expr(:call, :+, [Expr(:call, :*, Expr(:call, :/, rand(r, -9:9), rand(r, 1:6)), Expr(:call, :^, :x, k)) for k in 0:rand(r, 1:4)]...)
    else
        return Expr(:call, :+, [Expr(:call, :*, rand(r, [0.5, 0.25, -1.5, 0.1, 2.0, -0.75, 1.25]), Expr(:call, :^, :x, k)) for k in 0:rand(r, 1:3)]...)
    end
end
const RFIXED = [:((x-2)^9), :((x-1)*(x-2)*(x-3)), :(x^3 - 6x^2 + 11x - 6), :((x+1)*(x-2)), :(2x^2 - 2), :(-x^2 + 1),
    :(x^3 + 1), :(x^4 - 1), :(2x^2 + 3x + 1), :(x^5), :(3x^4 - 2x), :((2x-1)*(3x+2)), :(-(x-1)^3), :(x^2 - 2),
    :((x^2+1)*(x-1)), :(4x^2 - 4x + 1), :(x - 1), :(5), :(-x), :(x^2 + x), :((x+3)^2*(x-1)), :(6x^3 - 11x^2 + 6x - 1),
    :(x^3/2 - x), :(0.5x^2 - 1.5), :((x-1)*(x+1)*(x-2)*(x+2)), :(x^9 - 2), :(x^4 + 4), :(x^6 - 1), :(-2x^2 + 2),
    :(-2x^2 - 2), :(-x^2 - 1), :(-3x^3 + 6x), :(6x^3 + 4x), :(-6x^3 - 4x^2), :(-x^3 + 2x^2), :(-x^2 + x + 1),
    :(-(x+1)*(x+2)*(x+3)), :(x^5 - x^3 + x), :(-x^3 - 2x^2 + x), :(0.1x + 0.2), :(x/3 + 1/2), :((x - 0.5)*(x - 0.25))]
formrec(e) = begin
    ee = Reduce.rcall(e, :expand); eh = Reduce.rcall(e, :horner); ef = Reduce.rcall(e, :factor)
    Dict("input" => exrec(e), "expand" => exrec(ee), "horner" => exrec(eh), "factor" => exrec(ef),
         "exprval" => [f isa Number ? "DomainError" : fs(SyntaxTree.exprval(f)[1]) for f in (ee, eh, ef)])
end
polyfactors(x,a) = polyfactors(x,a,1)
polyfactors(x,a::Array{<:Any,1},k) = k==length(a) ? Algebra.:-(x,a[k]) : Algebra.:*(Algebra.:-(x,a[k]),polyfactors(x,a,k+1))
polyhorner(x,a) = polyhorner(x,a,1)
polyhorner(x,a::Array{<:Any,1},k) = k==length(a) ? a[k] : Algebra.:+(a[k],Algebra.:*(x,polyhorner(x,a,k+1)))
polyexpand(x,a) = polyexpand(x,a,length(a))
polyexpand(x,a::Array{<:Any,1},k) = k==1 ? a[k] : Algebra.:+(Algebra.:*(a[k],Algebra.:^(x,k-1)),polyexpand(x,a,k-1))
randcoeffs(r) = rand(r) < 0.7 ? rand(r, -6:6, rand(r, 1:6)) : rand(r, [0.5, 1.5, -2.25, 3.0, 0.1, -1.0, 4.0], rand(r, 1:4))
polyrec(f, a) = (e = f(:x, a); Dict("a" => [x isa Integer ? Dict("int" => string(x)) : Dict("f64" => repr(x)) for x in a],
                                    "out" => exrec(e)))
wjson("reduce.json", Dict("meta" => META,
    "forms" => [formrec(e) for e in vcat(RFIXED, [randpoly(rng) for _ in 1:400])],
    # the last 12: Wilkinson's `tests` experiment inputs, `rand(d)` roots (16-digit decimals
    # for REDUCE, so 50-150-digit coefficients); a separate stream keeps the rest unchanged
    "polyfactors" => [polyrec(polyfactors, a) for a in vcat([[1,2,3], [0.5,2.25], [-1,2], [3,3,3]],
                        [filter(!iszero, randcoeffs(rng)) for _ in 1:40],
                        (r2 = MersenneTwister(0x5EEE); [rand(r2, rand(r2, 2:6)) for _ in 1:12])) if !isempty(a)],
    "polyhorner" => [polyrec(polyhorner, a) for a in vcat([[1,2,3], [-1,0,2]], [randcoeffs(rng) for _ in 1:40])
                        if !iszero(a[end])],
    "polyexpand" => [polyrec(polyexpand, a) for a in vcat([[1,2,3]], [randcoeffs(rng) for _ in 1:40]) if !iszero(a[end])],
    # SyntaxTree on Int128/BigInt literals: not scalars for exprval, left alone by sub/abs
    "wide" => [exprvalrec(e) for e in WIDE]))
println("reduce done")

# ------------------------------------------------------------------ kernels copied from Wilkinson.jl
function floatset(T::DataType,N;scale=x->x)
    l = scale(eps(T))
    u = scale(prevfloat(T(Inf)))
    return l:(u-l)/(N-1):u
end
geonorm(x) = 1/(1-x)
function Ω(p::Array{<:Number,1})
    n = length(p)-1
    for k ∈ 1:length(p)
        p[k] == Inf && (n=k-1; break)
    end
    return n
end
genabs(expr,T::DataType) = SyntaxTree.genlatest(SyntaxTree.abs(SyntaxTree.sub(T,expr)),[:x])
genalg(expr,T::DataType) = SyntaxTree.genlatest(SyntaxTree.sub(T,expr),[:x])
function stieltjes(set::AbstractRange,expr,T::DataType,T2::DataType=T;logi=log,expi=exp)
    t = genabs(expr,T)
    sc = collect(set)
    esc = expi.(sc)
    te = (@timed p = t.(esc))[3]
    return Float64.((logi.(abs.(p))-sc).+logi(callcount(expr)*eps(T2))), te
end
function simpson(set::AbstractRange,p::Array{<:Number,1},n::Int=Ω(p))
    s = 4sum(p[1:2:n-1])+2sum(p[2:2:n-1])+sum(p[[1,n]])
    r = -(collect(set)[[n,1]]...)
    return s/(3n*r)
end
function exacterr(set::AbstractRange,expr::Array{<:Any,1},T::DataType,rx::Bool,ex::Bool;logi=log,expi=exp)
    funs = genalg.(expr[2:end],T)
    push!(funs,genalg(expr[1],BigFloat))
    esc = collect(set)
    sc = expi.(esc)
    bs = funs[end].(sc)
    out = Array{Array{Float64,1},1}(undef,length(funs)-1)
    for q ∈ 1:length(funs)-1
        out[q] = Float64.(logi.(abs.(bs-funs[q].(sc)))-esc)
    end
    return out
end
function optimal(expr)
    h = Reduce.horner(expr)
    f = Reduce.factor(h)
    eh = SyntaxTree.exprval(h)[1]
    ef = SyntaxTree.exprval(f)[1]
    eo = SyntaxTree.exprval(expr)[1]
    if eh ≤ ef
        return eh ≤ eo ? h : expr
    else
        return ef ≤ eo ? f : expr
    end
end

# ------------------------------------------------------------------ ranges
setrec(s) = Dict("first" => hex(first(s)), "last" => hex(last(s)), "step" => hex(step(s)), "len" => length(s),
                 "bits" => [hex(x) for x in collect(s)])
f32cases = [(0.1f0, 0.1f0, 1.0f0), (1f0, 0.5f0, 10f0), (-3f0, 0.25f0, 3f0), (0f0, 0.3f0, 2f0), (1f0, -0.1f0, -1f0),
            (0.5f0, 1f0/3f0, 7f0), (1f-3, 1f-3, 1f-1), (2f0, 2f0, 2f0), (5f0, 1f0, 1f0), (-1.5f0, 0.7f0, 4.2f0),
            (100f0, 7.5f0, 250f0), (0.2f0, 0.2f0, 3.4f0)]
f64cases = [(0.1, 0.1, 1.0), (-36.04365338911715, 0.2, 10.0), (1.0, 1/3, 5.0), (0.0, 0.3, 2.0), (3.0, -0.7, -2.0)]
wjson("ranges.json", Dict("meta" => META,
    "logset64" => setrec(floatset(Float64, 3000; scale = log)),
    "logset32" => setrec(floatset(Float32, 3000; scale = log)),
    "logset64_n" => [setrec(floatset(Float64, n; scale = log)) for n in (10, 100, 2999)],
    "idset64" => setrec(floatset(Float64, 10)),
    "colon32" => [merge(setrec(a:s:b), Dict("args" => hex.([a, s, b]))) for (a, s, b) in f32cases],
    "colon64" => [merge(setrec(a:s:b), Dict("args" => hex.([a, s, b]))) for (a, s, b) in f64cases]))
println("ranges done")

# ------------------------------------------------------------------ float kernels and BigFloat
randf(r) = (rand(r) < 0.5 ? -1 : 1) * rand(r) * 2.0^rand(r, -30:30)
powcases = [(x, n) for x in [randf(rng) for _ in 1:400] for n in (rand(rng, -40:40), rand(rng, -9:9), rand(rng, 100:2000))]
# `x^k` with a literal `k` lowers to `Base.literal_pow(^, x, Val(k))`
const LITFUNS = Dict(k => eval(:(x -> x^$k)) for k in -3:12)
litcases = [(x, k) for x in [randf(rng) for _ in 1:60] for k in -3:12]
pow32 = [(Float32(x), n) for (x, n) in powcases[1:600]]
sumlen = vcat([1, 2, 3, 15, 16, 17, 18, 31, 32, 33, 100, 1023, 1024, 1025, 1026, 2047, 2048, 2049, 2999, 3000, 4097],
              rand(rng, 1:5000, 20))
sumseed = rand(rng, UInt32, length(sumlen))
# a vector Lean can rebuild exactly: integers scaled by powers of two
sumvec(n, s) = [Float64(Int64((UInt64(i) * 0x9E3779B1 + UInt64(s)) % UInt64(2)^32) - 2^31) *
                2.0^(Int((UInt64(i) * UInt64(s) + 7) % 61) - 91) for i in 1:n]
bigops = []
for _ in 1:300
    a, b, c = randf(rng), randf(rng), randf(rng)
    A, B, C = big(a), big(b), big(c)
    n = rand(rng, -14:14)
    push!(bigops, Dict("a" => hex(a), "b" => hex(b), "c" => hex(c), "n" => n,
        "add" => bigrec(A + B), "sub" => bigrec(A - B), "mul" => bigrec(A * B), "div" => bigrec(A / B),
        "fma" => bigrec((A * B + C) / A), "pow" => bigrec(A^n), "log" => bigrec(log(abs(A))),
        "tofloat" => hex(Float64((A * B + C) / A)), "tofloat32" => hex(Float32((A * B + C) / A))))
end
ratcases = [(rand(rng, -10^6:10^6), rand(rng, 1:10^6)) for _ in 1:100]
# Julia's own exp/log kernels (base/special/exp.jl, log.jl), incl. the Wilkinson grid
expx = vcat([rand(rng) * 1500 - 760 for _ in 1:3000], [randn(rng) * 3 for _ in 1:1000],
            collect(floatset(Float64, 3000; scale = log))[1:7:end], [-745.1, -744.9, -708.5, 709.7, 709.79, 0.0, -0.0])
logx = vcat([exp(rand(rng) * 1400 - 700) for _ in 1:3000], [1 + randn(rng) * 0.03 for _ in 1:1000],
            [rand(rng) * 2.0^-1030 for _ in 1:100], [rand(rng) for _ in 1:500], [1.0, 2.0, floatmax(Float64), 5e-324])
exp32x = vcat([Float32(rand(rng) * 200 - 105) for _ in 1:3000], collect(floatset(Float32, 3000; scale = log))[1:7:end],
              [-103.9f0, -103.98f0, -87.4f0, 88.7f0, 88.73f0])
log32x = vcat([exp(Float32(rand(rng) * 170 - 85)) for _ in 1:3000], [1f0 + Float32(randn(rng)) * 0.03f0 for _ in 1:1000],
              [Float32(rand(rng)) * 1f-39 for _ in 1:100], [floatmax(Float32), 1f0, 2f0])
wjson("kernels.json", Dict("meta" => META,
    "pow" => [Dict("x" => hex(x), "n" => n, "r" => hex(x^n), "rf" => hex(x^Float64(n))) for (x, n) in powcases],
    "literal_pow" => [Dict("x" => hex(x), "k" => k, "r" => hex(Base.invokelatest(LITFUNS[k], x))) for (x, k) in litcases],
    "pow32" => [Dict("x" => hex(x), "n" => n, "r" => hex(x^n)) for (x, n) in pow32],
    "sum" => [Dict("n" => n, "seed" => Int(s), "r" => hex(sum(sumvec(n, s)))) for (n, s) in zip(sumlen, sumseed)],
    "big" => bigops,
    "bigrat" => [Dict("p" => string(p), "q" => string(q), "r" => bigrec(BigFloat(p // q))) for (p, q) in ratcases],
    "bigeps" => bigrec(eps(BigFloat)),
    "exp" => [[hex(x), hex(exp(x))] for x in expx], "log" => [[hex(x), hex(log(x))] for x in logx],
    "exp32" => [[hex(x), hex(exp(x))] for x in exp32x], "log32" => [[hex(x), hex(log(x))] for x in log32x]))
println("kernels done")

# ------------------------------------------------------------------ Stieltjes bounds
set64 = floatset(Float64, 3000; scale = log)
set32 = floatset(Float32, 3000; scale = log)
SFIXED = [:(x^9 - 2), :((x - 2)^9), :(((((((((x - 18) * x + 144) * x - 672) * x + 2016) * x - 4032) * x + 5376) * x - 4608) * x + 2304) * x - 512),
          :((x - 1) * (x - 2) * (x - 3)), :(((x - 6) * x + 11) * x - 6), :(x^3 - 6x^2 + 11x - 6)]
# `//` on floats is a MethodError in Julia (after `sub`), so those forms are left out
hasrat(e) = e isa Expr && (e.args[1] == :// || any(hasrat, e.args))
sforms = vcat(SFIXED, filter(!hasrat, [randexpr(rng) for _ in 1:45])[1:30], WIDE)
strec(e, full) = begin
    st, _ = stieltjes(set64, e, Float64)
    n = Ω(st)
    smp = simpson(set64, st, n)
    stb, _ = stieltjes(set64, e, BigFloat, Float64)
    st32, _ = stieltjes(set32, e, Float32)
    n32 = Ω(st32)
    d = Dict("expr" => exrec(e), "omega" => n, "smp" => hex(smp), "geonorm" => hex(geonorm(smp)),
             # Ω = 0 (the first Float32 point overflows) makes Julia's simpson throw
             "smp_big" => hex(simpson(set64, stb, n)), "omega32" => n32,
             "smp32" => n32 < 2 ? nothing : hex(simpson(set32, st32, n32)),
             "sample" => [[i, hex(st[i]), hex(stb[i]), hex(st32[i])] for i in unique(vcat(1:5, n-2:n, 17:97:2999, 3000))])
    full && (d["stj"] = hex.(st))
    d
end
wjson("stieltjes.json", Dict("meta" => META, "cases" => [strec(e, i <= 6) for (i, e) in enumerate(sforms)]))
println("stieltjes done")

# ------------------------------------------------------------------ PolynomialComparison
# the constructor of src/polynomial.jl:42-68 with the copied kernels
function comparison(j, T = Float64, N = 3000)
    set = floatset(T, N; scale = log)
    exprs = Any[optimal(j), Reduce.rcall(j, :expand), Reduce.rcall(j, :horner), Reduce.rcall(j, :factor),
                Reduce.rcall(j, :factor, :rounded)]
    forms = copy(exprs)
    extra = (j ≠ exprs[2]) & (j ≠ exprs[3]) & (j ≠ exprs[4])
    rxtra = exprs[4] ≠ exprs[5]
    !rxtra && deleteat!(exprs, 5)
    extra && push!(exprs, j)
    stj = [stieltjes(set, expr, T) for expr ∈ exprs[2:end]]
    ω = min(Ω.([stj[1][1], stj[2][1], stj[3][1]])...)
    res = [(exprs[k+1], SyntaxTree.exprval(exprs[k+1]), simpson(set, stj[k][1], ω)) for k in 1:length(stj)]
    best = stieltjes(set, exprs[1], BigFloat, T)[1]
    pushfirst!(res, (exprs[1], SyntaxTree.exprval(exprs[1]), simpson(set, best, ω)))
    EE = exacterr(set, exprs, T, rxtra, extra)
    s = [simpson(set, r, ω) for r ∈ EE]
    # print(::PolynomialComparison) (src/polynomial.jl:71-92) with REDUCE's 2-D display
    # replaced by string(expr) and allocation reported as 0.0
    labels = ["e", "h", "f"]; rxtra && push!(labels, "r"); extra && push!(labels, "o")
    io = IOBuffer()
    println(io, j)
    println(io, "characteristic values (c,σ,s,p):")
    [println(io, "$(labels[k]) = ", res[k+1][2][2:5]) for k in eachindex(labels)]
    println(io, "expression value ν:")
    [println(io, "$(labels[k]) = $(res[k+1][2][1])") for k in eachindex(labels)]
    println(io, "predicted error bound Φ:")
    [println(io, "$(labels[k]) = $(res[k+1][3]/res[1][3])") for k in eachindex(labels)]
    println(io, "bytes allocated:")
    [println(io, "$(labels[k]) = 0.0") for k in eachindex(labels)]
    Dict("input" => exrec(j), "forms" => [exrec(f) for f in forms], "extra" => extra, "rxtra" => rxtra, "omega" => ω,
         "smp" => [hex(r[3]) for r in res], "exprval" => [fs(r[2][1]) for r in res], "integral" => hex.(s),
         "exact_sample" => [[hex(E[i]) for i in (1, 2, 100, 500, ω)] for E in EE], "print" => String(take!(io)))
end
cinputs = [:((x - 2)^9), :((x - 1) * (x - 2) * (x - 3)), :(x^3 - 6x^2 + 11x - 6), :(x^9 - 2), :((x + 1) * (x - 2)),
           :((2x - 1) * (3x + 2)), :(x^4 - 10x^2 + 9), :((x - 3)^4), :(2x^2 + 3x + 1), :((x - 1)^2 * (x + 1)^3)]
# REDUCE's rounded factorization of e.g. x^9 - 2 has complex roots (`im`), which the
# port's real evaluator does not model; such inputs are left out
hasim(e) = e === :im || (e isa Expr && any(hasim, e.args))
cases = []
for j in cinputs
    hasim(Reduce.rcall(j, :factor, :rounded)) && (println("skip (complex rounded factor): ", j); continue)
    push!(cases, comparison(j))
end
wjson("comparison.json", Dict("meta" => META, "cases" => cases))
println("comparison done")

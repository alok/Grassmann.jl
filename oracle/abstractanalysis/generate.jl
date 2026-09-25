# Golden generator for the Lean port of AbstractAnalysis.jl (v0.2.2).
#
#   julia --startup-file=no --project=<env with AbstractAnalysis + JSON> \
#       oracle/abstractanalysis/generate.jl
#
# Writes oracle/golden/abstractanalysis/{sets,limits,metric,groups,floatprint}.json.
# Floats are stored as `repr` strings (bit-exact round trip), rationals as
# [num, den], complex numbers as [re, im]. Deterministic: MersenneTwister(0x5EED).

using AbstractAnalysis, JSON, Random, LinearAlgebra
import AbstractAnalysis: sternbrocot, integer, rational, positiverational, nonzerorational,
    cantorinversion, elegantinversion, elegantinversion1, counter, levicivita, center,
    leftcosets, rightcosets, extract

const OUT = joinpath(@__DIR__, "..", "golden", "abstractanalysis")
mkpath(OUT)

const META = Dict("julia" => string(VERSION),
                  "AbstractAnalysis" => string(pkgversion(AbstractAnalysis)),
                  "seed" => "0x5EED")

fs(x::AbstractFloat) = repr(Float64(x))
fs(x::Integer) = x
fs(x::AbstractVector) = [fs(y) for y in x]
rat(q) = [numerator(q), denominator(q)]
wjson(name, obj) = open(io -> JSON.print(io, obj), joinpath(OUT, name), "w")
perm(p) = collect(p.v)

# ---------------------------------------------------------------- sets
let N = 1000
    wjson("sets.json", Dict(
        "meta" => META,
        "integers" => [integer(i) for i in 1:N],
        "positiverationals" => [rat(PositiveRationals[i]) for i in 1:N],
        "rationals" => [rat(Rationals[i]) for i in 1:N],
        "nonzerorationals" => [rat(NonzeroRationals[i]) for i in 1:N],
        "cantorpairs" => [collect(CantorPairs[i]) for i in 1:N],
        "elegantpairs0" => [collect(ElegantPairs0[i]) for i in 1:N],
        "elegantpairs1" => [collect(ElegantPairs1[i]) for i in 1:N],
        "gaussiannaturals" => [[real(z), imag(z)] for z in (GaussianNaturals[i] for i in 1:N)],
        "gaussianintegers" => [[real(z), imag(z)] for z in (GaussianIntegers[i] for i in 1:N)],
        "gaussianrationals" => [[rat(real(z)), rat(imag(z))] for z in (GaussianRationals[i] for i in 1:N)],
        "sternbrocot" => [sternbrocot(n) for n in 1:10000],
        "SternBrocot" => [SternBrocot[n] for n in 1:N],
    ))
end

# ---------------------------------------------------------------- limits
valrepr(x::Number) = fs(x)
valrepr(x::AbstractVector) = fs(x)
limrec(L) = Dict("show" => sprint(show, L), "compact" => sprint(show, L; context = :compact => true),
                 "n" => length(L), "r" => fs(residual(L)), "first" => valrepr(first(L)),
                 "last" => valrepr(last(L)))

const MAPS = [
    ("cos", cos, 1.0, true),
    ("half_plus_one", x -> x / 2 + 1, 0.0, false),
    ("babylonian", x -> (x + 2 / x) / 2, 1.0, false),
    ("newton3", x -> x - (x^2 - 3) / (2x), 1.0, false),
    ("logistic", x -> 2.5x * (1 - x), 0.5, false),
    ("contraction", v -> [0.5v[1] + 0.2v[2], 0.1v[1] + 0.3v[2]], [1.0, 2.0], false),
    ("halve_vec", v -> v / 2, [1.0, 2.0], false),
]

collectvals(C::AbstractArray) = C isa AbstractAnalysis.SequenceArray && ndims(C.v) == 2 ?
    [fs(C.v[:, i]) for i in 1:size(C.v, 2)] : [valrepr(C[i]) for i in 1:length(C)]

maps = map(MAPS) do (name, f, x0, libm)
    L, errs = orbiterror(f, x0)
    Dict("name" => name, "libm" => libm, "x0" => valrepr(x0),
         "orbit" => limrec(orbit(f, x0)),
         "orbiterror" => fs(errs),
         "orbitN" => Dict(string(k) => limrec(orbit(f, x0, k)) for k in (1, 5, 10)),
         "fixedcycle10" => limrec(FixedCycle(10, f)(x0)),
         "collect5" => collectvals(collect(orbit(f, x0, 5))))
end

hold = let L = orbithold((x, y) -> (y + x / y) / 2, 2.0, 1:6)
    limrec(L)
end

# (name, term, sum converges to 1e-4 quickly, … to 1e-8 quickly). `1 + 1/i^2`
# diverges: Julia only stops when `i^2` overflows Int64 at i = 2^32, so no ϵ-limit.
const CVS = [
    ("inv_sq", i -> 1 / i^2, true, true),
    ("alt_harmonic", i -> (-1)^i / i, true, false),
    ("inv_pow2", i -> 1 / 2^i, true, true),
    ("one_plus_inv_sq", i -> 1 + 1 / i^2, false, false),
]

cvs = map(CVS) do (name, f, eps4, deep)
    x = CountableVector(f, 10)
    S = sum(x)
    P = prod(x)
    rec = Dict{String,Any}("name" => name,
        "terms" => fs([x[i] for i in 1:12]),
        "sum" => limrec(S), "prod" => limrec(P),
        "sum_seek" => Dict(string(k) => limrec(S[k]) for k in (1, 9, 10, 13)),
        "prod_seek" => Dict(string(k) => limrec(P[k]) for k in (1, 9, 13)),
        "sum_plus1" => limrec(S + 1), "one_minus_sum" => limrec(1 - S),
        "two_times_sum" => limrec(2 * S), "sum_div2" => limrec(S / 2),
        "sum_times_sum" => limrec(S * S), "sum_plus_prod" => limrec(S + P),
        "map_double" => limrec(map(v -> 2v, S)), "map_abs" => limrec(map(abs, S)),
        "collect_sum" => fs(collect(S)), "collect_prod" => fs(collect(P)),
        "limit" => limrec(limit(x)), "limit3" => limrec(limit(x, 3)),
        "limit_eps4" => limrec(limit(x, 1e-4)),
        "dot" => limrec(dot(x, x)),
        "cumsum" => fs([cumsum(x)[i] for i in 1:12]), "cumprod" => fs([cumprod(x)[i] for i in 1:12]),
        "supseq3" => fs([supseq(x, 3)[i] for i in 1:10]), "infseq3" => fs([infseq(x, 3)[i] for i in 1:10]),
        "sum_of_sum" => limrec(sum(S)), "prod_of_sum" => limrec(prod(S)),
        "sum_rerun" => limrec(S(1 => 0.5)))
    eps4 && (rec["sum_eps4"] = limrec(S[1e-4]))
    deep && (rec["sum_eps8"] = limrec(S[1e-8]))
    rec
end

series = Dict(
    "series_pow_0.5" => limrec(sum(FunctionVector((x, i) -> x^i, 5))(0.5)),
    "series_pow_0.3" => limrec(sum(FunctionVector((x, i) -> x^i, 5))(0.3)),
    "product_0.5" => limrec(prod(FunctionVector((x, i) -> 1 + x^i, 4))(0.5)),
    "product_0.3" => limrec(prod(FunctionVector((x, i) -> 1 + x^i, 4))(0.3)),
    "prod_naturals_10" => limrec(prod(Naturals(10))),
    "prod_naturals_20" => limrec(prod(Naturals(20))),
    "prod_naturals_25" => limrec(prod(Naturals(25))),
)

wjson("limits.json", Dict("meta" => META, "maps" => maps, "orbithold" => hold,
                          "countable" => cvs, "series" => series))

# ---------------------------------------------------------------- metric
rng = MersenneTwister(0x5EED)
vecs = map(1:200) do t
    n = rand(rng, 5:30)
    kind = t % 4
    x = kind == 0 ? randn(rng, n) :
        kind == 1 ? [0.7^k * (1 + 0.1randn(rng)) for k in 1:n] :
        kind == 2 ? sort(randn(rng, n)) : cumsum(abs.(randn(rng, n)))
    r = Dict{String,Any}("x" => fs(x),
        "residuals" => fs(residuals(x)), "lipschitz" => fs(lipschitz(x)),
        "isdiverging" => isdiverging(x), "iscauchy" => iscauchy(x),
        "isincreasing" => isincreasing(x), "isdecreasing" => isdecreasing(x),
        "ismonotonic" => ismonotonic(x),
        "supseq" => fs(supseq(x)), "infseq" => fs(infseq(x)),
        "maxabs" => fs(maxabs(x)), "minabs" => fs(minabs(x)), "supnorm" => fs(supnorm(x)))
    for m in (1, 2, 5)
        if n > m
            r["limsup$m"] = fs(limsup(x, m)); r["liminf$m"] = fs(liminf(x, m))
        end
    end
    r
end
scalars = Dict("supnorm_3_5" => fs(supnorm(3, 5)), "supnorm_m2.5" => fs(supnorm(-2.5)),
               "supnorm_34" => fs(supnorm([3, 4])), "infnorm_34" => fs(infnorm([3.0, 4.0])),
               "maxabs" => fs(maxabs([1, -5, 3])), "minabs" => fs(minabs([1, -5, 3])),
               "supnorm_vec_diff" => fs(supnorm([1.0, 2.0], [4.0, 6.0])))
cube(x) = x^3
derivs = map([("sin", sin, true), ("exp", exp, true), ("cube", cube, false)]) do (name, f, libm)
    xs = collect(-2.0:0.5:2.5)
    Dict("name" => name, "libm" => libm, "x" => fs(xs),
         "d1" => fs([AbstractAnalysis.derivative(f, x) for x in xs]),
         "d2" => fs([AbstractAnalysis.derivative2(f, x) for x in xs]))
end
wjson("metric.json", Dict("meta" => META, "vectors" => vecs, "scalars" => scalars,
                          "derivatives" => derivs, "h1" => fs(eps()^(1 / 5)),
                          "h2" => fs(sqrt(sqrt(eps(Float64))))))

# ---------------------------------------------------------------- groups
S3 = SymmetricGroup(3); S4 = SymmetricGroup(4)
cyc(c) = c isa AbstractAnalysis.Cycle ? [collect(c.v)] : [collect(x.v) for x in c.v]
elemrec(p) = Dict("p" => perm(p), "inv" => perm(inv(p)),
                  "pow" => Dict(string(k) => perm(p^k) for k in -3:3),
                  "cycles" => cyc(AbstractAnalysis.decompose(p)),
                  "order" => AbstractAnalysis.order(p), "levicivita" => levicivita(p),
                  "iseven" => iseven(p))
pairrec(p, q) = Dict("p" => perm(p), "q" => perm(q), "mul" => perm(p * q),
                     "div" => perm(p / q), "ldiv" => perm(p \ q))
subrec(H, G) = Dict("H" => [perm(h) for h in H.v],
    "center" => [perm(h) for h in center(H).v],
    "centralizer" => [perm(h) for h in centralizer(H, G).v],
    "normalizer" => [perm(h) for h in normalizer(H, G).v],
    "isnormal" => isnormal(H, G), "issubgroup" => issubgroup(H, G),
    "isabelian" => isabelian(H), "isgroup" => isgroup(H),
    "commutator" => [perm(h) for h in commutator(H).v],
    "leftcosets" => [[perm(h) for h in c.v] for c in leftcosets(H, G).v],
    "rightcosets" => [[perm(h) for h in c.v] for c in rightcosets(H, G).v],
    "subgroup" => [perm(h) for h in subgroup(H).v])
grng = MersenneTwister(0x5EED)
S4pairs = [(S4[rand(grng, 1:24)], S4[rand(grng, 1:24)]) for _ in 1:40]
modmagmas = [Dict("n" => n, "g" => g, "magma" => magma(g, (a, b) -> mod(a * b, n), identity).v)
             for n in 2:30 for g in 1:n-1]
zgroups = [Dict("n" => n, "g" => g,
                "group" => group([g], (a, b) -> mod(a + b, n), a -> mod(-a, n)).v,
                "iscyclic" => iscyclic(group([g], (a, b) -> mod(a + b, n), a -> mod(-a, n))))
           for n in 2:12 for g in 1:n-1]
m = magma(Complex(0, 1))
cplx(z) = [real(z), imag(z)]
gauss = Dict("m" => cplx.(m.v), "orders" => orders(m),
             "cayley" => [[cplx(m(g, h)) for h in m.v] for g in m.v],
             "times2" => cplx.((Complex(2, 0) * m).v), "plus1" => cplx.((m + Complex(1, 0)).v),
             "mm" => cplx.((m * m).v), "isgroup" => isgroup(m), "isabelian" => isabelian(m),
             "iscyclic" => iscyclic(m), "subgroup" => cplx.(subgroup(m).v))
roots = [Dict("n" => n, "z" => [[fs(real(z)), fs(imag(z))] for z in unityroots(n).v]) for n in 1:12]
C4 = AbstractAnalysis.Cycle{4}
cycles = Dict(
    "cycle134" => perm(Permutation(C4(1, 3, 4))),
    "product" => perm(Permutation(CycleProduct(C4(1, 2), C4(3, 4)))),
    "eq_rot" => C4(1, 2, 3) == C4(2, 3, 1), "eq_rev" => C4(1, 2, 3) == C4(1, 3, 2),
    "disjoint" => AbstractAnalysis.isdisjoint(C4(1, 2), C4(3, 4)))
dihedral = [perm(x) for x in (group([Permutation(C4(1, 3))]) * group([Permutation(C4(1, 2, 3, 4))])).v]
wjson("groups.json", Dict("meta" => META,
    "symmetric" => Dict(string(N) => [perm(p) for p in SymmetricGroup(N).v] for N in 1:4),
    "alternating" => Dict(string(N) => [perm(p) for p in AlternatingGroup(N).v] for N in 1:4),
    "elements" => [elemrec(p) for p in vcat(S3.v, S4.v)],
    "pairs" => [pairrec(p, q) for G in (S3, S4) for p in G.v for q in G.v],
    "cyclic" => [Dict("p" => perm(p), "group" => [perm(x) for x in group([p]).v]) for p in S4.v],
    "magma2" => [Dict("p" => perm(p), "q" => perm(q), "magma" => [perm(x) for x in magma([p, q]).v])
                 for (p, q) in S4pairs],
    "subgroups" => vcat([subrec(group([p]), S4) for p in S4.v],
                        [subrec(group([p, q]), S4) for (p, q) in S4pairs[1:12]],
                        [subrec(group([p]), S3) for p in S3.v], [subrec(S3, S3)]),
    "modmagmas" => modmagmas, "zgroups" => zgroups, "gaussian" => gauss,
    "unityroots" => roots, "cycles" => cycles, "dihedral" => dihedral))

# ---------------------------------------------------------------- float printing
frng = MersenneTwister(0x5EED)
f64 = Float64[]
for _ in 1:4000
    b = rand(frng, UInt64)
    x = reinterpret(Float64, b)
    isfinite(x) && push!(f64, x)
end
for _ in 1:3000
    push!(f64, round(randn(frng) * 10.0^rand(frng, -8:8); sigdigits = rand(frng, 1:17)))
end
append!(f64, [0.0, -0.0, 1.0, 0.1, 0.3, 1e5, 1e6, 999999.0, 1234567.0, 1e15, 1e16, 1e-4, 1e-5,
              5e-324, floatmax(Float64), floatmin(Float64), 2.0^53, 2.0^53 + 2, 9007199254740993.0,
              100000.05, 123456.7, 0.000123, 1.5e-10, 3.26592e6, Inf, -Inf, NaN])
f32 = Float32[]
for _ in 1:2000
    x = reinterpret(Float32, rand(frng, UInt32))
    isfinite(x) && push!(f32, x)
end
append!(f32, Float32[0.1, 1.0, 16777216.0, 3.4028235f38, 1f-45, 0.0, 1f6, 1f7])
wjson("floatprint.json", Dict("meta" => META,
    "f64" => [Dict("bits" => string(reinterpret(UInt64, x), base = 16), "str" => string(x)) for x in f64],
    "f32" => [Dict("bits" => string(reinterpret(UInt32, x), base = 16), "repr" => repr(x),
                   "str" => string(x)) for x in f32]))

println("wrote goldens to ", OUT)

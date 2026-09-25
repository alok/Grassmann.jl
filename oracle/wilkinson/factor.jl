# Golden generator for complete factorization over ℤ (REDUCE `factor`, the Berlekamp-Zassenhaus
# path of Wilkinson/Zassenhaus.lean): expanded products of irreducible factors of degree ≥ 2 that
# the rational-root stage cannot split, including Swinnerton-Dyer polynomials (irreducible, but
# split into linear or quadratic factors modulo every prime) and cyclotomic products.
#
#   julia --startup-file=no --project=<env with Reduce, JSON> oracle/wilkinson/factor.jl
#
# Writes oracle/golden/wilkinson/factor.json: {"cases": [{"input", "factor"}]} with expressions
# as in gen.jl ({"str", "tree"}). Deterministic (MersenneTwister(0x5EED)).

using JSON, Random
const Reduce = Base.require(Base.PkgId(Base.UUID("93e0c654-6965-5f22-aba9-9c1ae6b3c259"), "Reduce"))
Reduce.Rational(false)

const OUT = joinpath(@__DIR__, "..", "golden", "wilkinson")
tree(e::Symbol) = Dict("sym" => string(e))
tree(e::Integer) = Dict("int" => string(e))
tree(e::AbstractFloat) = Dict("f64" => repr(Float64(e)))
function tree(e::Expr)
    e.head == :macrocall && return Dict("bigint" => e.args[end])
    e.head == :call || error("unexpected head $(e.head) in $e")
    Dict("call" => string(e.args[1]), "args" => [tree(a) for a in e.args[2:end]])
end
exrec(e) = Dict("str" => string(e), "tree" => tree(e))

# a random polynomial of degree d with coefficients in -c:c (nonzero leading and constant terms)
function randpoly(r, d, c)
    a = rand(r, -c:c, d + 1)
    a[end] == 0 && (a[end] = rand(r, 1:c))
    a[1] == 0 && (a[1] = rand(r, [-1, 1]))
    Expr(:call, :+, [Expr(:call, :*, a[k + 1], Expr(:call, :^, :x, k)) for k in 0:d]...)
end
rng = MersenneTwister(0x5EED)
products = Any[]
for _ in 1:60
    fs = Any[randpoly(rng, rand(rng, 2:5), 9) for _ in 1:rand(rng, 2:3)]
    rand(rng) < 0.2 && push!(fs, Expr(:call, :^, fs[1], 2))
    rand(rng) < 0.2 && push!(fs, Expr(:call, :-, :x, rand(rng, -3:3)))
    push!(products, Expr(:call, :*, rand(rng, [1, 1, 1, -1, 2, -3]), fs...))
end
for _ in 1:10
    push!(products, Expr(:call, :*, randpoly(rng, rand(rng, 6:8), 30), randpoly(rng, rand(rng, 5:7), 30)))
end
fixed = Any[
    :((x^4 + x + 1) * (x^4 - x^3 + 2)),
    :(x^4 - 10x^2 + 1),                                   # Swinnerton-Dyer S₂
    :(x^8 - 40x^6 + 352x^4 - 960x^2 + 576),               # Swinnerton-Dyer S₃
    :((x^4 - 10x^2 + 1) * (x^4 - 10x^2 + 1 + x)),
    :((x^6 + x + 1) * (x^6 - x^5 + 3)),
    :(x^12 - 1), :(x^15 - 1), :(x^16 - 1), :(x^30 - 1),
    :((x^2 + 1) * (x^2 + 2) * (x^2 + 3) * (x^2 + 5)),
    :((x^2 + x + 1)^2 * (x^4 + 1) * (x^3 - 2)),
    :((5x^3 + 3x - 7) * (9x^4 + 2x^2 - 4x + 11)),
    :((x^4 / 2 + x / 3 + 1) * (x^3 - 2x + 1 / 5)),
    :((x^5 - x - 1) * (x^5 + x^4 + 1 + x^2) * x^2),
    :((1000x^4 + 1) * (x^4 - 1000)),
]
cases = map(vcat(fixed, products)) do e
    ee = Reduce.rcall(e, :expand)
    Dict("input" => exrec(ee), "factor" => exrec(Reduce.rcall(ee, :factor)))
end
open(io -> JSON.print(io, Dict("meta" => Dict("julia" => string(VERSION), "Reduce" => string(pkgversion(Reduce)),
                                              "seed" => "0x5EED"), "cases" => cases)),
     joinpath(OUT, "factor.json"), "w")
println("wrote ", length(cases), " cases")

# Golden generator for Wilkinson's `polyhorner`/`polyexpand` (src/Wilkinson.jl:23-30), which build
# their polynomial one `Reduce.Algebra` operation at a time (REDUCE with `exp` off per step): the
# `Reduce.Algebra` shapes of Wilkinson/Reduce.lean (`Reduce.Alg`). Edge lists (zero constant and
# middle terms, negative leading terms, float coefficients) and random lists with zeros.
#
#   julia --startup-file=no --project=<env with Reduce, JSON> oracle/wilkinson/algebra.jl
#
# Writes oracle/golden/wilkinson/algebra.json: {"polyhorner"|"polyexpand": [{"a", "out"}]}, as
# in gen.jl. Deterministic (MersenneTwister(0x5EED)).

using JSON, Random
const Reduce = Base.require(Base.PkgId(Base.UUID("93e0c654-6965-5f22-aba9-9c1ae6b3c259"), "Reduce"))
const Algebra = Reduce.Algebra
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

# src/Wilkinson.jl:23-30, verbatim
polyhorner(x,a) = polyhorner(x,a,1)
polyhorner(x,a::Array{<:Any,1},k) = k==length(a) ? a[k] : Algebra.:+(a[k],Algebra.:*(x,polyhorner(x,a,k+1)))
polyexpand(x,a) = polyexpand(x,a,length(a))
polyexpand(x,a::Array{<:Any,1},k) = k==1 ? a[k] : Algebra.:+(Algebra.:*(a[k],Algebra.:^(x,k-1)),polyexpand(x,a,k-1))

edges = Any[[0, -1, -1], [0, 0, -2, -4], [0, -2, -4], [0, 1.5, 1.5], [0, 0.5, 0, -1.5], [0, -6, 2, 1, 1],
            [0, -6, 2, 1, -1], [0, 2, -4], [0, -1, 2, 3], [1.5, 0], [0, 0, 1], [2, 0, 0, 4], [0, 6, 0, 3],
            [0, 3, -3], [0, -3, 3], [0, 0, 0, 5, -5], [0.5, 0, 0.25], [0, 0.1, 0.2, 0.3], [-1, 0, 0, -1],
            [0, -6, 2, 1], [0, 5, 1], [3, 6, 9, 3], [0, 0, 6, 2, 1], [0, 1, 0, 1, 0, 1], [0, -1, 0, -1, 0, -1],
            [4, 0, -2, 0, 1], [0, 2, 4, 6, 8, 10], [-3, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, -1]]
rng = MersenneTwister(0x5EED)
randlist(r) = rand(r) < 0.7 ? [rand(r) < 0.35 ? 0 : rand(r, -6:6) for _ in 1:rand(r, 2:7)] :
                              [rand(r) < 0.35 ? 0.0 : rand(r, [0.5, 1.5, -2.25, 3.0, 0.1, -1.0, 4.0]) for _ in 1:rand(r, 2:5)]
lists = vcat(edges, [randlist(rng) for _ in 1:400])
lit(x) = x isa Integer ? Dict("int" => string(x)) : Dict("f64" => repr(x))
rec(f, a) = (e = f(:x, a); Dict("a" => lit.(a), "out" => e isa Number ? Dict("str" => repr(e), "tree" => tree(e)) : exrec(e)))
open(io -> JSON.print(io, Dict("meta" => Dict("julia" => string(VERSION), "Reduce" => string(pkgversion(Reduce)),
                                              "seed" => "0x5EED"),
                               "polyhorner" => [rec(polyhorner, a) for a in lists if !iszero(a[end])],
                               "polyexpand" => [rec(polyexpand, a) for a in lists if !iszero(a[end])])),
     joinpath(OUT, "algebra.json"), "w")
println("wrote ", length(lists), " lists")

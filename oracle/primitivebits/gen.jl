# Oracle generator for PrimitiveBits.jl (port-notes/small-algebra.md §9.2).
#
# PrimitiveBits is not registered, so the source is `include`d from a checkout:
#   CHAKRAVALA=~/chakravala julia --startup-file=no --project=<env with JSON3> oracle/primitivebits/gen.jl
# Writes oracle/golden/primitivebits/bits.json.

using JSON3, Random

const SRC = joinpath(get(ENV, "CHAKRAVALA", joinpath(homedir(), "chakravala")),
                     "PrimitiveBits.jl", "src", "PrimitiveBits.jl")
include(SRC)
using .PrimitiveBits

Random.seed!(0x5EED)

const TYPES = Dict(8 => (PrimitiveBits8, UInt8), 16 => (PrimitiveBits16, UInt16),
                   32 => (PrimitiveBits32, UInt32), 64 => (PrimitiveBits64, UInt64),
                   128 => (PrimitiveBits128, UInt128))

errname(f) = try; f(); nothing; catch e; string(nameof(typeof(e))); end

words = Any[]
bools = Any[]
errors = Any[]
for w in (8, 16, 32, 64, 128)
    P, U = TYPES[w]
    vals = U[zero(U), one(U), typemax(U), U(7), one(U) << (w - 1)]
    append!(vals, rand(U, 60))
    for u in vals
        b = P(u)
        push!(words, Dict(
            "w" => w,
            "value" => string(u),
            "str" => sprint(print, b),
            "back" => string(U(b)),
            # Julia getindex, including the out-of-range quirk
            "idx" => [-1, 0, w + 1, w + 7],
            "idxval" => [b[-1], b[0], b[w + 1], b[w + 7]],
            "all" => b[:],
            "range25" => b[2:5],
            "range03" => b[0:3]))
    end
    for _ in 1:25
        n = rand(1:w)
        v = rand(Bool, n)
        b = P(v)
        push!(bools, Dict("w" => w, "bits" => v, "value" => string(U(b)), "str" => sprint(print, b)))
    end
    # errors: empty vector, overflowing vector, negative Int, too-large Int
    push!(errors, Dict("w" => w, "case" => "empty", "err" => errname(() -> P(Bool[]))))
    push!(errors, Dict("w" => w, "case" => "overflow_bools",
                       "bits" => fill(true, w + 1), "err" => errname(() -> P(fill(true, w + 1)))))
    push!(errors, Dict("w" => w, "case" => "leading_zeros",
                       "bits" => vcat(fill(true, w), [false, false]),
                       "err" => errname(() -> P(vcat(fill(true, w), [false, false])))))
    push!(errors, Dict("w" => w, "case" => "negative", "int" => "-1", "err" => errname(() -> P(-1))))
    push!(errors, Dict("w" => w, "case" => "too_large", "int" => string(big(2)^w),
                       "err" => errname(() -> P(big(2)^w))))
end

out = Dict("meta" => Dict("julia" => string(VERSION), "source" => "PrimitiveBits.jl 0.1.0 (include)",
                          "seed" => "0x5EED"),
           "words" => words, "bools" => bools, "errors" => errors)
dir = joinpath(@__DIR__, "..", "golden", "primitivebits")
mkpath(dir)
open(joinpath(dir, "bits.json"), "w") do io
    JSON3.write(io, out)
end
println("wrote ", length(words), " words, ", length(bools), " bool vectors, ", length(errors), " error cases")

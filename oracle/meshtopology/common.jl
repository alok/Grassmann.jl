# Shared JSON encoding for the MeshTopology goldens (see gen.jl).
#
# * `Values`, tuples and vectors become arrays; `Pair`s become `[a, b]`.
# * N-D grids are `{"dims": [...], "colmajor": [...]}` (Julia column-major order).
# * Sparse matrices are densified. `Inf` becomes the string "Inf".
# * `both(f)` evaluates `f(U)` and `f(F)` (upstream and fixed modules, load.jl). When they
#   agree it returns the value; otherwise `{"fixed": …, "julia": …}`. A Julia exception is
#   recorded as `{"error": "<ExceptionType>"}`. The Lean port must equal the fixed value.

using JSON, Random, SparseArrays, LinearAlgebra
import StaticVectors: Values

J(x::Bool) = x
J(x::Integer) = Int(x)
J(x::AbstractFloat) = isfinite(x) ? Float64(x) : (x > 0 ? "Inf" : x < 0 ? "-Inf" : "NaN")
# Type names print module-qualified because the two copies live in wrapper modules; the
# registered package (loaded with `using MeshTopology`) prints them bare.
J(x::AbstractString) = replace(String(x), r"Main\.(Fixed|Upstream)\.MeshTopology\." => "")
J(::Nothing) = nothing
J(x::Pair) = Any[J(x.first), J(x.second)]
J(x::Tuple) = Any[J(y) for y in x]
J(x::SparseMatrixCSC) = J(Matrix(x))
J(x::Dict) = x
J(x::AbstractVector) = Any[J(y) for y in x]
J(x::AbstractArray) = G(x)
J(x::AbstractArray{T,0} where T) = Dict("dims" => Int[], "colmajor" => Any[])
"An N-D array as `{dims, colmajor}` (also for vectors)."
G(x) = Dict("dims" => collect(size(x)), "colmajor" => Any[J(y) for y in vec(collect(x))])

function tryj(f)
    try
        J(f())
    catch e
        e isa InterruptException && rethrow()
        Dict("error" => string(nameof(typeof(e))))
    end
end

function both(f)
    u = tryj(() -> f(U))
    x = tryj(() -> f(F))
    u == x ? x : Dict("fixed" => x, "julia" => u)
end

"One axis of a `ProductTopology`, tagged with its Julia vector type."
function axj(v)
    T = typeof(v)
    if T <: Base.OneTo
        Dict("kind" => "OneTo", "n" => length(v))
    elseif T <: UnitRange
        Dict("kind" => "UnitRange", "start" => first(v), "stop" => last(v))
    elseif T <: StepRange
        Dict("kind" => "StepRange", "start" => first(v), "step" => step(v), "stop" => last(v))
    elseif nameof(T) == :CrossRange
        Dict("kind" => "CrossRange", "n" => length(v))
    else
        Dict("kind" => "Vector", "vals" => J(collect(v)))
    end
end
ptj(p) = Any[axj(v) for v in p.v]

"A `QuotientTopology` as its Julia tables `p, q, r, s, c` (`q` is null for 0-D maps)."
function qtj(m)
    Dict("p" => J(m.p), "q" => Any[x isa AbstractArray{T,0} where T ? nothing : ptj(x) for x in m.q],
         "r" => J(m.r), "s" => J(m.s), "c" => J(m.c))
end

writejson(file, x) = open(io -> JSON.json(io, x), joinpath(OUT, file), "w")

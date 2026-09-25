# Golden generator for the matrix functions of Outermorphism, Dyadic and Projector
# (Grassmann.jl src/forms.jl:401-408, 456-458, 774-776): exp, expm1, log.
#
#   julia --startup-file=no --project=oracle oracle/forms/gen_opfun.jl
#
# Writes oracle/golden/forms/opfun.json with the encoding of gen_parity.jl (floats as IEEE bit
# patterns "0x…", a Julia exception {"E": …}); matrices as row lists. Complex results (the
# logarithm of a singular or indefinite rank-one map) are recorded as errors of `enc`.
using Grassmann, LinearAlgebra, Random
include(joinpath(@__DIR__, "..", "unitsystems", "jsonw.jl"))
const OUT = joinpath(@__DIR__, "..", "golden", "forms")
mkpath(OUT)

hx(x::Real) = "0x" * string(reinterpret(UInt64, Float64(x)), base = 16, pad = 16)
errstr(e) = (s = sprint(showerror, e); string(nameof(typeof(e)), ": ", first(s, 160)))
enc(x::Real) = hx(x)
enc(x::AbstractVector) = [enc(y) for y in x]
enc(x::AbstractMatrix) = [[enc(x[i, j]) for j in axes(x, 2)] for i in axes(x, 1)]
enc(x::Values) = enc(collect(x))
enc(x::Chain) = enc(collect(value(x)))
enc(x::TensorOperator) = enc(Matrix(x))
enc(x::Outermorphism) = [enc(Matrix(TensorOperator(b))) for b in value(x)]
enc(x::Projector) = Dict("v" => enc(x.v), "lambda" => enc(x.λ))
macro safe(ex)
    quote
        try
            enc($(esc(ex)))
        catch e
            e isa InterruptException && rethrow()
            Dict("E" => errstr(e))
        end
    end
end
meta = Dict("julia" => string(VERSION), "grassmann" => string(pkgversion(Grassmann)), "seed" => 20260927)
Random.seed!(20260927)

op(n, A) = TensorOperator(Chain{Submanifold(n),1}(ntuple(j -> Chain{Submanifold(n),1}(ntuple(i -> A[i, j], n)...), n)...))
rnd(n) = round.(rand(n, n) .- 0.5, digits = 3)

outer = Any[]
for n in 2:4, trial in 1:3
    A = rnd(n) + 2I
    O = outermorphism(op(n, A))
    # Julia's `log(::Outermorphism)` throws (`Outermorphism(log(t[1]))` cannot convert the
    # `Endomorphism{V}(log(Matrix))` it gets): the grade-1 logarithm is recorded instead
    push!(outer, Dict("n" => n, "A" => enc(A), "exp" => @safe(exp(O)), "expm1" => @safe(expm1(O)),
        "log" => @safe(log(O)), "log_base" => @safe(log(op(n, A)))))
end

dyadic = Any[]
for n in 2:4, trial in 1:3
    V = Submanifold(n)
    x = round.(randn(n), digits = 3)
    y = round.(randn(n), digits = 3)
    D = Dyadic(Chain{V,1}(x...), Chain{V,1}(y...))
    push!(dyadic, Dict("n" => n, "x" => enc(x), "y" => enc(y), "exp" => @safe(exp(D)),
        "expm1" => @safe(expm1(D)), "log" => @safe(log(D))))
end

proj = Any[]
for n in 2:4, trial in 1:3
    V = Submanifold(n)
    v = round.(randn(n), digits = 3)
    λ = round(1 + rand(), digits = 3)
    P = Proj(Chain{V,1}(v...), λ)
    push!(proj, Dict("n" => n, "v" => enc(v), "lambda" => enc(λ), "P" => enc(P),
        "exp" => @safe(exp(P)), "log" => @safe(log(P))))
end

writejson(joinpath(OUT, "opfun.json"), Dict("meta" => meta, "outermorphism" => outer, "dyadic" => dyadic, "projector" => proj))
println("wrote opfun (", filesize(joinpath(OUT, "opfun.json")), " bytes)")

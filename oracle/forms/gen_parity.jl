# Golden generator for the parity-gap additions to Grassmann.Forms (docs/parity-gaps.json):
# polynomial roots of any degree (`roots`, `rootsreal`, `rootscomplex`, `monicroots*` of degree
# ≥ 5 through the companion matrix, complex constant terms) and real-typed eigenvectors
# (`eigvecs`, `eigvecsreal`), plus `vandermonde` (the Vandermonde operator of a point list and
# the least-squares fit `vandermonde(x, y, V)`).
#
#   julia --startup-file=no --project=oracle oracle/forms/gen_parity.jl
#
# Writes oracle/golden/forms/{roots2,eigvecs,vandermonde}.json with the encoding of gen.jl
# (floats as IEEE bit patterns "0x…", complex numbers [re, im], a Julia exception {"E": …}).
using Grassmann, LinearAlgebra, Random
include(joinpath(@__DIR__, "..", "unitsystems", "jsonw.jl"))
const OUT = joinpath(@__DIR__, "..", "golden", "forms")
mkpath(OUT)

hx(x::Real) = "0x" * string(reinterpret(UInt64, Float64(x)), base = 16, pad = 16)
errstr(e) = (s = sprint(showerror, e); string(nameof(typeof(e)), ": ", first(s, 160)))
enc(x::Bool) = x
enc(x::Integer) = Int(x)
enc(x::AbstractFloat) = hx(x)
enc(x::Complex) = [enc(real(x)), enc(imag(x))]
enc(x::AbstractVector) = [enc(y) for y in x]
enc(x::Tuple) = [enc(y) for y in x]
enc(x::AbstractMatrix) = [[enc(x[i, j]) for j in axes(x, 2)] for i in axes(x, 1)]
enc(x::Values) = enc(collect(x))
enc(x::Chain) = enc(collect(value(x)))
enc(x::TensorOperator) = enc(Matrix(x))
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
save(name, data) = (writejson(joinpath(OUT, name * ".json"), data);
    println("wrote ", name, " (", filesize(joinpath(OUT, name * ".json")), " bytes)"))
meta = Dict("julia" => string(VERSION), "grassmann" => string(pkgversion(Grassmann)), "seed" => 20260925)
Random.seed!(20260925)

# ------------------------------------------------------------------------------------------
# roots of any degree
# ------------------------------------------------------------------------------------------
roots = Any[]
function rootcase(a)
    d = Dict{String,Any}("a" => enc(collect(a)))
    d["roots"] = @safe Grassmann.roots(a...)
    d["rootsreal"] = @safe Grassmann.rootsreal(a...)
    d["rootscomplex"] = @safe Grassmann.rootscomplex(a...)
    if length(a) ≥ 2
        m = a[1:end-1] ./ a[end]
        d["monic"] = @safe Grassmann.monicroots(m...)
        d["monicreal"] = @safe Grassmann.monicrootsreal(m...)
        d["moniccomplex"] = @safe Grassmann.monicrootscomplex(m...)
    end
    push!(roots, d)
end
# fixed cases: the README-style degree-5 example, real and complex spectra, constants
for a in Any[(1.0, 2.0, 3.0, 4.0, 5.0, 6.0), (-1.0, 0.0, 5.0, 0.0, -5.0, 1.0),
        (120.0, -274.0, 225.0, -85.0, 15.0, -1.0), (2.0, 4.0), (2.0, -3.0, 1.0), (6.0, -11.0, 6.0, -1.0),
        (1.0, 0.0, 0.0, 0.0, 1.0), (1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0), (-720.0, 1764.0, -1624.0, 735.0, -175.0, 21.0, -1.0)]
    rootcase(a)
end
for deg in 1:7, trial in 1:6
    a = round.(randn(deg + 1) .* 3, digits = 3)
    a[end] == 0 && (a[end] = 1.0)
    rootcase(Tuple(a))
end
# degree 0 and complex constant terms
extra = Dict{String,Any}(
    "roots_const" => @safe(Grassmann.roots(2.0)),
    "rootsreal_const" => @safe(Grassmann.rootsreal(2.0)),
    "rootscomplex_const" => @safe(Grassmann.rootscomplex(2.0)),
    "monicroots_c1" => @safe(Grassmann.monicroots(1.0 + 2.0im)),
    "monicrootscomplex_c1" => @safe(Grassmann.monicrootscomplex(1.0 + 2.0im)),
    "roots_c2" => @safe(Grassmann.roots(1.0 + 1.0im, 2.0 + 0.0im)))
cq = Any[]
for (a0, a1) in Any[(1.0 + 2.0im, 3.0), (1.0 + 2.0im, -3.0), (-2.0 + 0.5im, 0.0), (0.25 - 1.0im, 1.5)]
    push!(cq, Dict("a0" => enc(a0), "a1" => enc(a1), "roots" => @safe(Grassmann.monicrootscomplex(a0, a1))))
end
extra["complex_quadratic"] = cq
save("roots2", Dict("meta" => meta, "cases" => roots, "extra" => extra))

# ------------------------------------------------------------------------------------------
# eigenvectors: real-typed eigvecs, eigvecsreal
# ------------------------------------------------------------------------------------------
eigs = Any[]
function eigcase(A)
    T = Endomorphism(A)
    d = Dict{String,Any}("A" => enc(A))
    d["eigvals"] = @safe eigvals(T)
    ev = try eigvecs(T) catch e; e end
    d["eigvecs_real"] = ev isa Exception ? false : eltype(Matrix(ev)) <: Real
    d["eigvecsreal"] = @safe Grassmann.eigvecsreal(T)
    push!(eigs, d)
end
for A in Any[[2.0 1.0; 1.0 3.0], [0.0 -1.0; 1.0 0.0], [4.0 1.0 0.0; 1.0 3.0 1.0; 0.0 1.0 2.0],
        [1.0 2.0 3.0; 0.0 4.0 5.0; 0.0 0.0 6.0], [0.0 1.0 0.0; 0.0 0.0 1.0; 1.0 0.0 0.0]]
    eigcase(A)
end
for n in 2:6, trial in 1:3
    A = round.(randn(n, n), digits = 2)
    trial == 1 && (A = A + A')   # symmetric: real
    eigcase(A)
end
save("eigvecs", Dict("meta" => meta, "cases" => eigs))

# ------------------------------------------------------------------------------------------
# Vandermonde operators and the least-squares fit
# ------------------------------------------------------------------------------------------
vands = Any[]
for x in Any[[1.0, 2.0, 3.0], [0.5, -1.0, 2.0, 3.0], [1.0, 2.0, 3.0, 4.0, 5.0]]
    n = length(x)
    push!(vands, Dict("x" => enc(x), "op" => @safe(vandermonde(Chain{Submanifold(n),1}(x...))),
        "disc" => @safe(value(det(vandermonde(Chain{Submanifold(n),1}(x...))))[1]^2)))
end
# The least-squares fit: Julia's `Array` method `vandermonde(x, y, N)` (`composite.jl:862-869`,
# LAPACK's pivoted QR). The `Values`/`Chain` method `vandermonde(x, y, V)` (`composite.jl:871`)
# is a Julia defect: `\` distributes over the entries of `y` (a `Values` of scaled
# pseudo-inverses, not the coefficients), so the port implements the Array semantics for both.
fits = Any[]
for (m, k) in Any[(6, 3), (8, 4), (5, 2), (10, 3), (4, 4)]
    x = sort(round.(randn(m) .* 2, digits = 3))
    y = round.(randn(m) .* 3, digits = 3)
    coef, xp, yp = Grassmann.vandermondeinterp(x, y, k, 8)
    push!(fits, Dict("x" => enc(x), "y" => enc(y), "k" => k,
        "fit" => @safe(Grassmann.vandermonde(x, y, k)),
        "matrix" => @safe(Grassmann.vandermonde(x, k)),
        "interp" => Dict("coef" => enc(coef), "xp" => enc(xp), "yp" => enc(yp)),
        "approx" => @safe(Grassmann.approx(0.75, Values(coef...)))))
end
save("vandermonde", Dict("meta" => meta, "ops" => vands, "fits" => fits))

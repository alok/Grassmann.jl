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

# ------------------------------------------------------------------------------------------
# ↑/↓ (project/reject) and the versor fields (src/Grassmann.jl:164-228, 312-314)
# ------------------------------------------------------------------------------------------
dense(x) = enc(collect(value(Multivector(x))))
updown = Any[]
for sig in ["∞+++", "∅+++", "∞∅+++", "∞∅++", "+++", "∞++"]
    V = Signature(sig)
    n = mdims(V)
    G = Λ(V)
    for trial in 1:6
        x = round.(randn(n) .* 1.5, digits = 3)
        ω = Chain{V,1}(x...)
        d = Dict{String,Any}("sig" => sig, "x" => enc(x))
        d["up"] = try dense(↑(ω)) catch e; Dict("E" => errstr(e)) end
        d["down"] = try dense(↓(ω)) catch e; Dict("E" => errstr(e)) end
        d["downup"] = try dense(↓(↑(ω))) catch e; Dict("E" => errstr(e)) end
        if hasinf(V) || hasorigin(V)
            b = hasinf(V) ? G.v∞ : G.v∅
            bc = Chain{V,1}(Values{n}([i == 1 ? 1.0 : 0.0 for i in 1:n]...))
            d["upb"] = try dense(project(ω, bc)) catch e; Dict("E" => errstr(e)) end
            d["downb"] = try dense(reject(ω, bc)) catch e; Dict("E" => errstr(e)) end
            if hasinf(V) && hasorigin(V)
                inf = Chain{V,1}(Values{n}([i == 1 ? 1.0 : 0.0 for i in 1:n]...))
                org = Chain{V,1}(Values{n}([i == 2 ? 1.0 : 0.0 for i in 1:n]...))
                d["uppm"] = try dense(project(ω, inf, org)) catch e; Dict("E" => errstr(e)) end
                d["downpm"] = try dense(reject(ω, inf, org)) catch e; Dict("E" => errstr(e)) end
            end
        end
        push!(updown, d)
    end
end
# the README curves (Grassmann README.md:271-316): f(t) = ↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3))
curves = Any[]
let V = S"∞+++", G = Λ(V)
    v1, v2, v3, v12, vi, vi3 = G.v1, G.v2, G.v3, G.v12, G.v∞, G.v∞3
    torus(t) = ↓(exp(π*t*((3/7)*v12+vi3))>>>↑(v1+v2+v3))
    orbit2(t) = ↓(exp(t*vi*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2)>>>↑(v1+v2-v3))
    orbit4(t) = ↓(exp(t*(v12+0.07vi*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2))>>>↑(v1+v2-v3))
    for t in [0.0, 0.25, 0.5, -1.3, 2.0, 5.5]
        push!(curves, Dict("curve" => "torus", "t" => enc(t), "out" => dense(torus(t))))
        push!(curves, Dict("curve" => "orbit2", "t" => enc(t), "out" => dense(orbit2(t))))
        push!(curves, Dict("curve" => "orbit4", "t" => enc(t), "out" => dense(orbit4(t))))
    end
end
let V = S"∞∅+++", G = Λ(V)
    v1, v2, v3, v12, vi3 = G.v1, G.v2, G.v3, G.v12, G.v∞3
    helix(t) = ↓(exp(π*t*((3/7)*v12+vi3))>>>↑(v1+v2+v3))
    for t in [0.0, 0.25, 0.5, -1.3, 2.0, 5.5]
        push!(curves, Dict("curve" => "helix", "t" => enc(t), "out" => dense(helix(t))))
    end
end
# chainfield / vectorfield of plane rotors and the orb versor (docs 42, 43)
fields = Any[]
let V = S"++", G = Λ(V)
    for (name, t) in Any[("plane1", exp(π*G.v12/2)), ("plane3", exp((π/4)*G.v12/2)), ("plane4", G.v1*exp((π/4)*G.v12/2))]
        F = chainfield(t)
        for p in Any[(1.0, 0.0), (0.5, -0.25), (-1.2, 0.7)]
            push!(fields, Dict("field" => name, "p" => enc(collect(p)), "out" => enc(collect(value(F(Chain{V,1}(p...)))))))
        end
    end
end
let V = S"+-", G = Λ(V)
    for (name, t) in Any[("plane5", exp((π/8)*G.v12/2)), ("plane6", G.v1*exp((π/4)*G.v12/2))]
        F = chainfield(t)
        for p in Any[(1.0, 0.5), (-0.3, 0.2)]
            push!(fields, Dict("field" => name, "p" => enc(collect(p)), "out" => enc(collect(value(F(Chain{V,1}(p...)))))))
        end
    end
end
let V = S"∞+++", G = Λ(V)
    t = exp((π/4)*(G.v12+G.v∞3))
    K = chainfield(t, V(2,3,4))
    W = chainfield(t, V(2,3,4), V(1,2,3))
    for p in Any[(0.5, 0.5, 0.5), (1.0, -0.5, 0.25), (-1.2, 0.3, 0.9)]
        push!(fields, Dict("field" => "orb", "p" => enc(collect(p)), "out" => enc(collect(value(K(Chain{V(2,3,4),1}(p...)))))))
        push!(fields, Dict("field" => "wave", "p" => enc(collect(p)), "out" => enc(collect(value(W(Chain{V(1,2,3),1}(p...)))))))
    end
end
save("updown", Dict("meta" => meta, "cases" => updown, "curves" => curves, "fields" => fields))

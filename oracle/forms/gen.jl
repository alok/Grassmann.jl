# Golden generator for the linear algebra of Grassmann elements (Grassmann.jl `src/forms.jl` and the
# determinant/roots/simplex part of `src/composite.jl`; port-notes/grassmann-forms.md).
#
#   julia --startup-file=no --project=oracle oracle/forms/gen.jl
#
# Writes oracle/golden/forms/*.json, consumed by Tests/Forms/*.lean. Encoding:
#   * integers are JSON numbers, floats are IEEE bit patterns "0x…" (exact), complex numbers
#     [re, im]; a Julia exception is {"E": "<Type>: <message>"};
#   * matrices are row lists (Julia `Matrix(T)`), chains are coefficient lists;
#   * spaces are {"n": n} (Julia `Submanifold(n)`, what `Endomorphism(::Matrix)` uses) or
#     {"sig": "-++"} / {"diag": "2,3,5"} (Julia `S"…"` / `D"…"`);
#   * display strings are Julia's 2-arg `repr` and the body of the 3-arg `show` (after the summary).
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
enc(x::Rational) = string(numerator(x), "//", denominator(x))
enc(x::AbstractVector) = [enc(y) for y in x]
enc(x::Tuple) = [enc(y) for y in x]
enc(x::AbstractMatrix) = [[enc(x[i, j]) for j in axes(x, 2)] for i in axes(x, 1)]
enc(x::Values) = enc(collect(x))
enc(x::Chain) = enc(collect(value(x)))
enc(x::Spinor) = enc(collect(value(x)))
enc(x::CoSpinor) = enc(collect(value(x)))
enc(x::Multivector) = enc(collect(value(x)))
enc(x::TensorOperator) = enc(Matrix(x))
enc(x::Outermorphism) = enc(Matrix(x))
enc(x::Grassmann.TensorTerm) = enc(Chain(x))           # Single / Submanifold: its grade's chain
enc(x::Grassmann.TensorAlgebra) = enc(Multivector(x))  # Couple, ...: dense
enc(x::AbstractString) = String(x)
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
body(x) = (s = sprint(show, MIME"text/plain"(), x); join(split(s, '\n')[2:end], '\n'))
save(name, data) = (writejson(joinpath(OUT, name * ".json"), data);
    println("wrote ", name, " (", filesize(joinpath(OUT, name * ".json")), " bytes)"))
meta = Dict("julia" => string(VERSION), "grassmann" => string(pkgversion(Grassmann)), "seed" => 20260924)
Random.seed!(20260924)

E(n) = Submanifold(n)
op(A) = Endomorphism(A)
chain(V, xs) = Chain{V,1}(xs...)
rows(A) = [collect(A[i, :]) for i in axes(A, 1)]

# ------------------------------------------------------------------------------------------
# exact (Int) operator algebra
# ------------------------------------------------------------------------------------------
function exactcase(A, B, x, y)
    n = size(A, 1)
    V = E(n)
    T, U = op(A), op(B)
    X, Y = chain(V, x), chain(V, y)
    d = Dict{String,Any}("A" => enc(A), "B" => enc(B), "x" => enc(x), "y" => enc(y))
    d["det"] = @safe value(det(T))[1]
    d["wedge"] = @safe ∧(T)
    d["tr"] = @safe tr(T)
    d["compound"] = [@safe(compound(T, g)) for g in 0:n]
    d["adjugate"] = @safe Grassmann.adjugate(T)
    d["cofactor"] = @safe Grassmann.cofactor(T)
    d["charexact"] = @safe Grassmann.characteristic_exact(T)
    d["outer"] = @safe outermorphism(T)
    d["outertr"] = @safe tr(outermorphism(T))
    d["transpose"] = @safe transpose(T)
    d["mul"] = @safe T * U
    d["add"] = @safe T + U
    d["sub"] = @safe T - U
    d["plusI"] = @safe T + I
    d["twoIminus"] = @safe 2I - T
    d["apply"] = @safe T(X)
    d["rowapply"] = @safe X ⋅ T
    d["form"] = @safe T(X, Y)
    d["gerschgorin"] = @safe Grassmann.gerschgorin(T)
    d["diag"] = @safe LinearAlgebra.diag(T)
    d["lie2"] = @safe 𝓛[T, U]
    d["lie3"] = @safe 𝓛[T, U, T * U]
    d["compoundmul"] = n ≥ 2 ? (@safe compound(T, 2) * compound(U, 2)) : nothing
    n ≥ 2 && (d["bivector"] = @safe bivector(T))
    n ≥ 2 && (d["pfaffian"] = @safe pfaffian(bivector(T)))
    d["show"] = @safe repr(T)
    d["display"] = @safe body(T)
    n ≤ 4 && (d["displayOuter"] = @safe body(outermorphism(T)))
    n ≤ 4 && (d["showOuter"] = @safe repr(outermorphism(T)))
    n ≤ 4 && n ≥ 2 && (d["displayCompound"] = @safe body(compound(T, 2)))
    # the outermorphism on every grade and on the halves / full algebra
    O = outermorphism(T)
    if 2 ≤ n ≤ 5  # Julia's `O ⋅ CoSpinor` reads out of bounds for n = 1 (an illegal instruction)
        m = rand(-3:3, 1 << n)
        M = Multivector{V}(m...)
        d["m"] = m
        d["outerMV"] = @safe O(M)
        d["outerSpinor"] = @safe O(even(M))
        d["outerCoSpinor"] = @safe O(odd(M))
        d["outerChains"] = [@safe(O(M(Val(g)))) for g in 1:n]
        d["outerOuter"] = @safe O ⋅ outermorphism(U)
        d["outerAdj"] = @safe Grassmann.adjugate(O)
    end
    return d
end

exact = Any[]
T0 = [1 4 7; 2 5 8; 3 6 10]
U0 = [2 0 1; 0 1 0; 1 0 3]
push!(exact, exactcase(T0, U0, [1, 1, 1], [1, 2, 3]))
for n in 1:6, trial in 1:(n ≤ 4 ? 12 : 6)
    A = rand(-5:5, n, n)
    B = rand(-5:5, n, n)
    push!(exact, exactcase(A, B, rand(-5:5, n), rand(-5:5, n)))
end
save("exact", Dict("meta" => meta, "cases" => exact))

# ------------------------------------------------------------------------------------------
# floating point: inverses, solve, characteristic, spectra, matrix functions
# ------------------------------------------------------------------------------------------
function floatcase(A, b)
    n = size(A, 1)
    V = E(n)
    T = op(A)
    d = Dict{String,Any}("A" => enc(A), "b" => enc(b))
    d["det"] = @safe value(det(T))[1]
    d["inv"] = @safe inv(T)
    d["invdet"] = @safe value(Grassmann.invdet(T)[2])[1]
    d["solve"] = @safe T \ chain(V, b)
    d["characteristic"] = @safe characteristic(T)
    d["eigpolys"] = @safe eigpolys(T)
    d["scalar"] = @safe scalar(T)
    d["div3"] = @safe T / 3
    n ≥ 2 && (d["discriminant"] = @safe discriminant(T))
    d["eigvals"] = @safe eigvals(T)
    d["eigvalsreal"] = @safe eigvalsreal(T)
    d["eigvalscomplex"] = @safe eigvalscomplex(T)
    d["sylvester"] = @safe Grassmann.sylvester(T)
    d["eigmults"] = @safe Grassmann.eigmults(T)
    # Julia's 2×2 closed form hangs when the discriminant vanishes (`T(1.0)` with a tensor `T`,
    # composite.jl:217): not generated
    hang = n == 2 && (A[1, 1] - A[2, 2])^2 + 4 * A[1, 2] * A[2, 1] == 0
    d["exp"] = hang ? Dict("E" => "hang") : @safe exp(T)
    d["expm1"] = hang ? Dict("E" => "hang") : @safe expm1(T)
    d["exp10"] = hang ? Dict("E" => "hang") : @safe exp(T / 10)
    d["show"] = @safe repr(T)
    d["displayInv"] = @safe body(inv(T))
    d["showInv"] = @safe repr(inv(T))
    return d
end

floats = Any[]
push!(floats, floatcase(Float64.(T0), [1.0, 2.0, 3.0]))
push!(floats, floatcase(Float64.(U0), [1.0, 0.0, 0.5]))
push!(floats, floatcase([0.0 -1.0; 1.0 0.0], [1.0, 2.0]))
push!(floats, floatcase([2.0 1.0; 1.0 2.0], [1.0, 1.0]))
push!(floats, floatcase([4.0 1 0 0; 1 3 1 0; 0 1 2 1; 0 0 1 1], [1.0, 2, 3, 4]))
push!(floats, floatcase([2.0 1 0 0 0; 1 2 1 0 0; 0 1 2 1 0; 0 0 1 2 1; 0 0 0 1 2], [1.0, 0, 0, 0, 1]))
push!(floats, floatcase([1.1 0.4 -0.5; 0.3 2.9 0.2; -0.7 1.3 4.22], [1.0, 2.0, 3.0]))
for n in 1:6, trial in 1:(n ≤ 4 ? 12 : 6)
    A = round.(randn(n, n), digits = 3)
    push!(floats, floatcase(A, round.(randn(n), digits = 3)))
end
# special families: symmetric positive definite, skew, rotations, repeated eigenvalues
for n in 2:5
    B = round.(randn(n, n), digits = 2)
    push!(floats, floatcase(B' * B + I, collect(1.0:n)))
    S = round.(randn(n, n), digits = 2)
    push!(floats, floatcase(S - S', collect(1.0:n)))
    push!(floats, floatcase(Matrix(Diagonal(Float64.([1:n-1..., 1]))), collect(1.0:n)))
end
save("float", Dict("meta" => meta, "cases" => floats))

# eigen-decompositions (LAPACK): eigenvalues, and eigenvectors compared by residual in Lean
eigens = Any[]
for (k, A) in enumerate(Any[[2.0 1.0; 1.0 2.0], [0.0 -1.0; 1.0 0.0], Float64.(T0), Float64.(U0),
        [4.0 1 0 0; 1 3 1 0; 0 1 2 1; 0 0 1 1]])
    T = op(A)
    S = eigen(T)
    push!(eigens, Dict("A" => enc(A), "vals" => enc(S.λ), "show" => repr(S), "tr" => enc(tr(S)),
        "real" => eltype(value(S.λ)) <: Real))
end
for n in 2:6, trial in 1:4
    A = round.(randn(n, n), digits = 3)
    trial == 1 && (A = A + A')
    T = op(A)
    S = eigen(T)
    push!(eigens, Dict("A" => enc(A), "vals" => enc(S.λ), "real" => eltype(value(S.λ)) <: Real))
end
save("eigen", Dict("meta" => meta, "cases" => eigens))

# matrix logarithm of symmetric positive definite matrices (Julia `log(::Symmetric)`)
logs = Any[]
push!(logs, Dict("A" => enc(Float64.(U0)), "log" => @safe log(op(Float64.(U0)))))
for n in 2:5
    B = round.(randn(n, n), digits = 2)
    A = B' * B + I
    push!(logs, Dict("A" => enc(A), "log" => @safe log(op(A))))
end
save("log", Dict("meta" => meta, "cases" => logs))

# ------------------------------------------------------------------------------------------
# polynomial roots (composite.jl)
# ------------------------------------------------------------------------------------------
roots = Any[]
for a in Any[(1.0,), (2.0, 3.0), (1.0, 0.0), (-6.0, 11.0, -6.0), (2.0, 3.0, 1.0), (24.0, -50.0, 35.0, -10.0),
        (1.0, 0.0, 0.0, 0.0), (1.0, 2.0, 3.0, 4.0), (0.0, 0.0, 0.0), (1.0, 3.0, 3.0)]
    push!(roots, Dict("a" => enc(collect(a)), "roots" => @safe(monicroots(a...)),
        "real" => @safe(monicrootsreal(a...)), "complex" => @safe(monicrootscomplex(a...))))
end
for deg in 1:4, trial in 1:25
    a = round.(randn(deg) .* 3, digits = 3)
    push!(roots, Dict("a" => enc(a), "roots" => @safe(monicroots(a...)),
        "real" => @safe(monicrootsreal(a...)), "complex" => @safe(monicrootscomplex(a...))))
end
extra = Dict("quartic1234" => enc(collect(Grassmann.quartic(1.0, 2.0, 3.0, 4.0))),
    "cubicmax231" => enc(Grassmann.cubicmax(2.0, 3.0, 1.0)))
save("roots", Dict("meta" => meta, "cases" => roots, "extra" => extra))

# ------------------------------------------------------------------------------------------
# diagonal operators
# ------------------------------------------------------------------------------------------
diags = Any[]
for dv in Any[[1, 2, 3], [2, 3, 5], [1, 1, 2], [4, -2], [3, 1, 4, 1], [2, 2, 2]]
    n = length(dv)
    V = E(n)
    D = DiagonalOperator(Chain{V,1}(dv...))
    Df = DiagonalOperator(Chain{V,1}(Float64.(dv)...))
    OD = outermorphism(D)
    x = rand(-4:4, n)
    m = rand(-3:3, 1 << n)
    M = Multivector{V}(m...)
    A = rand(-4:4, n, n)
    push!(diags, Dict("d" => dv, "x" => x, "m" => m, "A" => enc(A),
        "tr" => @safe(tr(D)), "det" => @safe(value(det(D))[1]), "wedge" => @safe(∧(D)),
        "compound2" => (n ≥ 2 ? @safe(value(value(compound(D, Val(2))))) : nothing),
        "outer" => @safe(value(value(OD))), "adjugate" => @safe(value(value(Grassmann.adjugate(D)))),
        "outerAdj" => @safe(value(value(Grassmann.adjugate(OD)))),
        "inv" => @safe(value(value(inv(Df)))), "exp" => @safe(value(value(exp(Df)))),
        "outerInv" => @safe(value(value(inv(outermorphism(Df))))),
        "apply" => @safe(D(Chain{V,1}(x...))), "form" => @safe(D(Chain{V,1}(x...), Chain{V,1}(x...))),
        "outerMV" => @safe(OD(M)), "outerSpinor" => @safe(OD(even(M))),
        "outerChain2" => (n ≥ 2 ? @safe(OD(M(Val(2)))) : nothing),
        "DT" => @safe(Matrix(D ⋅ op(A))), "charexact" => @safe(characteristic(D)),
        "eigpolys" => @safe(eigpolys(Df)), "eigvals" => @safe(eigvals(Df)),
        "sylvester" => @safe(Grassmann.sylvester(Df)), "eigmults" => @safe(Grassmann.eigmults(Chain{V,1}(dv...))),
        "scalar" => @safe(scalar(Df)), "half" => @safe(value(value(Df / 2))),
        "show" => @safe(repr(D)), "showOuter" => @safe(repr(OD)), "display" => @safe(body(D))))
end
save("diag", Dict("meta" => meta, "cases" => diags))

# ------------------------------------------------------------------------------------------
# non-square operators and simplices (homogeneous coordinates)
# ------------------------------------------------------------------------------------------
rect = Any[]
for (m, n) in [(3, 2), (2, 3), (4, 2), (4, 3), (3, 1)], trial in 1:3
    A = rand(-4:4, m, n)
    V, W = E(n), E(m)
    T = TensorOperator(Chain{V,1}([Chain{W,1}(A[:, j]...) for j in 1:n]...))
    x = rand(-3:3, n)
    mv = rand(-3:3, 1 << n)
    Af = Float64.(A)
    Tf = TensorOperator(Chain{V,1}([Chain{W,1}(Af[:, j]...) for j in 1:n]...))
    O = outermorphism(T)
    push!(rect, Dict("A" => enc(A), "x" => x, "mv" => mv,
        "apply" => @safe(T ⋅ Chain{V,1}(x...)), "wedge" => @safe(value(∧(T))),
        "compound" => [@safe(compound(T, g)) for g in 1:min(m, n)],
        "outer" => @safe(Matrix(O)), "outerMV" => @safe(O(Multivector{V}(mv...))),
        "pinv" => @safe(inv(Tf)), "transpose" => @safe(transpose(T)),
        "display" => @safe(body(T)), "show" => @safe(repr(T))))
end
save("rect", Dict("meta" => meta, "cases" => rect))

simplices = Any[]
function simplexcase(pts, probes)
    n = length(pts)
    V = E(length(pts[1]))
    t = Chain{V,1}([Chain{V,1}(p...) for p in pts]...)
    d = Dict{String,Any}("pts" => enc(pts))
    d["affineframe"] = @safe Matrix(affineframe(TensorOperator(t)))
    d["mean"] = @safe mean(t)
    d["barycenter"] = @safe barycenter(t)
    d["centroid"] = @safe Grassmann.centroid(t)
    d["det"] = @safe value(det(t))[1]
    d["inv"] = @safe Matrix(TensorOperator(inv(t)))
    d["gradient"] = @safe Matrix(TensorOperator(Grassmann.gradient(t)))
    d["cofactor"] = @safe Matrix(TensorOperator(Grassmann.cofactor(t)))
    d["probes"] = enc(probes)
    d["in"] = [@safe(Chain{V,1}(p...) ∈ t) for p in probes]
    d["solve"] = [@safe(t \ Chain{V,1}(p...)) for p in probes]
    d["showInv"] = @safe repr(inv(t))
    d["showGradient"] = @safe repr(Grassmann.gradient(t))
    return d
end
push!(simplices, simplexcase([[1.0, 0, 0], [1.0, 1, 0], [1.0, 0, 1]], [[1.0, 0.25, 0.25], [1.0, 0.75, 0.75], [1.0, -0.1, 0.2], [1.0, 0.2, 0.2]]))
push!(simplices, simplexcase([[1.0, 0, 0, 0], [1.0, 1, 0, 0], [1.0, 0, 1, 0], [1.0, 0, 0, 1]], [[1.0, 0.1, 0.2, 0.3], [1.0, 0.5, 0.5, 0.5]]))
for dim in 2:4, trial in 1:5
    pts = [vcat(1.0, round.(randn(dim), digits = 3)) for _ in 1:dim+1]
    probes = [vcat(1.0, round.(randn(dim) .* 0.5, digits = 3)) for _ in 1:4]
    push!(simplices, simplexcase(pts, probes))
end
save("simplex", Dict("meta" => meta, "cases" => simplices))

# ------------------------------------------------------------------------------------------
# operators of elements (sandwich), metric tensors, Cayley tables
# ------------------------------------------------------------------------------------------
spacecases = Any[]
spacedesc(s) = s isa String ? (occursin(",", s) ? Dict("diag" => s) : Dict("sig" => s)) : Dict("n" => s)
function spaceof(s)
    s isa Int && return Submanifold(s)
    occursin(",", s) ? DiagonalForm(parse.(Int, split(s, ","))...) : Signature(s)
end
for s in Any[2, 3, 4, "+++", "-++", "2,3,5", "∞∅++", "∅++", "-+++"]
    V = spaceof(s)
    n = mdims(V)
    B = Λ(V)
    d = Dict{String,Any}("space" => spacedesc(s))
    d["metric"] = @safe Matrix(metrictensor(V))
    d["metric2"] = n ≥ 2 ? @safe(Matrix(metrictensor(V, 2))) : nothing
    d["antimetric"] = @safe Matrix(Grassmann.antimetrictensor(V))
    d["metricext"] = @safe Matrix(metricextensor(V))
    d["displayMetric"] = @safe body(metrictensor(V))
    # sandwich operators of random chains of every grade and of a spinor
    elems = Any[]
    for g in 0:n
        c = rand(-2:2, binomial(n, g))
        all(iszero, c) && (c[1] = 1)
        t = Chain{V,g}(c...)
        push!(elems, Dict("grade" => g, "c" => c,
            "op" => [@safe(Matrix(operator(t, G))) for G in 1:n]))
    end
    sp = rand(-2:2, 1 << (n - 1))
    push!(elems, Dict("spinor" => sp,
        "op" => [@safe(Matrix(operator(Spinor{V}(sp...), G))) for G in 1:n]))
    d["operators"] = elems
    if !Grassmann.DirectSum.hasconformal(V) && n ≤ 3
        d["alltex"] = @safe collect(Grassmann.alltex(V))
        d["cayley1"] = @safe body(cayley(V, 1))
        d["cayleyFull"] = @safe body(cayley(V))
    end
    push!(spacecases, d)
end
save("spaces", Dict("meta" => meta, "cases" => spacecases))

# ------------------------------------------------------------------------------------------
# rank-one forms: projectors, dyadics, spectral operators
# ------------------------------------------------------------------------------------------
dyads = Any[]
for trial in 1:12
    n = 2 + trial % 3
    V = E(n)
    x = Chain{V,1}(round.(randn(n), digits = 2)...)
    y = Chain{V,1}(round.(randn(n), digits = 2)...)
    z = Chain{V,1}(round.(randn(n), digits = 2)...)
    lam = round(randn() * 2, digits = 2)
    P = Proj(x, lam)
    P1 = Proj(x)
    D = Dyadic(x, y)
    push!(dyads, Dict("x" => enc(x), "y" => enc(y), "z" => enc(z), "lam" => enc(lam),
        "Pv" => @safe(P.v), "Pz" => @safe(P(z)), "zP" => @safe(z ⋅ P), "Pzz" => @safe(P(z, z)),
        "PChain" => @safe(Matrix(TensorOperator(Chain(P)))), "Ptr" => @safe(tr(P)),
        "Dz" => @safe(D(z)), "zD" => @safe(z ⋅ D), "Dzz" => @safe(D(z, z)), "Dtr" => @safe(tr(D)),
        "DChain" => @safe(Matrix(TensorOperator(Chain(D)))), "DD" => Dict("x" => @safe((D ⋅ D).x), "y" => @safe((D ⋅ D).y)),
        "PD" => Dict("x" => @safe((P ⋅ D).x), "y" => @safe((P ⋅ D).y)),
        "DP" => Dict("x" => @safe((D ⋅ P).x), "y" => @safe((D ⋅ P).y)),
        "PP" => Dict("x" => @safe((P1 ⋅ P1).x), "y" => @safe((P1 ⋅ P1).y)),
        "showP" => @safe(repr(P)), "showP1" => @safe(repr(P1)), "showD" => @safe(repr(D))))
end
save("dyadic", Dict("meta" => meta, "cases" => dyads))

# ------------------------------------------------------------------------------------------
# element evaluation, subspaces, vecdot
# ------------------------------------------------------------------------------------------
evals = Any[]
for s in Any["+++", "-++", "2,3,5", 4, "-+++"]
    V = spaceof(s)
    n = mdims(V)
    for trial in 1:4
        g = rand(1:n)
        t = Chain{V,g}(rand(-3:3, binomial(n, g))...)
        ys = [Chain{V,1}(rand(-3:3, n)...) for _ in 1:g]
        m = Multivector{V}(rand(-3:3, 1 << n)...)
        push!(evals, Dict("space" => spacedesc(s), "g" => g, "t" => enc(t), "ys" => enc(ys), "m" => enc(m),
            "eval" => @safe(t(ys...)), "eval1" => @safe(t(ys[1])), "evalM" => @safe(m(ys...)),
            "vecdot" => @safe(Grassmann.vecdot(t, t)), "vecdotM" => @safe(Grassmann.vecdot(m, t)),
            "vecdotMM" => @safe(Grassmann.vecdot(m, m))))
    end
end
save("eval", Dict("meta" => meta, "cases" => evals))

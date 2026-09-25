# Oracle generator for Tests/AbstractTensors/Golden.lean.
#
#   julia --startup-file=no --project=oracle Tests/AbstractTensors/oracle/gen_goldens.jl > Tests/AbstractTensors/Golden.lean
#
# Suites:
#  * generic: AbstractTensors' derived formulas (cos = cosh(I⟑t), asin, …, the co family) and
#    Grassmann's generic series loops (expm1, cosh, sinh, qlog, log, sqrt) evaluated by the real
#    Julia methods on a scalar "tensor" carrier `Sc{V,T} <: TensorAlgebra{V,T}` whose value is a
#    Float64 (pseudoscalar I = 1, so I² = +1: the B2 cosh behaviour) or a ComplexF64
#    (I = im, I² = -1). The Lean side instantiates the same algorithms at Float / Complex Float.
#  * complex: Julia Base ComplexF64 functions (the Lean `Complex Float` port).
#  * float: Base expm1, log1p, hypot on Float64.
#  * sv: StaticVectors reductions and norms on Values{N,Float64}.
# Floats are dumped as IEEE bit patterns.
using AbstractTensors, Grassmann, DirectSum, StaticVectors, LinearAlgebra, Random
const AT = AbstractTensors
const SV = StaticVectors

# ---------------------------------------------------------------- scalar carrier
struct PS{P} end
struct Sc{V,T} <: AT.TensorAlgebra{V,T}
    x::T
end
Sc{V}(x::T) where {V,T} = Sc{V,T}(x)
"`one(V)`: adds to the scalar part only (Julia `One(V) + t`)."
struct OneM{V} end
AT.value(t::Sc) = t.x
AT.plus(a::Sc{V,T}, b::Sc{V,T}) where {V,T} = Sc{V,T}(a.x + b.x)
AT.minus(a::Sc{V,T}, b::Sc{V,T}) where {V,T} = Sc{V,T}(a.x - b.x)
Base.:-(a::Sc{V,T}) where {V,T} = Sc{V,T}(-a.x)
AT.wedgedot(a::Sc{V,T}, b::Sc{V,T}) where {V,T} = Sc{V,T}(a.x * b.x)
Base.inv(a::Sc{V,T}) where {V,T} = Sc{V,T}(inv(a.x))
Base.:/(a::Sc{V,T}, k::Real) where {V,T} = Sc{V,T}(a.x / k)
Base.:*(k::Real, a::Sc{V,T}) where {V,T} = Sc{V,T}(k * a.x)
Base.:*(a::Sc{V,T}, k::Real) where {V,T} = Sc{V,T}(a.x * k)
Base.:+(a::Sc{V,T}, k::Real) where {V,T} = Sc{V,T}(a.x + Float64(k))
Base.:+(::OneM{V}, b::Sc{V,T}) where {V,T} = Sc{V,T}(1.0 + b.x)
Base.:+(a::Sc{V,T}, ::OneM{V}) where {V,T} = Sc{V,T}(a.x + 1.0)
Base.:-(::OneM{V}, b::Sc{V,T}) where {V,T} = Sc{V,T}(1.0 - b.x)
Base.:-(a::Sc{V,T}, ::OneM{V}) where {V,T} = Sc{V,T}(a.x - 1.0)
Base.one(::PS{P}) where P = OneM{PS{P}()}()
Base.zero(::PS{P}) where P = Sc{PS{P}(),typeof(float(P))}(zero(float(P)))
Grassmann.One(v::PS) = one(v)
(::PS{P})(J::UniformScaling) where P = Sc{PS{P}(),typeof(float(P))}(float(P)*J.λ)
AT.isscalar(::Sc) = false
Base.:~(a::Sc{V,T}) where {V,T} = Sc{V,T}(conj(a.x))
AT.complementright(a::Sc{V,T}) where {V,T} = a ⟑ V(I)
AT.complementleft(a::Sc{V,T}) where {V,T} = a ⟑ V(I)
const VF = PS{1.0}()
const VC = PS{im}()
val(r::Sc) = r.x
val(::OneM) = 1.0
val(r::Number) = r

bits(x::Float64) = "0x" * string(reinterpret(UInt64, x), base=16, pad=16)

const gen1 = [
    ("expm1", expm1), ("exp", exp), ("cosh", cosh), ("sinh", sinh), ("log", log), ("log1p", log1p),
    ("sqrt", sqrt), ("cbrt", cbrt), ("qlog", Grassmann.qlog),
    ("cos", cos), ("sin", sin), ("tan", tan), ("cot", cot), ("sec", sec), ("csc", csc),
    ("tanh", tanh), ("coth", coth), ("sech", sech), ("csch", csch),
    ("asinh", asinh), ("acosh", acosh), ("atanh", atanh), ("acoth", acoth),
    ("asin", asin), ("acos", acos), ("atan", atan), ("acot", acot),
    ("asec", asec), ("acsc", acsc), ("asech", asech), ("acsch", acsch),
    ("sinc", sinc), ("cosc", cosc), ("exp2", exp2), ("exp10", exp10), ("log2", log2), ("log10", log10),
    ("rpow2", t -> 2.0^t), ("logb2", t -> log(t)/log(2.0)),
    ("abs", abs), ("abs2", abs2), ("unit", AT.unit), ("coabs", AT.coabs), ("geomabs", AT.geomabs),
    ("unitnorm", AT.unitnorm), ("coabs2", AT.coabs2), ("cosqrt", AT.cosqrt), ("cocbrt", AT.cocbrt),
    ("coexp", AT.coexp), ("colog", AT.colog), ("coinv", AT.coinv), ("cosin", AT.cosin),
    ("cocos", AT.cocos), ("cotan", AT.cotan), ("cosinh", AT.cosinh), ("cocosh", AT.cocosh),
    ("cotanh", AT.cotanh),
]
const gen2 = [
    ("div", (a, b) -> a / b), ("ldiv", (a, b) -> a \ b), ("metric", (a, b) -> abs(a - b)),
    ("cometric", (a, b) -> AT.pseudoabs(a - b)),
]

# Real carrier (I = 1): inputs inside each function's convergence domain (outside it,
# Grassmann's uncapped loops can run forever, e.g. expm1(-Inf)).
const genericReal = Dict(
    "default" => [0.1, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0, -0.3, -0.8, -1.7],
    "pos" => [0.1, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0],
    "unitball" => [0.1, 0.25, 0.5, 0.65, -0.3, -0.6],
    "asinacos" => [0.1, 0.25, 0.5, 0.75, 0.9, -0.3, -0.6],
    "gt1" => [1.1, 1.5, 2.0, 3.0],
    "sec" => [1.1, 1.5, 2.0, 3.0, -1.5, -2.5],
    "sech" => [0.1, 0.3, 0.6, 0.9],
    "nonzero" => [0.1, 0.5, 1.0, 2.0, -0.4, -1.5],
    "qlog" => [0.05, 0.2, 0.5, 0.8, -0.3, -0.7],
    "log1p" => [0.05, 0.3, 1.0, 2.5, -0.4, -0.8],
)
const domReal = Dict(
    "log" => "pos", "sqrt" => "pos", "cbrt" => "pos", "log2" => "pos", "log10" => "pos",
    "logb2" => "pos", "qlog" => "qlog", "log1p" => "log1p", "colog" => "pos", "cosqrt" => "pos",
    "cocbrt" => "pos", "asin" => "asinacos", "acos" => "asinacos", "atan" => "unitball",
    "atanh" => "unitball", "acot" => "gt1", "acosh" => "gt1", "acoth" => "gt1", "asec" => "sec",
    "acsc" => "sec", "asech" => "sech", "acsch" => "nonzero", "abs" => "nonzero", "unit" => "nonzero",
    "coabs" => "nonzero", "geomabs" => "nonzero", "unitnorm" => "nonzero", "coabs2" => "nonzero",
    "coinv" => "nonzero", "cot" => "nonzero", "csc" => "nonzero", "coth" => "nonzero",
    "csch" => "nonzero", "cotan" => "default",
)
# Complex carrier (I = im): logs converge for Re > 0.
const genericComplex = Dict(
    "default" => [0.1+0.2im, 0.5+0.25im, 0.3-0.4im, -0.6+0.5im, 1.0+0.0im, 0.0+0.7im, 1.2-0.9im],
    "rpos" => [0.1+0.2im, 0.5+0.25im, 0.3-0.4im, 1.0+0.0im, 2.0+1.5im, 0.7-1.1im],
    "small" => [0.1+0.2im, 0.3+0.25im, 0.4-0.3im, 0.2-0.1im, 0.5+0.1im],
    "atan" => [0.1+0.2im, 0.5+0.25im, 0.3-0.4im, -0.6+0.5im, 1.5-0.3im],
    "acosh" => [2.0+0.5im, 1.8-0.3im, 3.0+1.0im, 1.6+0.2im],
    "acoth" => [1.5+0.5im, 2.0-0.3im, 3.0+1.0im],
    "asec" => [2.0+0.5im, 2.5-0.4im, 3.0+1.0im],
    "asech" => [0.4+0.1im, 0.3-0.05im, 0.5+0.2im],
    "acsch" => [0.5+0.25im, 1.0+0.5im, 2.0-1.0im],
    "log1p" => [0.1+0.2im, 0.5+0.25im, -0.3-0.4im, 1.0+1.0im],
    "qlog" => [0.1+0.2im, 0.5+0.25im, -0.3-0.4im, 0.0+0.6im],
)
const domComplex = Dict(
    "log" => "rpos", "sqrt" => "rpos", "cbrt" => "rpos", "log2" => "rpos", "log10" => "rpos",
    "logb2" => "rpos", "qlog" => "qlog", "log1p" => "log1p", "abs" => "default",
    "unit" => "default", "coabs" => "default", "geomabs" => "default", "unitnorm" => "default",
    "coabs2" => "default", "colog" => "rpos", "cosqrt" => "rpos", "cocbrt" => "rpos",
    "asin" => "small", "acos" => "small", "atan" => "atan", "atanh" => "small", "acot" => "rpos",
    "asinh" => "rpos", "acosh" => "acosh", "acoth" => "acoth", "asec" => "asec", "acsc" => "asec",
    "asech" => "asech", "acsch" => "acsch",
)
# colog(t) = log(t⟑I)⟑I: for the complex carrier t⟑I must have Re > 0.
const coComplexArg = Dict("colog" => [0.2-0.3im, -0.4-0.5im, 1.0-2.0im],
                          "cosqrt" => [0.2-0.3im, -0.4-0.5im, 1.0-2.0im],
                          "cocbrt" => [0.2-0.3im, -0.4-0.5im, 1.0-2.0im])

out = IOBuffer()
println(out, "/-")
println(out, "Oracle goldens for AbstractTensors (generated; do not edit).")
println(out, "Regenerate with `julia --startup-file=no --project=oracle Tests/AbstractTensors/oracle/gen_goldens.jl`.")
println(out, "Julia $(VERSION), AbstractTensors $(pkgversion(AbstractTensors)), Grassmann $(pkgversion(Grassmann)), StaticVectors $(pkgversion(StaticVectors)).")
println(out, "-/")
println(out, "namespace Tests.AbstractTensors.Golden\n")

println(out, "/-- Generic algorithms on the real carrier (`I = 1`): (function, input, output) bits. -/")
println(out, "def genericReal : Array (String × UInt64 × UInt64) := #[")
for (name, f) in gen1
    for x in genericReal[get(domReal, name, "default")]
        r = val(f(Sc{VF}(x)))
        println(out, "  (\"$name\", $(bits(x)), $(bits(Float64(r)))),")
    end
end
println(out, "]\n")

println(out, "/-- Generic algorithms on the complex carrier (`I = i`): (function, re, im, out re, out im). -/")
println(out, "def genericComplex : Array (String × UInt64 × UInt64 × UInt64 × UInt64) := #[")
for (name, f) in gen1
    zs = haskey(coComplexArg, name) ? coComplexArg[name] : genericComplex[get(domComplex, name, "default")]
    for z in zs
        r = complex(val(f(Sc{VC}(ComplexF64(z)))))
        println(out, "  (\"$name\", $(bits(real(z))), $(bits(imag(z))), $(bits(real(r))), $(bits(imag(r)))),")
    end
end
println(out, "]\n")

println(out, "/-- Binary generic operations, real carrier: (function, a, b, output). -/")
println(out, "def genericRealBin : Array (String × UInt64 × UInt64 × UInt64) := #[")
for (name, f) in gen2
    for (a, b) in [(0.5, 2.0), (1.5, -0.25), (-3.0, 0.75), (2.0, 3.0)]
        r = val(f(Sc{VF}(a), Sc{VF}(b)))
        println(out, "  (\"$name\", $(bits(a)), $(bits(b)), $(bits(Float64(r)))),")
    end
end
println(out, "]\n")

println(out, "/-- Binary generic operations, complex carrier: (function, a re, a im, b re, b im, out re, out im). -/")
println(out, "def genericComplexBin : Array (String × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) := #[")
for (name, f) in gen2
    for (a, b) in [(0.5+0.1im, 2.0-1.0im), (1.5+0.0im, -0.25+0.5im), (-3.0+2.0im, 0.75+0.25im)]
        r = complex(val(f(Sc{VC}(a), Sc{VC}(b))))
        println(out, "  (\"$name\", $(bits(real(a))), $(bits(imag(a))), $(bits(real(b))), $(bits(imag(b))), $(bits(real(r))), $(bits(imag(r)))),")
    end
end
println(out, "]\n")

# ---------------------------------------------------------------- Base ComplexF64
const cbase1 = [("inv", inv), ("abs", z -> complex(abs(z))), ("sqrt", sqrt), ("exp", exp),
    ("expm1", expm1), ("log", log), ("log1p", log1p), ("sin", sin), ("cos", cos), ("tan", tan),
    ("sinh", sinh), ("cosh", cosh), ("tanh", tanh), ("asin", asin), ("acos", acos), ("atan", atan),
    ("asinh", asinh), ("acosh", acosh), ("atanh", atanh)]
rng = Xoshiro(20260924)
czs = ComplexF64[0.5+0.25im, -1.5+2.0im, 3.0-4.0im, 1e-3+2e-3im, -0.0+1.0im, 0.0-0.0im, 2.0+0.0im,
    -2.0+0.0im, -2.0-0.0im, 1e200+1e200im, 1e-200-3e-200im, 1.0+0.0im, 0.7-0.7im, -0.3-1e-12im,
    Inf+1.0im, -Inf+2.0im, 1.0+Inf*im, NaN+1.0im, 1.0+NaN*im, 0.0+2.0im, 0.0-0.5im]
for _ in 1:16
    push!(czs, ComplexF64(4rand(rng)-2, 4rand(rng)-2))
end
println(out, "/-- Julia `Base` on `ComplexF64`: (function, re, im, out re, out im). -/")
println(out, "def complexBase : Array (String × UInt64 × UInt64 × UInt64 × UInt64) := #[")
for (name, f) in cbase1, z in czs
    r = try complex(f(z)) catch; continue end
    println(out, "  (\"$name\", $(bits(real(z))), $(bits(imag(z))), $(bits(real(r))), $(bits(imag(r)))),")
end
println(out, "]\n")
cps = [(0.5+0.25im, 2.0-1.0im), (-1.5+2.0im, 0.5+0.0im), (3.0-4.0im, 3.0+0.0im), (2.0+0.0im, 0.5+0.0im),
    (-2.0+0.0im, 0.5+0.0im), (0.7-0.7im, -2.0+0.0im), (1e300+1e300im, 1e-300+2e-300im),
    (1.0+2.0im, 0.3+0.4im), (0.0+0.0im, 2.0+0.0im), (1.0+1.0im, Inf+0.0im)]
for _ in 1:8
    push!(cps, (ComplexF64(4rand(rng)-2, 4rand(rng)-2), ComplexF64(4rand(rng)-2, 4rand(rng)-2)))
end
println(out, "/-- Julia `Base` binary ops on `ComplexF64`: (op, a re, a im, b re, b im, out re, out im). -/")
println(out, "def complexBaseBin : Array (String × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) := #[")
for (name, f) in [("div", /), ("mul", *), ("pow", ^)], (a, b) in cps
    r = complex(f(a, b))
    println(out, "  (\"$name\", $(bits(real(a))), $(bits(imag(a))), $(bits(real(b))), $(bits(imag(b))), $(bits(real(r))), $(bits(imag(r)))),")
end
println(out, "]\n")

# ---------------------------------------------------------------- Base Float64
fxs = Float64[0.0, -0.0, 1e-300, 1e-17, -1e-17, 1e-10, 1e-5, -1e-5, 0.1, -0.1, 0.25, 0.5, -0.5,
    0.693, 1.0, -1.0, 2.0, 5.0, -5.0, 20.0, 700.0, -700.0, 709.0, -745.0, Inf, -Inf, NaN]
for _ in 1:24
    push!(fxs, 6randn(rng))
end
println(out, "/-- Julia `Base` on `Float64`: (function, x, f(x)). -/")
println(out, "def floatBase : Array (String × UInt64 × UInt64) := #[")
for (name, f) in [("expm1", expm1), ("log1p", log1p)], x in fxs
    r = try f(x) catch; continue end
    println(out, "  (\"$name\", $(bits(x)), $(bits(r))),")
end
println(out, "]\n")
hps = [(3.0, 4.0), (1.0, 1e-20), (1e300, 1e300), (1e-300, 3e-300), (0.0, -0.0), (-5.0, 12.0),
    (Inf, NaN), (NaN, 1.0), (1.0, 1.0), (0.1, 0.2)]
for _ in 1:24
    push!(hps, (randn(rng) * 10.0^rand(rng, -5:5), randn(rng) * 10.0^rand(rng, -5:5)))
end
println(out, "/-- Julia `hypot(x, y)`: (x, y, hypot). -/")
println(out, "def hypotCases : Array (UInt64 × UInt64 × UInt64) := #[")
for (x, y) in hps
    println(out, "  ($(bits(x)), $(bits(y)), $(bits(hypot(x, y)))),")
end
println(out, "]\n")

# ---------------------------------------------------------------- StaticVectors
vecs = Vector{Vector{Float64}}([[3.0, 4.0], [0.1, 0.2, 0.3], [-0.0], [0.0, -0.0], [1.0, NaN, 3.0],
    [1e200, 1e200], [1e-200, 1e-200], [1.0, -2.0, 3.0]])
for n in (1, 2, 3, 4, 5, 8, 16)
    push!(vecs, round.(20 .* rand(rng, n) .- 10, digits=3))
    push!(vecs, randn(rng, n))
end
fmt(v) = "#[" * join(bits.(v), ", ") * "]"
println(out, "/-- StaticVectors on `Values{N,Float64}`: (function, input, output). -/")
println(out, "def svUnary : Array (String × Array UInt64 × Array UInt64) := #[")
for v in vecs
    a = SV.Values{length(v)}(v...)
    for (name, f) in [("sum", x -> [sum(x)]), ("prod", x -> [prod(x)]), ("maximum", x -> [maximum(x)]),
                      ("minimum", x -> [minimum(x)]), ("cumsum", x -> collect(cumsum(x))),
                      ("cumprod", x -> collect(cumprod(x))), ("accumulate-", x -> collect(accumulate(-, x))),
                      ("reverse", x -> collect(reverse(x))), ("diff", x -> collect(diff(x))),
                      ("norm", x -> [norm(x)]), ("norm1", x -> [norm(x, 1)]), ("normInf", x -> [norm(x, Inf)]),
                      ("norm3", x -> [norm(x, 3)]), ("normalize", x -> collect(normalize(x))),
                      ("normalize1", x -> collect(normalize(x, 1))), ("neg", x -> collect(-x)),
                      ("scale2.5", x -> collect(x * 2.5)), ("div3", x -> collect(x / 3))]
        r = try f(a) catch; continue end
        println(out, "  (\"$name\", $(fmt(v)), $(fmt(Float64.(r)))),")
    end
end
println(out, "]\n")
println(out, "/-- StaticVectors binary ops on `Values{N,Float64}`: (function, a, b, output). -/")
println(out, "def svBinary : Array (String × Array UInt64 × Array UInt64 × Array UInt64) := #[")
for v in vecs
    n = length(v)
    w = randn(rng, n)
    a = SV.Values{n}(v...); b = SV.Values{n}(w...)
    for (name, f) in [("dot", (x, y) -> [dot(x, y)]), ("add", (x, y) -> collect(x + y)),
                      ("sub", (x, y) -> collect(x - y)), ("vcat", (x, y) -> collect(vcat(x, y))),
                      ("isapprox", (x, y) -> [Float64(isapprox(x, y))]),
                      ("isapproxself", (x, y) -> [Float64(isapprox(x, x .+ 1e-12))])]
        r = try f(a, b) catch; continue end
        println(out, "  (\"$name\", $(fmt(v)), $(fmt(w)), $(fmt(Float64.(r)))),")
    end
end
println(out, "]\n")
println(out, "end Tests.AbstractTensors.Golden")
print(String(take!(out)))

# Golden generator for FieldAlgebra's `Ring` (`@ring`) and bases with values
# (`@group2 … begin a = v … end`: `product`, `factorize`, the ` = value` display).
#   julia --startup-file=no --project=oracle oracle/similitude/ring.jl
# Writes oracle/golden/similitude/ring.json.
using FieldAlgebra, Random
const FA = FieldAlgebra
include(joinpath(@__DIR__, "..", "unitsystems", "jsonw.jl"))
const OUT = joinpath(@__DIR__, "..", "golden", "similitude")
mkpath(OUT)
Random.seed!(20260925)

showstr(x) = try sprint(show, x) catch e; "ERROR" end
h(x::Float64) = "0x" * string(reinterpret(UInt64, x), base = 16, pad = 16)
enc(x::Integer) = ["I", string(x)]
enc(x::Rational) = ["R", string(numerator(x), "/", denominator(x))]
enc(x::AbstractFloat) = ["F", h(Float64(x))]
# a ring as its terms in Julia's order: exponents, coefficient, and the printed form
encr(r::FA.Ring) = Dict("terms" => [Dict("v" => [enc(a) for a in r.v[i]], "c" => enc(r.c[i])) for i in 1:length(r)],
                        "show" => showstr(r))
encr(x) = "ERROR"
encg(g) = Dict("v" => [enc(a) for a in g.v], "c" => enc(g.c), "show" => showstr(g))
tryr(f) = try encr(f()) catch; "ERROR" end

FA.@ring xyz x y z
const gens = (x, y, z)

# README and documented cases (by name; replayed by the Lean test)
readme = Any[]
for (nm, f) in [("x*y^2", () -> x*y^2), ("x*y^2/x", () -> (x*y^2)/x), ("x+y^2", () -> x+y^2),
        ("(x+y)*(x-y)", () -> (x+y)*(x-y)), ("x-x", () -> x-x), ("x+x", () -> x+x), ("x+y+x", () -> x+y+x),
        ("x+y-x", () -> x+y-x), ("(x+y)-(x+y)", () -> (x+y)-(x+y)), ("2x", () -> 2x), ("x*2", () -> x*2),
        ("2.0x", () -> 2.0x), ("x/2", () -> x/2), ("0.5x", () -> 0.5x), ("x+1", () -> x+1), ("1+x", () -> 1+x),
        ("x-1", () -> x-1), ("1-x", () -> 1-x), ("(x+y)^2", () -> (x+y)^2), ("(x+y)^3", () -> (x+y)^3),
        ("inv(x)", () -> inv(x)), ("x^-2", () -> x^-2), ("x^0", () -> x^0), ("-x", () -> -x),
        ("-(x+y)", () -> -(x+y)), ("zero", () -> zero(x)), ("one", () -> one(x)), ("x+y+z", () -> x+y+z),
        ("(x+y+z)*(x-y)", () -> (x+y+z)*(x-y)), ("(x+2y)*(3x-y)", () -> (x+2y)*(3x-y)),
        ("0.5x+0.5y", () -> 0.5x+0.5y), ("(x-y)+(y-x)", () -> (x-y)+(y-x)), ("(x+y)+(x-y)", () -> (x+y)+(x-y)),
        ("(x+y)-(x-y)", () -> (x+y)-(x-y)), ("x*y*z", () -> x*y*z), ("x/y", () -> x/y), ("x*(y+z)", () -> x*(y+z)),
        ("(y+z)*x", () -> (y+z)*x), ("2*(x+y)", () -> 2*(x+y)), ("(x+y)*2", () -> (x+y)*2), ("(x+y)/2", () -> (x+y)/2),
        ("x-2x", () -> x-2x), ("2x-x", () -> 2x-x), ("x-(x+y)", () -> x-(x+y)), ("y-(x+y)", () -> y-(x+y)),
        ("(x+y)-y", () -> (x+y)-y), ("(x+y+z)^2", () -> (x+y+z)^2), ("(x-y)^3", () -> (x-y)^3),
        ("(2x+3y)^2", () -> (2x+3y)^2), ("(x*y^-1+z)^2", () -> (x*y^-1+z)^2)]
    push!(readme, [nm, tryr(f)])
end
evals = Any[]
for (nm, f, args) in [("x+y", x+y, (2.0, 3.0, 4.0)), ("x*y^2", x*y^2, (2.0, 3.0, 4.0)),
        ("(x+y)^2", (x+y)^2, (1.5, -2.5, 0.25)), ("x*y^-1+z", x*y^-1+z, (0.3, 0.7, 1.1)), ("x+y+z", x+y+z, (0.1, 0.2, 0.3))]
    push!(evals, [nm, [enc(a) for a in args], enc(Float64(f(args...)))])
end

# random rings with integer coefficients, and their arithmetic
function rmono()
    k = rand(0:3)
    zp(r, p) = p < 0 ? inv(r)^(-p) : r^p
    m = prod((zp(gens[i], rand(-2:3)) for i in randperm(3)[1:k]); init = one(x))
    c = rand((1, 1, 1, 2, -1, 3, -2))
    c == 1 ? m : c * m
end
function rring()
    r = rmono()
    for _ in 1:rand(0:3)
        r = rand(Bool) ? r + rmono() : r - rmono()
    end
    r
end
rgroup() = FA.valueat(rand(1:3), 3, :xyz)^rand(-2:2) * FA.valueat(rand(1:3), 3, :xyz)^rand(0:2)
rows = Any[]
for i in 1:400
    a = rring(); b = rring(); g = rgroup(); n = rand(0:3); k = rand((2, 3, -1, 5))
    push!(rows, Dict("a" => encr(a), "b" => encr(b), "g" => encg(g), "n" => n, "k" => k,
        "add" => tryr(() -> a + b), "sub" => tryr(() -> a - b), "mul" => tryr(() -> a * b),
        "addg" => tryr(() -> a + g), "gadd" => tryr(() -> g + a), "subg" => tryr(() -> a - g), "gsub" => tryr(() -> g - a),
        "mulg" => tryr(() -> a * g), "gmul" => tryr(() -> g * a), "divg" => tryr(() -> a / g),
        "pow" => tryr(() -> a^n), "neg" => tryr(() -> -a), "kmul" => tryr(() -> k * a), "divk" => tryr(() -> a / k),
        "addk" => tryr(() -> a + k), "ksub" => tryr(() -> k - a), "eq" => a == b, "eqself" => a == a))
end

# a basis with values: product, factorize, display
FA.@group2 Val begin
    a = 1.5
    b = 2
    c ≡ 2.5
    d = 3
end
vgens = (a, b, c, d)
vals = Any[]
for i in 1:120
    kk = rand(1:4)
    g = prod(vgens[j]^rand(-3:3) for j in randperm(4)[1:kk])
    cf = rand((1, 2, 5, 0.5, 7))
    g = cf == 1 ? g : FA.times(cf, g)
    push!(vals, Dict("g" => encg(g), "product" => enc(Float64(FA.product(g)))))
end
facts = Any[]
for n in (1, 2, 3, 4, 6, 12, 18, 72, 7, 35, 0, -12, 1024, 486)
    push!(facts, [enc(n), encg(FA.factorize(n, Val(:Val)))])
end
for f in (2.5, 6.25, 5.0, 3.75, 0.1, 12.0, 15.625, -2.5)
    push!(facts, [enc(f), encg(FA.factorize(f, Val(:Val)))])
end

writejson(joinpath(OUT, "ring.json"), Dict("julia" => string(VERSION), "readme" => readme, "evals" => evals,
    "rings" => rows, "values" => vals, "factorize" => facts))
println("wrote ring.json")

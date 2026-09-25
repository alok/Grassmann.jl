# Golden generator for FieldAlgebra (printing primitives, Group algebra and
# display on value-free bases, LogGroup/ExpGroup display).
#   julia --startup-file=no --project=oracle oracle/similitude/fieldalgebra.jl
# Writes oracle/golden/similitude/fieldalgebra.json.
using FieldAlgebra, Random
const FA = FieldAlgebra
include(joinpath(@__DIR__, "..", "unitsystems", "jsonw.jl"))
const OUT = joinpath(@__DIR__, "..", "golden", "similitude")
mkpath(OUT)
Random.seed!(20260924)

showstr(x) = try sprint(show, x) catch e; "ERROR" end
# exponent / coefficient encodings: ["I", "3"], ["R", "1/2"], ["F", "0x…"]
h(x::Float64) = "0x" * string(reinterpret(UInt64, x), base = 16, pad = 16)
enc(x::Integer) = ["I", string(x)]
enc(x::Rational) = ["R", string(numerator(x), "/", denominator(x))]
enc(x::AbstractFloat) = ["F", h(Float64(x))]
encg(g) = Dict("v" => [enc(a) for a in g.v], "c" => enc(g.c), "show" => showstr(g))
tryg(f) = try encg(f()) catch; "ERROR" end

# ---------- printing primitives ----------
prims = Any[]
for n in (-12, -1, 0, 1, 2, 3, 10, 123, 45678)
    push!(prims, ["printexpo", enc(n), sprint(FA.printexpo, n)])
end
for r in (1//2, -1//2, 3//4, -3//4, 7//2, 2//1, 1//1, -5//3, 12//7)
    push!(prims, ["printexpo", enc(r), sprint(FA.printexpo, r)])
end
for f in (2.5, -0.125, 1.0, 0.3, 1.5, -2.0, 0.6931471805599453, 1.0e-7, 12345.678, 2.0e20)
    push!(prims, ["printexpo", enc(f), sprint(FA.printexpo, f)])
end
for d in ("x", "10", "kB"), f in (0.25, 0.3, 0.5, -0.5, 1.5, 2.0, -3.0, 3.5, -3.5, 0.123456, 2.30103, 1.0e-7, 7.000000000000001, -2.5, 0.6931471805599453, 4.5, 1.25)
    push!(prims, ["printexpo_based", d, enc(f), sprint(FA.printexpo, d, f)])
end
for (d, n) in (("x", 0), ("x", 1), ("x", 2), ("x", -1), ("kB", -2), ("x", 1//2), ("x", -3//2), ("10", 3), ("10", -2))
    push!(prims, ["printexpo_based", d, enc(n), sprint(FA.printexpo, d, n)])
end
for f in (0.0, 2.0, 2.0000000000000004, 1.9999999999999998, 0.5, 1e15, 1e16, -3.0, 123456.00000000001, 4.5e15,
          0.1, 1e-20, 7.000000000000001, 6.999999999999999, -2.0000000000000004, -1.9999999999999998, 1e300, 3.0e-5)
    m = FA.makeint(f)
    push!(prims, ["makeint", enc(f), enc(m)])
end
for n in (1, 7, 10, 1000, 1200, 1234000, 5000000, 100, 1020, 999, 10203)
    push!(prims, ["findpower", n, FA.findpower(n)])
end
for f in (1.5e-20, 1.5e20, 15.0, 1.0e7, 1.380649e-23, 6.02214076e23, 0.001, 1.0e-5, 299792458.0, 2.99792458e8, -4.2e-9, 1.0e100)
    push!(prims, ["print_special", enc(f), sprint(FA.print_special, f)])
    push!(prims, ["special_print", enc(f), sprint(FA.special_print, f)])
end
for (d, n) in (("x", 3), ("x", 1), ("x", -1//2), ("x", 2.5), ("x", 0), ("kB", -2), ("x", 1//3), ("10", 2.5))
    push!(prims, ["latexpo_based", d, enc(n), sprint(FA.latexpo, d, n)])
end

# ---------- groups on value-free bases ----------
FA.@group2 XYZ x y z w
FA.@group2 Named ab cd ef gh ij
const chargens = (x, y, z, w)
const strgens = (ab, cd, ef, gh, ij)
coefs = Any[1, 2, -1, 12, 0.5, 2.5, 0.25, -0.25, 1//3, 2//3, 0.3, 1.0e-20, 0]
function rgroup(gens)
    k = rand(1:length(gens))
    g = prod(gens[i]^rand(-3:3) for i in randperm(length(gens))[1:k])
    c = rand(coefs)
    c == 1 ? g : FA.times(c, g)
end
groups = Any[]
for (nm, gens) in (("XYZ", chargens), ("Named", strgens))
    for i in 1:250
        a = rgroup(gens); b = rgroup(gens)
        e = rand(0:3); r = rand((1//2, 1//3, -1//2, 3//2, 2//3)); f = rand((0.5, 0.3, 1.5, -0.25))
        row = Dict("basis" => nm, "a" => encg(a), "b" => encg(b), "e" => e, "r" => enc(r), "f" => enc(f),
                   "mul" => tryg(() -> a * b), "div" => tryg(() -> a / b), "inv" => tryg(() -> inv(a)),
                   "pow" => tryg(() -> a^e), "powr" => tryg(() -> a^r), "sqrt" => tryg(() -> sqrt(a)),
                   "powf" => tryg(() -> a^f))
        push!(groups, row)
    end
end

# ---------- LogGroup / ExpGroup ----------
lg = Any[]
for (nm, gens) in (("XYZ", chargens), ("Named", strgens))
    for i in 1:40
        a = rgroup(gens); b = rgroup(gens)
        push!(lg, Dict("basis" => nm, "a" => encg(a), "b" => encg(b),
            "log" => showstr(log(a)), "log2" => showstr(log2(a)), "log10" => showstr(log10(a)),
            "log3" => showstr(log(3, a)), "logdb" => showstr(FA.logdb(a)),
            "exp" => showstr(exp(a)), "exp2" => showstr(exp2(a)), "exp10" => showstr(exp10(a)), "pow3" => showstr(3^a),
            "logmul2" => showstr(log(a) * 2), "logdiv2" => showstr(log(a) / 2), "logadd" => showstr(log(a) + log(b)),
            "logsub" => showstr(log(a) - log(b))))
    end
end

writejson(joinpath(OUT, "fieldalgebra.json"), Dict("julia" => string(VERSION), "prims" => prims, "groups" => groups, "loggroups" => lg))
println("wrote fieldalgebra.json")

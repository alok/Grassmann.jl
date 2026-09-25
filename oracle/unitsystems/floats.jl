# Golden generator for FieldConstants' Julia float semantics (printing, parsing,
# Base.Math exp/log/pow ports, round(digits/sigdigits), FieldConstants.Constant ops).
#   julia --startup-file=no --project=oracle oracle/unitsystems/floats.jl
# Writes oracle/golden/unitsystems/floats.json. Floats are hex bit patterns ("0x…").
using Random, FieldConstants
const OUT = joinpath(@__DIR__, "..", "golden", "unitsystems")
mkpath(OUT)
include(joinpath(@__DIR__, "jsonw.jl"))
Random.seed!(20260924)

h(x::Float64) = "0x" * string(reinterpret(UInt64, x), base = 16, pad = 16)
randbits() = reinterpret(Float64, rand(UInt64))
function finite_rand()
    while true
        x = randbits()
        isfinite(x) && return x
    end
end
logu(lo, hi) = (s = rand() < 0.5 ? -1.0 : 1.0; s * exp10(lo + (hi - lo) * rand()))

specials = Float64[0.0, -0.0, Inf, -Inf, NaN, 1.0, -1.0, 0.1, 0.2, 0.3, 1/3, 2/3, 1e-5, 1e-4, 9.999e-5,
    0.0001, 1e5, 1e6, 999999.0, 999999.9, 123456.0, 100000.0, 1e15, 1e16, 1e17, 1e21, 1e22, 1e23,
    5e-324, 1e-323, 2.2250738585072014e-308, 2.2250738585072009e-308, 1.7976931348623157e308,
    2.0^52, 2.0^53, 2.0^53 + 2, 2.0^63, 2.0^64, 9007199254740993.0, 0.5, 0.25, 0.125, 1.5, 2.5,
    299792458.0, 6.62607015e-34, 1.380649e-23, 6.02214076e23, 9.80665, 0.3048, 1.2566370614359173e-6,
    9.109383701558256e-31, 1.0e-10, 3.0e8, 4.35e-18, 100.0, 1000.0, 1e7, 12345.678, 0.001, 0.01]
for k in -30:30
    push!(specials, 10.0^k, 2.0^k, 3.0^k)
end

show_rows = Any[]
for x in specials
    push!(show_rows, [h(x), repr(x)])
end
for i in 1:1500
    push!(show_rows, (x = finite_rand(); [h(x), repr(x)]))
end
for i in 1:1500
    push!(show_rows, (x = logu(-40, 40); [h(x), repr(x)]))
end
for i in 1:300
    push!(show_rows, (x = Float64(rand(-10^6:10^6)) / 10.0^rand(0:6); [h(x), repr(x)]))
end

# parsing: decimal strings (not only shortest ones)
parse_rows = Any[]
for s in ("0", "1", "-1", "1.5", ".5", "5.", "1e10", "1E-5", "-2.5e+3", "123456789012345678901234567890",
          "0.1", "0.30000000000000004", "2.2250738585072011e-308", "4.9e-324", "2e-324", "1e-400", "1e400",
          "1.7976931348623158e308", "1.7976931348623159e308", "137.035999084", "0.00000002176434",
          "25812.8074555", "483597.8525", "149597870700", "Inf", "-Inf", "NaN", "infinity")
    r = tryparse(Float64, s)
    push!(parse_rows, [s, r === nothing ? "ERR" : h(r)])
end
for i in 1:500
    d = join(rand('0':'9', rand(1:25)))
    s = string(rand() < 0.3 ? "-" : "", d[1:min(end, rand(1:length(d)))], ".", d, "e", rand(-330:310))
    r = tryparse(Float64, s)
    push!(parse_rows, [s, r === nothing ? "ERR" : h(r)])
end

powi = Any[]
for i in 1:1500
    x = rand() < 0.2 ? Float64(rand(2:43)) : logu(-3, 3)
    n = rand() < 0.8 ? rand(-40:40) : rand(-5000:30000)
    push!(powi, [h(x), n, h(x^n)])
end
for x in (2.0, 10.0, 0.1, 6.283185307179586, 1.0000000000000002, 0.9999999999999999, -2.0, -0.5, 0.0, -0.0, Inf, -Inf, NaN)
    for n in (-3, -2, -1, 0, 1, 2, 3, 4, 5, 7, 12, 70)
        push!(powi, [h(x), n, h(x^n)])
    end
end
powf = Any[]
for i in 1:1500
    x = rand() < 0.2 ? Float64(rand(2:43)) : abs(logu(-30, 30))
    y = rand((0.5, -0.5, 1.5, -1.5, 2.5, 1/3, -1/3, 0.25, 3.5, -2.5, rand() * 8 - 4, 0.1))
    push!(powf, [h(x), h(y), h(x^y)])
end
for (x, y) in ((0.0, 0.5), (-0.0, -0.5), (Inf, 0.5), (Inf, -0.5), (-8.0, 1/3), (-2.0, 3.0), (-2.0, 2.0),
               (NaN, 1.0), (1.0, NaN), (2.0, Inf), (0.5, Inf), (2.0, 1e20), (5e-324, 0.5), (1e-310, 1.5))
    r = try x^y catch; NaN end
    push!(powf, [h(x), h(y), h(r)])
end
funs = Dict{String,Any}()
for (name, f, lo, hi) in (("exp", exp, -50, 50), ("exp2", exp2, -60, 60), ("exp10", exp10, -20, 20),
                           ("log", log, -40, 40), ("log2", log2, -40, 40), ("log10", log10, -40, 40))
    rows = Any[]
    for i in 1:1000
        x = name in ("log", "log2", "log10") ? abs(logu(lo, hi)) : lo + (hi - lo) * rand()
        push!(rows, [h(x), h(f(x))])
    end
    for x in (0.0, 1.0, -1.0, 0.1, 0.5, 2.0, 10.0, 100.0, 1e-310, 5e-324, 700.0, 709.7, -745.0, -740.0, 1000.0, Inf, -Inf, NaN, 0.95, 1.05, 3.0, 22.0, -22.0)
        r = try f(x) catch; NaN end
        push!(rows, [h(x), h(r)])
    end
    funs[name] = rows
end

rnd = Any[]
for i in 1:600
    x = logu(-20, 20)
    d = rand(-5:15)
    n = rand(1:4)
    push!(rnd, [h(x), d, h(round(x, digits = d)), n, h(round(x, sigdigits = n)), Base.hidigit(x, 10)])
end

pbs = Any[]
for (nm, c) in (("φ", Base.MathConstants.φ), ("γ", Base.MathConstants.γ), ("ℯ", ℯ))
    for p in 1:12
        push!(pbs, [nm, p, h(Float64(c^p))])
    end
end

# FieldConstants.Constant operator table on Int/Float payloads
const C = FieldConstants.Constant
kindv(x) = (y = x isa C ? FieldConstants.constant(x) : x; y isa Int ? ["Int64", string(y)] : ["Float64", h(Float64(y))])
cops = Any[]
payloads = Any[1, 2, 3, 10, -4, 0, 1000, 2.0, 0.5, 6.283185307179586, 1.380649e-23, 299792458.0, 0.001]
for a in payloads, b in payloads
    ca, cb = C(a), C(b)
    push!(cops, ["*", kindv(ca), kindv(cb), kindv(ca * cb)])
    push!(cops, ["/", kindv(ca), kindv(cb), kindv(ca / cb)])
    push!(cops, ["+", kindv(ca), kindv(cb), kindv(ca + cb)])
    push!(cops, ["-", kindv(ca), kindv(cb), kindv(ca - cb)])
end
for a in payloads
    ca = C(a)
    push!(cops, ["inv", kindv(ca), kindv(inv(ca))])
    push!(cops, ["^2", kindv(ca), kindv(ca^2)])
    push!(cops, ["^3", kindv(ca), kindv(ca^3)])
    push!(cops, ["^7", kindv(ca), kindv(ca^7)])
    push!(cops, ["^-1", kindv(ca), kindv(ca^-1)])
    push!(cops, ["^-2", kindv(ca), kindv(ca^-2)])
    push!(cops, ["^-3", kindv(ca), kindv(ca^-3)])
    a isa Real && a >= 0 && push!(cops, ["sqrt", kindv(ca), kindv(sqrt(ca))])
    a isa Real && a > 0 && push!(cops, ["log10", kindv(ca), kindv(log10(ca))])
    push!(cops, ["show", kindv(ca), repr(ca)])
end
for a in payloads
    ca = C(a)
    push!(cops, ["exp2", kindv(ca), kindv(exp2(ca))])
    a > 0 && push!(cops, ["log3", kindv(ca), kindv(log(3, ca))])
    r = try kindv(2^ca) catch; "ERROR" end
    push!(cops, ["2^", kindv(ca), r])
    push!(cops, ["1.5^", kindv(ca), kindv(1.5^ca)])
    a >= 0 && push!(cops, ["^1//2", kindv(ca), kindv(ca^(1//2))])
    a >= 0 && push!(cops, ["^-2//3", kindv(ca), kindv(ca^(-2//3))])
    push!(cops, ["Int", kindv(ca), (try kindv(Int(ca)) catch; "ERROR" end)])
    b = C(a isa Int ? a + 1 : a * (1 + 1e-9))
    push!(cops, ["isapprox", kindv(ca), kindv(b), isapprox(ca, b)])
    push!(cops, ["isapprox", kindv(ca), kindv(ca), isapprox(ca, ca)])
end
push!(cops, ["^70", kindv(C(2)), kindv(C(2)^70)])
push!(cops, ["^-28", kindv(C(10)), kindv(C(10)^-28)])
push!(cops, ["logdb", kindv(100), kindv(FieldConstants.logdb(100))])
push!(cops, ["expdb", kindv(20), kindv(FieldConstants.expdb(20))])
push!(cops, ["expdb", kindv(3.5), kindv(FieldConstants.expdb(3.5))])

writejson(joinpath(OUT, "floats.json"), Dict("julia" => string(VERSION), "show" => show_rows, "parse" => parse_rows,
    "powi" => powi, "powf" => powf, "funs" => funs, "round" => rnd, "pbs" => pbs, "constant_ops" => cops,
    "unit_rtol" => h(eps()^0.9), "exp10_0.1" => h(exp10(0.1))))
println("wrote floats.json")

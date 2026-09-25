# Golden generator for MeasureSystems: the measured constants group, Measurements
# parsing/arithmetic/printing, per-system constants and conversion ratios with
# uncertainties.
#   julia --startup-file=no --project=oracle oracle/measuresystems/gen.jl
# Writes oracle/golden/measuresystems/*.json.
using MeasureSystems, Random
const MS = MeasureSystems
const FA = MS.FieldAlgebra
const US = MS.UnitSystems
const M = MS.Measurements
include(joinpath(@__DIR__, "..", "unitsystems", "jsonw.jl"))
const OUT = joinpath(@__DIR__, "..", "golden", "measuresystems")
mkpath(OUT)
Random.seed!(20260924)

showstr(x) = try sprint(show, x) catch; "ERROR" end
h(x::Real) = "0x" * string(reinterpret(UInt64, Float64(x)), base = 16, pad = 16)
ex(x::Integer) = string(x)
ex(x::Rational) = isone(denominator(x)) ? string(numerator(x)) : string(numerator(x), "/", denominator(x))
ex(x::AbstractFloat) = h(x)
ev(v) = join([ex(a) for a in v], " ")
num(x::Integer) = ["I", string(x)]
num(x::Rational) = ["R", string(numerator(x), "/", denominator(x))]
num(x::AbstractFloat) = ["F", h(x)]
function ve(x)
    y = try FA.product(x) catch; return ["ERROR", "ERROR"] end
    y isa M.Measurement ? [h(y.val), h(y.err)] : [h(Float64(y)), h(0.0)]
end
mv(q) = q isa MS.Quantity ? ve(q.v) : ["ERROR", "ERROR"]
save(name, data) = (writejson(joinpath(OUT, name * ".json"), data); println("wrote ", name, " (", length(data), ")"))

const systems = [s for s in US.Systems]
const convs = [u for u in US.Convert]

# ---------- 1. the measured constants group ----------
mg = Dict{String,Any}()
mg["basis"] = [[i, showstr(MS.phys(i)), ve(MS.phys(i))...] for i in 1:44]
rnd = Any[]
for i in 1:300
    g = MS.𝟏
    for j in randperm(44)[1:rand(1:5)]
        e = rand((-3, -2, -1, 1, 2, 3, 1//2, -1//2, 3//2))
        (j in (34, 35) && e isa Integer && e < 0) && (e = -e)
        g = g * MS.phys(j)^e
    end
    push!(rnd, [ev(g.v), num(g.c), showstr(g), ve(g)...])
end
mg["random"] = rnd
named = Any[]
for (nm, x) in (("mₑ", MS.mₑ), ("μ₀", MS.μ₀), ("ħ", MS.ħ), ("αinv", MS.αinv), ("αG", MS.αG), ("Mᵤ", MS.Mᵤ),
                ("μₚₑ", MS.μₚₑ), ("Rᵤ", MS.Rᵤ), ("G", MS.G), ("GM☉", MS.GM☉), ("pc", MS.pc), ("em", MS.em),
                ("nm", MS.nm), ("th", MS.th), ("ΛC", MS.ΛC), ("𝘦ₙ", MS.𝘦ₙ), ("lc", MS.lc), ("mc", MS.mc),
                ("ρΛ", MS.ρΛ), ("lcq", MS.lcq), ("mcq", MS.mcq), ("tcq", MS.tcq), ("LD", MS.LD), ("JD", MS.JD))
    push!(named, [nm, ev(x.v), num(x.c), showstr(x), ve(x)...])
end
mg["named"] = named
save("measures", mg)

# ---------- 2. Measurements: parsing, printing, arithmetic ----------
ps = Any[]
for s in ("1.23456(78)e-10", "137.035999084(21)", "0.6889(56)", "67.66(42)", "5.0(1)", "5.0(1.5)", "500(20)",
          "-1.23(4)", "10973731.5681601(210)", "149597870700(3)", "0.00000002176434(24)", "1.007276466621(53)",
          "1822.888486209(53)", "8.3144598(48)", "25812.8074555(59)", "483597.8525(30)", "3.986004418(8)",
          "1.26686534(9)", "81.300568(3)", "1.0(0)", "12.5(3)", "0.0012(5)", "1.5(3)e20", "99.99(12)",
          "2.5(13)", "0.5(5)", "7(2)", "123456.789(12)", "1.5(1)e-3", "6.02(3)e23")
    m = M.measurement(s)
    push!(ps, [s, h(m.val), h(m.err), showstr(m), sprint(FA.print_special, m), sprint(FA.special_print, m)])
end
# arithmetic with correlations: every independent input is parsed once, in order
ar = Any[]
a = M.measurement("1.5(1)"); b = M.measurement("2.25(20)"); c = M.measurement("0.75(5)")
enc(m) = [h(m.val), h(m.err)]
for (nm, f) in (("a+b", () -> a + b), ("a-b", () -> a - b), ("a*b", () -> a * b), ("a/b", () -> a / b),
                ("a-a", () -> a - a), ("a/a", () -> a / a), ("a*a", () -> a * a), ("a^2", () -> a^2),
                ("a^-3", () -> a^-3), ("a^(1//2)", () -> a^(1//2)), ("a^0.75", () -> a^0.75),
                ("sqrt(a)", () -> sqrt(a)), ("cbrt(b)", () -> cbrt(b)), ("inv(c)", () -> inv(c)),
                ("2.5*a", () -> 2.5 * a), ("a*3", () -> a * 3), ("a/4.0", () -> a / 4.0), ("1.0/a", () -> 1.0 / a),
                ("a+1.0", () -> a + 1.0), ("1.0-a", () -> 1.0 - a), ("-a", () -> -a),
                ("(a*b+c)/(a-c)", () -> (a * b + c) / (a - c)), ("a*b*c-b*c*a", () -> a * b * c - b * c * a),
                ("(a+b)*(a-b)", () -> (a + b) * (a - b)), ("sqrt(a*a+b*b)", () -> sqrt(a * a + b * b)))
    push!(ar, [nm, enc(f())..., showstr(f())])
end
save("measurements", Dict("parse" => ps, "arith" => ar))

# ---------- 3. per-system constants with uncertainty ----------
sel = (:Metric, :SI2019, :SI1976, :CODATA, :Conventional, :International, :English, :British, :Gauss, :EMU, :ESU,
       :Planck, :PlanckGauss, :Stoney, :Hartree, :Rydberg, :Natural, :QCD, :IAU☉, :Hubble, :Cosmological,
       :IAUE, :IAUJ, :Survey, :MTS, :KKH, :Nautical, :Meridian)
sc = Any[]
for s in sel
    U = getfield(MS, s)
    for c in vcat(collect(US.Constants), collect(US.Physics))
        c == :gaussgravitation && continue
        q = try getfield(MS, c)(U) catch; nothing end
        push!(sc, [string(s), string(c), showstr(q), mv(q)...])
    end
end
save("system_constants", sc)

# ---------- 4. conversion ratios with uncertainty ----------
cv = Any[]
for (a, b) in ((:Metric, :English), (:Metric, :Gauss), (:Metric, :Planck), (:Metric, :Hartree), (:Metric, :IAU☉),
               (:SI2019, :CODATA), (:Metric, :Natural), (:Conventional, :Metric), (:Stoney, :Rydberg),
               (:PlanckGauss, :Hubble))
    Ua, Ub = getfield(MS, a), getfield(MS, b)
    for u in convs
        d = MS.Similitude.evaldim(u)
        r = try MS.ratio(d, Ua, Ub) catch; nothing end
        push!(cv, [string(a), string(b), string(u), showstr(try d(Ua, Ub) catch e; e end),
            (r === nothing ? ["ERROR", "ERROR"] : ve(r))...])
    end
end
save("ratios", cv)
println("done")

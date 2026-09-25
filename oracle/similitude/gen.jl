# Golden generator for Similitude: the exact constants group, the unit-system
# homomorphisms and their displays, Similitude's `UnitSystem(d)` isomorphism,
# conversion ratios, per-system constants, derived units, quotients and
# quantity arithmetic.
#   julia --startup-file=no --project=oracle oracle/similitude/gen.jl
# Writes oracle/golden/similitude/*.json.
using Similitude, Random
const S = Similitude
const FA = S.FieldAlgebra
const US = S.UnitSystems
include(joinpath(@__DIR__, "..", "unitsystems", "jsonw.jl"))
const OUT = joinpath(@__DIR__, "..", "golden", "similitude")
mkpath(OUT)
Random.seed!(20260924)

showstr(x) = try sprint(show, x) catch; "ERROR" end
h(x::Real) = "0x" * string(reinterpret(UInt64, Float64(x)), base = 16, pad = 16)
# exponents: "3", "-1/2" (exact) or "0x…" (Float64 bits)
ex(x::Integer) = string(x)
ex(x::Rational) = isone(denominator(x)) ? string(numerator(x)) : string(numerator(x), "/", denominator(x))
ex(x::AbstractFloat) = h(x)
ev(v) = join([ex(a) for a in v], " ")
# Julia numbers: ["I","3"], ["R","1/3"], ["F","0x…"]
num(x::Integer) = ["I", string(x)]
num(x::Rational) = ["R", string(numerator(x), "/", denominator(x))]
num(x::AbstractFloat) = ["F", h(x)]
prodh(g) = try h(Float64(FA.product(g))) catch; "ERROR" end
fval(q) = try (v = q.v; h(v isa FA.Group ? FA.product(v) : Float64(v))) catch; "ERROR" end
save(name, data) = (writejson(joinpath(OUT, name * ".json"), data); println("wrote ", name, " (", length(data), ")"))

const systems = [s for s in US.Systems]
const convs = [u for u in US.Convert]
sysname(s) = string(s)

# ---------- 1. the constants group ----------
cg = Dict{String,Any}()
cg["basis"] = [[i, showstr(S.phys(i)), prodh(S.phys(i))] for i in 1:44]
rnd = Any[]
for i in 1:400
    g = S.𝟏
    for j in randperm(44)[1:rand(1:5)]
        e = rand((-3, -2, -1, 1, 2, 3, 1//2, -1//2, 3//2))
        g = g * S.phys(j)^e
    end
    c = rand((1, 1, 1, 2, 3, -1, 13, 1//3, 2.5, 0.125))
    g = FA.Group(g.v, c, Val(:Constants))
    push!(rnd, [ev(g.v), num(g.c), showstr(g), prodh(g)])
end
cg["random"] = rnd
cg["factorize_int"] = [[n, showstr(FA.factorize(n, Val(:Constants))), prodh(FA.factorize(n, Val(:Constants)))]
    for n in vcat(-30:60, [97, 128, 360, 1024, 1339, 14237, 259493, 384399, 86400, 3600, 5280, 43560, 10^9, 2^40, 3^30, 2^62])]
cg["factorize_float"] = [[h(x), showstr(FA.factorize(x, Val(:Constants))), prodh(FA.factorize(x, Val(:Constants)))]
    for x in (0.5, 1.0, 2.0, 2π, 4π, Float64(π), 1e30, 0.1, 459.67, 1.293, 12.566370614359172, 3.0e8, -2.0, 8π^2, 0.0, 2.0^70, 81.300568)]
named = Any[]
for nm in (:mₑ, :μ₀, :ħ, :αinv, :αG, :Mᵤ, :μₚₑ, :μₑₚ, :Rᵤ, :G, :GM☉, :pc, :em, :nm, :fur, :°R, :K, :k, :th, :ΛC, :lc, :mc, :ρΛ, :𝘦ₙ, :ς, :lcq, :mcq, :tcq, :𝘦ᵣ, :LD, :JD, :milli, :kilo, :mega, :giga, :kibi, :zetta, :zepto, :yotta, :yocto, :DAY, :HOUR, :deka, :hecto, :centi, :nano, :zebi, :αL)
    x = getfield(S, nm)
    push!(named, [string(nm), showstr(x), prodh(x)])
end
cg["named"] = named
# addition and subtraction of exact constants (dimension.jl:112-129)
grp(g) = [ev(g.v), num(g.c)]
adds = Any[]
for (a, b) in ((S.𝟏, S.𝟏), (S.𝟐, S.𝟐), (S.𝟐, S.𝟑), (S.kB, S.kB), (3 * S.𝟐, S.𝟐), (S.𝟐 * S.𝟐, S.𝟐), (S.kB * S.NA, S.kB), (S.τ, S.τ / S.𝟐), (S.𝟏 / 3, S.𝟏 / 3), (FA.Group(S.𝘤.v, 2.5, Val(:Constants)), S.𝘤))
    push!(adds, [grp(a), grp(b), showstr(a + b), showstr(a - b)])
end
cg["addsub"] = adds
save("constants", cg)

# ---------- 2. homomorphisms and displays ----------
hom = Any[]
for s in systems
    U = getfield(S, s)
    rows = Any[]
    for u in convs
        d = S.evaldim(u)
        img = try U(d) catch; nothing end
        push!(rows, [string(u), img === nothing ? "ERROR" : ev(img.v), showstr(img), showstr(U(1, d))])
    end
    push!(hom, [sysname(s), S.unitname(S.normal(U)), rows])
end
save("homs", hom)

uni = Any[]
for u in convs
    d = S.evaldim(u)
    push!(uni, [string(u), ev(d.v), ev(S.UnitSystem(d).v), showstr(S.Unified(1, d))])
end
save("unified", uni)

# ---------- 3. conversion ratios ----------
rat = Any[]
pairs = vcat([(a, b) for a in systems, b in systems][:])
for k in 1:3000
    (a, b) = rand(pairs)
    u = rand(convs)
    Ua, Ub = getfield(S, a), getfield(S, b)
    d = S.evaldim(u)
    r = try S.ratio(d, Ua, Ub) catch; nothing end
    push!(rat, [sysname(a), sysname(b), string(u), showstr(r), r === nothing ? "ERROR" : prodh(r), showstr(try d(Ua, Ub) catch e; e end)])
end
for (a, b) in ((:English, :British), (:Gauss, :ESU), (:EMU, :Gauss), (:Planck, :Natural), (:IAU☉, :Metric), (:SI2019, :CODATA), (:Metric, :English), (:Metric, :Gauss))
    Ua, Ub = getfield(S, a), getfield(S, b)
    for u in convs
        d = S.evaldim(u)
        r = try S.ratio(d, Ua, Ub) catch; nothing end
        push!(rat, [sysname(a), sysname(b), string(u), showstr(r), r === nothing ? "ERROR" : prodh(r), showstr(try d(Ua, Ub) catch e; e end)])
    end
end
save("ratios", rat)

# ---------- 4. per-system physical constants ----------
consts = Any[]
for s in systems
    U = getfield(S, s)
    for c in vcat(collect(US.Constants), collect(US.Physics))
        q = try getfield(S, c)(U) catch; nothing end
        push!(consts, [sysname(s), string(c), showstr(q), q isa S.Quantity ? fval(q) : "ERROR",
            q isa S.Quantity && q.d isa FA.Group ? ev(q.d.v) : "ERROR"])
    end
end
save("system_constants", consts)

# ---------- 5. derived units ----------
der = Any[]
for u in US.Derived
    x = try getfield(S, u) catch; nothing end
    m = try x(S.Metric) catch; nothing end
    push!(der, [string(u), showstr(x), showstr(m), m isa S.Quantity ? fval(m) : "ERROR",
        x isa S.Quantity ? S.unitname(S.unitsystem2(x)) : "ERROR", x isa S.Quantity && x.d isa FA.Group ? ev(x.d.v) : "ERROR"])
end
save("derived", der)

# ---------- 6. quotients U/~ ----------
quo = Any[]
for s in systems
    U = getfield(S, s)
    q = try S.quotient(U) catch; nothing end
    q === nothing && continue
    push!(quo, [sysname(s), [[showstr(p.first), string.(p.second)] for p in q]])
end
save("quotients", quo)

# ---------- 7. quantity arithmetic ----------
qa = Any[]
for i in 1:300
    u1, u2 = rand(convs), rand(convs)
    d1, d2 = S.evaldim(u1), S.evaldim(u2)
    s = rand(systems); U = getfield(S, s)
    x = rand((1, 2, 3, 0.5, 2.5, 1//3)); y = rand((1, 2, 4, 0.25))
    a = U(x, d1); b = U(y, d2)
    push!(qa, [sysname(s), string(u1), string(u2), num(x), num(y), showstr(a), showstr(b),
        showstr(a * b), showstr(a / b), showstr(inv(a)), showstr(a^2), showstr(sqrt(a)),
        showstr(try a(S.Metric) catch e; e end), showstr(try a(S.English) catch e; e end)])
end
save("quantity_arith", qa)
println("done")

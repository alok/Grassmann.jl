# Golden generator for Geophysics.jl (planets, gases, fluid states, standard atmospheres).
#
#   julia --startup-file=no --project=oracle oracle/geophysics/gen.jl [path/to/Geophysics.jl]
#
# Geophysics is not in the oracle environment; its dependencies (UnitSystems, StaticVectors,
# LinearAlgebra) are, so the package source is `include`d from a checkout (default
# ~/chakravala/Geophysics.jl, commit 381a792 = v0.3.8) instead of being added to the project.
# Loaded that way its unexported types print as `Main.Geophysics.X`; display strings are
# rewritten to the `Geophysics.X` a package load prints.
#
# Writes oracle/golden/geophysics/*.json. Floats are IEEE bit patterns ("0x…"); a Julia
# exception is {"E": "<Type>: <message>"}; integers are JSON numbers.
using UnitSystems, StaticVectors, LinearAlgebra, Random
import FieldConstants
const SRC = length(ARGS) ≥ 1 ? ARGS[1] : joinpath(homedir(), "chakravala", "Geophysics.jl")
include(joinpath(SRC, "src", "Geophysics.jl"))
using .Geophysics
const G = Geophysics
include(joinpath(@__DIR__, "..", "unitsystems", "jsonw.jl"))
const OUT = joinpath(@__DIR__, "..", "golden", "geophysics")
mkpath(OUT)
Random.seed!(20260924)

hx(x::Real) = "0x" * string(reinterpret(UInt64, Float64(float(x))), base = 16, pad = 16)
errstr(e) = (s = sprint(showerror, e); string(nameof(typeof(e)), ": ", first(s, 120)))
enc(x::Bool) = x
enc(x::Integer) = x
enc(x::AbstractFloat) = hx(x)
enc(x::FieldConstants.Constant) = enc(FieldConstants.constant(x))   # an Int payload stays an Int
enc(x::Real) = hx(x)
enc(x::Union{Tuple,AbstractVector}) = [enc(y) for y in x]
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
fixshow(s) = replace(s, "Main.Geophysics." => "Geophysics.")
showstr(x) = try fixshow(sprint(show, x)) catch e; Dict("E" => errstr(e)) end
function capture(f)
    path, io = mktemp()
    redirect_stdout(io) do
        f()
    end
    close(io); s = read(path, String); rm(path); fixshow(s)
end
save(name, data) = (writejson(joinpath(OUT, name * ".json"), data);
    println("wrote ", name, " (", filesize(joinpath(OUT, name * ".json")), " bytes)"))

gitrev = try strip(read(`git -C $SRC rev-parse --short HEAD`, String)) catch; "unknown" end
meta = Dict("julia" => string(VERSION), "geophysics" => "0.3.8 @ " * gitrev,
    "unitsystems" => string(pkgversion(UnitSystems)), "staticvectors" => string(pkgversion(StaticVectors)))

systems = [("Metric", Metric), ("English", English), ("British", British), ("Gauss", UnitSystems.Gauss),
    ("IPS", UnitSystems.IPS)]

# ---------------------------------------------------------------- math samples
# Julia's own elementary functions (a regression sample; `mathsamples.jl` has the 10⁶ sweep).
let d = Dict{String,Any}("meta" => meta)
    xs = vcat(rand(600) .* 20 .- 10, rand(200) .* 2e6 .- 1e6, [0.0, -0.0, 1e-9, pi/2, pi/4, 1e22, 1e300])
    d["trig"] = [[hx(x), hx(sin(x)), hx(cos(x)), hx(tan(x))] for x in xs]
    at = vcat((ifelse.(rand(600) .< 0.5, -1, 1)) .* exp.(rand(600) .* 60 .- 30), [0.0, 0.4375, 1.1875, 2.4375, 1e20])
    d["atan"] = [[hx(x), hx(atan(x))] for x in at]
    ar = vcat(rand(600) .* 2 .- 1, [0.5, -0.975, 0.975, 1.0, -1.0, 1e-9])
    d["arc"] = [[hx(x), hx(asin(x)), hx(atanh(x)), hx(log1p(x))] for x in ar]
    ex = vcat(rand(600) .* 1400 .- 700, [-745.2, 709.9, 0.0, 1e-20])
    d["exp"] = [[hx(x), hx(exp(x))] for x in ex]
    pw = [(rand() * 4, rand() * 120 - 60) for _ in 1:400]
    append!(pw, [(rand() * 4, Float64(rand(-60:60))) for _ in 1:200])
    append!(pw, [(288.16, 1.5), (0.0, -1.5), (-0.0, 3.0), (Inf, -2.5), (-Inf, -3.0), (-2.0, 3.0), (2.0, 1e19), (5e-324, 0.5)])
    d["pow"] = [[hx(x), hx(y), hx(x^y)] for (x, y) in pw]
    save("math", d)
end

# ---------------------------------------------------------------- unit factors
let d = Dict{String,Any}("meta" => meta)
    for (nm, U) in systems
        d[nm] = Dict(
            "lengthM" => @safe(UnitSystems.length(Metric, U)), "timeM" => @safe(UnitSystems.time(Metric, U)),
            "gravitationDen" => @safe(UnitSystems.length(U, Metric) * UnitSystems.specificenergy(U, Metric)),
            "G" => @safe(gravitation(U)), "gc" => @safe(gravity(U)), "molar" => @safe(molarmass(U)),
            "avogadro" => @safe(avogadro(U)), "universal" => @safe(universal(U)),
            "viscosityM" => @safe(UnitSystems.viscosity(Metric, U)),
            "temperatureM" => @safe(UnitSystems.temperature(Metric, U)),
            "conductivityM" => @safe(UnitSystems.thermalconductivity(Metric, U)),
            "wavenumberM" => @safe(UnitSystems.wavenumber(Metric, U)),
            "lightspeed" => @safe(lightspeed(U)), "vibration" => @safe(planck(U) / boltzmann(U) / 1.2),
            "reference" => @safe(UnitSystems.temperature(288.16, U, Metric)))
    end
    save("units", d)
end

# ---------------------------------------------------------------- planets
planets = [("Sun", Sun), ("Mercury", Mercury), ("Venus", Venus), ("Earth", Earth), ("Moon", Moon),
    ("Mars", Mars), ("Jupiter", Jupiter), ("Saturn", Saturn), ("Uranus", Uranus), ("Neptune", Neptune),
    ("Pluto", Pluto), ("Ceres", Ceres), ("Eris", Eris)]
θfine = vcat(collect(-90:1:90) .* (π / 180), [π / 2, -π / 2, π / 4, 1.0111032235724 * π / 4, 0.0])
θcoarse = collect(-90:5:90) .* (π / 180)
hplanet = [-500.0, 0.0, 1000.0, 1.0e4, 1.0e5, 1.0e6]
let d = Dict{String,Any}("meta" => meta, "theta_fine" => enc(θfine), "theta_coarse" => enc(θcoarse),
        "h" => enc(hplanet))
    for (nm, P) in planets
        p = Dict{String,Any}()
        p["show"] = showstr(P)
        p["flattening"] = @safe(flattening(P)); p["eccentricity"] = @safe(eccentricity(P))
        p["eccentricity2"] = @safe(eccentricity2(P)); p["aspectratio"] = @safe(aspectratio(P))
        p["q0"] = @safe(G.q0(P)); p["q01"] = @safe(G.q01(P))
        p["dynamicformfactor"] = @safe(dynamicformfactor(P))
        p["secondzonalharmonic"] = @safe(secondzonalharmonic(P))
        for (un, U) in systems
            s = Dict{String,Any}()
            s["semimajor"] = @safe(semimajor(P, U)); s["period"] = @safe(period(P, U))
            s["gravitation"] = @safe(gravitation(P, U)); s["mass"] = @safe(mass(P, U))
            s["frequency"] = @safe(frequency(P, U)); s["angularfrequency"] = @safe(angularfrequency(P, U))
            s["meanradius"] = @safe(G.meanradius(P, U)); s["semiminor"] = @safe(semiminor(P, U))
            s["lineareccentricity"] = @safe(lineareccentricity(P, U))
            s["authalicradius"] = @safe(G.authalicradius(P, U))
            s["gravitySpherical"] = @safe(gravity(P, U)); s["oblateness"] = @safe(oblateness(P, U))
            a = semimajor(P, U)
            us = [0.5a, a, 2a, 10a]
            s["u"] = enc(us)
            s["q"] = [@safe(G.q(u, P, U)) for u in us]; s["q1"] = [@safe(G.q1(u, P, U)) for u in us]
            θs = un == "Metric" ? θfine : θcoarse
            s["thetas"] = enc(θs)
            s["radiusFast"] = [@safe(G.radius_fast(θ, P, U)) for θ in θs]
            s["radius"] = [@safe(G.radius(θ, P, U)) for θ in θs]
            s["radiusgeodetic"] = [@safe(radiusgeodetic(θ, P, U)) for θ in θs]
            s["speedRadial"] = [@safe(G._speed(θ, P, U)) for θ in θs]
            s["speed"] = [@safe(G.speed(θ, P, U)) for θ in θs]
            s["centripetalRadial"] = [@safe(G._centripetal(θ, P, U)) for θ in θs]
            s["centripetal"] = [@safe(centripetal(θ, P, U)) for θ in θs]
            s["oblatenessAt"] = [@safe(oblateness(θ, P, U)) for θ in θs]
            s["gravityNormal"] = [@safe(G._gravity(θ, P, U)) for θ in θs]
            s["gravity"] = [@safe(gravity(θ, P, U)) for θ in θs]
            hs = (un == "Metric" ? hplanet : hplanet[2:2:end]) .* UnitSystems.length(Metric, U)
            θh = un == "Metric" ? θcoarse : θcoarse[1:2:end]
            s["thetaH"] = enc(θh)
            s["hs"] = enc(hs)
            s["deflection"] = [[@safe(deflection(h, θ, P, U)) for θ in θh] for h in hs]
            s["latitudegeocentricAt"] = [[@safe(latitudegeocentric(h, θ, P, U)) for θ in θh] for h in hs]
            s["gravitygeodetic"] = [[@safe(gravitygeodetic(h, θ, P, U)) for θ in θh] for h in hs]
            s["gravitycomponents"] = [[@safe(gravitycomponents(h, θ, P, U)) for θ in θh] for h in hs]
            s["gravityNorm"] = [[@safe(G._gravity(h, θ, P, U)) for θ in θh] for h in hs]
            s["gravityAt"] = [[@safe(gravity(h, θ, P, U)) for θ in θh] for h in hs]
            p[un] = s
        end
        p["latitudegeodetic"] = [@safe(latitudegeodetic(θ, P)) for θ in θfine]
        p["deflectiongeodetic"] = [@safe(deflectiongeodetic(θ, P)) for θ in θfine]
        p["latitudegeocentric"] = [@safe(latitudegeocentric(θ, P)) for θ in θfine]
        p["deflectiongeocentric"] = [@safe(deflectiongeocentric(θ, P)) for θ in θfine]
        p["latitudeparametric"] = [@safe(latitudeparametric(θ, P)) for θ in θfine]
        d[nm] = p
    end
    save("planets", d)
end

# ---------------------------------------------------------------- gases
moles = [("N2", N2), ("O2", O2), ("Ar", Ar), ("CO2", CO2), ("H2", H2), ("He", He), ("Ne", Ne),
    ("Kr", Kr), ("Xe", Xe), ("CH4", CH4), ("air", G.air), ("Nitrox", Nitrox), ("AirMix", AirMix),
    ("Traces", Traces), ("MainGases", G.MainGases), ("TraceGases", G.TraceGases),
    ("Nested", 0.5Nitrox + 0.25N2 + 0.25(0.5Ar + 0.5CO2))]
Ts = sort(unique(vcat(exp.(range(log(20.0), log(5000.0), length = 70)),
    [100.0, 150.0, 200.0, 216.65, 250.0, 273.15, 288.15, 288.16, 300.0, 500.0, 1000.0, 2000.0])))
tfuns = [("viscosity", G.viscosity), ("thermalconductivity", G.thermalconductivity), ("heatvolume", G.heatvolume),
    ("heatpressure", G.heatpressure), ("heatratio", G.heatratio), ("specificenergy", G.specificenergy),
    ("specificenthalpy", G.specificenthalpy), ("freedom", G.freedom), ("prandtl", G.prandtl),
    ("sonicspeed", G.sonicspeed)]
# the SutherlandGas `air` overflows the stack in every heat function; evaluate once, record the rest
const OVERFLOW = Set(["heatvolume", "heatpressure", "heatratio", "specificenergy", "specificenthalpy",
    "freedom", "prandtl", "sonicspeed"])
airerr = try G.heatvolume(288.15, G.air, Metric); "none" catch e; errstr(e) end
let d = Dict{String,Any}("meta" => meta, "T" => enc(Ts))
    xs = vcat(exp.(range(log(1e-3), log(900.0), length = 60)), [700.0, 709.0, 710.0, 800.0])
    d["_einstein"] = Dict("x" => enc(xs), "y" => [@safe(G.vibration(x)) for x in xs])
    for (nm, M) in moles
        g = Dict{String,Any}()
        g["show"] = showstr(M)
        g["relativemass"] = @safe(G.relativemass(M))
        g["fractions"] = @safe(G.fractions(M))
        for (un, U) in systems
            s = Dict{String,Any}()
            tscale = UnitSystems.temperature(Metric, U)
            s["molarmass"] = @safe(G.molarmass(M, U)); s["molecularmass"] = @safe(G.molecularmass(M, U))
            s["gasconstant"] = @safe(G.gasconstant(M, U))
            s["viscosityParam"] = @safe(G.viscosity(M, U))
            s["conductivityParam"] = @safe(G.thermalconductivity(M, U))
            s["sutherlandviscosity"] = @safe(G.sutherlandviscosity(M, U))
            s["sutherlandconductivity"] = @safe(G.sutherlandconductivity(M, U))
            s["wavenumber"] = @safe(G.wavenumber(M, U)); s["wavelength"] = @safe(G.wavelength(M, U))
            s["frequency"] = @safe(G.frequency(M, U)); s["vibration"] = @safe(G.vibration(M, U))
            for (fn, f) in (("heatratioRef", G.heatratio), ("heatvolumeRef", G.heatvolume),
                    ("heatpressureRef", G.heatpressure))
                s[fn] = nm == "air" ? Dict("E" => airerr) : @safe(f(M, U))
            end
            TU = Ts .* tscale
            s["T"] = enc(TU)
            for (fn, f) in tfuns
                s[fn] = (nm == "air" && fn in OVERFLOW) ? [Dict("E" => airerr) for T in TU] :
                    [@safe(f(T, M, U)) for T in TU]
            end
            g[un] = s
        end
        d[nm] = g
    end
    save("gases", d)
end

# ---------------------------------------------------------------- fluid states
fstates = [(fnm, F, T, P) for (fnm, F) in (("Air", Air), ("N2", N2), ("Ar", Ar), ("CO2", CO2))
    for T in (150.0, 216.65, 288.15, 300.0, 1000.0, 2000.0) for P in (1.0, 5.0e4, 101325.0)]
ffuns = [("temperature", G.temperature), ("pressure", G.pressure), ("density", G.density),
    ("specificvolume", G.specificvolume), ("kinematic", G.kinematic), ("heatcapacity", G.heatcapacity),
    ("thermaldiffusivity", G.thermaldiffusivity), ("elasticity", G.elasticity),
    ("specificimpedance", G.specificimpedance), ("viscosity", G.viscosity),
    ("thermalconductivity", G.thermalconductivity), ("heatvolume", G.heatvolume),
    ("heatpressure", G.heatpressure), ("heatratio", G.heatratio), ("prandtl", G.prandtl),
    ("sonicspeed", G.sonicspeed), ("freedom", G.freedom), ("specificenergy", G.specificenergy),
    ("specificenthalpy", G.specificenthalpy), ("molecularmass", G.molecularmass),
    ("gasconstant", G.gasconstant), ("intensity", G.intensity)]
let d = Dict{String,Any}("meta" => meta)
    cases = []
    for (fnm, M, T, P) in fstates
        F = M(T, P)
        c = Dict{String,Any}("fluid" => fnm, "T" => enc(T), "P" => enc(P))
        for (un, U) in (("native", nothing), ("English", English), ("British", British))
            s = Dict{String,Any}()
            for (fn, f) in ffuns
                s[fn] = U === nothing ? @safe(f(F)) : @safe(f(F, U))
            end
            c[un] = s
        end
        E = English(F)
        c["toEnglish"] = [@safe(G.temperature(E)), @safe(G.pressure(E))]
        push!(cases, c)
    end
    d["cases"] = cases
    d["show"] = showstr(Air(288.15, 101325.0))
    save("fluidstate", d)
end

# ---------------------------------------------------------------- weathers
opnames = ["temperature", "pressure", "density", "specificweight", "specificvolume", "specificimpedance",
    "thermaldiffusivity", "intensity", "heatcapacity", "kinematic", "elasticity", "viscosity",
    "thermalconductivity", "heatvolume", "heatpressure", "heatratio", "prandtl", "sonicspeed",
    "freedom", "specificenergy", "specificenthalpy"]
opf(nm) = getfield(G, Symbol(nm))
ratiof(nm) = getfield(G, Symbol(nm, "ratio"))
hasratio(nm) = nm != "heatcapacity"

function metricgrid()
    base = vcat(collect(range(-2000.0, 120000.0, length = 245)), collect(range(120000.0, 1.0e6, length = 89))[2:end])
    vcat(base, [0.0, -0.0, 1.0, 1000.0, 5000.0, 44000.0, 45000.0])
end
function weathergrid(W)
    eng = G.units(W) === English
    hs = eng ? metricgrid() ./ 0.3048 : metricgrid()
    for hb in W.A.h[2:end]
        hg = G.altgeometric(hb, W)
        append!(hs, [hg, prevfloat(hg), nextfloat(hg), hg - 1, hg + 1])
    end
    r7 = 0.007 * G.radius(W)
    append!(hs, [r7, prevfloat(r7), nextfloat(r7)])
    sort!(unique(hs))
end
other(W) = G.units(W) === English ? Metric : English
uname(U) = U === Metric ? "Metric" : U === English ? "English" : U === British ? "British" : string(U)

function weatherdump(W; full = true)
    d = Dict{String,Any}("meta" => meta)
    U0 = G.units(W)
    U2 = other(W)
    d["units"] = uname(U0); d["other"] = uname(U2)
    d["latitude"] = @safe(G.latitude(W)); d["Tc"] = @safe(W.Tc); d["ha"] = @safe(W.ha)
    d["a"] = @safe(collect(W.A.a)); d["h"] = @safe(collect(W.A.h)); d["m"] = @safe(collect(W.A.m))
    d["T"] = @safe(collect(W.T)); d["p"] = @safe(collect(W.p)); d["rho"] = @safe(collect(W.ρ))
    d["radius"] = @safe(G.radius(W)); d["gravitySea"] = @safe(gravity(W))
    d["gasconstant"] = @safe(G.gasconstant(W)); d["molecularmass"] = @safe(G.molecularmass(W))
    d["radiusOther"] = @safe(G.radius(W, U2)); d["gravitySeaOther"] = @safe(gravity(W, U2))
    d["getindex"] = [@safe(W[i]) for i in 1:length(W.T)]
    d["getindexOther"] = [@safe(W[i, U2]) for i in 1:length(W.T)]
    d["display"] = capture(() -> display(W))
    d["type"] = fixshow(string(typeof(W)))
    # sea level: op(W) is Metric by default, op(W, U)
    d["seaMetric"] = Dict(nm => @safe(opf(nm)(W)) for nm in opnames)
    d["seaNative"] = Dict(nm => @safe(opf(nm)(W, U0)) for nm in opnames)
    d["seaOther"] = Dict(nm => @safe(opf(nm)(W, U2)) for nm in opnames)
    d["geopotentialSea"] = @safe(G.geopotential(W))
    # layer lookup at exact bases and neighbours (geopotential altitudes in W's units)
    lh = Float64[]
    for hb in W.A.h
        append!(lh, [hb, prevfloat(hb), nextfloat(hb), hb - 1, hb + 1])
    end
    append!(lh, [-1.0e5, 1.0e9, NaN])
    d["layerH"] = enc(lh)
    d["layer"] = [@safe(G.layer(h, W)) for h in lh]
    d["lapserate"] = [@safe(G.lapserate(h, W)) for h in lh]
    # dense geometric grid in W's units
    hs = full ? weathergrid(W) : collect(range(-1000.0, 200000.0, length = 121)) .* (U0 === English ? 1 / 0.3048 : 1.0)
    d["hs"] = enc(hs)
    hG = [G.altgeopotent(h, W) for h in hs]
    d["hG"] = enc(hG)
    d["altgeometric"] = [@safe(G.altgeometric(x, W)) for x in hG]
    d["altabs"] = [@safe(G.altabs(h, W)) for h in hs]
    d["layerOf"] = [@safe(G.layer(x, W)) for x in hG]
    d["gravity"] = [@safe(gravity(h, W)) for h in hs]
    d["geopotential"] = [@safe(G.geopotential(h, W)) for h in hs]
    d["state"] = [@safe((s = W(h); (s.T, s.P))) for h in hs]
    ops = Dict{String,Any}()
    for nm in opnames
        ops[nm] = [@safe(opf(nm)(h, W)) for h in hs]
        hasratio(nm) && (ops[nm * "ratio"] = [@safe(ratiof(nm)(h, W)) for h in hs])
    end
    d["ops"] = ops
    # layer-level primitives op(hG, i, W) around every base
    prim = []
    for i in 1:length(W.T)
        hb = W.A.h[i]
        for x in (hb - 500 * (U0 === English ? 3 : 1), hb, hb + 700 * (U0 === English ? 3 : 1))
            r = Dict{String,Any}("i" => i, "hG" => enc(x))
            for nm in opnames
                # the three-argument `pressure(hG, i, W)`/`density`/`kinematic` are ambiguous
                # with the `(hG, T, i)` methods in Julia; pass `U` explicitly
                r[nm] = @safe(opf(nm)(x, i, W, U0))
                hasratio(nm) && (r[nm * "ratio"] = @safe(ratiof(nm)(x, i, W, U0)))
            end
            r["state"] = @safe((s = W(x, i); (s.T, s.P)))
            push!(prim, r)
        end
    end
    d["primitive"] = prim
    d["primitiveAmbiguous"] = @safe(G.pressure(W.A.h[1], 1, W))
    # evaluation in the other system (h in that system) and in British
    for (key, U) in (("cross", U2), ("british", British))
        hx2 = key == "cross" ? hs[1:4:end] .* UnitSystems.length(U0, U) : hs[1:9:end] .* UnitSystems.length(U0, U)
        c = Dict{String,Any}("hs" => enc(hx2), "units" => uname(U))
        c["altgeopotent"] = [@safe(G.altgeopotent(h, W, U)) for h in hx2]
        c["altgeometric"] = [@safe(G.altgeometric(G.altgeopotent(h, W, U), W, U)) for h in hx2]
        c["altabs"] = [@safe(G.altabs(h, W, U)) for h in hx2]
        c["layerOf"] = [@safe(G.layer(G.altgeopotent(h, W, U), W, U)) for h in hx2]
        c["gravity"] = [@safe(gravity(h, W, U)) for h in hx2]
        c["geopotential"] = [@safe(G.geopotential(h, W, U)) for h in hx2]
        for nm in opnames
            c[nm] = [@safe(opf(nm)(h, W, U)) for h in hx2]
            hasratio(nm) && (c[nm * "ratio"] = [@safe(ratiof(nm)(h, W, U)) for h in hx2])
        end
        d[key] = c
    end
    # four-argument forms op(h, W, U, S): h given in S, result in U
    four = []
    for (U, S) in ((U0, U2), (U2, U0), (U2, U2), (British, U2))
        hs4 = hs[1:23:end] .* UnitSystems.length(U0, S)
        r = Dict{String,Any}("U" => uname(U), "S" => uname(S), "hs" => enc(hs4))
        r["altabs"] = [@safe(G.altabs(h, W, U, S)) for h in hs4]
        r["altgeopotent"] = [@safe(G.altgeopotent(h, W, U, S)) for h in hs4]
        r["altgeometric"] = [@safe(G.altgeometric(h, W, U, S)) for h in hs4]
        r["gravity"] = [@safe(gravity(h, W, U, S)) for h in hs4]
        r["geopotential"] = [@safe(G.geopotential(h, W, U, S)) for h in hs4]
        for nm in opnames
            r[nm] = [@safe(opf(nm)(h, W, U, S)) for h in hs4]
            hasratio(nm) && (r[nm * "ratio"] = [@safe(ratiof(nm)(h, W, U, S)) for h in hs4])
        end
        push!(four, r)
    end
    d["four"] = four
    d
end

weathers = [("Earth1922", Earth1922), ("Earth1925", Earth1925), ("Earth1956", Earth1956),
    ("Earth1959", Earth1959), ("Earth1962", Earth1962), ("Earth1966", Earth1966), ("Earth1976", Earth1976),
    ("Earth1922English", Earth1922English), ("Earth1925English", Earth1925English),
    ("Earth1956English", Earth1956English), ("Earth1959English", Earth1959English),
    ("Earth1962English", Earth1962English), ("Earth1966English", Earth1966English),
    ("Earth1976English", Earth1976English)]
for (nm, W) in weathers
    save("weather_" * nm, weatherdump(W))
end

# custom columns: another latitude and state, a pure-gas fluid, a nested mixture, converted
# tables, another planet
let d = Dict{String,Any}("meta" => meta)
    MarsA = Atmosphere{Mars}(Values(-2.5e-3, 0.0, 1.5e-3), Values(-0.0, 20.0e3, 40.0e3))
    customs = [
        ("US59_300_90000_0.3", US59(300.0, 90000.0, 0.3)),
        ("US62_N2", Weather{0.5}(US62, N2(288.15, 101325.0))),
        ("US76_Nested", Weather{π / 4}(US76, (0.5Nitrox + 0.5N2)(288.15, 101325.0))),
        ("Metric_US59E", Metric(US59E)(288.16)),
        ("English_US59", English(US59)(518.69, 2116.2)),
        ("Mars", MarsA(210.0, 610.0)),
        ("US56_CO2_English", Weather{0.2}(English(US56), CO2(500.0, 3000.0, English)))]
    for (nm, W) in customs
        d[nm] = weatherdump(W; full = false)
    end
    d["convertedTables"] = Dict(
        "Metric_US59E" => Dict("a" => @safe(collect(Metric(US59E).a)), "h" => @safe(collect(Metric(US59E).h))),
        "English_US76" => Dict("a" => @safe(collect(English(US76).a)), "h" => @safe(collect(English(US76).h))))
    save("weather_custom", d)
end

# ---------------------------------------------------------------- display
let d = Dict{String,Any}("meta" => meta)
    tables = [("US22", US22), ("US25", US25), ("US56", US56), ("US59", US59), ("US62", US62), ("US66", US66),
        ("US76", US76), ("US22E", US22E), ("US25E", US25E), ("US56E", US56E), ("US59E", US59E),
        ("US62E", US62E), ("US66E", US66E), ("US76E", US76E)]
    d["atmospheres"] = Dict(nm => capture(() -> display(A)) for (nm, A) in tables)
    d["moles"] = Dict(nm => showstr(M) for (nm, M) in moles)
    d["planets"] = Dict(nm => showstr(P) for (nm, P) in planets)
    d["states"] = Dict("Air" => showstr(Air(288.15, 101325.0)), "N2_English" => showstr(N2(500.0, 2116.2, English)),
        "Earth1959_1000" => showstr(Earth1959(1000.0)))
    d["standard"] = Dict("isEarth1959" => Standard === Earth1959)
    save("display", d)
end

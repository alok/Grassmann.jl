# Golden generator for UnitSystems: every named system's parameters and display,
# module-level constants, one-argument functions of every system, and a random
# sample of conversions between systems.
#   julia --startup-file=no --project=oracle oracle/unitsystems/systems.jl
# Writes oracle/golden/unitsystems/{systems,constants,scalars,conversions}.json.
using UnitSystems, Random
const US = UnitSystems
const FC = US.FieldConstants
include(joinpath(@__DIR__, "jsonw.jl"))
const OUT = joinpath(@__DIR__, "..", "golden", "unitsystems")
mkpath(OUT)
Random.seed!(20260924)

h(x::Float64) = "0x" * string(reinterpret(UInt64, x), base = 16, pad = 16)
val(x) = x isa FC.Constant ? FC.constant(x) : x
# ["I", "3"] for Int64, ["F", "0x…"] for Float64, ["E", message] for errors
enc(x) = (y = val(x); y isa Int ? ["I", string(y)] : y isa AbstractFloat ? ["F", h(Float64(y))] :
          y isa Bool ? ["B", string(y)] : ["?", repr(y)])
function tryenc(f)
    try
        enc(f())
    catch e
        ["E", first(split(sprint(showerror, e), '\n'))]
    end
end
function capture_display(x)
    old = stdout
    rd, wr = redirect_stdout()
    t = @async read(rd, String)
    try
        display(x)
    finally
        redirect_stdout(old)
        close(wr)
    end
    fetch(t)
end

sysnames = collect(US.Systems)
sys(S) = getfield(US, S)
slots = (:boltzmann, :planckreduced, :lightspeed, :vacuumpermeability, :electronmass, :molarmass,
         :luminousefficacy, :radian, :rationalization, :lorentz, :gravity)

# ---------- systems ----------
systems = Any[]
for S in sysnames
    U = sys(S)
    push!(systems, Dict("name" => string(S), "params" => [enc(getfield(US, f)(U)) for f in slots],
        "show" => sprint(show, U), "display" => capture_display(U), "isrationalized" => US.isrationalized(U)))
end
coupling = Dict("display" => capture_display(US.Universe),
    "slots" => [enc(f(US.Universe)) for f in (US.coupling, US.finestructure, US.electronunit, US.protonunit, US.darkenergydensity, US.protonelectron)])
aliases = Dict(string(a) => sprint(show, getfield(US, a)) for a in (:SI, :MKS, :ME, :GM, :IAU, :CGS, :CGSm, :CGSe, :HLU,
    :EnglishEngineering, :BritishGravitational, :BG, :EnglishUS, :AbsoluteEnglish, :AE, :EE, :MetricEngineering, :GravitationalMetric))
writejson(joinpath(OUT, "systems.json"), Dict("julia" => string(VERSION), "systems" => systems, "coupling" => coupling, "aliases" => aliases))

# ---------- module constants ----------
modnames = [:g₀, :atm, :T₀, :ft, :ftUS, :lb, :inHg, :Ωᵢₜ, :Vᵢₜ, :ΔνCs, :Kcd, :mP, :αinv, :R∞, :NA, :kB, :𝘩, :𝘤, :𝘦, :α,
    :μₑᵤ, :μₚᵤ, :μE☾, :RK1990, :KJ1990, :Rᵤ2014, :RK2014, :KJ2014, :GME, :GMJ, :kG, :H0, :ΩΛ, :aⱼ, :au, :LD, :JD,
    :zetta, :zepto, :yotta, :yocto, :τ, :deka, :byte, :sixty, :hecto, :kilo, :mega, :giga, :tera, :peta, :exa,
    :deci, :centi, :milli, :micro, :nano, :pico, :femto, :atto, :kibi, :mebi, :gibi, :tebi, :pebi, :exbi, :zebi, :yobi,
    :fur, :°R, :K, :HOUR, :k, :mₑ, :μ₀, :ħ, :μₚₑ, :μₑₚ, :Rᵤ, :αL, :αG, :Mᵤ, :pc, :G, :DAY, :nm, :GM☉, :th, :ΛC,
    :lc, :mc, :ρΛ, :𝘦ₙ, :ς, :lcq, :mcq, :𝘦ᵣ, :tcq, :em, :mi, :slug, :lbm, :lbmUS, :rankine, :kelvin, :ħ1990, :ħ2014,
    :mₑ1990, :mₑ2014, :δμ₀, :ly, :mₛ, :GG, :RK, :KJ, :eV, :κ, :σ, :μB, :ε₀, :kₑ, :mₚ, :Da, :𝔉, :Φ₀, :Z₀, :G₀, :Eₕ,
    :a₀, :rₑ, :RH, :Ry, :ℓP, :tP, :TP, :lS, :tS, :mS, :qS, :lA, :tA, :mA, :qA, :lQCD, :tQCD, :mQCD, :BTU, :BTUJ,
    :HP, :gal, :kcal, :cal,
    # ASCII and other aliases (`systems.jl:65-78`), calories (`UnitSystems.jl:343-344`)
    :BTUftlb, :Mu, :Ru, :SB, :hh, :cc, :m0, :e0, :ke, :me, :mp, :mu, :mᵤ, :ee, :FF, :Z0, :G0, :Eh, :a0, :re, :g0,
    :lP, :aL, :ϵ₀, :mpe, :mep, :meu, :mpu, :ainv, :aG,
    :kcalₜₕ, :kcal₄, :kcal₁₀, :kcal₂₀, :kcalₘ, :kcalᵢₜ, :calₜₕ, :cal₄, :cal₁₀, :cal₂₀, :calₘ, :calᵢₜ]
modconsts = Dict(string(n) => tryenc(() -> getfield(US, n)) for n in modnames)
# the irrationals UnitSystems re-exports, as Float64
for n in (:eulergamma, :golden, :φ)
    modconsts[string(n)] = enc(Float64(getfield(US, n)))
end
writejson(joinpath(OUT, "constants.json"), Dict("julia" => string(VERSION), "constants" => modconsts))

# ---------- one-argument functions of every system ----------
extra1 = (:sackurtetrode, :amagat, :thermalconductivity_water, :deka, :hecto, :kilo, :mega, :giga, :tera, :peta,
          :exa, :zetta, :yotta, :deci, :centi, :milli, :micro, :nano, :pico, :femto, :atto, :zepto, :yocto,
          :kibi, :mebi, :gibi, :tebi, :pebi, :exbi, :zebi, :yobi, :turn, :spat)
fnames = unique(vcat(collect(US.Dimensionless), collect(US.Constants), collect(US.Physics), collect(US.Derived), collect(extra1)))
scalars = Dict{String,Any}()
for f in fnames
    isdefined(US, f) || continue
    fn = getfield(US, f)
    scalars[string(f)] = [tryenc(() -> fn(sys(S))) for S in sysnames]
end
scalars["one"] = [enc(one(sys(S))) for S in sysnames]
scalars["zero"] = [enc(zero(sys(S))) for S in sysnames]
writejson(joinpath(OUT, "scalars.json"), Dict("julia" => string(VERSION), "systems" => sysnames, "functions" => scalars))

# ---------- conversions: q(U,S), q(U), q(v,U,S), q(v,U) ----------
convs = collect(US.Convert)
pairs = Any[]
# every quantity against Metric in both directions, plus a random sample of all pairs
for q in convs, S in sysnames
    push!(pairs, [string(q), "Metric", string(S)])
    push!(pairs, [string(q), string(S), "Metric"])
end
for i in 1:20000
    push!(pairs, [string(rand(convs)), string(rand(sysnames)), string(rand(sysnames))])
end
unique!(pairs)
factors = [vcat(p, [tryenc(() -> getfield(US, Symbol(p[1]))(sys(Symbol(p[2])), sys(Symbol(p[3]))))]) for p in pairs]
onearg = Dict(string(q) => [tryenc(() -> getfield(US, q)(sys(S))) for S in sysnames] for q in convs)
values = Any[]
for i in 1:3000
    q = rand(convs); a = rand(sysnames); b = rand((rand(sysnames), :Metric, a))
    v = rand((1.0, 2.5, -3.0, 1e10, 7, 0.1, 1.0e-20))
    push!(values, [string(q), string(a), string(b), enc(v), tryenc(() -> getfield(US, q)(v, sys(a), sys(b))),
                   tryenc(() -> getfield(US, q)(v, sys(a)))])
end
writejson(joinpath(OUT, "conversions.json"), Dict("julia" => string(VERSION), "convert" => convs, "factors" => factors,
    "onearg" => onearg, "values" => values))
println("wrote systems/constants/scalars/conversions: ", length(factors), " factors")

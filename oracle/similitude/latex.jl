# Golden generator for Similitude's LaTeX output: the unit-name LaTeX of every
# quantity's image in a selection of systems (`latexgroup(io, U(d), U)`, via the
# LaTeX registry or `dimlatex`) and FieldAlgebra's `showlatex` of named constants.
#   julia --startup-file=no --project=oracle oracle/similitude/latex.jl
# Writes oracle/golden/similitude/latex.json.
using Similitude
const S = Similitude
const FA = S.FieldAlgebra
const US = S.UnitSystems
include(joinpath(@__DIR__, "..", "unitsystems", "jsonw.jl"))
const OUT = joinpath(@__DIR__, "..", "golden", "similitude")
dims = Any[]
for s in (:Metric, :SI2019, :English, :British, :Gauss, :EMU, :ESU, :Planck, :PlanckGauss, :Hartree,
          :IAU☉, :MetricDegree, :Engineering, :FFF, :QCD, :Natural)
    U = S.normal(getfield(S, s))
    push!(dims, [string(s), [[string(u), sprint(S.latexgroup, U(S.evaldim(u)), U)] for u in US.Convert]])
end
consts = [[string(nm), FA.showlatex(getfield(S, nm))] for nm in
    (:mₑ, :μ₀, :ħ, :αinv, :αG, :Mᵤ, :μₚₑ, :Rᵤ, :G, :GM☉, :pc, :em, :nm, :th, :ΛC, :𝘦ₙ, :milli, :kilo, :LD)]
# the documentation helpers of `Similitude.jl:281-348`
tryv(f) = try collect(f()) catch; "ERROR" end
quants = Any[]
for nm in (:hyperfine, :loschmidt, :wienwavelength, :wienfrequency, :mechanicalheat, :eddington, :solarmass, :jupitermass, :earthmass, :lunarmass, :earthradius, :greatcircle, :radarmile, :hubble, :cosmological, :steradian, :spatian, :degree, :squaredegree, :gradian, :bradian, :arcminute, :arcsecond, :second, :minute, :hour, :day, :gaussianmonth, :siderealmonth, :synodicmonth, :year, :gaussianyear, :siderealyear, :jovianyear, :angstrom, :inch, :foot, :surveyfoot, :yard, :meter, :earthmeter, :mile, :statutemile, :meridianmile, :admiraltymile, :nauticalmile, :lunardistance, :astronomicalunit, :jupiterdistance, :lightyear, :parsec, :barn, :hectare, :acre, :surveyacre, :liter, :gallon, :quart, :pint, :cup, :fluidounce, :teaspoon, :tablespoon, :bubnoff, :ips, :fps, :fpm, :ms, :kmh, :mph, :knot, :mps, :grain, :gram, :earthgram, :kilogram, :tonne, :ton, :pound, :ounce, :slug, :slinch, :hyl, :dyne, :newton, :poundal, :poundforce, :kilopond, :psi, :pascal, :bar, :barye, :technicalatmosphere, :atmosphere, :inchmercury, :torr, :electronvolt, :erg, :joule, :footpound, :calorie, :kilocalorie, :meancalorie, :earthcalorie, :thermalunit, :gasgallon, :tontnt, :watt, :horsepower, :horsepowerwatt, :horsepowermetric, :electricalhorsepower, :tonsrefrigeration, :boilerhorsepower, :coulomb, :earthcoulomb, :ampere, :volt, :henry, :ohm, :siemens, :farad, :weber, :tesla, :abcoulomb, :abampere, :abvolt, :abhenry, :abohm, :abmho, :abfarad, :maxwell, :gauss, :oersted, :gilbert, :statcoulomb, :statampere, :statvolt, :stathenry, :statohm, :statmho, :statfarad, :statweber, :stattesla, :kelvin, :rankine, :celsius, :fahrenheit, :sealevel, :boiling, :mole, :earthmole, :poundmole, :slugmole, :slinchmole, :katal, :amagat, :lumen, :candela, :lux, :phot, :footcandle, :nit, :apostilb, :stilb, :lambert, :footlambert, :bril, :talbot, :lumerg, :hertz, :apm, :rpm, :kayser, :diopter, :rayleigh, :flick, :gforce, :galileo, :eotvos, :darcy, :poise, :reyn, :stokes, :rayl, :mpge, :langley, :jansky, :solarflux, :curie, :gray, :roentgen, :gaussgravitation)
    x = getfield(S, nm)
    x isa S.Quantity || continue
    push!(quants, [string(nm), tryv(() -> S.latexquantity(x))])
end
convs = Any[]
for (a, b) in ((:Metric, :English), (:Metric, :Gauss), (:SI2019, :Planck), (:English, :British), (:IAU☉, :Metric))
    for u in US.Convert
        d = S.evaldim(u)
        push!(convs, [string(a), string(b), string(u), tryv(() -> S.latexquantity(d(getfield(S, a), getfield(S, b))))])
    end
end
cgroups = [[string(nm), tryv(() -> S.latexquantity(getfield(S, nm)))] for nm in
    (:mₑ, :μ₀, :ħ, :αinv, :αG, :Mᵤ, :μₚₑ, :Rᵤ, :G, :GM☉, :pc, :em, :nm, :th, :ΛC, :𝘦ₙ, :milli, :kilo, :LD)]
quots = Any[[string(s), [collect(p) for p in S.latexquotient(getfield(S, s))]] for s in US.Systems]
ldims = Any[]
for s in (:Metric, :English, :Gauss, :Planck, :IAU☉, :MetricDegree), u in US.Convert
    push!(ldims, [string(s), string(u), S.latexdimensions(S.evaldim(u), getfield(S, s))])
end
writejson(joinpath(OUT, "latex.json"), Dict("dims" => dims, "constants" => consts, "quantities" => quants,
    "convs" => convs, "groups" => cgroups, "quotients" => quots, "latexdimensions" => ldims))
println("wrote latex")

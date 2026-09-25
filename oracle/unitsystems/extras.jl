# Golden generator for UnitSystems: Coupling-aware physics constants under a perturbed
# universe (exercises the value-dispatch overrides), and unit-system constructors called
# with random arguments.
#   julia --startup-file=no --project=oracle oracle/unitsystems/extras.jl
# Writes oracle/golden/unitsystems/extras.json.
using UnitSystems, Random
const US = UnitSystems
const FC = US.FieldConstants
include(joinpath(@__DIR__, "jsonw.jl"))
const OUT = joinpath(@__DIR__, "..", "golden", "unitsystems")
Random.seed!(0x5eed)
h(x::Float64) = "0x" * string(reinterpret(UInt64, x), base = 16, pad = 16)
val(x) = x isa FC.Constant ? FC.constant(x) : x
enc(x) = (y = val(x); y isa Int ? ["I", string(y)] : y isa AbstractFloat ? ["F", h(Float64(y))] : ["?", repr(y)])
tryenc(f) = try enc(f()) catch e; ["E", first(split(sprint(showerror, e), '\n'))] end
sysnames = collect(US.Systems)
sys(S) = getfield(US, S)
U0 = US.Universe
C = US.Coupling(US.coupling(U0) * 1.01, US.finestructure(U0) * 1.001, US.electronunit(U0) * 1.0001,
                US.protonunit(U0) * 0.9999, 0.7)
cfuns = (:planckmass, :planck, :gravitation, :elementarycharge, :dalton, :protonmass, :einstein, :molargas,
         :stefan, :radiationdensity, :vacuumpermittivity, :electrostatic, :biotsavart, :vacuumimpedance,
         :faraday, :josephson, :magneticfluxquantum, :klitzing, :conductancequantum, :hartree, :rydberg,
         :bohr, :electronradius, :magneton, :avogadro, :cosmological, :electronmass, :lightspeed,
         :planckreduced, :vacuumpermeability)
coupled = Dict(string(f) => [tryenc(() -> getfield(US, f)(sys(S), C)) for S in sysnames] for f in cfuns)
cslots = [enc(f(C)) for f in (US.coupling, US.finestructure, US.electronunit, US.protonunit, US.darkenergydensity)]

rnd() = round(exp(randn() * 1.5), sigdigits = 6)
slots(U) = [enc(getfield(US, f)(U)) for f in (:boltzmann, :planckreduced, :lightspeed, :vacuumpermeability,
    :electronmass, :molarmass, :luminousefficacy, :radian, :rationalization, :lorentz, :gravity)]
cons = Any[]
for i in 1:20
    a = [rnd() for _ in 1:8]
    push!(cons, Dict("ctor" => "MetricSystem", "args" => a[1:5], "out" => slots(US.MetricSystem(map(FC.Constant, a[1:5])...))))
    push!(cons, Dict("ctor" => "ConventionalSystem", "args" => a[1:2] .* [1e4, 1e14], "out" => slots(US.ConventionalSystem(FC.Constant(a[1] * 1e4), FC.Constant(a[2] * 1e14)))))
    for base in (:Metric, :English, :Gauss)
        B = sys(base)
        push!(cons, Dict("ctor" => "EntropySystem", "base" => string(base), "args" => a[1:4], "out" => slots(US.EntropySystem(B, map(FC.Constant, a[1:4])...))))
        push!(cons, Dict("ctor" => "AstronomicalSystem", "base" => string(base), "args" => a[1:3], "out" => slots(US.AstronomicalSystem(B, map(FC.Constant, a[1:3])...))))
        push!(cons, Dict("ctor" => "ElectricSystem", "base" => string(base), "args" => a[1:2], "out" => slots(US.ElectricSystem(B, map(FC.Constant, a[1:2])...))))
        push!(cons, Dict("ctor" => "GaussSystem", "base" => string(base), "args" => a[1:3], "out" => slots(US.GaussSystem(B, map(FC.Constant, a[1:3])...))))
        push!(cons, Dict("ctor" => "RankineSystem", "base" => string(base), "args" => a[1:3], "out" => slots(US.RankineSystem(B, map(FC.Constant, a[1:3])...))))
    end
end
# rescaled systems `U(JK, Js, ms, Hm, kg)` (`UnitSystems.jl:205-221`) and their names
resc = Any[]
for (base, args) in ((:Metric, (1.0, 1.0, 1.0, 1.0, 1.0)), (:Metric, (1, 1, 1, 1, 1)),
                     (:English, (2.0, 0.5, 3.0, 1.0, 0.25)), (:Gauss, (1.5, 2.0, 0.5, 4.0, 1.0)),
                     (:SI2019, (1.0, 2.0, 1.0, 1.0, 1.0)), (:Planck, (2, 3, 5, 7, 11)))
    R = sys(base)(args...)
    push!(resc, Dict("base" => string(base), "args" => [enc(a) for a in args], "out" => slots(R),
        "name" => sprint(show, R)))
end
# the conversion helpers of `kinematic.jl:20-41`, `thermodynamic.jl:32-39` (port notes §6.4)
helpers = Any[]
for (f, x) in ((:kilograms, 1), (:kilograms, 2.5), (:slugs, 1), (:slugs, 3.0), (:feet, 1), (:feet, 0.3048),
               (:meters, 1), (:meters, 5.0), (:moles, 6.02214076e23), (:molecules, 2.0))
    push!(helpers, [string(f), enc(x), tryenc(() -> getfield(US, f)(x)), ""])
end
for (f, x, s) in ((:kilograms, 1.0, :Metric), (:feet, 1.0, :English), (:meters, 2.0, :Metric),
                  (:slugs, 1.0, :English), (:moles, 1e24, :English), (:molecules, 1.0, :English))
    push!(helpers, [string(f), enc(x), tryenc(() -> getfield(US, f)(x, sys(s))), string(s)])
end
writejson(joinpath(OUT, "extras.json"), Dict("julia" => string(VERSION), "coupling" => cslots,
    "coupled" => coupled, "constructors" => cons, "rescale" => resc, "helpers" => helpers))
println("wrote extras.json")

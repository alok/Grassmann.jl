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
writejson(joinpath(OUT, "latex.json"), Dict("dims" => dims, "constants" => consts))
println("wrote latex")

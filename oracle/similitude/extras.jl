# Golden generator for Similitude's smaller helpers: `dimlist(U)` (the images of
# the eleven base dimensions), `naturalunits(U)` (the natural unit of each base
# dimension expressed in U).
#   julia --startup-file=no --project=oracle oracle/similitude/extras.jl
# Writes oracle/golden/similitude/extras.json.
using Similitude
const S = Similitude
const US = S.UnitSystems
include(joinpath(@__DIR__, "..", "unitsystems", "jsonw.jl"))
const OUT = joinpath(@__DIR__, "..", "golden", "similitude")
showstr(x) = try sprint(show, x) catch; "ERROR" end
rows = Any[]
for s in US.Systems
    U = getfield(S, s)
    push!(rows, [string(s), S.dimlist(U), [showstr(p.second) for p in S.naturalunits(U)]])
end
writejson(joinpath(OUT, "extras.json"), rows)
println("wrote extras (", length(rows), ")")

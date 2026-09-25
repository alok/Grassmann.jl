# Oracle generator for MeshTopology.jl 0.1.0 (port-notes/meshtopology.md §9).
#
#   julia --startup-file=no --project=<juliaenv> oracle/meshtopology/gen.jl
#
# <juliaenv> is an environment with the registered stack of oracle/Project.toml (MeshTopology
# 0.1.0, Grassmann, StaticVectors, JSON). Writes oracle/golden/meshtopology/*.json:
#
# * misc.json      CrossRange, simplex numbers, Leibniz combinatorics, range resampling
# * product.json   ProductTopology constructors, indexing, resize/resample/exclude/cross, show
# * quotient.json  every named QuotientTopology in 1-5 dimensions: tables, ghost lookups,
#                  slices, resize/resample, elementfuns/vertices, linear and bilinear cells
# * cross.json     products of quotient topologies (and cross_sphere / cross_sector)
# * simplex.json   Simplex/Discontinuous topologies on hand-made and randomly relabelled meshes
# * lagrange.json  Lagrange edges, triangles and tetrahedra of degree 1-5, subsets, refinement
#
# See load.jl for the upstream/fixed module pair and common.jl for the JSON conventions.

include(joinpath(@__DIR__, "load.jl"))
include(joinpath(@__DIR__, "common.jl"))

const OUT = joinpath(@__DIR__, "..", "golden", "meshtopology")
mkpath(OUT)

Random.seed!(0x3E54)
include(joinpath(@__DIR__, "meshes.jl"))

const PARTS = isempty(ARGS) ? ("misc", "product", "quotient", "simplex", "lagrange") : ARGS
for part in PARTS
    Random.seed!(0x3E54)
    t0 = time()
    include(joinpath(@__DIR__, "gen_$part.jl"))
    println(part, ": ", round(time() - t0; digits = 1), " s")
end

# Cartan `raster(ga)` (ext/ColorTypesExt.jl:18-35; no documented figure): the incidence raster of
# the five lines of a pentagram (bivectors A(k)∧A(k+2) of the projective plane ⟨1, x, y⟩), shown
# as an image of [-3,3]² (white ink `GrayA(c, c)` on a black axis). The dump holds every count.
include("cartan_common.jl")
using CairoMakie.Colors: gray
A(k) = Chain(1.0, 2.5cos(2π*k/5 + π/2), 2.5sin(2π*k/5 + π/2))
ga = [A(k) ∧ A(k+2) for k in 0:4]
out = Cartan.raster(ga)
counts = rotr90(Float64.(gray.(out)))              # z[i, j]: i ↔ x, j ↔ y from the bottom
dumpdata("cartan-raster", Dict("n" => size(counts), "counts" => vec(counts), "sum" => sum(counts)))
fig = Figure()
ax = Axis(fig[1, 1], backgroundcolor = :black, aspect = DataAspect())
image!(ax, -3..3, -3..3, rotr90(out); interpolate = false)
savefig("cartan-raster", fig)

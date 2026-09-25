# Cartan.jl docs/src/plot.md:31-38 (Makie's arrows3d example on a TensorField):
#   ps = OpenParameter(-5:2:5,-5:2:5,-5:2:5)
#   ns = map(p -> 0.1 * Chain(p[2], p[3], p[1]), ps)
#   arrows3d(TensorField(ps, ns), shaftcolor = :gray, tipcolor = :black, align = :center, axis=(type=Axis3,))
include("cartan_common.jl")
ps = OpenParameter(-5:2:5,-5:2:5,-5:2:5)
ns = map(p -> 0.1 * Chain(p[2], p[3], p[1]), ps)
fig, ax, pl = arrows3d(TensorField(ps, ns), shaftcolor = :gray, tipcolor = :black, align = :center, axis=(type=Axis3,))
dumpdata("cartan-plot-arrows3d", Dict("origins" => pts_summary(pl[1][]), "directions" => pts_summary(pl[2][]),
    "align" => string(pl.align[])))
savefig("cartan-plot-arrows3d", fig)

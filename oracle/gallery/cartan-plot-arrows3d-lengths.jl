# Cartan.jl docs/src/plot.md:40-46 (Makie's arrows3d example, coloured by length):
#   lengths = vec(norm.(ns))
#   arrows3d(TensorField(ps, ns), color = lengths, lengthscale = 1.5, align = :center, axis=(type=Axis3,))
include("cartan_common.jl")
ps = OpenParameter(-5:2:5,-5:2:5,-5:2:5)
ns = map(p -> 0.1 * Chain(p[2], p[3], p[1]), ps)
lengths = vec(norm.(ns))
fig, ax, pl = arrows3d(TensorField(ps, ns), color = lengths, lengthscale = 1.5, align = :center, axis=(type=Axis3,))
dumpdata("cartan-plot-arrows3d-lengths", Dict("origins" => pts_summary(pl[1][]), "directions" => pts_summary(pl[2][]),
    "color" => color_summary(pl.color[]), "lengthscale" => pl.lengthscale[]))
savefig("cartan-plot-arrows3d-lengths", fig)

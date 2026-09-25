# Cartan `scaledarrows` (ext/MakieExt.jl:371-379) of the plot.md:15-28 vector field, resampled:
#   xy = TensorField(OpenParameter(xs,ys),Chain.(us,vs))
#   scaledarrows(xy, gridsize = (10,10))
# `scaledarrows(t) = scaledarrows(TensorField(base(t)), t)`: arrows from the grid points with
# `lengthscale = spacing(M)/(Σ|t|/n)/3` after `gridargs` resamples both fields to 10×10.
include("cartan_common.jl")
xs = LinRange(0, 2pi, 20)
ys = LinRange(0, 3pi, 20)
us = [sin(x) * cos(y) for x in xs, y in ys]
vs = [-cos(x) * sin(y) for x in xs, y in ys]
xy = TensorField(OpenParameter(xs,ys),Chain.(us,vs))
fig, ax, pl = scaledarrows(xy, gridsize = (10,10))
dumpdata("cartan-scaledarrows-grid", Dict("origins" => pts_summary(pl[1][]), "directions" => pts_summary(pl[2][]),
    "lengthscale" => pl.lengthscale[]))
savefig("cartan-scaledarrows-grid", fig)

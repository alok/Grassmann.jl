# Cartan `scaledarrows!(M, t)` (ext/MakieExt.jl:371-379) along a space curve, the pattern of
# fiber.md:442-451 (`lines(lin); scaledarrows!(lin, unitframe(lin), …)`) with an analytic unit
# tangent field (the frames need Cartan's differential geometry):
#   t = TensorField(0:0.1:4pi); M = Chain.(cos(t), sin(t), t/4)
#   T = Chain.(-sin(t), cos(t), 0*t .+ 0.25)/sqrt(1.0625)
#   lines(M); scaledarrows!(M, T)
# 3-D fibers draw `arrows3d` with `lengthscale = spacing(M)/(Σ|T|/n)/3`.
include("cartan_common.jl")
t = TensorField(0:0.1:4pi)
M = Chain.(cos(t), sin(t), t/4)
T = TensorField(base(t), [Chain(-sin(x), cos(x), 0.25)/sqrt(1.0625) for x in fiber(t)])
fig, ax, pl0 = lines(M; axis = (type = Axis3,), figure = (size = (600, 500),))
pl = scaledarrows!(M, T)
dumpdata("cartan-scaledarrows-helix", Dict("origins" => pts_summary(pl[1][]), "directions" => pts_summary(pl[2][]),
    "lengthscale" => pl.lengthscale[], "spacing" => Cartan.spacing(M)))
savefig("cartan-scaledarrows-helix", fig)

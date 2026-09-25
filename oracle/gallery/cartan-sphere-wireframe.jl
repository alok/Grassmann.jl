# Cartan.jl docs/src/fiber.md:602-613 (C9 of plot-inventory.md), the sphere:
#   spher(x) = Chain(cos(x[2])*sin(x[1]), sin(x[2])*sin(x[1]), cos(x[1]))
#   sph = spher.(SphereParameter(60,60))
#   wireframe(sph)
# `wireframe(M::TensorField{…,Chain,2,GridBundle})` draws the quads of `GridBundle(fiber(M))`
# (ext/MakieExt.jl:822). SphereParameter needs the B1 shim of cartan_common.jl; an Axis3 replaces
# the LScene so the Lean render is comparable.
include("cartan_common.jl")
spher(x) = Chain(cos(x[2])*sin(x[1]), sin(x[2])*sin(x[1]), cos(x[1]))
sph = spher.(SphereParameter(60,60))
fig, ax, pl = wireframe(sph; axis = (type = Axis3,), figure = (size = (600, 500),))
segs = pl.plots[1][1][]
dump_segments("cartan-sphere-wireframe", segs; k = 64, extra = Dict("size" => collect(size(sph))))
savefig("cartan-sphere-wireframe", fig)

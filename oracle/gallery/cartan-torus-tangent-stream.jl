# Cartan.jl docs/src/fiber.md:778-797 (C17 of plot-inventory.md), the torus:
#   torus(x) = Chain((2+0.5cos(x[1]))*cos(x[2]), (2+0.5cos(x[1]))*sin(x[2]), 0.5sin(x[1]))
#   tor = torus.(TorusParameter(60,60))
#   f3(x) = Chain(cos(x[1])*cos(x[2]),sin(x[2])*sin(x[1])); vf3 = f3.(TorusParameter(100,100))
#   streamplot(tor,vf3)
# `streamplot(M, m)` (ext/MakieExt.jl:536-557): the 3-D streamplot of p ↦ (m(p)₁, m(p)₂, 0) over
# the parameter box × [-1e-15, 1e-15] (gridsize (32,32,1)), drawn through `transform_func = p ↦ M(p)`.
# The dump is Makie's streamplot_impl in parameter space. TorusParameter needs the B1 shim; an
# Axis3 replaces the LScene.
include("cartan_common.jl")
torus(x) = Chain((2+0.5cos(x[1]))*cos(x[2]), (2+0.5cos(x[1]))*sin(x[2]), 0.5sin(x[1]))
tor = torus.(TorusParameter(60,60))
f3(x) = Chain(cos(x[1])*cos(x[2]),sin(x[2])*sin(x[1]))
vf3 = f3.(TorusParameter(100,100))
w = Cartan.widths(points(vf3))
f = p -> (z = vf3(p); Makie.Point(z[1], z[2], 0))
dump_stream("cartan-torus-tangent-stream", f, Rect3d(0, 0, -1e-15, w[1], w[2], 2e-15), (32, 32, 1))
d = JSON.parsefile(joinpath(JULIA_DATA, "cartan-torus-tangent-stream.json"))
d["surfacearea"] = surfacearea(tor)
dumpdata("cartan-torus-tangent-stream", d)
fig, ax, pl = streamplot(tor, vf3; figure = (size = (600, 500),))
savefig("cartan-torus-tangent-stream", fig)

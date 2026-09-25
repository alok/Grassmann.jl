# Grassmann.jl README.md:298-302 (docs/src/algebra.md:1292-1297, paper/img/orb.png), a conformal
# versor field on the Riemann sphere, read and drawn in V(2,3,4) = (v1, v2, v3):
#   @basis S"∞+++"
#   streamplot(vectorfield(exp((π/4)*(v12+v∞3)),V(2,3,4)),-1.5..1.5,-1.5..1.5,-1.5..1.5,gridsize=(10,10))
# Makie 0.24 wants a 3-tuple gridsize for a 3D streamplot (the README's (10,10) predates it;
# `to_ndim` pads it with its last entry), so both sides use (10,10,10).
include("grassmann_common.jl")
@basis S"∞+++"
f = vectorfield(exp((π/4)*(v12+v∞3)), V(2,3,4))
dump_stream("grassmann-orb", f, Rect3d(Vec3d(-1.5), Vec3d(3.0)), (10, 10, 10); stride = 8)
fig = Figure(size = (600, 500))
ax = Axis3(fig[1, 1])
streamplot!(ax, f, -1.5 .. 1.5, -1.5 .. 1.5, -1.5 .. 1.5, gridsize = (10, 10, 10))
savefig("grassmann-orb", fig)

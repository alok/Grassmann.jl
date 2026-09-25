# Grassmann.jl README.md:63-67 (the header image) and 298-302, docs/src/algebra.md:1298-1302,
# paper/img/wave.png: the orb versor with the input point read in V(1,2,3) = (v∞, v1, v2):
#   @basis S"∞+++"
#   streamplot(vectorfield(exp((π/4)*(v12+v∞3)),V(2,3,4),V(1,2,3)),-1.5..1.5,-1.5..1.5,-1.5..1.5,gridsize=(10,10))
include("grassmann_common.jl")
@basis S"∞+++"
f = vectorfield(exp((π/4)*(v12+v∞3)), V(2,3,4), V(1,2,3))
dump_stream("grassmann-wave", f, Rect3d(Vec3d(-1.5), Vec3d(3.0)), (10, 10, 10); stride = 8)
fig = Figure(size = (600, 500))
ax = Axis3(fig[1, 1])
streamplot!(ax, f, -1.5 .. 1.5, -1.5 .. 1.5, -1.5 .. 1.5, gridsize = (10, 10, 10))
savefig("grassmann-wave", fig)

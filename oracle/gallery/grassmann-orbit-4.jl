# Grassmann.jl README.md:311-316 (docs/src/algebra.md:1311-1316, paper/img/orbit-4.png):
#   @basis S"∞+++"
#   f(t) = ↓(exp(t*(v12+0.07v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2))>>>↑(v1+v2-v3))
#   lines(V(2,3,4).(points(f)))
include("grassmann_common.jl")
@basis S"∞+++"
f(t) = ↓(exp(t*(v12+0.07v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2))>>>↑(v1+v2-v3))
pts = [Point3(value(p)...) for p in V(2,3,4).(points(f))]
dump_curve("grassmann-orbit-4", pts)
curve_figure("grassmann-orbit-4", pts)

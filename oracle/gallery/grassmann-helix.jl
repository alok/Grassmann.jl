# Grassmann.jl README.md:287-296 (docs/src/algebra.md:1281-1290, paper/img/helix.png), the
# torus expression evaluated in conformal space:
#   @basis S"∞∅+++"
#   f(t) = (↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3)))
#   lines(V(3,4,5).(points(f)))
include("grassmann_common.jl")
@basis S"∞∅+++"
f(t) = (↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3)))
pts = [Point3(value(p)...) for p in V(3,4,5).(points(f))]
dump_curve("grassmann-helix", pts)
curve_figure("grassmann-helix", pts)

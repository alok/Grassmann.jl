# Grassmann.jl README.md:287-296 (docs/src/algebra.md:1281-1290, paper/img/torus.png), a curve
# on the Riemann sphere:
#   @basis S"∞+++"
#   f(t) = (↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3)))
#   lines(V(2,3,4).(points(f)))
include("grassmann_common.jl")
@basis S"∞+++"
f(t) = (↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3)))
pts = [Point3(value(p)...) for p in V(2,3,4).(points(f))]
dump_curve("grassmann-torus", pts)
curve_figure("grassmann-torus", pts)

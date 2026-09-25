# Cartan.jl docs/src/fiber.md:477-487 ("Riemann sphere", C5 of plot-inventory.md), the first curve:
#   pts = TensorField(-2*pi:0.0001:2*pi)
#   @basis S"∞+++"
#   f(t) = ↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3))
#   lines(V(2,3,4).(f.(pts)))
# Cartan's `lines` of a space curve colours it by `speed` (ext/MakieExt.jl:171-174); an Axis3
# replaces the LScene so the Lean render is comparable.
include("cartan_common.jl")
pts = TensorField(-2*pi:0.0001:2*pi)
@basis S"∞+++"
f(t) = ↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3))
curve = V(2,3,4).(f.(pts))
dump_speed_curve("cartan-riemann-torus", curve)
fig, ax, pl = lines(curve; axis = (type = Axis3,), figure = (size = (600, 500),))
savefig("cartan-riemann-torus", fig)

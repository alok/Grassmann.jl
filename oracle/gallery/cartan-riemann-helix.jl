# Cartan.jl docs/src/fiber.md:488-493 ("Riemann sphere", C5), the conformal curve:
#   @basis S"∞∅+++" # conformal geometric algebra
#   f(t) = ↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3))
#   lines(V(3,4,5).(vector.(f.(pts))))
include("cartan_common.jl")
pts = TensorField(-2*pi:0.0001:2*pi)
@basis S"∞∅+++"
f(t) = ↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3))
curve = V(3,4,5).(vector.(f.(pts)))
dump_speed_curve("cartan-riemann-helix", curve)
fig, ax, pl = lines(curve; axis = (type = Axis3,), figure = (size = (600, 500),))
savefig("cartan-riemann-helix", fig)

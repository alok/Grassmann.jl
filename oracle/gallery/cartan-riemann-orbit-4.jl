# Cartan.jl docs/src/fiber.md:477-487 ("Riemann sphere", C5), the third curve:
#   f(t) = ↓(exp(t*(v12+0.07v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2))>>>↑(v1+v2-v3))
#   lines(V(2,3,4).(f.(pts)))
include("cartan_common.jl")
pts = TensorField(-2*pi:0.0001:2*pi)
@basis S"∞+++"
f(t) = ↓(exp(t*(v12+0.07v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2))>>>↑(v1+v2-v3))
curve = V(2,3,4).(f.(pts))
dump_speed_curve("cartan-riemann-orbit-4", curve)
fig, ax, pl = lines(curve; axis = (type = Axis3,), figure = (size = (600, 500),))
savefig("cartan-riemann-orbit-4", fig)

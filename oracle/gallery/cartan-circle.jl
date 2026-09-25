# Cartan.jl docs/src/fiber.md:602-613 (C9 of plot-inventory.md), the circle:
#   t = TensorField(0:0.001:2pi)
#   circ = Chain.(cos(t),sin(t))
#   lines(circ)
# Cartan's `lines` of a plane curve colours it by `speed` (ext/MakieExt.jl:171-174).
include("cartan_common.jl")
t = TensorField(0:0.001:2pi)
circ = Chain.(cos(t),sin(t))
dump_speed_curve("cartan-circle", circ; k = 16)
fig, ax, pl = lines(circ)
savefig("cartan-circle", fig)

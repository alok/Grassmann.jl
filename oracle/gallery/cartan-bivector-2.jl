# Cartan.jl docs/src/fiber.md:495-503 ("Bivector", C6):
#   streamplot(tensorfield(exp((pi/2)*v12/2)).(vdom))
include("cartan_common.jl")
basis"2"
vdom = TensorField(ProductSpace{V}(-1.5:0.1:1.5,-1.5:0.1:1.5))
field_stream("cartan-bivector-2", tensorfield(exp((pi/2)*v12/2)).(vdom), (32, 32))

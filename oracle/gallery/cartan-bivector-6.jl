# Cartan.jl docs/src/fiber.md:504-509 ("Bivector", C6), the Lobachevskian plane:
#   streamplot(tensorfield(v1*exp((pi/4)*v12/2)).(vdom))
include("cartan_common.jl")
@basis S"+-"
vdom = TensorField(ProductSpace{V}(-1.5:0.1:1.5,-1.5:0.1:1.5))
field_stream("cartan-bivector-6", tensorfield(v1*exp((pi/4)*v12/2)).(vdom), (32, 32))

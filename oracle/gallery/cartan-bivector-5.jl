# Cartan.jl docs/src/fiber.md:504-509 ("Bivector", C6), the Lobachevskian plane:
#   @basis S"+-"
#   vdom = TensorField(ProductSpace{V}(-1.5:0.1:1.5,-1.5:0.1:1.5))
#   streamplot(tensorfield(exp((pi/8)*v12/2)).(vdom))
include("cartan_common.jl")
@basis S"+-"
vdom = TensorField(ProductSpace{V}(-1.5:0.1:1.5,-1.5:0.1:1.5))
field_stream("cartan-bivector-5", tensorfield(exp((pi/8)*v12/2)).(vdom), (32, 32))

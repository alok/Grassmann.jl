# Cartan.jl docs/src/fiber.md:495-503 ("Bivector", C6 of plot-inventory.md), the first field:
#   basis"2" # Euclidean geometric algebra in 2 dimensions
#   vdom = TensorField(ProductSpace{V}(-1.5:0.1:1.5,-1.5:0.1:1.5))
#   streamplot(tensorfield(exp(pi*v12/2)).(vdom))
# The 31×31 grid field is streamplotted through its bilinear interpolation.
include("cartan_common.jl")
basis"2"
vdom = TensorField(ProductSpace{V}(-1.5:0.1:1.5,-1.5:0.1:1.5))
field_stream("cartan-bivector-1", tensorfield(exp(pi*v12/2)).(vdom), (32, 32))

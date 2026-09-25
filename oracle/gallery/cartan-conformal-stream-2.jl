# Cartan.jl docs/src/fiber.md:519-523 (C7 of plot-inventory.md), the second conformal field:
#   vdom2 = TensorField(ProductSpace{V(2,3,4)}(-1.5:0.1:1.5,-1.5:0.1:1.5,-1.5:0.1:1.5));
#   tf2 = tensorfield(exp((pi/4)*(v12+v∞3)),V(2,3,4)).(vdom2)
#   streamplot(tf2,gridsize=(10,10))
include("cartan_common.jl")
@basis S"∞+++"
vdom2 = TensorField(ProductSpace{V(2,3,4)}(-1.5:0.1:1.5,-1.5:0.1:1.5,-1.5:0.1:1.5));
tf2 = tensorfield(exp((pi/4)*(v12+v∞3)),V(2,3,4)).(vdom2)
field_stream("cartan-conformal-stream-2", tf2, (10, 10, 10); size = (600, 500), axis = (type = Axis3,), gridsize = (10, 10))

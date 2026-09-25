# Cartan.jl docs/src/fiber.md:511-518 (C7 of plot-inventory.md), the first conformal field:
#   @basis S"∞+++"
#   vdom1 = TensorField(ProductSpace{V(1,2,3)}(-1.5:0.1:1.5,-1.5:0.1:1.5,-1.5:0.1:1.5));
#   tf1 = tensorfield(exp((pi/4)*(v12+v∞3)),V(2,3,4)).(vdom1)
#   streamplot(tf1,gridsize=(10,10))
# The 31³ grid field is streamplotted through its trilinear interpolation; an Axis3 replaces the
# LScene so the Lean render is comparable.
include("cartan_common.jl")
@basis S"∞+++"
vdom1 = TensorField(ProductSpace{V(1,2,3)}(-1.5:0.1:1.5,-1.5:0.1:1.5,-1.5:0.1:1.5));
tf1 = tensorfield(exp((pi/4)*(v12+v∞3)),V(2,3,4)).(vdom1)
field_stream("cartan-conformal-stream-1", tf1, (10, 10, 10); size = (600, 500), axis = (type = Axis3,), gridsize = (10, 10))

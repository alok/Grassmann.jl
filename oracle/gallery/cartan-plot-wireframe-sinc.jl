# Cartan.jl docs/src/plot.md:409-415 (Makie's wireframe example on a TensorField):
#   x, y = collect(-8:0.5:8), collect(-8:0.5:8)
#   z = [sinc(√(X^2 + Y^2) / π) for X ∈ x, Y ∈ y]
#   xyz = TensorField(ProductSpace(x,y),z)
#   wireframe(graph(xyz), axis=(type=Axis3,), color=:black)
include("cartan_common.jl")
x, y = collect(-8:0.5:8), collect(-8:0.5:8)
z = [sinc(√(X^2 + Y^2) / π) for X ∈ x, Y ∈ y]
xyz = TensorField(ProductSpace(x,y),z)
fig, ax, pl = wireframe(graph(xyz), axis=(type=Axis3,), color=:black)
dump_segments("cartan-plot-wireframe-sinc", pl.plots[1][1][]; k = 16)
savefig("cartan-plot-wireframe-sinc", fig)

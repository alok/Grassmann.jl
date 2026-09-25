# Grassmann.jl paper/paper.tex:320-329 (paper/img/triangle-tetrahedron.png): the triangle v123
# and its complement, the tetrahedron !v123 = v4567, drawn as one directed graph:
#   x = Grassmann.Algebra(ℝ^7).v123; Grassmann.graph(x+!x)
# (`Grassmann.Algebra` is `Λ` today and `graph` was removed, src/Grassmann.jl:430-445; the
# edges come from the LightGraphsExt emulation). The 7-D multivector must be built at top
# level: inside a closure its compilation hangs Julia.
include("grassmann_common.jl")
B7 = Λ(ℝ^7)
t7 = B7.v123
graph_figure("grassmann-triangle-tetrahedron", t7 + !t7, "v123+!v123")

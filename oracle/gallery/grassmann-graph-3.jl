# Grassmann.jl paper/paper.tex:566-586 (paper/img/graph-3.png): the directed graph of
# a multivector (ext/LightGraphsExt.jl:19-48; the paper drew it with GraphPlot.gplot):
#   @basis ℝ^4; SimpleDiGraph(∂(v124)+v34)
include("grassmann_common.jl")
B = Λ(ℝ^4)
graph_figure("grassmann-graph-3", ∂(B.v124) + B.v34, "∂(v124)+v34")

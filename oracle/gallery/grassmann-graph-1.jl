# Grassmann.jl paper/paper.tex:566-586 (paper/img/graph-1.png): the directed graph of
# a multivector (ext/LightGraphsExt.jl:19-48; the paper drew it with GraphPlot.gplot):
#   @basis ℝ^4; SimpleDiGraph(v12+v34)
include("grassmann_common.jl")
B = Λ(ℝ^4)
graph_figure("grassmann-graph-1", B.v12 + B.v34, "v12+v34")

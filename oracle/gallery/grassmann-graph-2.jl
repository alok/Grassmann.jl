# Grassmann.jl paper/paper.tex:566-586 (paper/img/graph-2.png): the directed graph of
# a multivector (ext/LightGraphsExt.jl:19-48; the paper drew it with GraphPlot.gplot):
#   @basis ℝ^4; SimpleDiGraph(v14+v24+v34)
include("grassmann_common.jl")
B = Λ(ℝ^4)
graph_figure("grassmann-graph-2", B.v14 + B.v24 + B.v34, "v14+v24+v34")

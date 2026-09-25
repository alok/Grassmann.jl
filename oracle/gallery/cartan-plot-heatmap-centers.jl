# Cartan.jl docs/src/plot.md:176-188 (Makie's heatmap example with irregular cell centres):
#   f = Figure(); ax = Axis(f[1, 1])
#   centers_x = [1, 2, 4, 7, 11]; centers_y = [6, 7, 9, 12, 16]
#   xy = ProductSpace(centers_x,centers_y)
#   heatmap!(TensorField(xy,reshape(1:25, 5, 5)))
#   scatter!(TensorField(xy,collect(xy)), color=:white, strokecolor=:black, strokewidth=1)
include("cartan_common.jl")
f = Figure()
ax = Axis(f[1, 1])
centers_x = [1, 2, 4, 7, 11]
centers_y = [6, 7, 9, 12, 16]
xy = ProductSpace(centers_x,centers_y)
hm = heatmap!(TensorField(xy,reshape(1:25, 5, 5)))
sc = scatter!(TensorField(xy,collect(xy)), color=:white, strokecolor=:black, strokewidth=1)
dumpdata("cartan-plot-heatmap-centers", Dict("x" => Float64.(collect(hm[1][])), "y" => Float64.(collect(hm[2][])),
    "z" => summary_of(vec(hm[3][]), 1), "scatter" => pts_summary(sc[1][])))
savefig("cartan-plot-heatmap-centers", f)

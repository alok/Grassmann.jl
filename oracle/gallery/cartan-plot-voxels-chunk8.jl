# Cartan.jl docs/src/plot.md:394-403 (Makie's voxels example with a colour range and clipping):
#   chunk = TensorField(OpenParameter(8,8,8),reshape(collect(1:512), 8, 8, 8))
#   f, a, p = voxels(chunk, colorrange = (65, 448), colorscale = log10,
#       lowclip = :red, highclip = :orange, colormap = [:blue, :green])
# OpenParameter(8,8,8) needs the shim of cartan_common.jl; an Axis3 replaces the LScene.
include("cartan_common.jl")
chunk = TensorField(OpenParameter(8,8,8),reshape(collect(1:512), 8, 8, 8))
f, a, p = voxels(chunk, colorrange = (65, 448), colorscale = log10,
    lowclip = :red, highclip = :orange, colormap = [:blue, :green], axis = (type = Axis3,))
dumpdata("cartan-plot-voxels-chunk8", Dict("values" => summary_of(vec(p[4][]), 1),
    "x" => [Float64(p[1][][1]), Float64(p[1][][2])]))
savefig("cartan-plot-voxels-chunk8", f)

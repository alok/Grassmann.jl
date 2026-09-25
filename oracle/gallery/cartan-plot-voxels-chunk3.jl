# Cartan.jl docs/src/plot.md:389-393 (Makie's voxels example on a TensorField):
#   chunk = TensorField(OpenParameter(3,3,3),reshape(collect(1:27), 3, 3, 3))
#   voxels(chunk, gap = 0.33)
# OpenParameter(3,3,3) throws in Cartan 0.4.16 (B2/B1); the shim of cartan_common.jl restores it.
# An Axis3 replaces the LScene so the Lean render is comparable.
include("cartan_common.jl")
chunk = TensorField(OpenParameter(3,3,3),reshape(collect(1:27), 3, 3, 3))
fig, ax, pl = voxels(chunk, gap = 0.33, axis = (type = Axis3,))
dumpdata("cartan-plot-voxels-chunk3", Dict("values" => summary_of(vec(pl[4][]), 1),
    "x" => [Float64(pl[1][][1]), Float64(pl[1][][2])], "gap" => pl.gap[]))
savefig("cartan-plot-voxels-chunk3", fig)

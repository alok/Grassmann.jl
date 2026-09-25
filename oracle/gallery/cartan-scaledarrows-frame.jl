# Cartan `scaledarrows(M, t::TensorOperator)` (ext/MakieExt.jl:380-384, 407-413): a frame of two
# tangent columns on the surface z = xy/4, one arrow set per column with
# `lengthscale = spacing(M)/max(Σ|colᵢ|/n)/3`.
include("cartan_common.jl")
p = TensorField(ProductSpace(0:0.25:2, 0:0.25:2))
S = (x -> Chain(x[1], x[2], x[1]*x[2]/4)).(p)
c1 = (x -> Chain(1.0, 0.0, x[2]/4)).(p)
c2 = (x -> Chain(0.0, 1.0, x[1]/4)).(p)
F = TensorField(base(p), TensorOperator.(Chain.(fiber(c1), fiber(c2))))
fig = Figure(size = (600, 500))
ax = Axis3(fig[1, 1])
scaledarrows!(S, F)
arr = [q for q in ax.scene.plots if hasproperty(q, :lengthscale)]
dumpdata("cartan-scaledarrows-frame", Dict("narrows" => length(arr), "lengthscales" => [q.lengthscale[] for q in arr],
    "origins" => pts_summary(arr[1][1][]), "directions" => [pts_summary(q[2][]) for q in arr]))
savefig("cartan-scaledarrows-frame", fig)

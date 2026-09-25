# Cartan `arrowsbundle(M, t)` (ext/MakieExt.jl:290-299) of the helix and its unit tangents:
# `scatter(fiber(M))`, then arrows of `t` and `-t` with `lengthscale = spacing(M)/(Σ|t|/n)/2`.
include("cartan_common.jl")
t = TensorField(0:0.2:4pi)
M = Chain.(cos(t), sin(t), t/4)
T = TensorField(base(t), [Chain(-sin(x), cos(x), 0.25)/sqrt(1.0625) for x in fiber(t)])
fig = Figure(size = (600, 500))
ax = Axis3(fig[1, 1])
arrowsbundle!(M, T)
pl = first(p for p in ax.scene.plots if p isa Scatter)
arr = [p for p in ax.scene.plots if !(p isa Scatter)]
dumpdata("cartan-arrowsbundle-helix", Dict("points" => pts_summary(pl[1][]), "narrows" => length(arr),
    "lengthscales" => [p.lengthscale[] for p in arr], "directions" => [pts_summary(p[2][]) for p in arr]))
savefig("cartan-arrowsbundle-helix", fig)

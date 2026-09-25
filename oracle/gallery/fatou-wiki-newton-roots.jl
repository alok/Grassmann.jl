# Fatou.jl wiki, Explore-Fatou-sets-&-fractals.md, example (1): the Newton basins of z^3 - 1 by the root reached:
#   nf = newton(:(z^3-1), ϵ=0.001, n=800, cmap="brg"); nf |> fatou |> plot
include("fatou_common.jl")
nf = newton(:(z^3-1), ϵ=0.001, n=800, cmap="brg")
fatou_figure("fatou-wiki-newton-roots", nf; figsize = (620, 500))

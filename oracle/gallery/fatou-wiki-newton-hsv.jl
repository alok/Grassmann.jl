# Fatou.jl wiki, Explore-Fatou-sets-&-fractals.md, example (3): multiplicity m = -0.5, coloured by the limit angle:
#   nf = newton(:(z^3-1), m=-0.5, n=800, N=10, cmap="hsv"); nf |> fatou |> plot
include("fatou_common.jl")
nf = newton(:(z^3-1), m=-0.5, n=800, N=10, cmap="hsv")
fatou_figure("fatou-wiki-newton-hsv", nf; figsize = (620, 500))

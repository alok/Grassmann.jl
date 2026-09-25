# Fatou.jl wiki, Explore-Fatou-sets-&-fractals.md, example (2): multiplicity m = 2:
#   nf = newton(:(z^3-1), m=2, n=800, N=37, ϵ=0.27, iter=true, cmap="ocean"); nf |> fatou |> plot
include("fatou_common.jl")
nf = newton(:(z^3-1), m=2, n=800, N=37, ϵ=0.27, iter=true, cmap="ocean")
fatou_figure("fatou-wiki-newton-snowflake", nf; figsize = (620, 500))

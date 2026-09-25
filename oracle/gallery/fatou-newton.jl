# Fatou.jl README.md:96-104, the Newton fractal of z³ - 1 (iteration counts):
#   nf = newton(:(z^3-1),n=800,ϵ=0.1,N=25,iter=true,cmap="jet"); nf |> fatou |> plot
include("fatou_common.jl")
nf = newton(:(z^3-1), n=800, ϵ=0.1, N=25, iter=true, cmap="jet")
fatou_figure("fatou-newton", nf; figsize = (620, 500))

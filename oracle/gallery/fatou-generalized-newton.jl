# Fatou.jl README.md:106-116, the generalized Newton fractal of sin(z) - 1 with m = 1 - 1im:
#   nf = newton(:(sin(z)-1),m=1-1im,∂=[-2π/3,-π/3,-π/6,π/6],n=500,N=33,iter=true,ϵ=0.05,cmap="cubehelix")
#   nf |> fatou |> plot
include("fatou_common.jl")
nf = newton(:(sin(z)-1), m=1-1im, ∂=[-2π/3,-π/3,-π/6,π/6], n=500, N=33, iter=true, ϵ=0.05, cmap="cubehelix")
fatou_figure("fatou-generalized-newton", nf; figsize = (620, 500))

# Fatou.jl README.md:76-82, the Mandelbrot set coloured by exp(-|z_N|):
#   mandelbrot(:(z^2+c),n=800,N=20,∂=[-1.91,0.51,-1.21,1.21],cmap="gist_earth") |> fatou |> plot
include("fatou_common.jl")
K = mandelbrot(:(z^2+c), n=800, N=20, ∂=[-1.91,0.51,-1.21,1.21], cmap="gist_earth")
fatou_figure("fatou-mandelbrot", K; figsize = (600, 500))

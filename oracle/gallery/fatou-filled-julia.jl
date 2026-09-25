# Fatou.jl README.md:66-74, the filled Julia set of z² + (-0.06 + 0.67im):
#   nf = juliafill(:(z^2+$c),∂=[-1.5,1.5,-1,1],N=80,n=1501,cmap="gnuplot",iter=true)
#   plot(fatou(nf), bare=true)
include("fatou_common.jl")
c = -0.06 + 0.67im
nf = juliafill(:(z^2+$c), ∂=[-1.5,1.5,-1,1], N=80, n=1501, cmap="gnuplot", iter=true)
fatou_figure("fatou-filled-julia", nf; figsize = (640, 440), bare = true)

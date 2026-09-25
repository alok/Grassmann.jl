# Grassmann.jl README.md:271-285 (docs/src/algebra.md:1265-1279, paper/img/plane-3.png),
# a versor outermorphism field on the Euclidean plane:
#   basis"2"
#   streamplot(vectorfield(exp((π/4)*v12/2)),-1.5..1.5,-1.5..1.5)
include("grassmann_common.jl")
basis"2"
plane_figure("grassmann-plane-3", exp((π/4)*v12/2))

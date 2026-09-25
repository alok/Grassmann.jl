# Grassmann.jl README.md:271-285 (docs/src/algebra.md:1265-1279, paper/img/plane-2.png),
# a versor outermorphism field on the Euclidean plane:
#   basis"2"
#   streamplot(vectorfield(exp((π/2)*v12/2)),-1.5..1.5,-1.5..1.5)
include("grassmann_common.jl")
basis"2"
plane_figure("grassmann-plane-2", exp((π/2)*v12/2))

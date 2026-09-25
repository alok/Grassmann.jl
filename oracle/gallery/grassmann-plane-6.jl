# Grassmann.jl README.md:271-285 (docs/src/algebra.md:1265-1279, paper/img/plane-6.png),
# a versor outermorphism field on the hyperbolic plane:
#   @basis S"+-"
#   streamplot(vectorfield(v1*exp((π/4)*v12/2)),-1.5..1.5,-1.5..1.5)
include("grassmann_common.jl")
@basis S"+-"
plane_figure("grassmann-plane-6", v1*exp((π/4)*v12/2))

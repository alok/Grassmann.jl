# Wilkinson.jl `plot(PolynomialComparison(:((2x - 1) * (3x + 2))))` (src/polynomial.jl:96-133):
# the input differs from all three REDUCE forms (`extra`), so the figure also shows the
# "original" bound and actual error.
include("wilkinson_common.jl")
wilkinson_figure("wilkinson-product", :((2x - 1) * (3x + 2)))

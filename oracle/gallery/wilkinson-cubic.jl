# Wilkinson.jl `plot(PolynomialComparison(:(x^3 - 6x^2 + 11x - 6)))` (src/polynomial.jl:96-133):
# REDUCE's rounded factorization differs from the exact one here (`rxtra`), so the figure also
# shows the "approx" bound and actual error.
include("wilkinson_common.jl")
wilkinson_figure("wilkinson-cubic", :(x^3 - 6x^2 + 11x - 6))

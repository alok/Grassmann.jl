# Wilkinson.jl `plot(PolynomialComparison(:((x-2)^9)))` (src/polynomial.jl:96-133): the
# Stieltjes error bounds and the actual errors of the expanded, Horner and factored forms of
# (x-2)^9, relative to the BigFloat bound of the optimal form.
include("wilkinson_common.jl")
wilkinson_figure("wilkinson-x-2-pow-9", :((x - 2)^9))

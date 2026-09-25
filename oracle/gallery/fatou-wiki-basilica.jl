# Fatou.jl wiki, Explore-Fatou-sets-&-fractals.md, example orbit example (3): the basilica z^2 - 1 (the wiki passes the string "z^2-1"; parse(::String) is gone, so an Expr):
#   nf = juliafill(:(z^2-1), ∂=[-2,2], iter=true, n=800); nf |> fatou |> plot
include("fatou_common.jl")
nf = juliafill(:(z^2-1), ∂=[-2,2], iter=true, n=800)
fatou_figure("fatou-wiki-basilica", nf; figsize = (620, 500))

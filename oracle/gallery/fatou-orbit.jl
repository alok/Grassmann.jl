# Fatou.jl README.md:58-64, the cobweb orbit of x ↦ x² - 0.67:
#   juliafill(:(z^2-0.67),∂=[-1.25,1.5],x0=1.25,orbit=17,depth=3,n=147) |> orbit
# The data is Fatou's own `real_orb` (src/orbitplot.jl:23-54); the figure follows the PyPlot
# backend (ext/PyPlotExt.jl:42-73) with Makie's palette: y = x dashed black, ϕ and its
# compositions, the red cobweb, the orbit as a gray dotted time series with × markers.
include("common.jl")
using Fatou
K = juliafill(:(z^2-0.67), ∂=[-1.25,1.5], x0=1.25, orbit=17, depth=3, n=147)
bi = convert(Array{Float64}, [K.Ω.∂[1:2]..., K.x0]')
x, N, N2, orb, bis = Fatou.real_orb(K.E, z -> K.F(z, 0), bi, K.orbit, K.depth, Int(K.Ω.n))
ylim = [min(1.07minimum(N[:, 2]), 0), max(1.07maximum(N[:, 2]), 0)]
dumpdata("fatou-orbit", Dict("x" => collect(x), "N_cols" => [N[:, j] for j in 1:size(N, 2)], "N2" => N2,
    "cobweb_x" => orb[:, 1], "cobweb_y" => orb[:, 2], "ylim" => ylim))
title = "x ↦ $(K.E), IC: x₀ = $(bis[3]), n∈0:$(K.orbit)"
fig = Figure(size = (640, 480))
ax = Axis(fig[1, 1], title = title)
lines!(ax, x, N[:, 1], color = :black, linestyle = :dash, label = "y=x")
lines!(ax, x, N[:, 2], label = "ϕ(x)")
lines!(ax, orb[:, 1], orb[:, 2], color = :red, label = "(xₙ,ϕ(xₙ))")
for h in 3:K.depth+1
    lines!(ax, x, N[:, h], linewidth = 1, label = "ϕ^$(h-1)(x)")
end
ran = range(bi[1], bi[2], length = length(N2))
lines!(ax, ran, N2, color = :gray, linestyle = :dot, linewidth = 1, label = "ϕ(x₀:$(K.orbit))")
scatter!(ax, ran, N2, color = :gray, marker = :xcross)
xlims!(ax, bi[1], bi[2]); ylims!(ax, ylim...)
axislegend(ax, position = :ct)
savefig("fatou-orbit", fig)

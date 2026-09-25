# Fatou.jl README rasters: compute `fatou(K)`, dump its statistics, and render it the way
# `plot(K)` (PyPlot `imshow(extent = bounds)`, `ext/PyPlotExt.jl:19-40`) lays it out, with
# CairoMakie: a heatmap over the bounds with DataAspect, the plain-text `String(K)` title,
# the Newton y-label and a colorbar unless `bare`.
include("common.jl")
using Fatou

function fatou_figure(name, K; figsize, bare = false)
    S = fatou(K)
    it = Int.(S.iter)
    hist = zeros(Int, Int(K.N) + 1)
    for v in it; hist[v+1] += 1; end
    mix = S.mix
    dumpdata(name, Dict("rows" => size(it, 1), "cols" => size(it, 2), "hist" => hist, "fnv" => fnv1a16(S.iter),
        "mix_nan" => count(isnan, mix), "mix_sum" => sum(filter(isfinite, mix)),
        "mix_abs_sum" => sum(abs, filter(isfinite, mix)), "title" => String(S)))
    Z = K.iter ? Float64.(S.iter) : mix          # rows × cols, row 1 = top (y = ∂[4])
    ∂ = K.Ω.∂
    fig = Figure(size = figsize)
    ylabel = K.newt ? "Fatou set: z ↦ z-m×f(z)/f'(z)" : ""
    ax = Axis(fig[1, 1], title = bare ? "" : String(S), ylabel = ylabel, aspect = DataAspect())
    # cell edges exactly at the bounds, like `imshow(extent = bounds)`
    xe = range(∂[1], ∂[2], length = size(Z, 2) + 1)
    ye = range(∂[3], ∂[4], length = size(Z, 1) + 1)
    hm = heatmap!(ax, xe, ye, permutedims(reverse(Z, dims = 1)), colormap = Symbol(K.cmap))
    bare || Colorbar(fig[1, 2], hm)
    savefig(name, fig)
end

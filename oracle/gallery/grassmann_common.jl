# Grassmann README figures: the curve and streamplot helpers shared by
# oracle/gallery/grassmann-*.jl.
include("common.jl")
using Grassmann, LinearAlgebra

"FNV-1a (64-bit) over the Float32 bit patterns of the coordinates (NaN as 0x7fc00000)."
function fnv1a32(pts)
    h = 0xcbf29ce484222325
    for p in pts, x in p
        b = isnan(x) ? 0x7fc00000 : reinterpret(UInt32, Float32(x))
        for s in (0, 8, 16, 24)
            h = (h ⊻ UInt64((b >> s) & 0xff)) * 0x100000001b3
        end
    end
    "0x" * string(h, base = 16, pad = 16)
end

"""
Dump a sampled 3D curve (Julia `V(…).(points(f))`): the number of points, every 64th point,
and the coordinate sums over all points.
"""
function dump_curve(name, pts)
    xs = [Float64(p[1]) for p in pts]; ys = [Float64(p[2]) for p in pts]; zs = [Float64(p[3]) for p in pts]
    dumpdata(name, Dict("n" => length(pts), "stride" => 64,
        "x" => every(xs, 64), "y" => every(ys, 64), "z" => every(zs, 64),
        "sum" => [sum(xs), sum(ys), sum(zs)], "sumabs" => [sum(abs, xs), sum(abs, ys), sum(abs, zs)]))
end

"A README curve figure: the points as one polyline in an `Axis3` (Makie's default look)."
function curve_figure(name, pts; size = (600, 500))
    fig = Figure(size = size)
    ax = Axis3(fig[1, 1])
    lines!(ax, pts)
    savefig(name, fig)
end

"""
Run Makie's own `streamplot_impl` (the data `streamplot` draws) and dump it: counts, every
arrow, every `stride`-th line point (Float32 values) and a hash of all line points.
"""
function dump_stream(name, f, rect, gridsize; stride = 4)
    ap, ad, lp, ac, lc = Makie.streamplot_impl(Point, f, rect, gridsize, 0.01, 500, 1.0, norm)
    N = length(first(ap))
    # Float32 values in their shortest decimal form (JSON.jl prints a Float32 as such)
    j32(x) = isfinite(x) ? Float32(x) : string(Float32(x))
    flat(v, k) = [j32(p[i]) for p in v[1:k:end] for i in 1:N]
    dumpdata(name, Dict("dim" => N, "n_arrows" => length(ap), "n_points" => length(lp),
        "n_nan" => count(p -> isnan(p[1]), lp), "stride" => stride,
        "arrow_pos" => flat(ap, 1), "arrow_dir" => flat(ad, 1), "line_points" => flat(lp, stride),
        "line_fnv" => fnv1a32(lp), "arrow_color" => [j32(c) for c in ac]))
    println(name, ": ", length(ap), " arrows, ", length(lp), " line points")
end

"A README plane figure: `streamplot(vectorfield(t), -1.5..1.5, -1.5..1.5)` and its data."
function plane_figure(name, t)
    f = vectorfield(t)
    dump_stream(name, f, Rect2d(-1.5, -1.5, 3.0, 3.0), (32, 32))
    fig = Figure(size = (600, 450))
    ax = Axis(fig[1, 1])
    streamplot!(ax, f, -1.5 .. 1.5, -1.5 .. 1.5)
    savefig(name, fig)
end

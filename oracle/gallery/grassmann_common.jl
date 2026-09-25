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

# ---- paper graphs: the LightGraphsExt emulation (ext/LightGraphsExt.jl:19-48) with an
# ordered, de-duplicated edge list (`add_edge!` into a SimpleDiGraph)
function sdg_term!(E, x)
    ind = (signbit(value(x)) ? reverse : identity)(Grassmann.indices(basis(x)))
    if Grassmann.rank(x) == 2
        e = (ind[1], ind[2]); e ∉ E && push!(E, e)
    else
        sdg!(E, ∂(x))
    end
    E
end
function sdg!(E, x::Chain{V}) where V
    N, G = mdims(V), Grassmann.rank(x)
    ib = Grassmann.indexbasis(N, G)
    for k in 1:Grassmann.binomial(N, G)
        if !iszero(x.v[k])
            B = Grassmann.symmetricmask(V, ib[k], ib[k])[1]
            count_ones(B) ≠ 1 && sdg_term!(E, x.v[k] * Grassmann.getbasis(V, B))
        end
    end
    E
end
function sdg!(E, x::Multivector{V}) where V
    N = mdims(V)
    for i in 2:N
        R = Grassmann.binomsum(N, i); ib = Grassmann.indexbasis(N, i)
        for k in 1:Grassmann.binomial(N, i)
            if !iszero(x.v[k+R])
                B = Grassmann.symmetricmask(V, ib[k], ib[k])[1]
                count_ones(B) ≠ 1 && sdg_term!(E, x.v[k+R] * Grassmann.getbasis(V, B))
            end
        end
    end
    E
end
sdg!(E, x::Grassmann.TensorTerm) = sdg_term!(E, x)

"""
A paper graph figure: GraphPlot's `circular_layout` drawn y-down (vertex k at
(cos θ, -sin θ), θ = 2π(k-1)/n), grey disks with labels, light edges with grey arrowheads;
disks and heads are data-space polygons, as in the Lean render.
"""
function graph_figure(name, x, expr)
    n = mdims(Manifold(x))
    E = sdg!(Tuple{Int,Int}[], x)
    dumpdata(name, Dict("expr" => expr, "nv" => n, "edges" => [[a, b] for (a, b) in E]))
    pos(k) = (θ = 2π * (k - 1) / n; (cos(θ), -sin(θ)))
    r, L, W = 0.12, 0.11, 0.045
    fig = Figure(size = (500, 500))
    ax = Axis(fig[1, 1], aspect = DataAspect())
    hidedecorations!(ax); hidespines!(ax); limits!(ax, -1.3, 1.3, -1.3, 1.3)
    for (a, b) in E
        (px, py), (qx, qy) = pos(a), pos(b)
        d = hypot(qx - px, qy - py); ux, uy = (qx - px) / d, (qy - py) / d
        lines!(ax, [px + r * ux, qx - (r + L) * ux], [py + r * uy, qy - (r + L) * uy], color = "#D3D3D3", linewidth = 3)
        tx, ty = qx - r * ux, qy - r * uy; bx, by = tx - L * ux, ty - L * uy
        poly!(ax, Point2f[(tx, ty), (bx - W * uy, by + W * ux), (bx + W * uy, by - W * ux)], color = :gray)
    end
    for k in 1:n
        x0, y0 = pos(k)
        poly!(ax, Point2f[(x0 + r * cos(2π * i / 48), y0 + r * sin(2π * i / 48)) for i in 0:47], color = "#A9A9A9")
        text!(ax, x0, y0, text = string(k), fontsize = 18, align = (:center, :center))
    end
    savefig(name, fig)
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

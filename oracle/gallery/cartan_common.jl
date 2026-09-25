# Cartan.jl figures (docs/src/fiber.md sessions, docs/src/plot.md Makie gallery): helpers
# shared by oracle/gallery/cartan-*.jl. Every figure is drawn by Cartan's own Makie methods
# (ext/MakieExt.jl); the scripts dump the plotted data for the Lean port (GrassmannPlot) to
# compare, via the plot objects Makie built wherever possible.
include("grassmann_common.jl")
using Cartan

# Cartan 0.4.16 cannot build any multi-dimensional XParameter (docs/port-notes/cartan-core.md
# §8.6 B1: the MeshTopology split dropped `XTopology(::ProductSpace)`); restore the pre-split
# method (the same shim as oracle/cartan/gen.jl), so the documented examples run.
const MT = Cartan.MeshTopology
for fun in (:Open,:Cylinder,:Mobius,:Wing,:Mirror,:Clamped,:Torus,:Hopf,:Klein,:Cone,:Tube,:Ball,:Sphere,:Geographic)
    top = Symbol(fun,:Topology)
    @eval MT.$top(p::Cartan.ProductSpace) = MT.$top(Cartan.PointArray(p))
end

"The coordinates of the fibers of a field, as vectors of Float64 (column-major order)."
coords(t) = [Float64.(collect(Grassmann.value(p))) for p in vec(fiber(t))]

"Sums and a sample (every `k`-th entry) of a float vector."
summary_of(v, k) = Dict("n" => length(v), "stride" => k, "sample" => jf(every(v, k)),
    "sum" => jf(sum(v)), "sumabs" => jf(sum(abs, v)))

"""
Dump a curve field and its `speed` colouring (what `lines(t)` draws, `MakieExt.jl:171-176`):
the coordinates of every `k`-th point, the speed of every `k`-th point, and sums over all.
"""
function dump_speed_curve(name, curve; k = 64, extra = Dict())
    cs = coords(curve)
    d = length(cs[1])
    s = Float64.(vec(fiber(speed(curve))))
    out = Dict{String,Any}("dim" => d, "speed" => summary_of(s, k))
    for i in 1:d
        out["x$i"] = summary_of([c[i] for c in cs], k)
    end
    merge!(out, extra)
    dumpdata(name, out)
end

"""
A `fiber.md` streamplot of a grid field (`streamplot(tf; args...)`, `MakieExt.jl:527-533`):
dump Makie's `streamplot_impl` of the interpolated field `p ↦ Point(tf(Chain(p...)))` over the box
of the grid axes (the data the plot draws), then render with Cartan's method.
"""
function field_stream(name, tf, gridsize; size = (600, 450), axis = NamedTuple(), kw...)
    ax1 = points(tf).v
    lo = [first(a) for a in ax1]; hi = [last(a) for a in ax1]
    rect = length(ax1) == 2 ? Rect2d(lo[1], lo[2], hi[1] - lo[1], hi[2] - lo[2]) :
        Rect3d(lo[1], lo[2], lo[3], hi[1] - lo[1], hi[2] - lo[2], hi[3] - lo[3])
    f = p -> Makie.Point(tf(Chain(p.data...)))
    dump_stream(name, f, rect, gridsize)
    fig, ax, pl = streamplot(tf; axis = axis, figure = (size = size,), kw...)
    savefig(name, fig)
end

"Dump the segment points of a (single) wireframe/linesegments plot object: every `k`-th point and sums."
function dump_segments(name, pts; k = 16, extra = Dict())
    d = length(pts[1])
    out = Dict{String,Any}("n" => length(pts), "dim" => d)
    for i in 1:d
        out["x$i"] = summary_of([Float64(p[i]) for p in pts], k)
    end
    merge!(out, extra)
    dumpdata(name, out)
end

# Julia twin of gallery/PlotBench.lean (`plot` suite): the hot paths behind Cartan's Makie
# methods, on the gallery's fields (oracle/gallery/cartan-riemann-torus.jl, cartan-bivector-1.jl,
# cartan-conformal-stream-1.jl), measured by the shared harness (oracle/bench/harness.jl).
#   julia --startup-file=no --project=oracle oracle/gallery/bench.jl [--json out.json] [--smoke]
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "..", "bench", "harness.jl"))
using .BenchHarness
using Grassmann, Cartan, CairoMakie, LinearAlgebra

module PTRiemann
using Grassmann, Cartan
pts = TensorField(-2*pi:0.0001:2*pi)
@basis S"∞+++"
f(t) = ↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3))
const curve = V(2,3,4).(f.(pts))
end

module PTPlane
using Grassmann, Cartan
basis"2"
vdom = TensorField(ProductSpace{V}(-1.5:0.1:1.5,-1.5:0.1:1.5))
const field = tensorfield(exp(pi*v12/2)).(vdom)
end

module PTConformal
using Grassmann, Cartan
@basis S"∞+++"
vdom1 = TensorField(ProductSpace{V(1,2,3)}(-1.5:0.1:1.5,-1.5:0.1:1.5,-1.5:0.1:1.5))
const field = tensorfield(exp((pi/4)*(v12+v∞3)),V(2,3,4)).(vdom1)
end

function pt_sweep2(tf, n)
    acc = 0.0
    for k in 0:n-1
        z = tf(Chain(-1.5 + 3 * k / 1000, -1.4 + 2.9 * k / 1000))
        acc += z[1]
    end
    acc
end

function pt_stream(tf, rect, gridsize)
    f = p -> Makie.Point(tf(Chain(p.data...)))
    ap, ad, lp, ac, lc = Makie.streamplot_impl(Point, f, rect, gridsize, 0.01, 500, 1.0, norm)
    length(lp)
end

CairoMakie.activate!(px_per_unit = 1)
"Render a figure to PNG bytes in memory (CairoMakie, px_per_unit = 1); the check is the pixel count."
pt_render(fig, npx) = (io = IOBuffer(); show(io, MIME"image/png"(), fig); position(io) > 0 ? npx : 0)

function suite_plot(ctx)
    c = PTRiemann.curve
    bench!(i -> sum(fiber(speed(blackbox(i, c)))), ctx, "speed_riemann"; ops = 125664, param = "n=125664")
    b = PTPlane.field
    bench!(i -> pt_sweep2(blackbox(i, b), 1000), ctx, "eval2_bivector"; ops = 1000, param = "31x31, 1000 points")
    bench!(i -> pt_stream(blackbox(i, b), Rect2d(-1.5, -1.5, 3.0, 3.0), (32, 32)), ctx, "stream2_bivector";
        param = "31x31, gridsize 32x32")
    cf = PTConformal.field
    bench!(i -> pt_stream(blackbox(i, cf), Rect3d(-1.5, -1.5, -1.5, 3.0, 3.0, 3.0), (10, 10, 10)), ctx,
        "stream3_conformal"; param = "31^3, gridsize 10^3")
    # whole figures: Cartan's method, then CairoMakie's raster
    bench!(i -> pt_render(lines(blackbox(i, c); axis = (type = Axis3,), figure = (size = (600, 500),)).figure, 300000), ctx,
        "figure_riemann"; param = "lines, 125664 points, 600x500 PNG")
    bench!(i -> pt_render(streamplot(blackbox(i, b)).figure, 270000), ctx, "figure_bivector"; param = "streamplot, 600x450 PNG")
end

register!("plot", suite_plot)
(abspath(PROGRAM_FILE) == @__FILE__) && main_suites(["plot" => suite_plot])

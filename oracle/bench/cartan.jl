# Julia twin of Bench/Cartan.lean (`cartan` suite): tensor-field kernels on a 1000×1000 grid
# (smoke 20×20) and a 10⁶-point interval. ns per grid point. The check of a field is
# data[1] + data[n÷2+1] + data[n] of its flat fibers (Lean `fieldCheck`).
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "harness.jl"))
using .BenchHarness
using Grassmann, Cartan
import LinearAlgebra
const CMT = Cartan.MeshTopology
# Cartan 0.4.16 builds `TorusTopology(::ProductSpace)`, which MeshTopology 0.1.0 lacks (defect B1
# of oracle/cartan/defects.toml); the intended method goes through the point array's size.
CMT.TorusTopology(p::Cartan.ProductSpace) = CMT.TorusTopology(Cartan.PointArray(p))

cflat(x::AbstractVector{<:Real}) = x
cflat(x::AbstractArray{<:Real}) = vec(x)
cflat(x::AbstractArray) = reinterpret(Float64, vec(collect(x)))
function ccheck(t::TensorField)
    a = cflat(fiber(t))
    n = length(a)
    n == 0 ? 0.0 : Float64(a[1] + a[n÷2+1] + a[n])
end
ccheck(x::Real) = Float64(x)

ctorus(x) = (r = 3 + cos(x[2]); Chain(r * cos(x[1]), r * sin(x[1]), sin(x[2])))

function suite_cartan(ctx)
    n = sized(ctx, 1000, 20)
    pts = n * n
    p = "$(n)×$(n)"
    g = TensorField(ProductSpace(range(0, 1, length = n), range(0, 1, length = n)))
    line = range(0, 10, length = pts)
    lp = "$pts"
    bench!(i -> ccheck((x -> Chain(x[1], x[2], 1.0)).(blackbox(i, g))), ctx, "tabulate_chain3"; ops = pts, param = p)
    bench!(i -> ccheck((x -> Chain(1.0, -x[2], x[1])).(blackbox(i, g))), ctx, "tabulate_w"; ops = pts, param = p)
    bench!(i -> ccheck((x -> x[1] + 2x[2]).(blackbox(i, g))), ctx, "tabulate_scalar"; ops = pts, param = p)
    bench!(i -> ccheck((x -> Chain(x[1], x[2], 1.0)).(blackbox(i, g))), ctx, "tabulate2_chain3"; ops = pts, param = p)
    bench!(i -> ccheck((x -> x[1] + 2x[2]).(blackbox(i, g))), ctx, "tabulate2_scalar"; ops = pts, param = p)
    bench!(i -> ccheck(TensorField(blackbox(i, line))), ctx, "identity_range"; ops = pts, param = lp)
    v = (x -> Chain(x[1], x[2], 1.0)).(g)
    w = (x -> Chain(1.0, -x[2], x[1])).(g)
    a = (x -> x[1] + 2x[2]).(g)
    t = TensorField(line)
    s = sin(t)
    bench!(i -> ccheck(sin(blackbox(i, t))), ctx, "sin"; ops = pts, param = lp)
    bench!(i -> ccheck(exp(blackbox(i, t))), ctx, "exp"; ops = pts, param = lp)
    bench!(i -> ccheck(blackbox(i, t) + s), ctx, "add_ts"; ops = pts, param = lp)
    bench!(i -> ccheck(blackbox(i, s) * 2), ctx, "scale_s2"; ops = pts, param = lp)
    bench!(i -> ccheck(blackbox(i, s) * t), ctx, "mul_st"; ops = pts, param = lp)
    bench!(i -> ccheck(blackbox(i, v) + w), ctx, "add_vw"; ops = pts, param = p)
    bench!(i -> ccheck(2 * blackbox(i, v)), ctx, "scale_2v"; ops = pts, param = p)
    bench!(i -> ccheck(blackbox(i, a) * v), ctx, "mul_av"; ops = pts, param = p)
    bench!(i -> ccheck(blackbox(i, v) ∧ w), ctx, "wedge_vw"; ops = pts, param = p)
    bench!(i -> ccheck(blackbox(i, v) * w), ctx, "geom_vw"; ops = pts, param = p)
    bench!(i -> ccheck(blackbox(i, v) ⋅ w), ctx, "dot_vw"; ops = pts, param = p)
    bench!(i -> ccheck(⋆(blackbox(i, v))), ctx, "hodge_v"; ops = pts, param = p)
    bench!(i -> ccheck(LinearAlgebra.norm(blackbox(i, v))), ctx, "norm_v"; ops = pts, param = p)
    h = n ÷ 2
    bench!(i -> ccheck(Cartan.resample(blackbox(i, a), (h, h))), ctx, "resample_a"; ops = h * h, param = "$(h)×$(h)")
    bench!(i -> ccheck(sum(blackbox(i, s))), ctx, "sum_s"; ops = pts, param = lp)
    bench!(i -> ccheck(supnorm(blackbox(i, v))), ctx, "supnorm_v"; ops = pts, param = p)
    T = TorusParameter(n, n)
    bench!(i -> ccheck(ctorus.(blackbox(i, T))), ctx, "torus"; ops = pts, param = p)
end

register!("cartan", suite_cartan)
(abspath(PROGRAM_FILE) == @__FILE__) && main_suites(["cartan" => suite_cartan])

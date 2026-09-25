# Wilkinson.jl `plot(::PolynomialComparison)` (src/polynomial.jl:96-133), redrawn with CairoMakie.
#
# Wilkinson itself does not load (its PyPlot/Conda dependency fails to precompile), so, as in
# oracle/wilkinson/gen.jl, its numeric kernels (src/Wilkinson.jl:17-103, src/polynomial.jl:42-68)
# are copied verbatim and SyntaxTree and Reduce are loaded through their package ids. The
# series, colours and line styles are those of the PyPlot figure; the LaTeX labels are written
# as plain text. Upstream `legend(leg)` assigns its labels by position and so mislabels the
# lines when the original form is drawn (`extra`), and spells "orignal": here every line
# carries its own label (a documented defect fixed, not replicated).
include("common.jl")
using Printf
const SyntaxTree = Base.require(Base.PkgId(Base.UUID("a4af3ec5-f8ac-5fed-a759-c2e80b4d74cb"), "SyntaxTree"))
const Reduce = Base.require(Base.PkgId(Base.UUID("93e0c654-6965-5f22-aba9-9c1ae6b3c259"), "Reduce"))
import .SyntaxTree: callcount

# ---- kernels copied from Wilkinson.jl
function floatset(T::DataType, N; scale = x -> x)
    l = scale(eps(T))
    u = scale(prevfloat(T(Inf)))
    return l:(u-l)/(N-1):u
end
function Ω(p::Array{<:Number,1})
    n = length(p) - 1
    for k ∈ 1:length(p)
        p[k] == Inf && (n = k - 1; break)
    end
    return n
end
genabs(expr, T::DataType) = SyntaxTree.genlatest(SyntaxTree.abs(SyntaxTree.sub(T, expr)), [:x])
genalg(expr, T::DataType) = SyntaxTree.genlatest(SyntaxTree.sub(T, expr), [:x])
function stieltjes(set::AbstractRange, expr, T::DataType, T2::DataType = T; logi = log, expi = exp)
    t = genabs(expr, T)
    sc = collect(set)
    esc = expi.(sc)
    p = t.(esc)
    return Float64.((logi.(abs.(p)) - sc) .+ logi(callcount(expr) * eps(T2)))
end
function exacterr(set::AbstractRange, expr::Array{<:Any,1}, T::DataType; logi = log, expi = exp)
    funs = genalg.(expr[2:end], T)
    push!(funs, genalg(expr[1], BigFloat))
    esc = collect(set)
    sc = expi.(esc)
    bs = funs[end].(sc)
    return [Float64.(logi.(abs.(bs - funs[q].(sc))) - esc) for q ∈ 1:length(funs)-1]
end
function optimal(expr)
    h = Reduce.horner(expr)
    f = Reduce.factor(h)
    eh = SyntaxTree.exprval(h)[1]
    ef = SyntaxTree.exprval(f)[1]
    eo = SyntaxTree.exprval(expr)[1]
    eh ≤ ef ? (eh ≤ eo ? h : expr) : (ef ≤ eo ? f : expr)
end

"The PyPlot colour letters of `plot(::PolynomialComparison)`."
const PYCOLOR = Dict("y" => RGBf(0.75, 0.75, 0), "r" => RGBf(1, 0, 0), "b" => RGBf(0, 0, 1),
                     "g" => RGBf(0, 0.5, 0), "k" => RGBf(0, 0, 0))

"""
`PolynomialComparison(j)` (src/polynomial.jl:42-68) and its `plot` (src/polynomial.jl:96-133):
render docs/gallery/julia/<name>.png and dump the plotted series.
"""
function wilkinson_figure(name, j; T = Float64, N = 3000)
    set = floatset(T, N; scale = log)
    Reduce.Rational(false)
    exprs = Any[optimal(j), Reduce.rcall(j, :expand), Reduce.rcall(j, :horner), Reduce.rcall(j, :factor),
                Reduce.rcall(j, :factor, :rounded)]
    extra = (j ≠ exprs[2]) & (j ≠ exprs[3]) & (j ≠ exprs[4])
    rxtra = exprs[4] ≠ exprs[5]
    !rxtra && deleteat!(exprs, 5)
    extra && push!(exprs, j)
    stj = [stieltjes(set, e, T) for e ∈ exprs[2:end]]
    best = stieltjes(set, exprs[1], BigFloat, T)
    EE = exacterr(set, exprs, T)
    # the series of plot(), in drawing order: (label, colour, actual?, values)
    series = Tuple{String,String,Bool,Vector{Float64}}[]
    rel(v) = v - best
    rxtra && push!(series, ("approx (bound)", "y", false, rel(stj[4])))
    push!(series, ("expand (bound)", "r", false, rel(stj[1])), ("horner (bound)", "b", false, rel(stj[2])),
          ("factor (bound)", "g", false, rel(stj[3])))
    rxtra && push!(series, ("approx (actual)", "y", true, rel(EE[4])))
    extra && push!(series, ("original (bound)", "k", false, rel(stj[end])), ("original (actual)", "k", true, rel(EE[end])))
    push!(series, ("expand (actual)", "r", true, rel(EE[1])), ("horner (actual)", "b", true, rel(EE[2])),
          ("factor (actual)", "g", true, rel(EE[3])))
    sc = collect(set)
    xlabel = "log|x|, Δ=$(@sprintf("%.2e", Float64(set.step)))"
    ylabel = "log |[alg(f)](x)−f(x)| / δ(f,x,2^$(Int(log(2, eps(BigFloat))))),  log δ(f,x,2^$(Int(log(2, eps(T)))))/δ(f,x,2^$(Int(log(2, eps(BigFloat)))))"
    finite(v) = [isfinite(y) ? y : NaN for y in v]
    dumpdata(name, Dict("expr" => string(j), "forms" => string.(exprs), "extra" => extra, "rxtra" => rxtra,
        "x" => every(sc, 10), "labels" => [s[1] for s in series], "stride" => 10,
        "series" => [jf(every(s[4], 10)) for s in series],
        "sums" => [sum(filter(isfinite, s[4])) for s in series], "xlabel" => xlabel))
    fig = Figure(size = (820, 480))
    ax = Axis(fig[1, 1], xlabel = xlabel, ylabel = ylabel, title = string(j), ylabelsize = 11)
    for (label, c, actual, ys) in series
        if actual
            lines!(ax, sc, finite(ys), color = PYCOLOR[c], linewidth = 0.7, linestyle = :dash, label = label)
            scatter!(ax, sc, finite(ys), color = PYCOLOR[c], markersize = 2)
        else
            lines!(ax, sc, finite(ys), color = PYCOLOR[c], linewidth = 0.7, label = label)
        end
    end
    Legend(fig[1, 2], ax)
    savefig(name, fig)
end

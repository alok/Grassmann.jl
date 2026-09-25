# Julia twin of Bench/JuliaBase.lean (`juliabase` suite): Base's float printing and parsing,
# pairwise sum, TwicePrecision ranges, round(digits) and ComplexF64 kernels on identical inputs.
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "harness.jl"))
using .BenchHarness

jb_wordfloat(w::UInt64) = reinterpret(Float64, (w & 0x800FFFFFFFFFFFFF) | ((UInt64(991) + ((w >> 52) & 63)) << 52))

function jb_totalbytes(f::F, xs::Vector{Float64}) where {F}
    acc = 0
    for x in xs
        acc += sizeof(f(x))
    end
    acc
end
jb_compact(x) = sprint(show, x; context = :compact => true)
function jb_sumparse(ss::Vector{String})
    acc = 0.0
    for s in ss
        acc += parse(Float64, s)
    end
    acc
end
function jb_summap(f::F, xs::Vector{Float64}) where {F}
    acc = 0.0
    for x in xs
        acc += f(x)
    end
    acc
end
function jb_sumcomplex(f::F, zs::Vector{Float64}) where {F}
    acc = 0.0
    for i in 1:2:length(zs)-1
        w = f(ComplexF64(zs[i], zs[i+1]))
        acc += real(w) + imag(w)
    end
    acc
end
function jb_sumdiv(zs::Vector{Float64})
    acc = 0.0
    for i in 1:4:length(zs)-3
        q = ComplexF64(zs[i], zs[i+1]) / ComplexF64(zs[i+2], zs[i+3])
        acc += real(q) + imag(q)
    end
    acc
end
function jb_sumrange(r)
    acc = 0.0
    for i in 1:length(r)
        acc += r[i]
    end
    acc
end
jb_round3(x) = round(x; digits = 3)

function suite_juliabase(ctx)
    m = 1000
    xs = jb_wordfloat.(randwords(m, UInt64(0x5EED)))
    pm = "n=$m"
    bench!(i -> jb_totalbytes(string, blackbox(i, xs)), ctx, "show_float"; ops = m, param = pm)
    bench!(i -> jb_totalbytes(jb_compact, blackbox(i, xs)), ctx, "show_float_compact"; ops = m, param = pm)
    strs = string.(xs)
    bench!(i -> jb_sumparse(blackbox(i, strs)), ctx, "parse_float"; ops = m, param = pm)
    n = sized(ctx, 100000, 1000)
    ys = randfloats(n, UInt64(0xB0B), -1.0, 1.0)
    bench!(i -> sum(blackbox(i, ys)), ctx, "sum_f64"; ops = n, param = "n=$n")
    r = 10000
    pr = "n=$r"
    bench!(i -> collect(range(0.0, 1.0; length = blackbox(i, r))), ctx, "range_collect"; ops = r, param = pr)
    bench!(i -> collect(blackbox(i, 0.1):0.1:1000.0), ctx, "colon_collect"; ops = r, param = pr)
    rr = range(0.0, 1.0; length = r)
    bench!(i -> jb_sumrange(blackbox(i, rr)), ctx, "range_getindex"; ops = r, param = pr)
    us = randfloats(m, UInt64(0xF00D), -1000.0, 1000.0)
    bench!(i -> jb_summap(jb_round3, blackbox(i, us)), ctx, "round_digits"; ops = m, param = pm)
    zs = randfloats(2m, UInt64(0xC0FFEE), -10.0, 10.0)
    bench!(i -> jb_sumdiv(blackbox(i, zs)), ctx, "complex_div"; ops = m ÷ 2, param = pm)
    bench!(i -> jb_sumcomplex(sqrt, blackbox(i, zs)), ctx, "complex_sqrt"; ops = m, param = pm)
    bench!(i -> jb_sumcomplex(exp, blackbox(i, zs)), ctx, "complex_exp"; ops = m, param = pm)
    bench!(i -> jb_sumcomplex(log, blackbox(i, zs)), ctx, "complex_log"; ops = m, param = pm)
end

register!("juliabase", suite_juliabase)
(abspath(PROGRAM_FILE) == @__FILE__) && main_suites(["juliabase" => suite_juliabase])

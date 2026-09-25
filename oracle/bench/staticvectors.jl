# Julia twin of Bench/StaticVectors.lean (`staticvectors` suite): Values{n,Float64} operations
# over arrays of 1000 vectors with the same SplitMix64 components.
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "harness.jl"))
using .BenchHarness
using StaticVectors, LinearAlgebra

sv_vecs(k, m, xs) = [Values{k,Float64}(ntuple(j -> xs[(i-1)*k+j], k)) for i in 1:m]
function sv_sumpair(f::F, as, bs) where {F}
    acc = 0.0
    @inbounds for i in eachindex(as)
        acc += f(as[i], bs[i])
    end
    acc
end
function sv_sumone(f::F, as) where {F}
    acc = 0.0
    @inbounds for i in eachindex(as)
        acc += f(as[i])
    end
    acc
end
sv_addall(as::Vector{Values{k,Float64}}) where {k} = sum(foldl(+, as; init = zero(Values{k,Float64})))
sv_cross1(a, b) = cross(a, b)[1]
sv_normalize1(a) = normalize(a)[1]
sv_scale1(a) = (a * 2.5)[1]

function sv_dimcases(ctx, d, m)
    p = "$(m)×$(d)"
    as = sv_vecs(d, m, randfloats(d * m, UInt64(0xA11CE), -1.0, 1.0))
    bs = sv_vecs(d, m, randfloats(d * m, UInt64(0xB0B0), -1.0, 1.0))
    bench!(i -> sv_addall(blackbox(i, as)), ctx, "add$d"; ops = m, param = p)
    bench!(i -> sv_sumpair(dot, blackbox(i, as), bs), ctx, "dot$d"; ops = m, param = p)
    bench!(i -> sv_sumone(norm, blackbox(i, as)), ctx, "norm$d"; ops = m, param = p)
    bench!(i -> sv_sumone(sv_normalize1, blackbox(i, as)), ctx, "normalize$d"; ops = m, param = p)
    bench!(i -> sv_sumone(sv_scale1, blackbox(i, as)), ctx, "scale$d"; ops = m, param = p)
end

function suite_staticvectors(ctx)
    m = 1000
    sv_dimcases(ctx, 3, m)
    as = sv_vecs(3, m, randfloats(3m, UInt64(0xA11CE), -1.0, 1.0))
    bs = sv_vecs(3, m, randfloats(3m, UInt64(0xB0B0), -1.0, 1.0))
    bench!(i -> sv_sumpair(sv_cross1, blackbox(i, as), bs), ctx, "cross3"; ops = m, param = "$(m)×3")
    sv_dimcases(ctx, 16, m)
end

register!("staticvectors", suite_staticvectors)
(abspath(PROGRAM_FILE) == @__FILE__) && main_suites(["staticvectors" => suite_staticvectors])

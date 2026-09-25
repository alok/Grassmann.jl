# Julia twin of Bench/DirectSum.lean (`directsum` suite): blade products, parity, plans, Leibniz
# index tables and blade labels, through Grassmann 0.8 / DirectSum / Leibniz.
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "harness.jl"))
using .BenchHarness
using Grassmann
const ds_Leibniz = Grassmann.Leibniz

ds_weight(x::Submanifold) = 1.0
ds_weight(x::Grassmann.Single) = Float64(sign(Grassmann.value(x)))
ds_weight(x::Grassmann.Zero) = 0.0
ds_weight(x) = Float64(count(!iszero, Grassmann.value(x)))

function ds_mulall(bs::Vector)
    acc = 0.0
    for a in bs, b in bs
        acc += ds_weight(a * b)
    end
    acc
end
function ds_paritycount(s::UInt, n::Int)
    acc = 0
    for a in UInt(0):UInt(n - 1), b in UInt(0):UInt(n - 1)
        acc += Grassmann.parity(8, s, a, b)
    end
    acc
end
ds_bits(x::Submanifold) = UInt(x)
ds_bits(x::Grassmann.Single) = UInt(Grassmann.basis(x))
function ds_plan(bs::Vector, n::Int)
    out = NTuple{4,Int}[]
    for (i, a) in enumerate(bs), (j, b) in enumerate(bs)
        r = a * b
        push!(out, (i, j, ds_Leibniz.basisindex(n, ds_bits(r)), Int(ds_weight(r))))
    end
    length(out)
end
function ds_tables(n::Int)
    ib = ds_Leibniz.indexbasis_calc.(n, 1:n)
    bi = ds_Leibniz.bladeindex_calc.(1:(1<<n)-1, n)
    1 + sum(length, ib) + 1 + length(bi)
end
function ds_sumbasisindex(n::Int)
    acc = 0
    for b in UInt(0):UInt((1 << n) - 1)
        acc += ds_Leibniz.basisindex(n, b)
    end
    acc
end
function ds_labelbytes(bs::Vector)
    acc = 0
    for b in bs
        acc += sizeof(string(b))
    end
    acc
end

function suite_directsum(ctx)
    bench!(i -> ds_paritycount(blackbox(i, UInt(1)), 256), ctx, "parity_R8"; ops = 65536, param = "256²")
    b5 = collect(Λ(Submanifold(ℝ^5)).b)
    bench!(i -> ds_mulall(blackbox(i, b5)), ctx, "blade_mul_R5"; ops = 1024, param = "32²")
    c5 = collect(Λ(Submanifold(S"∞∅+++")).b)
    bench!(i -> ds_mulall(blackbox(i, c5)), ctx, "blade_mul_CGA3"; ops = 1024, param = "32²")
    bench!(i -> ds_plan(blackbox(i, b5), 5), ctx, "plan_mul_R5"; ops = 1024, param = "32²")
    bench!(i -> ds_tables(blackbox(i, 10)), ctx, "index_tables_n10"; param = "n=10")
    bench!(i -> ds_sumbasisindex(blackbox(i, 10)), ctx, "basis_index_n10"; ops = 1024, param = "n=10")
    b10 = collect(Λ(Submanifold(ℝ^10)).b)
    bench!(i -> ds_labelbytes(blackbox(i, b10)), ctx, "blade_show_R10"; ops = 1024, param = "n=10")
end

register!("directsum", suite_directsum)
(abspath(PROGRAM_FILE) == @__FILE__) && main_suites(["directsum" => suite_directsum])

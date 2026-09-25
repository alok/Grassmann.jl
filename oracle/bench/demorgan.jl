# Julia twin of the `demorgan` suite of Bench/Dendriform.lean. Runs in oracle/bench/env2.
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "harness.jl"))
using .BenchHarness
using DeMorgan
import DeMorgan: TruthValues, TruthTable, select

function dm_formulasum(ps)
    acc = 0.0
    for (p, q) in ps
        acc += Float64(((p --> q) <--> ((p ∧ q) ∨ !p)).p)
    end
    acc
end
function dm_table4(vs)
    p, q, r, s = vs
    pq = p ∧ q
    string((pq --> (r ∨ !s)) <--> (!pq ∨ r))
end

function suite_demorgan(ctx)
    m = 1000
    ws = randwords(2m, UInt64(0xDE3))
    ps = [(TruthValues{6}(ws[2i-1]), TruthValues{6}(ws[2i])) for i in 1:m]
    bench!(i -> dm_formulasum(blackbox(i, ps)), ctx, "tv_formula_N6"; ops = m, param = "n=$m")
    names = ["p", "q", "r", "s"]
    vs = [TruthTable{4}(select(5 - k, 4), names[k]) for k in 1:4]
    bench!(i -> dm_table4(blackbox(i, vs)), ctx, "truthtable_N4")
end

register!("demorgan", suite_demorgan)
(abspath(PROGRAM_FILE) == @__FILE__) && main_suites(["demorgan" => suite_demorgan])

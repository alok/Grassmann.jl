# Julia twin of the `dendriform` suite of Bench/Dendriform.lean. Runs in oracle/bench/env2
# (Dendriform conflicts with AbstractAnalysis in the main environment).
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "harness.jl"))
using .BenchHarness
using Dendriform
import Dendriform: Cn

df_trees(d) = [PBTree(d, i) for i in 1:Int(Cn(d))]
function df_pairops(ts)
    acc = 0
    for dx in 1:5, dy in 1:5
        dx + dy <= 6 || continue
        for x in ts[dx+1], y in ts[dy+1]
            acc += Int((x + y).size) + Int((x ⊣ y).size) + Int((x ⊢ y).size)
        end
    end
    acc
end
df_paircount(ts) = sum(length(ts[dx+1]) * length(ts[dy+1]) for dx in 1:5, dy in 1:5 if dx + dy <= 6)

function suite_dendriform(ctx)
    redirect_stdout(devnull) do; Dendriform.Υ(8); end
    bench!(i -> Int((Grove(blackbox(i, 4)) + Grove(3)).size), ctx, "grove_sum_4_3")
    bench!(i -> Int((Grove(blackbox(i, 3)) * Grove(2)).size), ctx, "grove_mul_3_2")
    bench!(i -> Int((Grove(blackbox(i, 4)) ⊣ Grove(3)).size), ctx, "grove_dashv_4_3")
    bench!(i -> Int((Grove(blackbox(i, 4)) ⊢ Grove(3)).size), ctx, "grove_vdash_4_3")
    ts = [df_trees(d) for d in 0:6]
    np = df_paircount(ts)
    bench!(i -> df_pairops(blackbox(i, ts)), ctx, "tree_pairs_d6"; ops = np, param = "$np pairs")
end

register!("dendriform", suite_dendriform)
(abspath(PROGRAM_FILE) == @__FILE__) && main_suites(["dendriform" => suite_dendriform])

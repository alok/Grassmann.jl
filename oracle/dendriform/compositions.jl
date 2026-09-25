# Grove compositions of one degree, in a fresh Julia process (called by gen.jl):
#   julia --startup-file=no --project=<juliaenv2> oracle/dendriform/compositions.jl d
# Julia caches Compose(n) keyed by n only, so results depend on call history
# (port-notes §4.4.9); one process per degree gives the intended semantics.

using Dendriform, JSON3, Random
d = parse(Int, ARGS[1])
Random.seed!(0x5EED + d)
redirect_stdout(devnull) do; Dendriform.Υ(8); end
top = big(2)^Cn(d) - 1
inds = d <= 3 ? collect(1:top) : vcat(big.([1, 2, 3, top]), [rand(1:top) for _ in 1:150])
cases = Any[]
for ind in inds
    tmp = tempname()
    n = open(tmp, "w") do io
        redirect_stdout(() -> grovecomposition(d, ind), io)
    end
    push!(cases, Dict("ind" => string(ind), "count" => n, "text" => read(tmp, String)))
    rm(tmp)
end
open(joinpath(@__DIR__, "..", "golden", "dendriform", "compositions_$d.json"), "w") do io
    JSON3.write(io, Dict("d" => d, "cases" => cases))
end

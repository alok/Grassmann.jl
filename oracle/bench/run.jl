# Run several Julia benchmark suites in one process (used by scripts/bench/run.py).
#
#   julia --startup-file=no --project=<env> oracle/bench/run.jl --include math,juliabase \
#         [--smoke] [--json out.json] [--filter substr]... [suite ...]
#
# Each included file registers its suite; the remaining arguments are the harness CLI.
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "harness.jl"))
using .BenchHarness

let args = copy(ARGS), files = String[]
    k = findfirst(==("--include"), args)
    if k !== nothing
        append!(files, split(args[k+1], ','; keepempty = false))
        deleteat!(args, k:k+1)
    end
    for f in files
        include(joinpath(@__DIR__, endswith(f, ".jl") ? f : f * ".jl"))
    end
    main_suites(copy(BenchHarness.REGISTRY), args)
end

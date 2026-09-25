# oracle/run_suite.jl: run one oracle suite (all shards, or the named ones) in this process.
#
#   julia --startup-file=no --project=oracle oracle/run_suite.jl <suite> --list
#   julia --startup-file=no --project=oracle oracle/run_suite.jl <suite> [shard ...]
#
# Each shard is written to oracle/golden/<suite>/<shard>.json. The per-suite manifest
# oracle/golden/<suite>.json is written by oracle/generate_all.jl, which also runs every shard
# in a fresh process (Julia's regressive/interior caches are keyed without the tangent
# parameters, so spaces must not share a process; see defects.toml `cache-key-collision`).

include(joinpath(@__DIR__, "common.jl"))

length(ARGS) >= 1 || error("usage: run_suite.jl <suite> [--list | shard ...]")
const SUITE = ARGS[1]
include(joinpath(@__DIR__, "suites", SUITE * ".jl"))

if "--list" in ARGS
    foreach(println, shards())
else
    const DEFECTS = load_defects()
    todo = length(ARGS) > 1 ? ARGS[2:end] : shards()
    for sh in todo
        sh in shards() || error("unknown shard `$sh` for suite `$SUITE`")
        t0 = time()
        top = build(sh, DEFECTS)
        path = write_golden(joinpath(GOLDEN_DIR, SUITE, sh * ".json"), top)
        st = get(top, "stats", Obj())
        println(stderr, "[$SUITE/$sh] ", get(st, "cases", "?"), " cases, ", get(st, "errors", 0), " errors, ",
                get(st, "ref_mismatch", 0), " ref mismatches, ", get(st, "unexplained", 0), " unexplained in ",
                round(time() - t0; digits = 1), " s -> ", relpath(path, ORACLE_DIR))
    end
end

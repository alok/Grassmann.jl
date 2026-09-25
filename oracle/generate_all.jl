# oracle/generate_all.jl: regenerate every element-level golden suite.
#
#   julia --startup-file=no --project=oracle oracle/generate_all.jl [options] [suite | suite:shard ...]
#
# Options:
#   --jobs N        parallel worker processes (default: min(CPU threads ÷ 2, 8))
#   --timeout SEC   per-shard wall-clock limit (default 3600)
#   --list          print the suites and shards, run nothing
#   --retag         do not run Julia operations: re-apply oracle/defects.toml to the existing
#                   shard files (tags + stats) and rewrite the manifests (seconds, not minutes)
#
# Every shard runs in a fresh `julia` process (oracle/run_suite.jl) using this process's active
# project, writing oracle/golden/<suite>/<shard>.json. Afterwards each suite manifest
# oracle/golden/<suite>.json is rewritten from the shard files, which are re-read with JSON.jl
# as validation, and oracle/golden/defects.json is rewritten from oracle/defects.toml. Exits
# non-zero if any shard failed. The output format is specified in
# docs/port-notes/oracle-schema.md.

include(joinpath(@__DIR__, "common.jl"))
import JSON

const SUITES = ["construct", "arith", "products", "unary", "composite", "floats", "docs"]
const RUNNER = joinpath(ORACLE_DIR, "run_suite.jl")

function parse_args(args)
    jobs = max(1, min(Sys.CPU_THREADS ÷ 2, 8))
    timeout = 3600.0
    listonly = false
    retagonly = false
    targets = String[]
    i = 1
    while i <= length(args)
        a = args[i]
        if a == "--jobs"
            jobs = parse(Int, args[i+1]); i += 1
        elseif a == "--timeout"
            timeout = parse(Float64, args[i+1]); i += 1
        elseif a == "--list"
            listonly = true
        elseif a == "--retag"
            retagonly = true
        else
            push!(targets, a)
        end
        i += 1
    end
    return jobs, timeout, listonly, retagonly, targets
end

"Re-apply defects.toml to an existing shard file in place."
function retag_file(path, defects)
    top = toobj(JSON.parsefile(path))
    retag!(top, defects)
    write_golden(path, top)
end

project_dir() = dirname(something(Base.active_project(), joinpath(ORACLE_DIR, "Project.toml")))
suite_cmd(args...) = `$(Base.julia_cmd()) --startup-file=no --project=$(project_dir()) $RUNNER $args`

list_shards(suite) = split(readchomp(suite_cmd(suite, "--list")), '\n'; keepempty = false)

"Run jobs `[(suite, shard)]` on `n` workers; returns Dict((suite, shard) => (ok, seconds, logpath))."
function run_jobs(jobs, n, timeout)
    logdir = mktempdir(; cleanup = false)
    results = Dict{Tuple{String,String},Tuple{Bool,Float64,String}}()
    queue = Channel{Tuple{String,String}}(length(jobs))
    foreach(j -> put!(queue, j), jobs)
    close(queue)
    lk = ReentrantLock()
    @sync for w in 1:n
        @async for (suite, shard) in queue
            logpath = joinpath(logdir, "$suite-$shard.log")
            t0 = time()
            p = open(logpath, "w") do io
                run(pipeline(suite_cmd(suite, shard); stdout = io, stderr = io); wait = false)
            end
            while process_running(p)
                if time() - t0 > timeout
                    kill(p)
                    break
                end
                sleep(0.5)
            end
            wait(p)
            ok = success(p)
            dt = time() - t0
            lock(lk) do
                results[(suite, shard)] = (ok, dt, logpath)
                status = ok ? "ok  " : "FAIL"
                lines = readlines(logpath)
                tail = !ok ? "see $logpath" : isempty(lines) ? "" : strip(lines[end])
                println(stderr, "$status $(rpad("$suite/$shard", 40)) $(lpad(round(dt; digits = 1), 7)) s  $tail")
            end
        end
    end
    return results
end

"Rewrite oracle/golden/<suite>.json from its shard files; returns the manifest totals."
function write_manifest(suite, shards)
    entries = Obj[]
    tot = Dict{String,Int}("cases" => 0, "errors" => 0, "ref_mismatch" => 0, "unexplained" => 0)
    dtot = Dict{String,Int}()
    meta = nothing
    for sh in shards
        rel = "$suite/$sh.json"
        path = joinpath(GOLDEN_DIR, rel)
        isfile(path) || error("missing shard file $rel")
        d = JSON.parsefile(path)              # validates the JSON
        st = d["stats"]
        for k in keys(tot)
            tot[k] += get(st, k, 0)
        end
        for (k, v) in get(st, "defects", Dict())
            dtot[k] = get(dtot, k, 0) + v
        end
        m = d["meta"]
        meta === nothing && (meta = m)
        e = Obj("shard" => sh, "file" => rel, "cases" => st["cases"], "bytes" => filesize(path),
                "errors" => get(st, "errors", 0), "ref_mismatch" => get(st, "ref_mismatch", 0),
                "unexplained" => get(st, "unexplained", 0))
        haskey(d, "space") && (e["space"] = d["space"]["name"])
        push!(entries, e)
    end
    man = Obj("meta" => Obj("schema" => SCHEMA_VERSION, "suite" => suite, "julia" => meta["julia"],
                            "packages" => toobj(meta["packages"]), "generator" => "oracle/suites/$suite.jl"),
              "totals" => Obj("cases" => tot["cases"], "errors" => tot["errors"],
                              "ref_mismatch" => tot["ref_mismatch"], "unexplained" => tot["unexplained"],
                              "defects" => Obj((k => dtot[k] for k in sort!(collect(keys(dtot))))...)),
              "shards" => entries)
    write_golden(joinpath(GOLDEN_DIR, suite * ".json"), man)
    JSON.parsefile(joinpath(GOLDEN_DIR, suite * ".json"))
    return tot
end

"""
Write oracle/golden/defects.json: the defect table of oracle/defects.toml as JSON, so consumers
(the Lean tests) get every id's `policy` without a TOML parser. Entry keys are emitted in a fixed
order; `match` tables keep their fields (`kinds` as an array, everything else a string).
"""
function write_defects_json()
    t = TOML.parsefile(joinpath(ORACLE_DIR, "defects.toml"))
    fieldorder = ("suite", "space", "op", "kinds", "when", "out", "msg", "block", "input", "file")
    entries = Obj[]
    for d in get(t, "defect", Any[])
        e = Obj("id" => d["id"], "policy" => get(d, "policy", "skip"))
        for k in ("title", "source", "notes", "correct")
            haskey(d, k) && (e[k] = d[k])
        end
        ms = Obj[]
        for m in get(d, "match", Any[])
            unknown = setdiff(keys(m), fieldorder)
            isempty(unknown) || error("defect $(d["id"]): unknown match field(s) $(join(unknown, ", "))")
            push!(ms, Obj((k => (k == "kinds" ? Any[m[k]...] : m[k]) for k in fieldorder if haskey(m, k))...))
        end
        e["match"] = ms
        push!(entries, e)
    end
    ids = [e["id"] for e in entries]
    allunique(ids) || error("duplicate defect ids in defects.toml")
    path = joinpath(GOLDEN_DIR, "defects.json")
    write_golden(path, Obj("meta" => Obj("schema" => SCHEMA_VERSION, "generator" => "oracle/defects.toml"),
                           "defects" => entries))
    JSON.parsefile(path)
    return length(entries)
end

function main(args)
    njobs, timeout, listonly, retagonly, targets = parse_args(args)
    wanted = Dict{String,Union{Nothing,Vector{String}}}()
    if isempty(targets)
        foreach(s -> wanted[s] = nothing, SUITES)
    else
        for t in targets
            if occursin(':', t)
                s, sh = split(t, ':'; limit = 2)
                s in SUITES || error("unknown suite $s")
                v = get(wanted, s, String[])
                v === nothing || push!(v, sh)
                wanted[s] = v === nothing ? nothing : v
            else
                t in SUITES || error("unknown suite $t")
                wanted[t] = nothing
            end
        end
    end
    allshards = Dict(s => String.(list_shards(s)) for s in keys(wanted))
    if listonly
        for s in SUITES
            haskey(allshards, s) && println(s, ": ", join(allshards[s], " "))
        end
        return 0
    end
    jobs = Tuple{String,String}[]
    # longest-running suites first so the pool stays busy
    for s in ("products", "unary", "arith", "composite", "construct", "docs", "floats")
        haskey(wanted, s) || continue
        for sh in (wanted[s] === nothing ? allshards[s] : wanted[s])
            sh in allshards[s] || error("unknown shard $s:$sh")
            push!(jobs, (s, sh))
        end
    end
    t0 = time()
    if retagonly
        defects = load_defects()
        for (s, sh) in jobs
            path = joinpath(GOLDEN_DIR, s, sh * ".json")
            isfile(path) ? retag_file(path, defects) : println(stderr, "missing $s/$sh.json (not retagged)")
        end
        results = Dict{Tuple{String,String},Tuple{Bool,Float64,String}}()
    else
        println(stderr, "running $(length(jobs)) shard(s) on $njobs worker(s) with project $(project_dir())")
        results = run_jobs(jobs, njobs, timeout)
    end
    failed = [k for (k, v) in results if !v[1]]
    for s in SUITES
        haskey(wanted, s) || continue
        # prune stale shard files when the whole suite was regenerated
        if !retagonly && wanted[s] === nothing && isdir(joinpath(GOLDEN_DIR, s))
            for f in readdir(joinpath(GOLDEN_DIR, s))
                endswith(f, ".json") && !(f[1:end-5] in allshards[s]) && rm(joinpath(GOLDEN_DIR, s, f))
            end
        end
        if all(sh -> isfile(joinpath(GOLDEN_DIR, s, sh * ".json")), allshards[s])
            tot = write_manifest(s, allshards[s])
            println(stderr, "manifest golden/$s.json: $(tot["cases"]) cases, $(tot["errors"]) errors, ",
                    "$(tot["ref_mismatch"]) ref mismatches, $(tot["unexplained"]) unexplained")
        else
            println(stderr, "manifest golden/$s.json NOT written (missing shards)")
        end
    end
    println(stderr, "defects golden/defects.json: $(write_defects_json()) entries")
    println(stderr, "done in $(round(time() - t0; digits = 1)) s; $(length(failed)) failed shard(s)")
    for (s, sh) in failed
        println(stderr, "  FAILED $s/$sh: log at $(results[(s, sh)][3])")
    end
    return isempty(failed) ? 0 : 1
end

exit(main(ARGS))

# oracle/suites/docs.jl: the README/docs golden corpus (grassmann-docs.md §6), re-run on the
# oracle as (expression source, output) pairs.
#
# Sources live in oracle/docs/*.txt. Format: a line `### <label>` starts a block, `### <label> | fresh`
# starts a block in a new sandbox module; every other line is Julia code, parsed into top-level
# statements and evaluated REPL-style (`ans` is bound, a trailing `;` suppresses display).
# One shard per "fresh group" (a fresh block plus the non-fresh blocks after it), each in its own
# process, so Julia's global caches cannot leak between examples.
#
# The sandbox is what a user has after `using Grassmann` (plus `import DirectSum, LinearAlgebra`
# for qualified names), matching the docs.

const DOC_FILES = ["readme_design", "algebra", "tutorials", "probe1", "probe2", "probe3", "probe4"]

"Parse all doc block files into fresh groups: `[(shardname, file, [(label, code)])]`."
function doc_groups()
    groups = Tuple{String,String,Vector{Tuple{String,String}}}[]
    for f in DOC_FILES
        lines = readlines(joinpath(ORACLE_DIR, "docs", f * ".txt"))
        cur = nothing
        buf = String[]
        blocks = Tuple{String,Bool,String}[]
        for l in lines
            if startswith(l, "### ")
                cur !== nothing && push!(blocks, (cur[1], cur[2], join(buf, "\n")))
                hdr = strip(l[5:end])
                fresh = endswith(hdr, "| fresh")
                label = fresh ? strip(replace(hdr, "| fresh" => "")) : hdr
                cur = (String(label), fresh)
                buf = String[]
            else
                push!(buf, l)
            end
        end
        cur !== nothing && push!(blocks, (cur[1], cur[2], join(buf, "\n")))
        for (i, (label, fresh, code)) in enumerate(blocks)
            if fresh || i == 1
                push!(groups, ("", f, Tuple{String,String}[]))
            end
            push!(groups[end][3], (label, code))
        end
    end
    sanitize(s) = replace(replace(s, r"[^A-Za-z0-9.]+" => "-"), r"^-+|-+$" => "")
    return [(lpad(i, 2, '0') * "-" * sanitize(g[3][1][1]), g[2], g[3]) for (i, g) in enumerate(groups)]
end

shards() = [g[1] for g in doc_groups()]

"Split code into top-level statements `(source, expr)`."
function statements(code::AbstractString)
    out = Tuple{String,Any}[]
    pos = 1
    n = ncodeunits(code)
    while pos <= n
        while pos <= n && isspace(code[pos])
            pos = nextind(code, pos)
        end
        pos > n && break
        ex, newpos = Meta.parse(code, pos; greedy = true, raise = false)
        src = String(strip(code[pos:prevind(code, newpos)]))
        push!(out, (src, ex))
        pos = newpos
    end
    return out
end

function doc_sandbox(k)
    m = Module(Symbol("DocSandbox", k))
    Core.eval(m, :(using Grassmann))
    Core.eval(m, :(import DirectSum, LinearAlgebra))
    return m
end

repl_display(x) = sprint(io -> show(IOContext(io, :limit => true, :displaysize => (40, 200)), MIME"text/plain"(), x))

"Evaluate `ex` in `m` with stdout captured; returns `(ok, value_or_exception, stdout_text)`."
function eval_captured(m::Module, ex)
    path, io = mktemp()
    local res
    try
        res = redirect_stdout(io) do
            attempt(() -> Core.eval(m, ex))
        end
    finally
        close(io)
    end
    txt = read(path, String)
    rm(path; force = true)
    return res[1], res[2], txt
end

function build(sh, defects)
    groups = doc_groups()
    gi = findfirst(g -> g[1] == sh, groups)
    _, file, blocks = groups[gi]
    top = Obj("meta" => meta_obj("docs", sh; source = "oracle/docs/$file.txt"))
    top["sandbox"] = "using Grassmann; import DirectSum, LinearAlgebra"
    cl = CaseLog()
    m = doc_sandbox(gi)
    for (label, code) in blocks
        for (src, ex) in statements(code)
            ok, res, txt = eval_captured(m, ex)
            ok && Core.eval(m, :(ans = $(QuoteNode(res))))
            c = Obj("block" => label, "input" => src)
            if ok
                shown = !endswith(src, ";") && res !== nothing
                d = shown ? (try repl_display(res) catch; nothing end) : nothing
                c["display"] = d
                if res !== nothing
                    c["out"] = encode(res; compact = true)
                end
            else
                c["out"] = error_obj(res)
            end
            isempty(txt) || (c["stdout"] = txt)
            addcase!(cl, c)
        end
    end
    top["cases"] = cl.cases
    return retag!(top, defects)
end

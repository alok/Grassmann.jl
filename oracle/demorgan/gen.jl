# Oracle generator for DeMorgan.jl 0.1.0 (port-notes/small-algebra.md §9.3).
#
#   julia --startup-file=no --project=<juliaenv2> oracle/demorgan/gen.jl
#
# Writes oracle/golden/demorgan/{truthvalues,truthtable,parstring}.json.
# UInt columns are written as decimal strings; truth-table indices i, j are Julia's
# (1-based).

using DeMorgan, JSON3, Random
import DeMorgan: TruthValues, TruthTable, select, parstring

Random.seed!(0x5EED)
const OUT = joinpath(@__DIR__, "..", "golden", "demorgan")
mkpath(OUT)
u(x) = string(x)                       # UInt → decimal string
mask(N) = N >= 6 ? typemax(UInt) : (UInt(1) << (1 << N)) - UInt(1)

# ---------------------------------------------------------------- truth values
tv = Any[]
for N in 1:6, _ in 1:40
    p = rand(UInt) & mask(N); q = rand(UInt) & mask(N)
    P = TruthValues{N}(p); Q = TruthValues{N}(q)
    push!(tv, Dict("N" => N, "p" => u(p), "q" => u(q),
        "not" => u((!P).p), "and" => u((P ∧ Q).p), "or" => u((P ∨ Q).p),
        "amp" => u((P & Q).p), "bar" => u((P | Q).p),
        "imp" => u((P --> Q).p), "rimp" => u((P <-- Q).p), "iff" => u((P <--> Q).p),
        # lifting of ⊥ (TruthValues{0}) and ⊤ (Tautology), DM:148-153
        "bot_or" => u((⊥ ∨ P).p), "and_top" => u((P ∧ ⊤).p), "top_imp" => u((⊤ --> P).p),
        "rimp_bot" => u((P <-- ⊥).p), "iff_top" => u((P <--> ⊤).p),
        "show" => repr(P)))
end
sel = [Dict("n" => n, "N" => N, "value" => u(select(n, N))) for N in 1:6 for n in 1:N]
bools = Any[]
for k in 1:6, _ in 1:5
    v = rand(Bool, k)
    push!(bools, Dict("bits" => v, "N" => k, "value" => u(TruthValues(v...).p),
                      "not" => u((!TruthValues(v...)).p)))
end
misc = Dict("not_bot" => repr(!⊥), "not_top" => repr(!⊤), "bot" => repr(⊥), "top" => repr(⊤),
            "bot_call" => repr(⊥(TruthValues{2}(UInt(3)))), "top_call" => repr(⊤(TruthValues{2}(UInt(3)))))
open(joinpath(OUT, "truthvalues.json"), "w") do io
    JSON3.write(io, Dict("tv" => tv, "select" => sel, "bools" => bools, "misc" => misc))
end

# ---------------------------------------------------------------- truth tables
const NAMES = ["p", "q", "r", "s", "t", "u"]
const OPS = ["not", "and", "or", "imp", "rimp", "iff"]

# random expression with deliberate reuse of earlier subterms (exercises combine quirks)
function randexpr(N, depth, pool)
    if !isempty(pool) && rand() < 0.25
        return rand(pool)
    end
    e = if depth == 0 || rand() < 0.2
        Any["var", rand(0:N-1)]
    else
        op = rand(OPS)
        op == "not" ? Any["not", randexpr(N, depth - 1, pool)] :
                      Any[op, randexpr(N, depth - 1, pool), randexpr(N, depth - 1, pool)]
    end
    push!(pool, e)
    return e
end

function evalexpr(e, vars)
    op = e[1]
    op == "var" && return vars[e[2] + 1]
    op == "not" && return !evalexpr(e[2], vars)
    a = evalexpr(e[2], vars); b = evalexpr(e[3], vars)
    op == "and" ? a ∧ b : op == "or" ? a ∨ b : op == "imp" ? (a --> b) :
    op == "rimp" ? (a <-- b) : (a <--> b)
end

projections(N) = [TruthTable{N}(select(N + 1 - m, N), NAMES[m]) for m in 1:N]

# PrettyTables v2 unicode renderer (DM:163-169), reimplemented (PrettyTables is absent)
function render(t::TruthTable{N,M}) where {N,M}
    H = maximum(length.(t.n))
    header = [[k <= length(t.n[c]) ? t.n[c][k] : "" for c in 1:M] for k in 1:H]
    body = [[string((t.p[c] >> k) & 1) for c in 1:M] for k in 0:(1 << N) - 1]
    w = [maximum(length(r[c]) for r in vcat(header, body)) for c in 1:M]
    rule(l, m, r) = l * join([repeat("─", x + 2) for x in w], m) * r * "\n"
    line(r) = "│" * join([" " * lpad(r[c], w[c]) * " " for c in 1:M], "│") * "│\n"
    rule("┌", "┬", "┐") * join(line.(header)) * rule("├", "┼", "┤") * join(line.(body)) *
        rule("└", "┴", "┘")
end

tables = Any[]
for N in (1, 2, 3, 4, 6), k in 1:(N == 6 ? 40 : 115)
    pool = Any[]
    e = randexpr(N, rand(1:4), pool)
    t = evalexpr(e, projections(N))
    push!(tables, Dict("N" => N, "expr" => e,
        "cols" => [u(x) for x in t.p], "names" => [collect(x) for x in t.n],
        "i" => t.i, "j" => t.j, "str" => string(t),
        "render" => N <= 4 && k <= 20 ? render(t) : nothing))
end
open(joinpath(OUT, "truthtable.json"), "w") do io
    JSON3.write(io, Dict("tables" => tables))
end

# ---------------------------------------------------------------- parstring
strs = String["p", "¬(p)", "¬(p→q)", "¬(p)∧¬(q)", "¬((p→q)∧r)", "¬(¬(p))", "⊤", "pq", "¬p",
              "¬()", "()", "(p)", "¬(p))", "¬", "¬(", "¬(a b c)", "p∧q"]
for t in tables, n in t["names"], s in n
    push!(strs, s)
end
strs = unique(strs)
open(joinpath(OUT, "parstring.json"), "w") do io
    JSON3.write(io, Dict("cases" => [Dict("s" => s, "out" => parstring(s)) for s in strs]))
end
println("wrote ", length(tv), " tv, ", length(tables), " tables, ", length(strs), " parstrings")

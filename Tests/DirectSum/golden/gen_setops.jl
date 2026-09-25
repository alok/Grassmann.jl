# Oracle generator for the DirectSum set-theory suite (Tests/DirectSum/SetOps.lean):
# ∪, ∩, ⊆, ==, ⊕ of spaces, subspaces and basis blades, plus `+`, `^`, `subtangent`,
# subspace metrics and bases (DirectSum.jl src/operations.jl:36-168).
#
#   julia --startup-file=no --project=oracle Tests/DirectSum/golden/gen_setops.jl Tests/DirectSum/golden/setops.json
#
# Items use the recipe trees of gen_spaces.jl, plus {"op":"sub","of":…,"idx":[…]} (Julia `V(i…)`) and
# {"op":"blade","of":…,"bits":b} (the basis blade `Submanifold{Submanifold(V),G,b}`). `Int` spaces
# (recipe "I") are Julia's handles `ℝn = Submanifold(n)`.
using DirectSum, Leibniz, JSON

errstr(e) = "error: " * first(split(sprint(showerror, e), '\n'))
function safe(f)
    try
        r = f()
        r isa Bool ? r : repr(r)
    catch e
        e isa StackOverflowError ? "error: StackOverflowError" : errstr(e)
    end
end

S(s) = (Signature(s), Dict("op" => "S", "s" => s))
D(v...) = (DiagonalForm(v...), Dict("op" => "D", "vals" => collect(v)))
I(n) = (Submanifold(n), Dict("op" => "I", "n" => n))
R(n) = (ℝ^n, Dict("op" => "R", "n" => n))
adj((V, s)) = (V', Dict("op" => "adjoint", "of" => s))
tan((V, s), mu = 1, nu = nothing) = nu === nothing ? (tangent(V, mu), Dict("op" => "tangent", "of" => s, "mu" => mu)) :
    (tangent(V, mu, nu), Dict("op" => "tangent", "of" => s, "mu" => mu, "nu" => nu))
osum((A, a), (B, b)) = (A ⊕ B, Dict("op" => "oplus", "a" => a, "b" => b))
sub((V, s), idx...) = (V(idx...), Dict("op" => "sub", "of" => s, "idx" => collect(idx)))
blade((V, s), b) = (Submanifold{Submanifold(V),count_ones(b),UInt(b)}(), Dict("op" => "blade", "of" => s, "bits" => b))

const BUNDLES = Any[
    R(1), adj(R(1)), R(2), adj(R(2)), R(3), adj(R(3)), R(4), S("-++"), S("+-"), S("+-+"), S("∞∅+"),
    osum(R(1), adj(R(1))), osum(R(2), adj(R(2))), osum(adj(R(2)), R(2)), osum(R(3), adj(R(3))),
    tan(R(3)), tan(R(3), 1, 2), tan(R(3), 2, 1), tan(R(2)), adj(tan(R(3))), osum(tan(R(2)), adj(tan(R(2)))),
    D(1, 2, 3), tan(D(1, 2, 3)), adj(D(1, 2, 3)), D(1, 2), osum(D(1, 2), adj(D(1, 2))), I(3), I(4),
]
const SUBS = Any[
    sub(R(3), 1, 2), sub(R(3), 2, 3), sub(R(3), 1, 2, 3), sub(R(3), 2), sub(R(4), 2, 3), sub(R(4), 1, 2, 3, 4),
    sub(adj(R(2)), 1), sub(R(2), 1), sub(R(2), 1, 2), sub(adj(R(2)), 2), sub(tan(R(2)), 1, 3), sub(adj(tan(R(2))), 2, 3),
    sub(S("-++"), 1, 3), sub(D(1, 2, 3), 1, 3), sub(I(3), 1, 2), sub(I(3), 3),
]
const BLADES = Any[blade(R(3), b) for b in (0, 1, 2, 3, 5, 6, 7)]

cases = Any[]
push_case!(kind, (x, sx), (y, sy); ops...) = push!(cases, Dict("kind" => kind, "a" => sx, "b" => sy,
    [string(k) => safe(f) for (k, f) in ops]...))

# `∩`/`∪` of two `Int` handles of different sizes recurse through Leibniz's variadic fold until the
# stack overflows (uncatchable here); they are recorded as that error without being run.
isint(s) = s["op"] == "I"
overflow(f, A, B) = isint(A[2]) && isint(B[2]) && A[2]["n"] != B[2]["n"] ? (() -> throw(StackOverflowError())) : f
# An `Int` handle against a space falls back to `Base.union`/`issubset` of iterables (a `Vector`
# of spaces) or fails type promotion; only `⊆`/`==` against the same-size `Signature` are meaningful.
for A in BUNDLES, B in BUNDLES
    a, b = A[1], B[1]
    if isint(A[2]) != isint(B[2])
        n = isint(A[2]) ? A[2]["n"] : B[2]["n"]
        other = isint(A[2]) ? B[2] : A[2]
        other == R(n)[2] && push_case!("bundle", A, B; subset = () -> a ⊆ b, equal = () -> a == b)
        continue
    end
    push_case!("bundle", A, B; union = overflow(() -> a ∪ b, A, B), inter = overflow(() -> a ∩ b, A, B),
        subset = () -> a ⊆ b, equal = () -> a == b)
end
# subspaces of the same space, and of different spaces
# Subspaces of different spaces: `⊆` goes through `interop` (and overflows the stack) unless the
# right operand is a whole space, `∩` always does; such calls are recorded without being run.
parent(x::Submanifold{V}) where V = V
full(x) = count_ones(UInt(x)) == mdims(parent(x))
for A in SUBS, B in SUBS
    a, b = A[1], B[1]
    same = parent(a) === parent(b)
    so = () -> throw(StackOverflowError())
    subok = same || full(b)
    firstok = full(b) && (try parent(a) ⊆ parent(b) catch; true end)
    unionok = same || (dyadmode(a) == dyadmode(b) && full(b) && (firstok || full(a)))
    push_case!("sub", A, B; union = unionok ? (() -> a ∪ b) : so, inter = same ? (() -> a ∩ b) : so,
        subset = subok ? (() -> a ⊆ b) : so, oplus = () -> a ⊕ b)
end
# subspaces against spaces
# `Int` handles are `Submanifold`s in Julia (subspace rules) but spaces in the port: they are only
# compared with spaces above.
for A in SUBS, B in BUNDLES
    (isint(A[2]["of"]) || isint(B[2])) && continue
    a, b = A[1], B[1]
    push_case!("subbundle", A, B; union = () -> a ∪ b, subset = () -> a ⊆ b)
    push_case!("bundlesub", B, A; union = () -> b ∪ a, inter = () -> b ∩ a, subset = () -> b ⊆ a)
end
# blades of ℝ^3 against each other and against spaces
for A in BLADES, B in BLADES
    a, b = A[1], B[1]
    push_case!("blade", A, B; union = () -> a ∪ b, inter = () -> a ∩ b, subset = () -> a ⊆ b)
end
for A in BLADES, B in (R(3), R(4), adj(R(3)), S("-++"))
    a, b = A[1], B[1]
    push_case!("bladebundle", A, B; subset = () -> a ⊆ b)
    push_case!("bundleblade", B, A; union = () -> b ∪ a, inter = () -> b ∩ a, subset = () -> b ⊆ a)
end

# `+`, `^`, n-ary folds, subtangent, subspace metrics/bases
misc = Any[]
for (A, B) in ((R(3), adj(R(3))), (R(1), R(3)), (adj(R(1)), R(3)), (D(1, 2), adj(D(1, 2))), (S("∞∅+"), R(1)))
    push!(misc, Dict("op" => "plus", "a" => A[2], "b" => B[2], "out" => safe(() -> A[1] + B[1])))
end
for A in (R(1), R(2), adj(R(2)), S("-+"), D(1, 2)), i in 0:3
    push!(misc, Dict("op" => "pow", "a" => A[2], "i" => i, "out" => safe(() -> A[1]^i)))
end
for xs in ((R(1), adj(R(1)), R(1)), (R(3), tan(R(3)), tan(R(3), 1, 2)), (osum(R(2), adj(R(2))), R(2), adj(R(2))))
    push!(misc, Dict("op" => "unionall", "xs" => [x[2] for x in xs], "out" => safe(() -> ∪([x[1] for x in xs]...))))
    push!(misc, Dict("op" => "interall", "xs" => [x[2] for x in xs], "out" => safe(() -> ∩([x[1] for x in xs]...))))
end
for A in (tan(R(3)), tan(R(3), 1, 2), tan(R(2), 2, 2), adj(tan(R(3))))
    push!(misc, Dict("op" => "subtangent", "a" => A[2], "out" => safe(() -> DirectSum.subtangent(A[1]))))
end
for A in SUBS
    a = A[1]
    push!(misc, Dict("op" => "subinfo", "a" => A[2], "mdims" => mdims(a), "diffvars" => diffvars(a),
        "metrics" => string.(a[:]), "collect" => safe(() -> collect(a))))
end

open(ARGS[1], "w") do io
    JSON.print(io, Dict("meta" => Dict("julia" => string(VERSION),
            "DirectSum" => string(pkgversion(DirectSum)), "Leibniz" => string(pkgversion(Leibniz))),
        "cases" => cases, "misc" => misc))
end
println("wrote $(length(cases)) set-operation cases and $(length(misc)) misc records to $(ARGS[1])")

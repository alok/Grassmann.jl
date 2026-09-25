# Oracle generator for the DirectSum space/index/printing suite (Tests/DirectSum/Spaces.lean).
#
#   julia --startup-file=no --project=oracle Tests/DirectSum/golden/gen_spaces.jl Tests/DirectSum/golden/spaces.json
#
# Every space is described by a small JSON tree ("spec") that the Lean test rebuilds with
# the DirectSum API, so the Lean side never has to interpret Julia type strings.
using DirectSum, Leibniz, LinearAlgebra, JSON

err(e) = Dict("error" => first(split(sprint(showerror, e), '\n')))
macro safe(ex)
    quote
        try
            $(esc(ex))
        catch e
            err(e)
        end
    end
end
u(x) = Int(UInt(x))

# ---------------------------------------------------------------- spaces with specs
S(s) = (Signature(s), Dict("op" => "S", "s" => s))
D(v...) = (DiagonalForm(v...), Dict("op" => "D", "vals" => collect(v)))
I(n) = (n, Dict("op" => "I", "n" => n))
R(n) = (ℝ^n, Dict("op" => "R", "n" => n))
adj((V, s)) = (V', Dict("op" => "adjoint", "of" => s))
tan((V, s), mu = 1, nu = nothing) = nu === nothing ? (tangent(V, mu), Dict("op" => "tangent", "of" => s, "mu" => mu)) :
    (tangent(V, mu, nu), Dict("op" => "tangent", "of" => s, "mu" => mu, "nu" => nu))
osum((A, a), (B, b)) = (A ⊕ B, Dict("op" => "oplus", "a" => a, "b" => b))
# Int ⊕ Int is defined on the handles: Submanifold(5) ⊕ Submanifold(3) = Submanifold(8)
function osumI(a, b)
    @assert repr(Submanifold(a) ⊕ Submanifold(b)) == repr(Submanifold(a + b))
    (a + b, Dict("op" => "oplus", "a" => I(a)[2], "b" => I(b)[2]))
end
raw(n, m, s, f, d, l) = (Signature{n,m,UInt(s),f,d,l}(), Dict("op" => "raw", "n" => n, "opts" => m, "metric" => s, "F" => f, "D" => d, "L" => l))

const SPACES = Any[
    ("R0", R(0)), ("R1", R(1)), ("R2", R(2)), ("R3", R(3)), ("R4", R(4)), ("R5", R(5)),
    ("I0", I(0)), ("I1", I(1)), ("I3", I(3)), ("I4", I(4)),
    ("S-+++", S("-+++")), ("S+-+-", S("+-+-")), ("S-+-", S("-+-")), ("S---", S("---")),
    ("S∞+++", S("∞+++")), ("S∅+++", S("∅+++")), ("S∞∅+++", S("∞∅+++")), ("S∞∅+-", S("∞∅+-")),
    ("S∞∅++", S("∞∅++")), ("S∞∅+", S("∞∅+")), ("S∞∅", S("∞∅")), ("S∞-+", S("∞-+")), ("S∅++", S("∅++")),
    ("R3'", adj(R(3))), ("S+-'", adj(S("+-"))), ("S∞∅+++'", adj(S("∞∅+++"))), ("S∞∅+-'", adj(S("∞∅+-"))),
    ("R1'+R3", osum(adj(R(1)), R(3))),
    ("(R1'+R3)'", adj(osum(adj(R(1)), R(3)))),
    ("W", osum(osum(adj(R(1)), R(3)), adj(osum(adj(R(1)), R(3))))),
    ("R2+R2'", osum(R(2), adj(R(2)))), ("R3+R3'", osum(R(3), adj(R(3)))),
    ("S+-+S+-'", osum(S("+-"), adj(S("+-")))), ("S+-'+S+-", osum(adj(S("+-")), S("+-"))),
    ("S+-+S-++'", osum(S("+-"), adj(S("-++")))), ("S+-'+S-+'", osum(adj(S("+-")), adj(S("-+")))),
    ("I5+I3", osumI(5, 3)),
    ("T(R3)", tan(R(3))), ("T(R3)'", adj(tan(R(3)))), ("T(T(R3))", tan(tan(R(3)))),
    ("T(T(R3)')", tan(adj(tan(R(3))))), ("T(R3,2,3)", tan(R(3), 2, 3)), ("T(R2)", tan(R(2))),
    ("T(R2,2,2)", tan(R(2), 2, 2)), ("T(R2,1,2)", tan(R(2), 1, 2)), ("T(R2)'", adj(tan(R(2)))),
    ("T(R2)+T(R2)'", osum(tan(R(2)), adj(tan(R(2))))), ("T(R3)+T(R3)'", osum(tan(R(3)), adj(tan(R(3))))),
    ("T(R1)+T(R1)'", osum(tan(R(1)), adj(tan(R(1))))),
    ("T(R3,1,2)+T(R3,1,2)'", osum(tan(R(3), 1, 2), adj(tan(R(3), 1, 2)))),
    ("T(R3+R3',1,2)", tan(osum(R(3), adj(R(3))), 1, 2)), ("T(S∞∅+)", tan(S("∞∅+"))),
    ("T(S-+,2,1)", tan(S("-+"), 2, 1)),
    ("D123", D(1, 2, 3)), ("D123'", adj(D(1, 2, 3))), ("D1,-1,2", D(1, -1, 2)), ("D1110", D(1, 1, 1, 0)),
    ("D235", D(2, 3, 5)), ("D2,-1,3,-4", D(2, -1, 3, -4)), ("D123+D123'", osum(D(1, 2, 3), adj(D(1, 2, 3)))),
    ("D123+D45", osum(D(1, 2, 3), D(4, 5))), ("T(D123)", tan(D(1, 2, 3))),
    ("Spoly", raw(3, 16, 0, 1, 1, 1)), ("Sdualpoly", raw(3, 20, 7, 1, 1, 1)), ("Sname2", raw(3, 0, 0, 0, 0, 2)),
    ("Sname2dual", raw(3, 4, 7, 0, 0, 2)),
]

params(V::Int) = Dict("kind" => "Int", "n" => V, "options" => 0, "metric" => 0, "diffvars" => 0, "diffmode" => 0, "name" => 1)
function params(V)
    T = typeof(V)
    N, M, Sg, F, Dm, L = T.parameters
    Dict("kind" => V isa Signature ? "Signature" : "DiagonalForm", "n" => N, "options" => M,
         "metric" => V isa Signature ? u(Sg) : nothing,
         "diag" => V isa DiagonalForm ? string.(collect(V[:])) : nothing,
         "diffvars" => F, "diffmode" => Dm, "name" => L)
end
showspace(V::Int) = repr(Submanifold(V))
showspace(V) = repr(V)

spaces = Any[]
for (name, (V, spec)) in SPACES
    H = Submanifold(V)
    n = mdims(V)
    rec = Dict{String,Any}("name" => name, "spec" => spec, "params" => params(V),
        "show" => showspace(V), "handle" => repr(H),
        "grade" => grade(V isa Int ? Submanifold(V) : V), "isdiag" => @safe(LinearAlgebra.isdiag(V)),
        "diffmask" => (d = Leibniz.diffmask(V); d isa Tuple ? [u(d[1]), u(d[2])] : [u(d), 0]),
        # an `Int` space is modelled by its handle `Submanifold(n)` (Julia `ℝn`), whose adjoint is `Signature(n)'`
        "adjoint" => @safe(showspace(V isa Int ? Submanifold(V)' : V')),
        "dual" => @safe(showspace(V isa Int ? DirectSum.dual(Submanifold(V)) : DirectSum.dual(V))),
        "labels" => string.(DirectSum.labels(H)))
    if n <= 6
        # blades in basis order, built directly (Λ(V) segfaults for options ≥ 12, quirk Q5)
        bs = vcat([Leibniz.indexbasis(n, g) for g in 0:n]...)
        rec["blades"] = [@safe(repr(Submanifold{H,count_ones(b),b}())) for b in bs]
        rec["bits"] = [u(b) for b in bs]
    end
    if n <= 5 && !(V isa Int) && !(isdyadic(V) && diffvars(V) > 0)
        rec["subspaces"] = [@safe(repr(Submanifold{V,count_ones(UInt(b)),UInt(b)}())) for b in 0:(1<<n)-1]
    elseif V isa Int && n <= 5
        rec["subspaces"] = [@safe(repr(Submanifold{V,count_ones(UInt(b)),UInt(b)}())) for b in 0:(1<<n)-1]
    end
    push!(spaces, rec)
end

# ---------------------------------------------------------------- string grammars
sigstrs = ["", "+", "-", "++", "+-", "-+", "+++", "-+++", "+-+-", "---", "++-", "∞+++", "∅+++", "∞∅+++",
           "∞∅---", "∞∅+-", "∞∅", "∞", "∅", "3", "31", "311", "3005", "0", "10000", "5110", "4003",
           repeat("+", 22), repeat("-+", 11)]
sigparse = [Dict("input" => s, "show" => @safe(repr(Signature(s))), "params" => @safe(params(Signature(s)))) for s in sigstrs]
diagstrs = ["1,1,1,0", "1,-1,2", "2,3,5", "1,2,3,4,5", "0,0", "0,1,1,1", "2,-1,3,-4"]
diagparse = [Dict("input" => s, "show" => @safe(repr(DiagonalForm(s))), "params" => @safe(params(DiagonalForm(s)))) for s in diagstrs]
# V-strings on which Julia's `TensorBundle(str)` is correct (port-notes/directsum.md §4.1)
vstrs = ["+++", "++", "--", "+", "-", "++-", "+--", "---", "-+++", "1,2,3", "1,1,1,0", "3"]
vparse = [Dict("input" => s, "show" => @safe(showspace(TensorBundle(s)))) for s in vstrs]

# ---------------------------------------------------------------- index tables
tabs = Any[]
for n in 0:12
    push!(tabs, Dict("n" => n,
        "indexbasis" => [u.(Leibniz.indexbasis(n, g)) for g in 0:n],
        "bladeindex" => [Leibniz.bladeindex(n, UInt(b)) for b in 0:(1<<n)-1],
        "basisindex" => [Leibniz.basisindex(n, UInt(b)) for b in 0:(1<<n)-1],
        "spinindex" => [Leibniz.spinindex(n, UInt(b)) for b in 0:(1<<n)-1],
        "antiindex" => [Leibniz.antiindex(n, UInt(b)) for b in 0:(1<<n)-1],
        "binomcumsum" => collect(Leibniz.binomcumsum(n)), "spincumsum" => collect(Leibniz.spincumsum(n)),
        "anticumsum" => collect(Leibniz.anticumsum(n)), "gdimsall" => collect(Leibniz.gdimsall(n))))
end
spots = Any[]
let x = UInt64(0x9E3779B97F4A7C15)
    for n in (13, 14, 16, 18, 20, 22), k in 1:64
        x = x * 0x5851F42D4C957F2D + 0x14057B7EF767814F
        b = (x >> 7) & ((UInt(1) << n) - 1)
        push!(spots, Dict("n" => n, "b" => u(b), "bladeindex" => Leibniz.bladeindex(n, b),
            "basisindex" => Leibniz.basisindex(n, b)))
    end
end

# ---------------------------------------------------------------- printing primitives
printidx = Any[]
for i in -1:62, l in (false, true), e in ("v", "w", "∂", "ϵ", "X", "e")
    push!(printidx, Dict("i" => i, "label" => l, "prefix" => e, "out" => string(Leibniz.printindex(i, l, e))))
end
pi62 = Dict("v" => sprint(io -> Leibniz.printindices(io, Leibniz.indices(UInt(2^62 - 1)), false, "v")),
            "w" => sprint(io -> Leibniz.printindices(io, Leibniz.indices(UInt(2^62 - 1)), false, "w")),
            "vl" => sprint(io -> Leibniz.printindices(io, Leibniz.indices(UInt(2^62 - 1)), true, "v")))
compl = Any[]
for (N, D, P) in ((3, 0, 0), (4, 0, 0), (5, 0, 2), (4, 1, 0), (4, 0, 2), (6, 2, 0), (5, 1, 2), (6, 1, 1))
    for B in 0:(1<<N)-1
        push!(compl, Dict("N" => N, "D" => D, "P" => P, "B" => B, "C" => u(Leibniz.complement(N, UInt(B), D, P))))
    end
end
parities = Dict("reverse" => [Leibniz.parityreverse(g) for g in 0:64],
                "involute" => [Leibniz.parityinvolute(g) for g in 0:64],
                "clifford" => [Leibniz.parityclifford(g) for g in 0:64])
pdep = Any[]
for (N, Sm) in ((6, 0b101101), (5, 0b10110), (8, 0b11011010)), B in 0:(1<<count_ones(Sm))-1
    push!(pdep, Dict("N" => N, "S" => Sm, "B" => B, "expandbits" => u(Leibniz.expandbits(N, UInt(Sm), UInt(B)))))
end
powers = [Dict("expr" => e, "show" => @safe(repr(v))) for (e, v) in (
    "R^0" => (ℝ^1)^0, "R^5" => (ℝ^1)^5, "(R^2)^3" => (ℝ^2)^3, "(R')^2" => ((ℝ^1)')^2)]

open(ARGS[1], "w") do io
    JSON.print(io, Dict("spaces" => spaces, "signature_parse" => sigparse, "diagonal_parse" => diagparse,
        "bundle_parse" => vparse, "index_tables" => tabs, "index_spots" => spots, "printindex" => printidx,
        "printindices_62" => pi62, "complement" => compl, "grade_parities" => parities,
        "expandbits" => pdep, "powers" => powers))
end

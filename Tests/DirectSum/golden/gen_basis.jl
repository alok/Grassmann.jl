# Oracle generator for the `Λ` container suite (Tests/DirectSum/Basis.lean): `Λ(V)[i]`,
# `Λ(n,d,o,s)`, `Λ"…"`, `Λ(V)'`, `Λ(V) ⊕ Λ(W)` and the README blade names
# (DirectSum.jl src/basis.jl).
#
#   julia --startup-file=no --project=oracle Tests/DirectSum/golden/gen_basis.jl Tests/DirectSum/golden/basis.json
using DirectSum, Leibniz, JSON

safe(f) = try repr(f()) catch e; "error: " * first(split(sprint(showerror, e), '\n')) end

S(s) = (Signature(s), Dict("op" => "S", "s" => s))
I(n) = (n, Dict("op" => "I", "n" => n))
R(n) = (ℝ^n, Dict("op" => "R", "n" => n))
D(v...) = (DiagonalForm(v...), Dict("op" => "D", "vals" => collect(v)))
adj((V, s)) = (V', Dict("op" => "adjoint", "of" => s))
osum((A, a), (B, b)) = (A ⊕ B, Dict("op" => "oplus", "a" => a, "b" => b))

getidx = Any[]
for (V, s) in (R(3), I(3), S("-+++"), S("∞∅++"), adj(R(2)), osum(R(2), adj(R(2))), D(1, 2, 3))
    L = Λ(V)
    push!(getidx, Dict("space" => s, "show" => repr(L), "items" => [repr(L[i]) for i in 1:length(L)]))
end
codes = [Dict("n" => n, "d" => d, "o" => o, "s" => s, "show" => safe(() -> Λ(n, d, o, s)))
         for (n, d, o, s) in ((3, 0, 0, 0), (4, 1, 1, 0), (4, 1, 0, 0), (4, 0, 1, 0), (3, 0, 0, 1), (4, 0, 0, 5))]
strs = [Dict("s" => s, "show" => safe(() -> DirectSum.Basis(s))) for s in ("+++", "-+++", "∞∅+++", "++", "3")]
sums = Any[]
for (A, B) in ((R(3), adj(R(3))), (R(14), adj(R(14))), (R(7), adj(R(7))), (S("-+"), R(2)), (R(2), R(2)))
    push!(sums, Dict("a" => A[2], "b" => B[2], "show" => safe(() -> Λ(A[1]) ⊕ Λ(B[1]))))
end
duals = [Dict("space" => s, "show" => safe(() -> Λ(V)')) for (V, s) in (R(3), S("-+"), D(1, 2))]
readme = Dict(
    "indices(Λ(3).v12)" => collect(indices(Λ(3).v12)),
    "Λ(62).v32a87Ng == -1Λ(62).v2378agN" => Λ(62).v32a87Ng == -1Λ(62).v2378agN,
    "Λ(3).v21" => repr(Λ(3).v21), "Λ(3)[5]" => repr(Λ(3)[5]), "Λ(62).v2378agN" => repr(Λ(62).v2378agN),
    "Λ(62).v32a87Ng" => repr(Λ(62).v32a87Ng), "Λ(ℝ^3).v312" => repr(Λ(ℝ^3).v312),
    "Λ(S\"-+++\").v11" => repr(Λ(S"-+++").v11), "Λ(D\"1,2,3\").v33" => repr(Λ(D"1,2,3").v33))

open(ARGS[1], "w") do io
    JSON.print(io, Dict("getindex" => getidx, "codes" => codes, "strs" => strs, "sums" => sums,
        "duals" => duals, "readme" => readme))
end
println("wrote $(ARGS[1])")

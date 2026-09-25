# Oracle generator for the Leibniz additions (Tests/DirectSum/Leibniz.lean): `Derivation`
# (`∇`, `Δ`, powers, arithmetic, display), `gdimseven`/`gdimsodd`, `indexsplit`,
# `symmetricsplit`, `order`, `isorigin`/`isinf` of blades, `≅`, `χ` and `count_gdims` of terms
# and chains (Leibniz.jl src/Leibniz.jl:107-160, src/generic.jl; DirectSum.jl).
#
#   julia --startup-file=no --project=oracle Tests/DirectSum/golden/gen_leibniz.jl Tests/DirectSum/golden/leibniz.json
using Grassmann, Leibniz, DirectSum, JSON

safe(f) = try
    r = f()
    r isa Bool || r isa Integer ? r : repr(r)
catch e
    "error: " * first(split(sprint(showerror, e), '\n'))
end

# ---------------------------------------------------------------- Derivation
der = Any[]
for O in 0:36
    push!(der, Dict("expr" => "nabla^$O", "sign" => 1, "pow" => O, "show" => safe(() -> ∇^O)))
    push!(der, Dict("expr" => "(-nabla)^$O", "sign" => -1, "pow" => O, "show" => safe(() -> (-∇)^O)))
end
arith = Any[
    ("-nabla", () -> -∇), ("-Delta", () -> -Δ), ("2*nabla", () -> 2 * ∇), ("nabla*3", () -> ∇ * 3),
    ("2.5*nabla", () -> 2.5 * ∇), ("nabla/2", () -> ∇ / 2), ("2\\nabla", () -> 2 \ ∇),
    ("(2*nabla)+(3*nabla)", () -> (2 * ∇) + (3 * ∇)), ("(2*nabla)-(3*nabla)", () -> (2 * ∇) - (3 * ∇)),
    ("(2*nabla)*(3*nabla)", () -> (2 * ∇) * (3 * ∇)), ("(2*Delta)^2", () -> (2 * Δ)^2),
    ("(2*nabla)^3", () -> (2 * ∇)^3), ("(-2*nabla)^3", () -> (-2 * ∇)^3), ("-(2*nabla)", () -> -(2 * ∇)),
    ("(4*nabla)/(2*nabla)", () -> (4 * ∇) / (2 * ∇)), ("nabla+nabla", () -> ∇ + ∇),
    ("Delta+Delta", () -> Δ + Δ), ("nabla+1", () -> ∇ + 1), ("nabla^37", () -> ∇^37),
    ("nabla^2==Delta", () -> ∇^2 == Δ), ("(-nabla)^2==Delta", () -> (-∇)^2 == Δ),
    ("nabla==nabla", () -> ∇ == ∇), ("(-nabla)==nabla", () -> (-∇) == ∇),
]
for (e, f) in arith
    push!(der, Dict("expr" => e, "show" => safe(f)))
end

# ---------------------------------------------------------------- combinatorics / masks
gd = [Dict("n" => n, "even" => safe(() -> collect(Leibniz.gdimseven(n))), "odd" => safe(() -> collect(Leibniz.gdimsodd(n))))
      for n in 0:10]
isplit = [Dict("b" => b, "out" => Int.(Leibniz.indexsplit(UInt(b), 12))) for b in (0, 1, 5, 0b101101, 0xfff)]

S(s) = (Signature(s), Dict("op" => "S", "s" => s))
R(n) = (ℝ^n, Dict("op" => "R", "n" => n))
adj((V, s)) = (V', Dict("op" => "adjoint", "of" => s))
tan((V, s), mu = 1, nu = nothing) = nu === nothing ? (tangent(V, mu), Dict("op" => "tangent", "of" => s, "mu" => mu)) :
    (tangent(V, mu, nu), Dict("op" => "tangent", "of" => s, "mu" => mu, "nu" => nu))
osum((A, a), (B, b)) = (A ⊕ B, Dict("op" => "oplus", "a" => a, "b" => b))

spaces = Any[R(3), S("∞∅++"), S("∅++"), S("∞++"), tan(R(3)), tan(R(2), 2, 2), adj(tan(R(3))),
             osum(tan(R(2)), adj(tan(R(2)))), osum(R(2), adj(R(2)))]
blades = Any[]
for (V, spec) in spaces
    N = mdims(V)
    H = Submanifold(V)
    for b in 0:(1<<N)-1
        B = Submanifold{H,count_ones(UInt(b)),UInt(b)}()
        push!(blades, Dict("space" => spec, "b" => b,
            "order" => safe(() -> DirectSum.order(B)),
            "isorigin" => safe(() -> isorigin(B)), "isinf" => safe(() -> isinf(B)),
            "symsplit" => safe(() -> (x = Leibniz.symmetricsplit(V, UInt(b)); x isa Tuple ? [Int(x[1]), Int(x[2])] : [Int(x)])),
            "chi" => safe(() -> χ(B)), "count_gdims" => safe(() -> collect(count_gdims(B)))))
    end
end
# ≅ between blades of tangent spaces (grade, order, diffmode)
same = Any[]
let (V, spec) = tan(R(2)), H = Submanifold(tangent(ℝ^2))
    for a in 0:7, b in 0:7
        A = Submanifold{H,count_ones(UInt(a)),UInt(a)}(); B = Submanifold{H,count_ones(UInt(b)),UInt(b)}()
        push!(same, Dict("space" => spec, "a" => a, "b" => b, "out" => safe(() -> A ≅ B)))
    end
end
# χ and count_gdims of chains (coefficients 0/1 patterns)
chains = Any[]
for (V, spec) in (R(3), R(4), tan(R(3)))
    N = mdims(V)
    for G in 0:N, pat in 0:min(2^binomial(N, G) - 1, 15)
        coeffs = [(pat >> (k - 1)) & 1 for k in 1:binomial(N, G)]
        c = Chain{V,G}(coeffs...)
        push!(chains, Dict("space" => spec, "G" => G, "coeffs" => coeffs,
            "count_gdims" => safe(() -> collect(count_gdims(c))), "chi" => safe(() -> χ(c))))
    end
end

open(ARGS[1], "w") do io
    JSON.print(io, Dict("derivation" => der, "gdims" => gd, "indexsplit" => isplit, "blades" => blades,
        "same" => same, "chains" => chains))
end
println("wrote $(ARGS[1])")

# Golden generator for Grassmann.Calculus: Julia's `V(∇)`, `∂`, `d`, `δ`, `gradient`,
# `divergence`, `curl` (src/Grassmann.jl:88-112, src/composite.jl:942-951) in spaces without
# tangent variables (where `V(∇)` is the all-ones vector), the simplex boundary
# `∂(ω::Chain{V,1,<:Chain{W,1}}) = ∧(ω)⋅Λ(W).v1`, and the order-1 derivation `Σₖ ∂ₖvₖ` of
# tangent spaces with the operators built on it.
#
#   julia --startup-file=no --project=oracle oracle/forms/gen_calculus.jl
#
# Writes oracle/golden/forms/calculus.json with the encoding of gen_parity.jl (floats as IEEE
# bit patterns "0x…", a Julia exception {"E": …}); every result is the dense coefficient
# vector of `Multivector(result)` (Julia's `Real` results as the scalar of a multivector).
using Grassmann, LinearAlgebra, Random
include(joinpath(@__DIR__, "..", "unitsystems", "jsonw.jl"))
const OUT = joinpath(@__DIR__, "..", "golden", "forms")
mkpath(OUT)

hx(x::Real) = "0x" * string(reinterpret(UInt64, Float64(x)), base = 16, pad = 16)
errstr(e) = (s = sprint(showerror, e); string(nameof(typeof(e)), ": ", first(s, 160)))
dense(x::Real, V) = [hx(i == 1 ? x : 0.0) for i in 1:(1 << mdims(V))]
dense(x, V) = [hx(Float64(c)) for c in value(Multivector(x))]
macro safe(ex, V)
    quote
        try
            dense($(esc(ex)), $(esc(V)))
        catch e
            e isa InterruptException && rethrow()
            Dict("E" => errstr(e))
        end
    end
end
save(name, data) = (writejson(joinpath(OUT, name * ".json"), data);
    println("wrote ", name, " (", filesize(joinpath(OUT, name * ".json")), " bytes)"))
meta = Dict("julia" => string(VERSION), "grassmann" => string(pkgversion(Grassmann)), "seed" => 20260926)
Random.seed!(20260926)
using Serialization

# ------------------------------------------------------------------------------------------
# tangent spaces: V(∇) = Σₖ ∂ₖvₖ and the operators on it (docs algebra.md:1104-1120, 1408)
#
# Each space is evaluated in a fresh Julia process: Grassmann 0.8.46 caches its tangent-space
# product code by the number of generators only, so after `tangent(ℝ^3,1,1)` (4 generators)
# the contraction of `tangent(ℝ^2,2,2)` (also 4) drops terms (`∂(0.038v₁ + 1.033v₂)` gives
# `1.033∂₂` instead of `0.038∂₁ + 1.033∂₂`, which a fresh session returns).
# ------------------------------------------------------------------------------------------
function tangent_entries(base, mu, nu)
    Random.seed!(20260926 + 100base + 10mu + nu)
    out = Any[]
    V = tangent(ℝ^base, mu, nu)
    n = mdims(V)
    push!(out, Dict("base" => base, "mu" => mu, "nu" => nu, "what" => "nabla", "out" => @safe(V(∇), V)))
    for G in 1:base, trial in 1:2
        x = round.(randn(binomial(base, G)) .* 1.5, digits = 3)
        # a chain of the non-tangent generators: `x` on the blades below `2^base`, in order
        idx = collect(Grassmann.indexbasis(n, G))
        vals = zeros(length(idx))
        j = 0
        for (i, b) in enumerate(idx)
            if b < (1 << base)
                j += 1
                vals[i] = x[j]
            end
        end
        ω = Chain{V,G}(vals...)
        r = Dict{String,Any}("base" => base, "mu" => mu, "nu" => nu, "what" => "chain", "grade" => G,
            "x" => [hx(c) for c in x])
        r["boundary"] = @safe(∂(ω), V)
        r["differential"] = @safe(d(ω), V)
        r["hodge_differential"] = @safe(⋆d(ω), V)
        push!(out, r)
    end
    out
end

# the goldens (skipped when this file is included by a tangent-space child process)
if !isdefined(Main, :CHILD)
    # ------------------------------------------------------------------------------------------
    # spaces without tangent variables: every element kind, every operator
    # ------------------------------------------------------------------------------------------
    plain = Any[]
    for sig in ["++", "+++", "++++", "-+++", "∞∅++"]
        V = Signature(sig)
        n = mdims(V)
        push!(plain, Dict("sig" => sig, "what" => "nabla", "out" => @safe(V(∇), V)))
        for G in 0:n, trial in 1:2
            x = round.(randn(binomial(n, G)) .* 1.5, digits = 3)
            ω = Chain{V,G}(x...)
            r = Dict{String,Any}("sig" => sig, "what" => "chain", "grade" => G, "x" => [hx(c) for c in x])
            r["boundary"] = @safe(∂(ω), V)
            r["differential"] = @safe(d(ω), V)
            r["codifferential"] = @safe(δ(ω), V)
            r["gradient"] = @safe(Grassmann.gradient(ω), V)
            r["divergence"] = @safe(divergence(ω), V)
            r["curl"] = @safe(curl(ω), V)
            push!(plain, r)
        end
        for trial in 1:2
            x = round.(randn(1 << n) .* 1.5, digits = 3)
            ω = Multivector{V}(Values(x...))
            r = Dict{String,Any}("sig" => sig, "what" => "multivector", "x" => [hx(c) for c in x])
            r["boundary"] = @safe(∂(ω), V)
            r["differential"] = @safe(d(ω), V)
            r["codifferential"] = @safe(δ(ω), V)
            r["curl"] = @safe(curl(ω), V)
            push!(plain, r)
        end
    end

    # ------------------------------------------------------------------------------------------
    # simplices: ∂(ω) = ∧(ω)⋅Λ(W).v1 for the vertex operator of points in homogeneous coordinates
    # ------------------------------------------------------------------------------------------
    simplices = Any[]
    for (m, W) in [(2, 2), (2, 3), (3, 3), (3, 4), (4, 4)]
        V = Submanifold(m)
        Ws = Submanifold(W)
        for trial in 1:3
            pts = [vcat(1.0, round.(randn(W - 1) .* 2, digits = 3)) for _ in 1:m]
            ω = Chain{V,1}(Values((Chain{Ws,1}(Values(p...)) for p in pts)...))
            push!(simplices, Dict("m" => m, "W" => W, "points" => [[hx(c) for c in p] for p in pts],
                "boundary" => @safe(∂(ω), Ws)))
        end
    end


    tangentc = Any[]
    for (base, mu, nu) in [(3, 1, 1), (3, 2, 3), (2, 2, 2), (4, 2, 4), (3, 1, 3), (2, 1, 1)]
        tmp = tempname()
        code = "const CHILD = true; include($(repr(@__FILE__))); serialize($(repr(tmp)), tangent_entries($base, $mu, $nu))"
        run(`$(Base.julia_cmd()) --startup-file=no --project=$(Base.active_project()) -e $code`)
        append!(tangentc, Serialization.deserialize(tmp))
        rm(tmp)
    end

    save("calculus", Dict("meta" => meta, "plain" => plain, "simplices" => simplices, "tangent" => tangentc))
end

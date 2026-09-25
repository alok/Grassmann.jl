# chaos.json: the systems of examples/chaos.jl with the default odesolve (RK4, h = 2^-15, t ∈ [0, 2π]).
Lorenz(σ, r, b) = x -> Chain(σ * (x[2] - x[1]), x[1] * (r - x[3]) - x[2], x[1] * x[2] - b * x[3])
DiskDynamo(a, b, c) = x -> Chain(a * (x[2] - x[1]), x[3] * x[1] - x[2], b - x[1] * x[2] - c * x[3])
Rossler(a, b, c) = x -> Chain(-(x[2] + x[3]), x[1] + a * x[2], b + x[3] * (x[1] - c))
# the two broken systems of the file, fixed as in the port (defect B22)
ChemicalKinetics(a1, a2, a3, a4, a5, k1, k2, k5) = x -> Chain(
    x[1] * (a1 - k1 * x[1] - x[3] - x[2]) + k2 * x[2] * x[2] + a3,
    x[2] * (x[1] - k2 * x[2] - a5) + a2,
    x[3] * (a4 - x[1] - k5 * x[3]) + a3)
Rossler4(a, b, c, d) = x -> Chain(-(x[2] + x[3]), x[1] + a * x[2] + x[4], b + x[3] * x[1], d * x[4] - c * x[3])

function chaoscase(name, ps, f, xs)
    s = odesolve(f, xs)
    ts = collect(Float64, points(s)); X = flatstates(fiber(s)); d = length(coeffs(xs))
    progress("  ", name, " ", ps, " n=", length(ts), " last=", fiber(s)[end])
    Dict("system" => name, "params" => hxs(ps), "x0" => hxs(coeffs(xs)), "n" => length(ts),
        "tlast" => hx(ts[end]), "last" => hxs(X[end-d+1:end]),
        "every4096" => hxs(flatstates([X[(k-1)*d+1:k*d] for k in 1:4096:length(ts)])),
        "digest" => digest(vcat(ts, X)))
end

function chaoscases()
    out = Any[]
    push!(out, chaoscase("Lorenz", [10.0, 28.0, 8 / 3], Lorenz(10.0, 28.0, 8 / 3), x0))
    push!(out, chaoscase("Lorenz", [10.0, 60.0, 8 / 3], Lorenz(10.0, 60.0, 8 / 3), x0))
    push!(out, chaoscase("DiskDynamo", [14.625, 1.0, 5.0], DiskDynamo(14.625, 1.0, 5.0), x0))
    for c in (2.4, 3.5, 4.0, 4.23, 4.3, 5.0, 5.7)
        push!(out, chaoscase("Rossler", [1 / 5, 1 / 5, c], Rossler(1 / 5, 1 / 5, c), x0))
    end
    for ps in ([0.0, 0.0, 12.0], [0.0, 0.0, 25.0], [0.343, 1.82, 9.75])
        push!(out, chaoscase("Rossler", ps, Rossler(ps...), x0))
    end
    ck = [30.0, 0.01, 0.01, 16.5, 10.0, 0.25, 0.001, 0.5]
    push!(out, chaoscase("ChemicalKinetics", ck, ChemicalKinetics(ck...), x0))
    r4 = [1 / 4, 3.0, 0.5, 0.05]
    push!(out, chaoscase("Rossler4", r4, Rossler4(r4...), Chain(10.0, 10.0, 10.0, 10.0)))
    out
end
save("chaos", Dict("meta" => meta, "cases" => chaoscases()))

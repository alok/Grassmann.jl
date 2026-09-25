# geodesic.json: geodesics of the upper half plane (README), geosolve(Γ, x0, v0, 10π, 7) (RK4, h = 2^-7).
halfplane(x) = TensorOperator(Chain(
    Chain(Chain(0.0, inv(x[2])), Chain(-inv(x[2]), 0.0)),
    Chain(Chain(-inv(x[2]), 0.0), Chain(0.0, -inv(x[2])))))

function geocase(a, v)
    z = geosolve(halfplane, a, v, 10pi, 7)
    ts = collect(Float64, points(z)); X = flatstates(fiber(z))
    c = a[1] + a[2] * v[2] / v[1]; r = sqrt((a[1] - c)^2 + a[2]^2)
    Dict("x0" => hxs(coeffs(a)), "v0" => hxs(coeffs(v)), "n" => length(ts), "tlast" => hx(ts[end]),
        "every64" => hxs(flatstates([X[2k-1:2k] for k in 1:64:length(ts)])), "last" => hxs(X[end-1:end]),
        "digest" => digest(vcat(ts, X)), "analytic_endpoint_x" => hx(c + r))
end

function geocases()
    [geocase(a, v) for (a, v) in ((Chain(1.0, 1.0), Chain(1.0, 2.0)), (Chain(1.0, 0.1), Chain(1.0, 2.0)),
        (Chain(1.0, 0.5), Chain(1.0, 2.0)), (Chain(1.0, 1.0), Chain(1.0, 1.0)), (Chain(1.0, 1.0), Chain(1.0, 1.5)))]
end
save("geodesic", Dict("meta" => meta, "cases" => geocases()))

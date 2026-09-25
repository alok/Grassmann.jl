# runtests.json: test/runtests.jl's odesolve(Lorenz, x0, 2π, 7, Val(k), Val(4)) for k = 0 … 4
# (Heun, RK4, adaptive Cash–Karp, ABM4, adaptive ABM4; the adaptive ones with the load.jl patches).
function runtestcase(k)
    s = odesolve(lorenz, x0, 2π, 7, Val(k), Val(4))
    ts = collect(Float64, points(s)); X = flatstates(fiber(s))
    Dict("k" => k, "n" => length(ts), "tlast" => hx(ts[end]), "last" => hxs(X[end-2:end]), "digest" => digest(vcat(ts, X)))
end
save("runtests", Dict("meta" => meta, "cases" => [runtestcase(k) for k in 0:4]))

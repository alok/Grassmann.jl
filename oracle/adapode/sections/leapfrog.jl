# leapfrog.json: LeapIntegrator{1,2} on u' = -fprime(u) / u'' = fprime(u) with fprime(v) = -K v,
# K = tridiag(-1, 2, -1) (3×3), the state a TensorField over 1:3.
const Kleap = [2.0 -1 0; -1 2 -1; 0 -1 2]
leapfprime(v) = -(Kleap * collect(localfiber(v)))

function leapcase(o, dt, tmax, gap)
    u0 = TensorField(1:3, [1.0, 0.0, -0.5])
    u1 = TensorField(1:3, [0.9, 0.1, -0.45])
    s = odesolve(LeapCondition(leapfprime, u0, u1, dt, tmax), LeapIntegrator{o}(gap))
    Dict("order" => o, "dt" => hx(dt), "tmax" => hx(tmax), "gap" => gap, "size" => collect(size(s)),
        "data" => hxs(vec(fiber(s))), "times" => hxs(collect(points(s).v[end])))
end

leapcases() = [leapcase(o, dt, tmax, gap) for o in (1, 2) for (dt, tmax, gap) in ((0.01, 1.0, 5), (0.013, 0.7, 3))]
save("leapfrog", Dict("meta" => meta, "u0" => hxs([1.0, 0.0, -0.5]), "u1" => hxs([0.9, 0.1, -0.45]), "cases" => leapcases()))

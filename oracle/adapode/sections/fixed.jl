# fixed.json: fixed-step integrators on the test problems, full trajectories.
function runcase(pn, method, o, h, skip, tmax; compat = false)
    _, f, x0 = only(filter(p -> p[1] == pn, probs))
    ic = InitialCondition(f, x0, tmax)
    I = method == "RK" ? ExplicitIntegrator{o}(h, skip) :
        method == "Heun" ? EulerHeunIntegrator(h, skip) :
        method == "ABM" ? MultistepIntegrator{o}(h, skip) : error(method)
    d = Dict{String,Any}("problem" => pn, "method" => method, "order" => o, "h" => hx(h), "skip" => skip,
        "tmax" => hx(tmax), "compat" => compat)
    try
        s = odesolve(ic, I)
        if skip == 0
            d["n"] = 1; d["t"] = [hx(point(s))]; d["x"] = hxs(coeffs(fiber(s)))
        else
            d["n"] = length(s); d["t"] = hxs(collect(points(s))); d["x"] = hxs(flatstates(fiber(s)))
        end
    catch e
        d["E"] = errstr(e)
    end
    d
end

function fixedcases()
    fixed = Any[]
    h8 = 2.0^-8
    for (pn, _, _) in probs
        for o in 1:4, skip in (0, 1, 4)
            push!(fixed, runcase(pn, "RK", o, h8, skip, 1.0))
        end
        push!(fixed, runcase(pn, "Heun", 0, h8, 1, 1.0))
        push!(fixed, runcase(pn, "Heun", 0, h8, 4, 1.0; compat = true))   # B7: one step per stored point
        for o in 1:5
            push!(fixed, runcase(pn, "ABM", o, h8, 1, 1.0))
        end
        push!(fixed, runcase(pn, "ABM", 4, h8, 0, 1.0; compat = true))     # B3: discarded bootstrap
        push!(fixed, runcase(pn, "RK", 4, h8, 0, -0.5))                    # backward
    end
    # non-dyadic steps: grid times differ from accumulated ones
    for (m, o, skip) in (("RK", 4, 1), ("RK", 4, 3), ("RK", 2, 0), ("Heun", 0, 1), ("ABM", 3, 1), ("ABM", 5, 1), ("ABM", 2, 1))
        push!(fixed, runcase("nonauto", m, o, 0.1, skip, 1.0))
    end
    push!(fixed, runcase("osc", "RK", 4, h8, 1, 1.3))
    push!(fixed, runcase("osc", "RK", 4, h8, 0, 1.3))
    push!(fixed, runcase("osc", "ABM", 4, h8, 1, 1.3))
    fixed
end
save("fixed", Dict("meta" => meta, "cases" => fixedcases()))

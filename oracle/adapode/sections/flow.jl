# flow.json: the flow API (Lorenz, h = 2^-11), flows of fields of states, field-valued systems, and
# the flow of a vector field sampled on a grid.
lt(r) = Dict("t" => hx(point(r)), "x" => hxs(coeffs(fiber(r))))
fieldstart() = (t -> Chain(10.0 + t, 10.0 - t, 10.0 + 2t)).(TensorField(0:0.5:1.5))
fieldsystem(x) = TensorField(base(fiber(x)), (c -> Chain(-c[2], c[1], 0.1c[3])).(fiber(fiber(x))))

function flowout()
    flows = Dict{String,Any}("meta" => meta)
    L1 = Flow(lorenz, 1.0)
    for o in 1:4
        flows["RK$(o)_skip0"] = lt(L1(x0, ExplicitIntegrator{o}(2^-11, 0)))
    end
    flows["default_ASIS"] = lt(L1(x0))                                   # MultistepIntegrator{4}(2^-11,0): B3
    flows["integrator_default"] = lt(L1(x0, Adapode.integrator(L1)))     # RK4 2^-11 skip 0
    flows["backward"] = lt(Flow(lorenz, -0.5)(x0, ExplicitIntegrator{4}(2^-11, 0)))
    flows["localtensor_ASIS"] = lt(L1(0.5 ↦ x0, ExplicitIntegrator{4}(2^-11, 0)))   # B5: over [0, 1.5]
    flows["from0_to_1.5"] = lt(Flow(lorenz, 1.5)(x0, ExplicitIntegrator{4}(2^-11, 0)))
    let s = FlowIntegral(lorenz, 1.0)(x0)
        ts = collect(Float64, points(s)); X = flatstates(fiber(s))
        flows["FlowIntegral"] = Dict("n" => length(ts), "last" => hxs(X[end-2:end]), "digest" => digest(vcat(ts, X)))
    end
    # a flow applied to a field of states (Julia `(Φ::Flow)(x0::TensorField)`, skip 0)
    x0f = fieldstart()
    let r = Flow(lorenz, 0.25)(x0f, ExplicitIntegrator{4}(2.0^-8, 0))
        flows["field_flow"] = Dict("t" => hx(point(r)), "x" => hxs(flatstates(fiber(fiber(r)))), "x0" => hxs(flatstates(fiber(x0f))))
    end
    # a field-valued system on a field state (skip 0; Julia's skip >= 1 fails to convert the output base)
    let r = odesolve(InitialCondition(fieldsystem, x0f, 1.0), ExplicitIntegrator{4}(2.0^-6, 0))
        flows["field_system"] = Dict("t" => hx(point(r)), "x" => hxs(flatstates(fiber(fiber(r)))))
    end
    # the flow of a vector field sampled on a grid (Julia `exp(X)`: multilinear interpolation)
    vf = (x -> Chain(-x[2], x[1])).(TensorField(ProductSpace(-2:0.5:2, -2:0.5:2)))
    flows["vectorfield_exp"] = lt(exp(vf)(Chain(1.0, 0.25), ExplicitIntegrator{4}(2.0^-6, 0)))
    flows["vectorfield_rk2"] = lt(Flow(vf, 1.0)(Chain(1.0, 0.25), ExplicitIntegrator{2}(2.0^-5, 0)))
    flows
end
save("flow", flowout())

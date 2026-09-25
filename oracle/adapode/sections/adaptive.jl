# adaptive.json: ExplicitAdaptor{1:5} and MultistepAdaptor{1:5} (Julia's controller, B2 included).
# tol = 7 on every problem, tol = 10 on osc/nonauto, and h0 = 1e-4 (≤ 1e-4, so hmax = 1e-4 and the
# step may double) for the fifth orders on osc/nonauto. (Julia's error window is
# 10^(log2 h - 3) … 10^(log2 h): h0 = 1e-5 asks for errors below 2.5e-17, and the low orders halve
# the step down to hmin and never finish.)
function adaptivecase(pn, f, x0, tl, tol, o, lab)
    ic = InitialCondition(f, x0, 1.0)
    I = lab == "RKA" ? ExplicitAdaptor{o}(tol) : MultistepAdaptor{o}(tol)
    d = Dict{String,Any}("problem" => pn, "method" => lab, "order" => o, "tol" => tl, "h0" => hx(I.tol), "tmax" => hx(1.0))
    try
        s = odesolve(ic, I)
        ts = collect(Float64, points(s)); X = flatstates(fiber(s)); k = length(coeffs(x0))
        d["n"] = length(ts); d["digest"] = digest(vcat(ts, X))
        m = length(ts) <= 1500 ? length(ts) : 20
        d["t_head"] = hxs(ts[1:m]); d["x_head"] = hxs(X[1:m*k])
        d["t_tail"] = hxs(ts[max(1, end - 4):end])
        d["x_tail"] = hxs(X[max(1, length(X) - 5k + 1):end])
    catch e
        d["E"] = errstr(e)
    end
    progress("  ", pn, " ", lab, o, " tol=", tl, " n=", get(d, "n", -1))
    d
end

function adaptivecases()
    out = Any[]
    for (pn, f, x0) in probs, (tl, tol) in (("7", 7), ("10", 10), ("1e-4", 1e-4)), o in 1:5, lab in ("RKA", "ABMA")
        tl == "10" && !(pn in ("osc", "nonauto")) && continue
        tl == "1e-4" && !(pn in ("osc", "nonauto") && o == 5) && continue
        push!(out, adaptivecase(pn, f, x0, tl, tol, o, lab))
    end
    out
end
save("adaptive", Dict("meta" => meta, "cases" => adaptivecases()))

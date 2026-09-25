# oracle/suites/composite.jl: transcendental and inverse functions on Float elements
# (grassmann-algebra.md §4.10-4.11, composite.jl, AbstractTensors generic trig).
#
# Grassmann evaluates most of these with power series that stop when the running norm changes by
# less than Julia's default `isapprox` tolerance (rtol = √eps ≈ 1.5e-8), or in closed form when
# the argument squares to a scalar. Compare with the per-op tolerances in the `tolerance` table
# (dense vectors, `‖out − expect‖₂ ≤ atol + rtol·max(‖out‖₂, ‖expect‖₂)`); result kinds are
# informational here.

shards() = ["E2", "E3", "E4", "M4", "CGA3"]

const COMPOSITE_TOL = Obj(
    "exp"  => Obj("rtol" => 1e-7, "atol" => 1e-9),
    "log"  => Obj("rtol" => 1e-6, "atol" => 1e-8),
    "sqrt" => Obj("rtol" => 1e-6, "atol" => 1e-8),
    "sin"  => Obj("rtol" => 1e-7, "atol" => 1e-9),
    "cos"  => Obj("rtol" => 1e-7, "atol" => 1e-9),
    "tan"  => Obj("rtol" => 1e-6, "atol" => 1e-8),
    "sinh" => Obj("rtol" => 1e-7, "atol" => 1e-9),
    "cosh" => Obj("rtol" => 1e-7, "atol" => 1e-9),
    "inv"  => Obj("rtol" => 1e-12, "atol" => 1e-14),
    "div"  => Obj("rtol" => 1e-12, "atol" => 1e-14),
    "pow"  => Obj("rtol" => 1e-12, "atol" => 1e-12),
)

const COMPOSITE_OPS = Obj(
    "exp" => "exp(a)", "log" => "log(a)", "sqrt" => "sqrt(a)", "sin" => "sin(a)", "cos" => "cos(a)",
    "tan" => "tan(a)", "sinh" => "sinh(a)", "cosh" => "cosh(a)", "inv" => "inv(a)", "div" => "a / b",
    "pow" => "a ^ k  (k given in the case)",
)

"Composite-suite inputs: `(label, src, roles)`; roles select which ops apply."
function composite_samples(V, rng, spacename)
    n = mdims(V)
    I = (UInt(1) << n) - 1
    e1, e2 = blade(n, 1, 1), blade(n, 1, 2)
    e12 = blade(n, 2, 1)
    small(k) = coeffs(rng, r -> round(0.5 * randn(r); digits = 3), k)
    s = Tuple{String,String,Vector{Symbol}}[]
    push!(s, ("scalar", "Single{V}(0.3)", [:exp, :trig, :log, :inv, :pow]))
    push!(s, ("scalar1", "Single{V}(1.2)", [:log, :inv]))
    push!(s, ("vec1", "0.7*" * bsrc(n, e1), [:exp, :trig, :inv, :pow]))
    push!(s, ("vec", "Chain{V,1}($(vals(small(n))))", [:exp, :trig, :inv, :pow, :div]))
    for θ in (0.1, 0.5, 1.0)
        push!(s, ("biv$θ", "$θ*" * bsrc(n, e12), [:exp, :trig, :inv, :pow]))
    end
    push!(s, ("biv", "Chain{V,2}($(vals(small(binomial(n, 2)))))", [:exp, :trig, :pow]))
    push!(s, ("pseudo", "0.4*" * bsrc(n, I), [:exp, :trig, :inv, :pow]))
    push!(s, ("rotor", "exp(0.3*" * bsrc(n, e12) * ")", [:exp, :log, :sqrt, :inv, :pow, :div]))
    push!(s, ("couple", "Couple{V,$(bsrc(n, e12))}(1.0, 0.5)", [:exp, :trig, :log, :sqrt, :inv, :pow, :div]))
    push!(s, ("couple_vec", "Couple{V,$(bsrc(n, e1))}(1.0, 0.25)", [:exp, :trig, :pow]))
    sp = small(1 << (n - 1))
    push!(s, ("spinor", "Spinor{V}($(vals(0.5 .* sp)))", [:exp, :trig, :pow]))
    sp1 = copy(sp) .* 0.3
    sp1[1] = 1.0
    push!(s, ("spinor1", "Spinor{V}($(vals(round.(sp1; digits = 4))))", [:exp, :log, :sqrt, :inv, :pow, :div]))
    mv = small(1 << n) .* 0.5
    push!(s, ("mv", "Multivector{V}($(vals(round.(mv; digits = 4))))", [:exp, :trig, :pow]))
    mv1 = small(1 << n) .* 0.2
    mv1[1] = 1.0
    push!(s, ("mv1", "Multivector{V}($(vals(round.(mv1; digits = 4))))", [:exp, :log, :sqrt, :pow]))
    push!(s, ("blade_versor", "Multivector{V}($(vals([1.0; zeros((1 << n) - 2); 0.5])))", [:inv, :div, :pow]))
    if Leibniz.hasconformal(V) || hasinf(V)
        # null bivector v∞∧v₁ (translator generator) and the Minkowski-plane bivector v∞∅
        einf1 = UInt(1) | blade(n, 1, 1 + (hasorigin(V) ? 2 : 1))
        push!(s, ("null_biv", "0.5*" * bsrc(n, einf1), [:exp, :pow]))
        hasorigin(V) && push!(s, ("minkowski_biv", "0.5*" * bsrc(n, UInt(3)), [:exp, :trig, :inv, :pow]))
    end
    return s
end

function build(sh, defects)
    rng = rng_for("composite", sh)
    top, desc = space_header("composite", sh, sh)
    m = sandbox(sh)
    V = evalsrc(m, "V")
    samples = composite_samples(V, rng, sh)
    xs, inobjs = build_inputs(m, [(l, s) for (l, s, _) in samples]; vshow = desc["show"])
    roles = Dict(l => r for (l, _, r) in samples)
    top["ops"] = COMPOSITE_OPS
    top["tolerance"] = COMPOSITE_TOL
    top["inputs"] = inobjs
    cl = CaseLog()
    run1!(op, i, f; extra = Pair{String,Any}[]) = make_case(cl, desc, op, [i - 1], f; extra = extra)
    labels = [o["label"] for o in inobjs]
    for i in eachindex(xs)
        a = xs[i]
        r = roles[labels[i]]
        :exp in r && run1!("exp", i, () -> exp(a))
        if :trig in r
            for (op, f) in (("sin", sin), ("cos", cos), ("tan", tan), ("sinh", sinh), ("cosh", cosh))
                run1!(op, i, () -> f(a))
            end
        end
        :log in r && run1!("log", i, () -> log(a))
        :sqrt in r && run1!("sqrt", i, () -> sqrt(a))
        :inv in r && run1!("inv", i, () -> inv(a))
        if :pow in r
            for k in (0, 1, 2, 3, 5, 8, 9)
                run1!("pow", i, () -> a^k; extra = Pair{String,Any}["k" => k])
            end
        end
    end
    divs = [i for i in eachindex(xs) if :div in roles[labels[i]]]
    for i in divs, j in divs
        a, b = xs[i], xs[j]
        make_case(cl, desc, "div", [i - 1, j - 1], () -> a / b)
    end
    top["cases"] = cl.cases
    return retag!(top, defects)
end

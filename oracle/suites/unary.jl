# oracle/suites/unary.jl: unary maps (involutions, complements/Hodge, metric maps, parity parts,
# grade projections, abs2/norm, adjoint, Multivector conversion) over the per-space kind sample.
#
# Reference (`ref`): for the linear maps, the same map applied to the input converted to
# Multivector; for `Multivector` the input's own dense vector. `abs2`, `norm` and `adjoint` have
# no reference (they are not linear, or change the space).

shards() = ["E2", "E3", "E4", "E5", "I4", "M4", "S4", "D3", "PGA2", "PGA3", "INF3", "ORG3",
            "CGA2", "CGA3", "DUAL3", "TAN2"]

function unary_ref(op, a, V)
    n = mdims(V)
    da = todense(a)
    da === nothing && return nothing
    op == "Multivector" && return da
    mv = mv_of(V, da)
    if startswith(op, "grade:")
        return todense(Grassmann.grade(mv, parse(Int, op[7:end])))
    end
    op in LINEAR_UNARY || return nothing
    return todense(UNARY[op][2](mv))
end

function build(sh, defects)
    rng = rng_for("unary", sh)
    top, desc = space_header("unary", sh, sh)
    m = sandbox(sh)
    V = evalsrc(m, "V")
    n = mdims(V)
    samples = lattice_samples(V, rng; infinity = true, zero_single = false, floats = true)
    filter!(s -> !(s[1] in ("Single1b", "Single2b")), samples)
    xs, inobjs = build_inputs(m, samples; vshow = desc["show"])
    opkeys = [k for (k, _, _) in UNARY_OPS]
    ops = ops_table(opkeys, UNARY)
    for g in 0:n
        ops["grade:$g"] = "grade(a, $g)"
    end
    top["ops"] = ops
    top["reference"] = "linear maps: same map on the Multivector-converted input; Multivector: the input's dense vector"
    top["inputs"] = inobjs
    cl = CaseLog()
    for i in eachindex(xs)
        a = xs[i]
        for op in opkeys
            f = UNARY[op][2]
            make_case(cl, desc, op, [i - 1], () -> f(a); ref = () -> unary_ref(op, a, V))
        end
        for g in 0:n
            op = "grade:$g"
            make_case(cl, desc, op, [i - 1], () -> Grassmann.grade(a, g); ref = () -> unary_ref(op, a, V))
        end
    end
    top["cases"] = cl.cases
    return retag!(top, defects)
end

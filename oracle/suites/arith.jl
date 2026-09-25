# oracle/suites/arith.jl: `+`/`-` over all ordered kind pairs (the representation lattice of
# grassmann-types.md §4.5, including Zero/One/Infinity), unary minus, and scalar arithmetic
# (`s*x`, `x*s`, `x/s`, `x//s`, `x±s`, `s±x`) with Julia numbers.
#
# Reference (`ref`): the exact dense sum/difference/scaling of the inputs' dense vectors
# (numbers act as multiples of One). A `ref_mismatch` flag means Julia's value is not the
# linear combination of its inputs (e.g. the PseudoCouple ± PseudoCouple defect).

shards() = ["E2", "E3", "E4", "M4", "D3", "PGA3", "INF3", "CGA2", "CGA3", "DUAL3", "TAN2"]

const ARITH_OPS = ["add", "sub", "mul", "div", "rdiv", "neg"]

function arith_ref(op, a, b, n)
    da = dense_in(a, n)
    da === nothing && return nothing
    if op == "neg"
        return Any[-x for x in da]
    end
    db = dense_in(b, n)
    db === nothing && return nothing
    if op == "add"
        return Any[x + y for (x, y) in zip(da, db)]
    elseif op == "sub"
        return Any[x - y for (x, y) in zip(da, db)]
    elseif op == "mul"
        kindof(a) == "Number" && return Any[a * y for y in db]
        kindof(b) == "Number" && return Any[x * b for x in da]
        return nothing
    elseif op == "div"
        return Any[x / b for x in da]
    elseif op == "rdiv"
        return Any[x // b for x in da]
    end
    return nothing
end

function build(sh, defects)
    rng = rng_for("arith", sh)
    top, desc = space_header("arith", sh, sh)
    m = sandbox(sh)
    V = evalsrc(m, "V")
    n = mdims(V)
    samples = lattice_samples(V, rng; infinity = true, zero_single = true, floats = true)
    # Julia never forms Couple/PseudoCouple by + in tangent spaces, and its Couple algebra assumes
    # the pseudoscalar grade is grade(V), which excludes the derivation indices; leave them out
    diffvars(V) > 0 && filter!(s -> !startswith(s[1], "Couple") && !startswith(s[1], "PseudoCouple"), samples)
    nums = [("n:2", "2"), ("n:0", "0"), ("n:0.5", "0.5")]
    xs, inobjs = build_inputs(m, vcat(samples, nums); vshow = desc["show"])
    top["ops"] = Obj("add" => "a + b", "sub" => "a - b", "mul" => "a * b", "div" => "a / b",
                     "rdiv" => "a // b", "neg" => "-a")
    top["reference"] = "exact linear combination of the inputs' dense vectors (numbers = multiples of One)"
    top["inputs"] = inobjs
    cl = CaseLog()
    isnum(i) = kindof(xs[i]) == "Number"
    elems = [i for i in eachindex(xs) if !isnum(i)]
    num(v) = findfirst(i -> isnum(i) && xs[i] == v && typeof(xs[i]) == typeof(v), eachindex(xs))
    i2, i0, ih = num(2), num(0), num(0.5)
    run!(op, is) = begin
        f = length(is) == 1 ? (() -> -xs[is[1]]) : (() -> BINARY[op][2](xs[is[1]], xs[is[2]]))
        make_case(cl, desc, op, [i - 1 for i in is], f;
                  ref = () -> arith_ref(op, xs[is[1]], length(is) == 2 ? xs[is[2]] : nothing, n))
    end
    # the lattice: every ordered pair of elements under + and -
    for i in elems, j in elems
        run!("add", [i, j])
        run!("sub", [i, j])
    end
    # unary minus and scalar arithmetic
    for i in elems
        run!("neg", [i])
        for s in (i2, i0, ih)
            run!("add", [i, s]); run!("add", [s, i])
            run!("sub", [i, s]); run!("sub", [s, i])
        end
        run!("mul", [i2, i]); run!("mul", [i, i2]); run!("mul", [ih, i])
        run!("div", [i, i2])
        isexact(first(todense_or_zero(xs[i]))) && run!("rdiv", [i, i2])
    end
    top["cases"] = cl.cases
    return retag!(top, defects)
end

todense_or_zero(x) = (d = todense(x); d === nothing ? Any[0.0] : d)

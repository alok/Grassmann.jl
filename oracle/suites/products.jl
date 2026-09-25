# oracle/suites/products.jl: every binary product of grassmann-products.md §2.1 over all ordered
# pairs of the per-space kind sample (Int coefficients, plus Float Chain{1}/Multivector for n ≤ 4).
#
# Reference (`ref`): the same operation evaluated on the inputs converted to Multivector (Julia's
# Multivector×Multivector kernels), i.e. the bilinear extension of the basis tables. For the
# sandwich products `⊘`/`>>>` with a graded left operand and a non-Multivector right operand the
# reference is projected onto the left operand's grade (Julia's documented behavior, §4.6).

shards() = ["E2", "E3", "E4", "E5", "M4", "D3", "PGA3", "INF3", "CGA2", "CGA3"]

const PRODUCT_OPS = ["mul", "wedge", "vee", "contraction", "lcontraction", "lshift", "rshift", "revmul",
                     "scalarprod", "cross", "sandwich", "tsandwich", "veedot", "antidot"]

const TERM_KINDS = ("Zero", "One", "Infinity", "Submanifold", "Single")

function product_ref(op, a, b, V)
    n = mdims(V)
    da, db = todense(a), todense(b)
    (da === nothing || db === nothing) && return nothing
    f = BINARY[op][2]
    op in ("sandwich", "tsandwich") && return sandwich_ref(op, a, b, da, db, V)
    return todense(f(mv_of(V, da), mv_of(V, db)))
end

"""
Reference for `x ⊘ y` (op `sandwich`, x = a) and `y >>> x` (op `tsandwich`, x = b), following
Julia's documented projection rule (grassmann-products.md §4.6): a graded `x` sandwiched by a
parity-homogeneous non-Multivector `y` is projected onto grade(x), except when both are terms;
a Couple/PseudoCouple `x` is split into its two parts, each sandwiched (and projected) separately.
"""
function sandwich_ref(op, a, b, da, db, V)
    n = mdims(V)
    f = BINARY[op][2]
    x, y, dx, dy = op == "sandwich" ? (a, b, da, db) : (b, a, db, da)
    sw(xd) = todense(op == "sandwich" ? f(mv_of(V, xd), mv_of(V, dy)) : f(mv_of(V, dy), mv_of(V, xd)))
    ky = kindof(y)
    # a Couple with odd B, or a PseudoCouple whose B parity differs from n's, is not
    # parity-homogeneous: Julia sandwiches with multispin(y), a Multivector (no projection)
    if ky == "Couple" && isodd(count_ones(blade_bits(y)))
        ky = "Multivector"
    elseif ky == "PseudoCouple" && isodd(count_ones(blade_bits(y))) != isodd(n)
        ky = "Multivector"
    end
    part(xd, G, isterm) = (ky == "Multivector" || (isterm && ky in TERM_KINDS)) ? sw(xd) : project_grade(sw(xd), n, G)
    kx = kindof(x)
    if kx in GRADED_KINDS
        return part(dx, sgrade(x), kx in TERM_KINDS)
    elseif kx in ("Couple", "PseudoCouple")
        B = blade_bits(x)
        i1, i2 = kx == "Couple" ? (1, Leibniz.basisindex(n, B)) : (Leibniz.basisindex(n, B), 1 << n)
        g1, g2 = kx == "Couple" ? (0, count_ones(B)) : (count_ones(B), n)
        p1 = Any[zero(c) for c in dx]
        p1[i1] = realvalue(x)
        p2 = Any[zero(c) for c in dx]
        p2[i2] = imagvalue(x)
        return Any[u + v for (u, v) in zip(part(p1, g1, true), part(p2, g2, true))]
    end
    return sw(dx)
end

function build(sh, defects)
    rng = rng_for("products", sh)
    top, desc = space_header("products", sh, sh)
    m = sandbox(sh)
    V = evalsrc(m, "V")
    n = mdims(V)
    # Infinity is left out here: its product rules are the trivial absorbing ones (products.md
    # §4.8) and most of its methods are missing in Julia (see the arith/unary suites)
    samples = lattice_samples(V, rng; infinity = false, zero_single = false, floats = n <= 4)
    # the second vector/bivector Singles only matter for the + lattice (arith suite)
    filter!(s -> !(s[1] in ("Single1b", "Single2b")), samples)
    xs, inobjs = build_inputs(m, samples; vshow = desc["show"])
    top["ops"] = ops_table(PRODUCT_OPS, BINARY)
    top["reference"] = "same op on Multivector-converted inputs (sandwich: projected to grade(a) when a is graded and b is not a Multivector and not both are terms)"
    top["inputs"] = inobjs
    cl = CaseLog()
    for op in PRODUCT_OPS
        f = BINARY[op][2]
        for i in eachindex(xs), j in eachindex(xs)
            a, b = xs[i], xs[j]
            make_case(cl, desc, op, [i - 1, j - 1], () -> f(a, b); ref = () -> product_ref(op, a, b, V))
        end
    end
    top["cases"] = cl.cases
    return retag!(top, defects)
end

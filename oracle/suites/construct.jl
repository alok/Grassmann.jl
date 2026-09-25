# oracle/suites/construct.jl: every element kind in every registered space, built from Julia
# source, recorded with its native storage (`native`), dense vector, `show` and compact `show`,
# and the full Julia type string. Tests constructors, index maps (native order ↔ Multivector
# order) and display. Display-heavy coefficient types (Rational, Complex, Bool, NaN/Inf/-0.0,
# compact rounding, typemin) are added in E3, M4 and CGA2.

shards() = [n for (n, _, _) in SPACE_REGISTRY]

const DISPLAY_SPACES = ("E3", "M4", "CGA2")

"Float with three decimals (typical user input; prints identically in full and compact form)."
cr(rng) = round(randn(rng); digits = 3)

function construct_samples(V, rng, spacename)
    n = mdims(V)
    I = (UInt(1) << n) - 1
    s = Tuple{String,String}[]
    for k in 1:(1 << n)
        push!(s, ("blade:$(string(Λ(V).b[k]))", "Λ(V).b[$k]"))
    end
    append!(s, lattice_samples(V, rng; infinity = true, zero_single = true, floats = true))
    # Float variants of every container kind
    push!(s, ("Single1R", "$(lit(cr(rng)))*" * bsrc(n, blade(n, 1, 1))))
    for g in 0:n
        push!(s, ("Chain$(g)R", "Chain{V,$g}($(vals(coeffs(rng, cr, binomial(n, g)))))"))
    end
    if n >= 2
        h = 1 << (n - 1)
        push!(s, ("SpinorR", "Spinor{V}($(vals(coeffs(rng, cr, h))))"))
        push!(s, ("CoSpinorR", "CoSpinor{V}($(vals(coeffs(rng, cr, h))))"))
        push!(s, ("CoupleR", "Couple{V,$(bsrc(n, blade(n, 2, 1)))}($(lit(cr(rng))), $(lit(cr(rng))))"))
        push!(s, ("PseudoCoupleR", "PseudoCouple{V,$(bsrc(n, blade(n, 1, 1)))}($(lit(cr(rng))), $(lit(cr(rng))))"))
        push!(s, ("SpinorZero", "Spinor{V}($(vals(zeros(Int, h))))"))
        push!(s, ("Phasor", "Phasor(2.0, 0.5*" * bsrc(n, blade(n, 2, 1)) * ")"))
        push!(s, ("PhasorSub", "Phasor(1, " * bsrc(n, blade(n, 2, 1)) * ")"))
    end
    push!(s, ("MultivectorR", "Multivector{V}($(vals(coeffs(rng, cr, 1 << n))))"))
    # zero-skipping and the `v⃖` suffix in Multivector display
    push!(s, ("Chain1Zero", "Chain{V,1}($(vals(zeros(Int, n))))"))
    push!(s, ("MultivectorZero", "Multivector{V}($(vals(zeros(Int, 1 << n))))"))
    push!(s, ("MultivectorScalar", "Multivector{V}($(vals([3; zeros(Int, (1 << n) - 1)])))"))
    push!(s, ("MultivectorScalarF", "Multivector{V}($(vals([1.0; zeros((1 << n) - 1)])))"))
    push!(s, ("MultivectorNegScalar", "Multivector{V}($(vals([-3; zeros(Int, (1 << n) - 2); 1])))"))
    spacename in DISPLAY_SPACES && append!(s, display_samples(V, rng))
    return s
end

"Coefficient types and special values that stress Julia's number display inside elements."
function display_samples(V, rng)
    n = mdims(V)
    e1, e12 = blade(n, 1, 1), blade(n, 2, 1)
    s = Tuple{String,String}[]
    push!(s, ("Chain1Rational", "Chain{V,1}($(vals([(1//2), (-1//3), (0//1), (5//1), (-7//4)][mod1.(1:n, 5)])))"))
    push!(s, ("Chain1ComplexInt", "Chain{V,1}($(vals([Complex(1,2), Complex(-1,-2), Complex(0,0), Complex(0,-3), Complex(3,0)][mod1.(1:n, 5)])))"))
    push!(s, ("Chain1ComplexF", "Chain{V,1}($(vals([Complex(1.5,-2.5), Complex(-0.0,1/3), Complex(NaN,Inf), Complex(1e-5,1e6), Complex(0.1,0.2)][mod1.(1:n, 5)])))"))
    push!(s, ("Chain1Bool", "Chain{V,1}($(vals([true, false, true, true, false][mod1.(1:n, 5)])))"))
    push!(s, ("Chain1Special", "Chain{V,1}($(vals([1.0, -0.0, NaN, Inf, -Inf][mod1.(1:n, 5)])))"))
    push!(s, ("Chain1Compact", "Chain{V,1}($(vals([1/3, 2/3, 1e-20, 123456.789, 1.0e6][mod1.(1:n, 5)])))"))
    push!(s, ("Chain1Big", "Chain{V,1}($(vals([typemin(Int), 3, typemax(Int), -1, 0][mod1.(1:n, 5)])))"))
    push!(s, ("Chain2Compact", "Chain{V,2}($(vals([0.1+0.2, 1e-5, 1e-4, 999999.0, 1234567.0, 5e-324][mod1.(1:binomial(n,2), 6)])))"))
    push!(s, ("SingleRational", "(1//2)*" * bsrc(n, e1)))
    push!(s, ("SingleNegRational", "(-3//4)*" * bsrc(n, e12)))
    push!(s, ("SingleComplex", "Complex(1, 2)*" * bsrc(n, e1)))
    push!(s, ("SingleComplexF", "Complex(1.5, -2.5)*" * bsrc(n, e12)))
    push!(s, ("SingleNaN", "NaN*" * bsrc(n, e1)))
    push!(s, ("SingleInf", "Inf*" * bsrc(n, e1)))
    push!(s, ("SingleNegInf", "-Inf*" * bsrc(n, e1)))
    push!(s, ("SingleNegZero", "-0.0*" * bsrc(n, e1)))
    push!(s, ("SingleThird", "(1/3)*" * bsrc(n, e1)))
    push!(s, ("SingleBool", "true*" * bsrc(n, e1)))
    push!(s, ("SingleScalarF", "Single{V}(2.5)"))
    push!(s, ("SingleTypemin", "typemin(Int)*" * bsrc(n, e1)))
    push!(s, ("MultivectorRational", "Multivector{V}($(vals([(1//2); fill(0//1, (1 << n) - 2); (-1//3)])))"))
    push!(s, ("MultivectorRationalScalar", "Multivector{V}($(vals([(1//2); fill(0//1, (1 << n) - 1)])))"))
    push!(s, ("MultivectorComplexScalar", "Multivector{V}($(vals([Complex(1,2); fill(Complex(0,0), (1 << n) - 1)])))"))
    push!(s, ("MultivectorComplex", "Multivector{V}($(vals([Complex(1,0); Complex(-1,2); fill(Complex(0,0), (1 << n) - 2)])))"))
    push!(s, ("MultivectorBoolScalar", "Multivector{V}($(vals([true; fill(false, (1 << n) - 1)])))"))
    push!(s, ("MultivectorNaN", "Multivector{V}($(vals([1.0; NaN; zeros((1 << n) - 2)])))"))
    push!(s, ("MultivectorNaNScalar", "Multivector{V}($(vals([NaN; zeros((1 << n) - 1)])))"))
    push!(s, ("MultivectorInfScalar", "Multivector{V}($(vals([Inf; zeros((1 << n) - 1)])))"))
    push!(s, ("MultivectorCompact", "Multivector{V}($(vals([-0.617273; 0.70369; fill(0.0, (1 << n) - 3); 1/3])))"))
    push!(s, ("SpinorCompact", "Spinor{V}($(vals([1/3; -2/3; 0.0; -0.0; fill(0.0, max(0, (1 << (n - 1)) - 4))][1:(1 << (n - 1))])))"))
    push!(s, ("SpinorComplex", "Spinor{V}($(vals([Complex(1,1); Complex(0,-2); fill(Complex(0,0), (1 << (n - 1)) - 2)])))"))
    push!(s, ("CoSpinorNegFirst", "CoSpinor{V}($(vals([-1.5; zeros((1 << (n - 1)) - 1)])))"))
    push!(s, ("CoupleThirds", "Couple{V,$(bsrc(n, e1))}(1/3, 2/3)"))
    push!(s, ("CoupleNeg", "Couple{V,$(bsrc(n, e12))}(1.5, -2.5)"))
    push!(s, ("CoupleNegZero", "Couple{V,$(bsrc(n, e12))}(-0.0, -0.0)"))
    push!(s, ("CoupleComplex", "Couple{V,$(bsrc(n, e1))}(Complex(1,2), Complex(3,-4))"))
    push!(s, ("CoupleRational", "Couple{V,$(bsrc(n, e1))}(1//2, -3//4)"))
    push!(s, ("CoupleOne", "Couple{V,One(V)}(1, 0)"))
    push!(s, ("PseudoCoupleOne", "PseudoCouple{V,One(V)}(0, 1)"))
    push!(s, ("PseudoCoupleNeg", "PseudoCouple{V,$(bsrc(n, e1))}(-1.5, -2.5)"))
    push!(s, ("PhasorFloatAngle", "Phasor(2.0, π/3)"))
    push!(s, ("PhasorCouple", "Phasor(2.0, Couple{V,$(bsrc(n, e12))}(0.5, 0.25))"))
    return s
end

function build(sh, defects)
    rng = rng_for("construct", sh)
    top, desc = space_header("construct", sh, sh)
    m = sandbox(sh)
    V = evalsrc(m, "V")
    samples = construct_samples(V, rng, sh)
    cl = CaseLog()
    for (label, src) in samples
        ok, x = attempt(() -> evalsrc(m, src))
        out = ok ? encode(x; vshow = desc["show"], native = true, compact = true, typestr = true) : error_obj(x)
        addcase!(cl, Obj("label" => label, "src" => src, "out" => out))
    end
    top["cases"] = cl.cases
    return retag!(top, defects)
end

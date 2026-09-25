# oracle/common.jl: shared machinery for the element-level Julia oracle.
#
# Included by oracle/run_suite.jl (one suite per process). Provides:
#   * an ordered, deterministic JSON writer (`Obj`, `jwrite`, `write_golden`);
#   * the space registry (`SPACE_REGISTRY`, `space_descriptor`);
#   * element encoders (`encode`, `enc`, `todense`, `kindof`);
#   * deterministic seeded generators of sample elements (`lattice_samples`, ...);
#   * the defect matcher driven by oracle/defects.toml (`DefectTable`, `tag_defects!`).
#
# The JSON schema produced here is specified in docs/port-notes/oracle-schema.md (checked by
# oracle/validate.py); keep them in sync.

using Grassmann, DirectSum, Leibniz, AbstractTensors, StaticVectors
using LinearAlgebra, Random, TOML

const ORACLE_DIR = @__DIR__
const GOLDEN_DIR = joinpath(ORACLE_DIR, "golden")
const SCHEMA_VERSION = 1

# ---------------------------------------------------------------------------------------
# Ordered JSON
# ---------------------------------------------------------------------------------------

"Ordered JSON object (insertion order is preserved, so goldens diff cleanly)."
struct Obj
    kv::Vector{Pair{String,Any}}
end
Obj() = Obj(Pair{String,Any}[])
Obj(ps::Pair...) = Obj(Pair{String,Any}[String(first(p)) => last(p) for p in ps])
function Base.setindex!(o::Obj, v, k::AbstractString)
    i = findfirst(p -> first(p) == k, o.kv)
    i === nothing ? push!(o.kv, String(k) => v) : (o.kv[i] = String(k) => v)
    return o
end
function Base.getindex(o::Obj, k::AbstractString)
    i = findfirst(p -> first(p) == k, o.kv)
    i === nothing && throw(KeyError(k))
    return last(o.kv[i])
end
Base.haskey(o::Obj, k::AbstractString) = any(p -> first(p) == k, o.kv)
Base.get(o::Obj, k::AbstractString, d) = haskey(o, k) ? o[k] : d
Base.delete!(o::Obj, k::AbstractString) = (filter!(p -> first(p) != k, o.kv); o)

"Convert parsed JSON (JSON.jl's insertion-ordered objects) back to `Obj` trees."
toobj(x::AbstractDict) = Obj(Pair{String,Any}[String(k) => toobj(v) for (k, v) in x])
toobj(x::AbstractVector) = Any[toobj(v) for v in x]
toobj(x) = x

function jstr(io::IO, s::AbstractString)
    print(io, '"')
    for c in s
        if c == '"'
            print(io, "\\\"")
        elseif c == '\\'
            print(io, "\\\\")
        elseif c == '\n'
            print(io, "\\n")
        elseif c == '\t'
            print(io, "\\t")
        elseif c == '\r'
            print(io, "\\r")
        elseif c < ' ' || c == '\x7f'
            print(io, "\\u", string(UInt32(c), base = 16, pad = 4))
        else
            print(io, c)
        end
    end
    print(io, '"')
end

jwrite(io::IO, x::Obj) = begin
    print(io, '{')
    for (i, (k, v)) in enumerate(x.kv)
        i > 1 && print(io, ',')
        jstr(io, k)
        print(io, ':')
        jwrite(io, v)
    end
    print(io, '}')
end
jwrite(io::IO, x::AbstractString) = jstr(io, x)
jwrite(io::IO, x::Symbol) = jstr(io, String(x))
jwrite(io::IO, x::Bool) = print(io, x ? "true" : "false")
jwrite(io::IO, x::Integer) = print(io, Int128(x))
jwrite(io::IO, x::AbstractFloat) = isfinite(x) ? print(io, repr(Float64(x))) : error("non-finite float $x cannot be a JSON number")
jwrite(io::IO, ::Nothing) = print(io, "null")
jwrite(io::IO, x::Union{AbstractVector,Tuple}) = begin
    print(io, '[')
    for (i, v) in enumerate(x)
        i > 1 && print(io, ',')
        jwrite(io, v)
    end
    print(io, ']')
end
jwrite(io::IO, x::AbstractDict) = jwrite(io, Obj(Pair{String,Any}[string(k) => v for (k, v) in sort!(collect(x); by = first)]))

"""
    write_golden(path, top)

Write `top` as JSON. Top-level arrays and objects are expanded one entry per line; everything
nested is compact. Deterministic: no timestamps, insertion-ordered keys.
"""
function write_golden(path::AbstractString, top::Obj)
    mkpath(dirname(path))
    open(path, "w") do io
        println(io, "{")
        for (i, (k, v)) in enumerate(top.kv)
            print(io, "  ")
            jstr(io, k)
            print(io, ": ")
            if v isa AbstractVector && !isempty(v)
                println(io, "[")
                for (j, e) in enumerate(v)
                    print(io, "    ")
                    jwrite(io, e)
                    j < length(v) && print(io, ",")
                    println(io)
                end
                print(io, "  ]")
            elseif v isa Obj && !isempty(v.kv)
                println(io, "{")
                for (j, (kk, e)) in enumerate(v.kv)
                    print(io, "    ")
                    jstr(io, kk)
                    print(io, ": ")
                    jwrite(io, e)
                    j < length(v.kv) && print(io, ",")
                    println(io)
                end
                print(io, "  }")
            else
                jwrite(io, v)
            end
            i < length(top.kv) && print(io, ",")
            println(io)
        end
        println(io, "}")
    end
    return path
end

# ---------------------------------------------------------------------------------------
# Environment metadata and seeding
# ---------------------------------------------------------------------------------------

const PKG_NAMES = ("Grassmann", "AbstractTensors", "DirectSum", "Leibniz", "StaticVectors")

function meta_obj(suite::AbstractString, shard::AbstractString; extra...)
    pk = Obj()
    for p in PKG_NAMES
        m = getfield(Main, Symbol(p))
        pk[p] = string(pkgversion(m))
    end
    o = Obj("schema" => SCHEMA_VERSION, "suite" => suite, "shard" => shard,
            "julia" => string(VERSION), "packages" => pk,
            "generator" => "oracle/suites/$suite.jl")
    for (k, v) in extra
        o[string(k)] = v
    end
    return o
end

"64-bit FNV-1a hash (stable across Julia versions, unlike `hash`)."
function fnv1a(s::AbstractString)
    h = 0xcbf29ce484222325
    for b in codeunits(s)
        h = (h ⊻ UInt64(b)) * 0x00000100000001b3
    end
    return h
end

"Deterministic RNG for a suite/shard pair. The seed key and value are recorded in the golden."
seedkey(suite, shard) = "grassmann-oracle/$suite/$shard"
rng_for(suite, shard) = Xoshiro(fnv1a(seedkey(suite, shard)))

# ---------------------------------------------------------------------------------------
# Space registry
# ---------------------------------------------------------------------------------------

"""
Registry of named spaces: `(name, julia_source, description)`. The Julia source is evaluated
in `Main` (Grassmann loaded) to obtain the bundle; elements always live on `Submanifold(bundle)`.
"""
const SPACE_REGISTRY = [
    ("E2",    "S\"++\"",               "Euclidean plane (Signature)"),
    ("E3",    "S\"+++\"",              "Euclidean 3-space (Signature)"),
    ("E4",    "S\"++++\"",             "Euclidean 4-space (Signature)"),
    ("E5",    "S\"+++++\"",            "Euclidean 5-space (Signature)"),
    ("I4",    "4",                     "Int-based Euclidean 4-space (prints ⟨1111⟩)"),
    ("M4",    "S\"-+++\"",             "Minkowski spacetime algebra"),
    ("S4",    "S\"+-+-\"",             "split signature (2,2)"),
    ("D3",    "D\"1,2,-3\"",           "DiagonalForm with non-unit entries"),
    ("PGA2",  "D\"0,1,1\"",            "degenerate DiagonalForm, 2D projective (R*_{2,0,1})"),
    ("PGA3",  "D\"0,1,1,1\"",          "degenerate DiagonalForm, 3D projective (R*_{3,0,1})"),
    ("INF3",  "S\"∞+++\"",             "projective ∞ (Riemann sphere), diagonal, v∞²=+1"),
    ("ORG3",  "S\"∅+++\"",             "projective ∅, diagonal, v∅²=-1"),
    ("CGA2",  "S\"∞∅++\"",             "conformal 2D (null basis ∞,∅)"),
    ("CGA3",  "S\"∞∅+++\"",            "conformal 3D (null basis ∞,∅)"),
    ("DUAL3", "(S\"+++\")'",           "dual (covector) space of E3; labels w¹…"),
    ("DYAD2", "S\"++\"⊕(S\"++\")'",    "mixed (dyadic) space V⊕V'"),
    ("TAN2",  "tangent(S\"++\")",      "tangent bundle, 1 derivation variable (∂₁)"),
    ("TAN22", "tangent(S\"++\",2,2)",  "tangent bundle, 2 variables, order 2"),
]

const SPACE_SRC = Dict(n => s for (n, s, _) in SPACE_REGISTRY)
const SPACE_DESC = Dict(n => d for (n, _, d) in SPACE_REGISTRY)

"The Julia bundle (Signature/DiagonalForm/Int) of a registered space."
bundle(name::AbstractString) = Core.eval(Main, Meta.parse(SPACE_SRC[name]))
"The element space `Submanifold(bundle)` of a registered space."
space(name::AbstractString) = Submanifold(bundle(name))

function metric_obj(S)
    if S isa Integer
        return Obj("kind" => "euclidean")
    elseif S isa DiagonalForm
        return Obj("kind" => "diagonal", "diag" => Any[enc(c) for c in collect(Submanifold(S)[:])])
    else
        return Obj("kind" => "signature", "neg" => Int(DirectSum.metric(S)))
    end
end

"Self-contained descriptor of a registered space (the Lean loader never needs Julia)."
function space_descriptor(name::AbstractString)
    S = bundle(name)
    V = Submanifold(S)
    n = mdims(V)
    b = n <= 8 ? collect(Λ(V).b) : Any[]
    opts = S isa Integer ? 0 : Int(DirectSum.options(S))
    # scalar part of I⟑I for the top blade (sign decides Julia's scalar trig behavior, AT B2)
    isq = nothing
    if !isempty(b)
        ok, sq = attempt(() -> b[end] * b[end])
        if ok
            d = todense(sq)
            isq = d === nothing ? nothing : enc(d[1])
        end
    end
    return Obj(
        "julia" => SPACE_SRC[name],
        "description" => SPACE_DESC[name],
        "show" => string(V),
        "show_bundle" => sprint(show, S),
        "n" => n,
        "grade" => grade(V),
        "metric" => metric_obj(S),
        "options" => opts,
        "hasinf" => hasinf(V),
        "hasorigin" => hasorigin(V),
        "conformal" => Leibniz.hasconformal(V),
        "isdiag" => isdiag(V),
        "dyadmode" => Int(dyadmode(V)),
        "isdual" => DirectSum.isdual(V),
        "diffvars" => Int(diffvars(V)),
        "diffmode" => Int(diffmode(V)),
        "Isq" => isq,
        "basis" => Any[Int(UInt(x)) for x in b],
        "names" => Any[string(x) for x in b],
    )
end

# ---------------------------------------------------------------------------------------
# Scalars and elements
# ---------------------------------------------------------------------------------------

"Coefficient encoding: exact ints/rationals as strings, floats as `repr`, complex as `[re, im]`."
enc(c::Bool) = c ? "true" : "false"
enc(c::Integer) = string(c)
enc(c::Rational) = string(numerator(c)) * "//" * string(denominator(c))
enc(c::Float64) = repr(c)
enc(c::AbstractFloat) = repr(Float64(c))
enc(c::Complex) = Any[enc(real(c)), enc(imag(c))]
enc(c) = string(c)

"Normalized Julia type name of a coefficient type (`ComplexF64` is spelled `Complex{Float64}`)."
tname(::Type{Complex{T}}) where {T} = "Complex{" * tname(T) * "}"
tname(::Type{Rational{T}}) where {T} = "Rational{" * tname(T) * "}"
tname(T::Type) = string(T)
tname(x) = string(x)

"The oracle kind tag of a value (docs/port-notes/oracle-schema.md §7)."
function kindof(x)
    x isa Zero && return "Zero"
    x isa DirectSum.Infinity && return "Infinity"
    if x isa Submanifold
        DirectSum.isbasis(x) || return "Space"
        return UInt(x) == 0 ? "One" : "Submanifold"
    end
    x isa Single && return "Single"
    x isa Chain && return "Chain"
    x isa Multivector && return "Multivector"
    x isa Spinor && return "Spinor"
    x isa CoSpinor && return "CoSpinor"
    x isa Couple && return "Couple"
    x isa PseudoCouple && return "PseudoCouple"
    x isa Phasor && return "Phasor"
    x isa TensorAlgebra && return "Other"
    x isa Bool && return "Bool"
    x isa Number && return "Number"
    return "Other"
end

const GRADED_KINDS = ("Zero", "One", "Infinity", "Submanifold", "Single", "Chain")
const BITS_KINDS = ("One", "Submanifold", "Single", "Couple", "PseudoCouple")
const ELEMENT_KINDS = ("Zero", "One", "Infinity", "Submanifold", "Single", "Chain", "Multivector",
                       "Spinor", "CoSpinor", "Couple", "PseudoCouple", "Phasor")

blade_bits(x::Submanifold) = UInt(x)
blade_bits(x) = UInt(basis(x))

"""
Storage grade: the type parameter `G` of `Chain`/`Single`/`Submanifold` (= popcount of the
blade bits), 0 for `Zero`/`Infinity`. Differs from Leibniz `grade(x)` in tangent spaces, where
`grade` does not count derivation indices.
"""
sgrade(x::Union{Chain,Single,Submanifold}) = Int(typeof(x).parameters[2])
sgrade(x) = 0

"Largest dimension for which elements carry a `dense` vector (larger ones carry `terms`)."
const MAX_DENSE_N = 10

"""
    toterms(x)

Sparse form `[[bits, coef], ...]` (nonzero-or-stored terms, ascending Multivector order) for
elements of spaces too large for `dense`; `nothing` when not cheaply available.
"""
function toterms(x)
    k = kindof(x)
    n = mdims(Manifold(x))
    if k == "Zero"
        return Any[]
    elseif k == "One" || k == "Submanifold"
        return Any[Any[Int(UInt(x)), "1"]]
    elseif k == "Single"
        return Any[Any[Int(blade_bits(x)), enc(value(x))]]
    elseif k == "Couple"
        return Any[Any[0, enc(realvalue(x))], Any[Int(blade_bits(x)), enc(imagvalue(x))]]
    elseif k == "PseudoCouple"
        return Any[Any[Int(blade_bits(x)), enc(realvalue(x))], Any[Int((UInt(1) << n) - 1), enc(imagvalue(x))]]
    elseif k == "Chain" && binomial(n, sgrade(x)) <= 4096
        ib = Leibniz.indexbasis(n, sgrade(x))
        v = value(x)
        return Any[Any[Int(ib[i]), enc(v[i])] for i in eachindex(ib) if !iszero(v[i])]
    end
    return nothing
end

"""
    todense(x)

Full `2^n` coefficient vector of `x` in Julia `Multivector` order (grade-major, lexicographic
within a grade), computed directly from the storage layout (so it also works where Julia's own
`Multivector(x)` is broken, e.g. `Zero`). Returns `nothing` for `Infinity`/`Phasor`/non-elements.
"""
function todense(x)
    k = kindof(x)
    k in ("Infinity", "Phasor", "Space", "Other", "Number", "Bool") && return nothing
    V = Manifold(x)
    n = mdims(V)
    n > MAX_DENSE_N && return nothing
    T = valuetype(x)
    z = T <: Number ? zero(T) : 0
    d = Any[z for _ in 1:(1 << n)]
    if k == "Zero"
    elseif k == "One" || k == "Submanifold"
        d[Leibniz.basisindex(n, UInt(x))] = one(z)
    elseif k == "Single"
        d[Leibniz.basisindex(n, blade_bits(x))] = value(x)
    elseif k == "Chain"
        G = sgrade(x)
        ib = Leibniz.indexbasis(n, G)
        v = value(x)
        for i in eachindex(ib)
            d[Leibniz.basisindex(n, ib[i])] = v[i]
        end
    elseif k == "Multivector"
        v = value(x)
        for i in 1:(1 << n)
            d[i] = v[i]
        end
    elseif k == "Spinor" || k == "CoSpinor"
        v = value(x)
        idx = k == "Spinor" ? Leibniz.spinindex : Leibniz.antiindex
        for g in (k == "Spinor" ? (0:2:n) : (1:2:n))
            for B in Leibniz.indexbasis(n, g)
                d[Leibniz.basisindex(n, B)] = v[idx(n, B)]
            end
        end
    elseif k == "Couple" || k == "PseudoCouple"
        # assign (not `+=`) so a stored -0.0 keeps its sign; only a degenerate B (B = 1 for a
        # Couple, B = I for a PseudoCouple) puts both parts on one blade, which then holds the sum
        iB = Leibniz.basisindex(n, blade_bits(x))
        i1, i2 = k == "Couple" ? (1, iB) : (iB, 1 << n)
        d[i1] = realvalue(x)
        d[i2] = i1 == i2 ? d[i1] + imagvalue(x) : imagvalue(x)
    end
    return d
end

function msgline(e)
    s = try
        sprint(showerror, e)
    catch
        string(typeof(e))
    end
    line = first(split(s, '\n'))
    return length(line) > 200 ? first(line, 200) : String(line)
end

error_obj(e) = Obj("kind" => "Error", "error" => string(nameof(typeof(e))), "msg" => msgline(e))

function safe_show(x; compact::Bool = false)
    try
        return compact ? sprint(show, x; context = :compact => true) : sprint(show, x)
    catch e
        return nothing
    end
end

"""
    encode(x; vshow, compact=false, native=false, typestr=false)

Encode a Julia value as an oracle element object (docs/port-notes/oracle-schema.md §7).
`vshow` is the `show` string of the shard's space; `"V"` is emitted only when the element's
space differs from it.
"""
function encode(x; vshow::Union{Nothing,AbstractString} = nothing, compact::Bool = false,
                native::Bool = false, typestr::Bool = false)
    k = kindof(x)
    o = Obj("kind" => k)
    if k == "Number" || k == "Bool"
        o["T"] = tname(typeof(x))
        o["value"] = enc(x)
        o["str"] = safe_show(x)
        compact && (o["compact_str"] = safe_show(x; compact = true))
        return o
    elseif k == "Other" || k == "Space"
        o["type"] = string(typeof(x))
        o["str"] = safe_show(x)
        compact && (o["compact_str"] = safe_show(x; compact = true))
        return o
    end
    V = Manifold(x)
    o["T"] = tname(valuetype(x))
    vs = string(V)
    (vshow === nothing || vs != vshow) && (o["V"] = vs)
    k in GRADED_KINDS && (o["grade"] = sgrade(x))
    k in BITS_KINDS && (o["bits"] = Int(blade_bits(x)))
    if k == "Phasor"
        o["amp"] = encode(amplitude(x); vshow = vs)
        o["angle"] = encode(angle(x); vshow = vs)
    elseif k != "Infinity"
        if mdims(V) <= MAX_DENSE_N
            o["dense"] = Any[enc(c) for c in todense(x)]
        else
            t = toterms(x)
            t === nothing || (o["terms"] = t)
        end
    end
    if native && k in ("Single", "Chain", "Multivector", "Spinor", "CoSpinor", "Couple", "PseudoCouple")
        o["native"] = k == "Single" ? Any[enc(value(x))] : Any[enc(c) for c in collect(value(x))]
    end
    s = safe_show(x)
    s === nothing ? (o["str_error"] = true) : (o["str"] = s)
    compact && (o["compact_str"] = safe_show(x; compact = true))
    typestr && (o["type"] = string(typeof(x)))
    return o
end

# ---------------------------------------------------------------------------------------
# Evaluating Julia source in a sandbox with `V` bound
# ---------------------------------------------------------------------------------------

"A fresh module with Grassmann loaded and `V` bound to the space of `spacename`."
function sandbox(spacename::AbstractString)
    m = Module(Symbol("Oracle_", replace(spacename, r"[^A-Za-z0-9]" => "_")))
    Core.eval(m, :(using Grassmann, DirectSum, Leibniz, AbstractTensors, StaticVectors, LinearAlgebra))
    Core.eval(m, :(import Grassmann: Λ))
    Core.eval(m, Meta.parse("const V = Submanifold(" * SPACE_SRC[spacename] * ")"))
    return m
end

evalsrc(m::Module, src::AbstractString) = Core.eval(m, Meta.parse(src))

"Run `f()`; return `(true, value)` or `(false, exception)`."
function attempt(f)
    try
        return (true, f())
    catch e
        e isa InterruptException && rethrow()
        return (false, e)
    end
end

# ---------------------------------------------------------------------------------------
# Julia literals for generated sources
# ---------------------------------------------------------------------------------------

lit(c::Bool) = string(c)
lit(c::Integer) = c == typemin(Int64) ? "typemin(Int)" : string(c)
lit(c::Rational) = string(numerator(c)) * "//" * string(denominator(c))
function lit(c::Float64)
    isnan(c) && return "NaN"
    isinf(c) && return c > 0 ? "Inf" : "-Inf"
    return repr(c)
end
lit(c::Complex) = "Complex(" * lit(real(c)) * ", " * lit(imag(c)) * ")"
vals(cs) = "Values(" * join((lit(c) for c in cs), ", ") * ")"

# ---------------------------------------------------------------------------------------
# Deterministic sample generators
# ---------------------------------------------------------------------------------------

"Nonzero small integer in ±{1,2,3}."
ci(rng) = rand(rng, (-3, -2, -1, 1, 2, 3))
"Small integer with ~30% zeros (exercises zero-skipping in display)."
cz(rng) = rand(rng) < 0.3 ? 0 : ci(rng)
"Dyadic float k/4, k ∈ -12:12 (exact in binary, so products stay exact)."
cd(rng) = rand(rng, -12:12) / 4
"Nonzero dyadic float."
cdn(rng) = (x = cd(rng); x == 0 ? 0.75 : x)

"A coefficient vector of length `m` drawn with `gen`, resampled until it has a nonzero entry."
function coeffs(rng, gen, m::Integer)
    while true
        cs = [gen(rng) for _ in 1:m]
        any(!iszero, cs) && return cs
    end
end

"Bits of the `i`-th blade of grade `g` in lexicographic order (1-based)."
blade(n, g, i) = Leibniz.indexbasis(n, g)[i]
"1-based `Λ(V).b` index of a blade."
bidx(n, B) = Leibniz.basisindex(n, UInt(B))
bsrc(n, B) = "Λ(V).b[$(bidx(n, B))]"

"""
    lattice_samples(V, rng; infinity=true, zero_single=false, floats=true)

The per-space kind sample used by the `arith`, `products` and `unary` suites: every element kind,
Singles/Submanifolds of every grade (two different blades for grades 1 and 2), Chains of every
grade, Couples/PseudoCouples on vector, bivector and pseudoscalar blades, Spinor, CoSpinor,
Multivector (all Int), plus Float Chain{1} and Multivector. Returns `[(label, src)]`.
"""
function lattice_samples(V, rng; infinity::Bool = true, zero_single::Bool = false, floats::Bool = true)
    n = mdims(V)
    I = (UInt(1) << n) - 1
    s = Tuple{String,String}[]
    push!(s, ("Zero", "Zero(V)"), ("One", "One(V)"))
    infinity && push!(s, ("Infinity", "Infinity(V)"))
    push!(s, ("Single0", "Single{V}($(ci(rng)))"))
    push!(s, ("Sub1", bsrc(n, blade(n, 1, 1))))
    n >= 2 && push!(s, ("SubI", bsrc(n, I)))
    for g in 1:n
        push!(s, ("Single$g", "$(ci(rng))*" * bsrc(n, blade(n, g, 1))))
        if g <= 2 && binomial(n, g) >= 2
            push!(s, ("Single$(g)b", "$(ci(rng))*" * bsrc(n, blade(n, g, 2))))
        end
    end
    zero_single && push!(s, ("Single1z", "0*" * bsrc(n, blade(n, 1, 1))))
    for g in 0:n
        push!(s, ("Chain$g", "Chain{V,$g}($(vals(coeffs(rng, cz, binomial(n, g)))))"))
    end
    cblades = UInt[blade(n, 1, 1)]
    n >= 3 && push!(cblades, blade(n, 2, 1))
    n >= 2 && push!(cblades, I)
    for B in cblades
        push!(s, ("Couple:$(string(Λ(V).b[bidx(n, B)]))", "Couple{V,$(bsrc(n, B))}($(ci(rng)), $(ci(rng)))"))
    end
    for B in (n >= 3 ? UInt[blade(n, 1, 1), blade(n, 2, 1)] : UInt[blade(n, 1, 1)])
        push!(s, ("PseudoCouple:$(string(Λ(V).b[bidx(n, B)]))", "PseudoCouple{V,$(bsrc(n, B))}($(ci(rng)), $(ci(rng)))"))
    end
    if n >= 2
        h = 1 << (n - 1)
        push!(s, ("Spinor", "Spinor{V}($(vals(coeffs(rng, cz, h))))"))
        push!(s, ("CoSpinor", "CoSpinor{V}($(vals(coeffs(rng, cz, h))))"))
    end
    push!(s, ("Multivector", "Multivector{V}($(vals(coeffs(rng, cz, 1 << n))))"))
    if floats
        push!(s, ("Chain1F", "Chain{V,1}($(vals(coeffs(rng, cd, n))))"))
        push!(s, ("MultivectorF", "Multivector{V}($(vals(coeffs(rng, cd, 1 << n))))"))
    end
    return s
end

"""
    build_inputs(m, samples; vshow, native=false, compact=false)

Evaluate sample sources in sandbox `m`. Returns `(values, objs)` where `objs[i]` is the encoded
input (with `label` and `src`). Sources that fail to evaluate are dropped (and reported).
"""
function build_inputs(m::Module, samples; vshow, native::Bool = false, compact::Bool = false)
    xs = Any[]
    objs = Obj[]
    for (label, src) in samples
        ok, x = attempt(() -> evalsrc(m, src))
        if !ok
            @warn "sample failed to construct" label src msg = msgline(x)
            continue
        end
        o = Obj("label" => label, "src" => src)
        for (k, v) in encode(x; vshow = vshow, native = native, compact = compact).kv
            o[k] = v
        end
        push!(xs, x)
        push!(objs, o)
    end
    return xs, objs
end

# ---------------------------------------------------------------------------------------
# Dense comparisons (used for the automatic consistency flags)
# ---------------------------------------------------------------------------------------

isexact(c) = c isa Integer || c isa Rational || (c isa Complex && isexact(real(c)))

function coef_equal(a, b)
    if isexact(a) && isexact(b)
        return a == b
    end
    (a isa Number && b isa Number) || return string(a) == string(b)
    fa, fb = complex(float(a)), complex(float(b))
    for (x, y) in ((real(fa), real(fb)), (imag(fa), imag(fb)))
        (isnan(x) && isnan(y)) && continue
        x == y && continue
        isapprox(x, y; rtol = 1e-12, atol = 1e-12) || return false
    end
    return true
end

dense_equal(a, b) = a !== nothing && b !== nothing && length(a) == length(b) && all(coef_equal(x, y) for (x, y) in zip(a, b))

"A Multivector with the given dense coefficients (promoted element type)."
function mv_of(V, d)
    T = mapreduce(typeof, promote_type, d)
    return Multivector{V}(Values{length(d),T}(Tuple(convert.(T, d))))
end

# ---------------------------------------------------------------------------------------
# Defects (oracle/defects.toml)
# ---------------------------------------------------------------------------------------

struct DefectMatch
    fields::Dict{String,Any}
end
struct Defect
    id::String
    policy::String
    matches::Vector{DefectMatch}
end

function load_defects(path = joinpath(ORACLE_DIR, "defects.toml"))
    isfile(path) || return Defect[]
    t = TOML.parsefile(path)
    out = Defect[]
    for d in get(t, "defect", Any[])
        ms = DefectMatch[DefectMatch(Dict{String,Any}(m)) for m in get(d, "match", Any[])]
        push!(out, Defect(d["id"], get(d, "policy", "skip"), ms))
    end
    return out
end

"Glob with `|` alternatives and `*` wildcards."
function globmatch(pat::AbstractString, s::AbstractString)
    for alt in split(pat, '|')
        rx = Regex("^" * join((replace(p, r"([.+?^$(){}\[\]\\])" => s"\\\1") for p in split(alt, '*')), ".*") * "\$")
        occursin(rx, s) && return true
    end
    return false
end

"Does kind pattern `pat` (e.g. `Chain`, `Chain:0`, `Single|Submanifold:n`, `*`) match an input object?"
function kindmatch(pat::AbstractString, a, topgrade::Int)
    pat == "*" && return true
    k = get(a, "kind", "")
    g = get(a, "grade", nothing)
    for alt in split(pat, '|')
        parts = split(alt, ':')
        parts[1] == k || continue
        length(parts) == 1 && return true
        want = parts[2] == "n" ? topgrade : parse(Int, parts[2])
        g == want && return true
    end
    return false
end

"Named predicates usable in `when = ...` (docs/port-notes/oracle-schema.md §10)."
function whenmatch(name::AbstractString, args, sp)
    n = sp === nothing ? 0 : sp["n"]
    bitsof(a) = get(a, "bits", nothing)
    if name == "same_bits"
        return length(args) == 2 && bitsof(args[1]) !== nothing && bitsof(args[1]) == bitsof(args[2])
    elseif name == "diff_bits"
        return length(args) == 2 && bitsof(args[1]) !== nothing && bitsof(args[2]) !== nothing && bitsof(args[1]) != bitsof(args[2])
    elseif name == "couple_rev_plus"
        # a Couple argument whose blade B has reverse sign +1 (grade ≡ 0,1 mod 4), i.e. B² = +|B|²
        for a in args
            if get(a, "kind", "") == "Couple"
                g = count_ones(UInt(a["bits"]))
                g % 4 in (0, 1) && return true
            end
        end
        return false
    elseif name == "null_blade"
        # a term argument whose blade contains exactly one of the null vectors ∞ (bit 0), ∅ (bit 1)
        (sp === nothing || !(sp["conformal"])) && return false
        for a in args
            b = bitsof(a)
            b === nothing && continue
            b = UInt(b)
            xor((b & 1) != 0, (b & 2) != 0) && return true
        end
        return false
    elseif name == "mixed_parity_first"
        # the first operand is a Couple with odd B, or a PseudoCouple whose B parity differs from
        # n's: not parity-homogeneous, so Julia's sandwich falls back to multispin
        isempty(args) && return false
        a = args[1]
        k = get(a, "kind", "")
        k in ("Couple", "PseudoCouple") || return false
        odd = isodd(count_ones(UInt(a["bits"])))
        return k == "Couple" ? odd : odd != isodd(n)
    elseif name == "Isq_plus"
        # the pseudoscalar squares to a positive scalar (AT's scalar trig functions become hyperbolic)
        isq = sp === nothing ? nothing : get(sp, "Isq", nothing)
        return isq isa AbstractString && something(tryparse(Float64, isq), 0.0) > 0
    end
    error("unknown defect predicate `$name`")
end

"""
    defect_ids(defects, suite, spacename, sp, op, args; extra)

IDs of all defects whose `match` tables match this case. `args` are the encoded input objects,
`sp` the space descriptor (or `nothing`), `extra` a Dict of additional string fields
(`block`, `input`, ...).
"""
function defect_ids(defects, suite, spacename, sp, op, args; extra = Dict{String,String}())
    ids = String[]
    topgrade = sp === nothing ? 0 : sp["grade"]
    for d in defects
        for m in d.matches
            f = m.fields
            haskey(f, "suite") && !globmatch(f["suite"], suite) && continue
            haskey(f, "space") && !globmatch(f["space"], spacename) && continue
            haskey(f, "op") && !globmatch(f["op"], op) && continue
            if haskey(f, "kinds")
                ks = f["kinds"]
                (length(ks) == length(args) && all(kindmatch(ks[i], args[i], topgrade) for i in eachindex(ks))) || continue
            end
            haskey(f, "when") && !whenmatch(f["when"], args, sp) && continue
            ok = true
            for key in ("out", "msg", "block", "input", "file")
                if haskey(f, key)
                    ok &= haskey(extra, key) && globmatch(f[key], extra[key])
                end
            end
            ok || continue
            push!(ids, d.id)
            break
        end
    end
    return ids
end

# ---------------------------------------------------------------------------------------
# Operation tables (op key => Julia expression template over `a`, `b`)
# ---------------------------------------------------------------------------------------

# The templates are written as a user sees them after `using Grassmann`; the closures use
# module-qualified names because this file also loads DirectSum/Leibniz/AbstractTensors/
# LinearAlgebra, whose exports would otherwise make `metric`, `norm`, ... ambiguous.
const G = Grassmann
const BINARY_OPS = [
    ("add",          "a + b",             (a, b) -> a + b),
    ("sub",          "a - b",             (a, b) -> a - b),
    ("mul",          "a * b",             (a, b) -> a * b),
    ("div",          "a / b",             (a, b) -> a / b),
    ("rdiv",         "a // b",            (a, b) -> a // b),
    ("wedge",        "a ∧ b",             (a, b) -> G.:∧(a, b)),
    ("vee",          "a ∨ b",             (a, b) -> G.:∨(a, b)),
    ("contraction",  "contraction(a, b)", (a, b) -> G.contraction(a, b)),
    ("lcontraction", "a ⨼ b",             (a, b) -> G.:⨼(a, b)),
    ("lshift",       "a << b",            (a, b) -> a << b),
    ("rshift",       "a >> b",            (a, b) -> a >> b),
    ("revmul",       "a ∗ b",             (a, b) -> G.:∗(a, b)),
    ("scalarprod",   "a ⊛ b",             (a, b) -> G.:⊛(a, b)),
    ("cross",        "a × b",             (a, b) -> G.:×(a, b)),
    ("sandwich",     "a ⊘ b",             (a, b) -> G.:⊘(a, b)),
    ("tsandwich",    "a >>> b",           (a, b) -> a >>> b),
    ("veedot",       "veedot(a, b)",      (a, b) -> G.veedot(a, b)),
    ("antidot",      "antidot(a, b)",     (a, b) -> G.antidot(a, b)),
]
const BINARY = Dict(k => (e, f) for (k, e, f) in BINARY_OPS)

const UNARY_OPS = [
    ("neg",                 "-a",                     a -> -a),
    ("reverse",             "reverse(a)",             a -> Base.reverse(a)),
    ("involute",            "involute(a)",            a -> G.involute(a)),
    ("clifford",            "clifford(a)",            a -> G.clifford(a)),
    ("antireverse",         "antireverse(a)",         a -> G.antireverse(a)),
    ("complementright",     "complementright(a)",     a -> G.complementright(a)),
    ("complementleft",      "complementleft(a)",      a -> G.complementleft(a)),
    ("hodge",               "hodge(a)",               a -> G.hodge(a)),
    ("complementlefthodge", "complementlefthodge(a)", a -> G.complementlefthodge(a)),
    ("metric",              "metric(a)",              a -> G.metric(a)),
    ("antimetric",          "antimetric(a)",          a -> G.antimetric(a)),
    ("even",                "even(a)",                a -> G.even(a)),
    ("odd",                 "odd(a)",                 a -> G.odd(a)),
    ("real",                "real(a)",                a -> Base.real(a)),
    ("imag",                "imag(a)",                a -> Base.imag(a)),
    ("scalar",              "scalar(a)",              a -> G.scalar(a)),
    ("vector",              "vector(a)",              a -> G.vector(a)),
    ("bivector",            "bivector(a)",            a -> G.bivector(a)),
    ("trivector",           "trivector(a)",           a -> G.trivector(a)),
    ("volume",              "AbstractTensors.volume(a)", a -> AbstractTensors.volume(a)),
    ("abs2",                "abs2(a)",                a -> Base.abs2(a)),
    ("norm",                "norm(a)",                a -> G.norm(a)),
    ("adjoint",             "a'",                     a -> a'),
    ("Multivector",         "Multivector(a)",         a -> G.Multivector(a)),
]
const UNARY = Dict(k => (e, f) for (k, e, f) in UNARY_OPS)
"Unary ops that are linear maps of the dense vector (checked against the Multivector path)."
const LINEAR_UNARY = Set(["neg", "reverse", "involute", "clifford", "antireverse", "complementright",
    "complementleft", "hodge", "complementlefthodge", "metric", "antimetric", "even", "odd", "real",
    "imag", "scalar", "vector", "bivector", "trivector", "volume"])

ops_table(keys, table) = Obj((k => table[k][1] for k in keys)...)

# ---------------------------------------------------------------------------------------
# Case construction and bookkeeping
# ---------------------------------------------------------------------------------------

"Accumulates the cases of one shard."
struct CaseLog
    cases::Vector{Obj}
end
CaseLog() = CaseLog(Obj[])
addcase!(log::CaseLog, case::Obj) = (push!(log.cases, case); case)

"""
    retag!(top, defects)

Recompute every case's `defects` tags from defects.toml and the shard's `stats`
(`cases`, `errors`, `ref_mismatch`, `unexplained`, per-defect counts). `unexplained` counts
Julia errors and ref mismatches not covered by any defect; the goal is 0 (every anomaly
documented). Run after building a shard and again by `generate_all.jl --retag`.
"""
function retag!(top::Obj, defects)
    meta = top["meta"]
    suite = meta["suite"]
    desc = get(top, "space", nothing)
    spname = desc === nothing ? "" : desc["name"]
    inputs = get(top, "inputs", Any[])
    file = replace(basename(string(get(meta, "source", ""))), ".txt" => "")
    nerr = nmis = nunex = 0
    dcount = Dict{String,Int}()
    for c in top["cases"]
        haskey(c, "defects") && delete!(c, "defects")
        suite == "floats" && continue
        out = get(c, "out", nothing)
        okind = out === nothing ? "Nothing" : out["kind"]
        extra = Dict{String,String}("out" => okind)
        okind == "Error" && (extra["msg"] = out["msg"])
        if suite == "construct"
            extra["block"] = c["label"]
            extra["input"] = c["src"]
        elseif suite == "docs"
            extra["block"] = c["block"]
            extra["input"] = c["input"]
            extra["file"] = file
        end
        args = Any[inputs[c[k]+1] for k in ("a", "b") if haskey(c, k)]
        ids = defect_ids(defects, suite, spname, desc, string(get(c, "op", suite)), args; extra = extra)
        isempty(ids) || (c["defects"] = Any[ids...])
        iserr = okind == "Error"
        ismis = "ref_mismatch" in get(c, "flags", Any[])
        nerr += iserr
        nmis += ismis
        (iserr || ismis) && isempty(ids) && (nunex += 1)
        for d in ids
            dcount[d] = get(dcount, d, 0) + 1
        end
    end
    top["stats"] = Obj("cases" => length(top["cases"]), "errors" => nerr, "ref_mismatch" => nmis,
        "unexplained" => nunex, "defects" => Obj((k => dcount[k] for k in sort!(collect(keys(dcount))))...))
    return top
end

"Header shared by the per-space suites."
function space_header(suite, shard, spacename; extra...)
    desc = space_descriptor(spacename)
    o = Obj("meta" => meta_obj(suite, shard; seed_key = seedkey(suite, shard),
                               seed = string(fnv1a(seedkey(suite, shard))), extra...),
            "space" => Obj("name" => spacename, desc.kv...))
    return o, o["space"]
end

"""
    make_case(log, desc, op, args, f; ref, extra)

Evaluate `f()` (the Julia operation), encode the result (or error) and attach `ref` (dense)
with flag `ref_mismatch` when the reference computation `ref()` differs from the result's dense
vector, or when Julia errored but the reference is computable. `args` are 0-based indices into
the shard's `inputs`. Defect tags are added afterwards by `retag!`.
"""
function make_case(log::CaseLog, desc, op, args::Vector{Int}, f;
                   ref = nothing, extra = Pair{String,Any}[], vshow = desc === nothing ? nothing : desc["show"])
    ok, r = attempt(f)
    out = ok ? encode(r; vshow = vshow) : error_obj(r)
    c = Obj("op" => op)
    names = ("a", "b", "c")
    for (i, ai) in enumerate(args)
        c[names[i]] = ai
    end
    for (k, v) in extra
        c[k] = v
    end
    c["out"] = out
    if ref !== nothing
        rok, rd = attempt(ref)
        if rok && rd !== nothing
            od = ok ? todense(r) : nothing
            if !ok || (od !== nothing && !dense_equal(od, rd))
                c["flags"] = Any["ref_mismatch"]
                c["ref"] = Any[enc(x) for x in rd]
            end
        end
    end
    return addcase!(log, c)
end

"Dense vector of an input for reference computations (numbers act as multiples of `One`)."
function dense_in(x, n::Int)
    if kindof(x) in ("Number", "Bool")
        d = Any[zero(x) for _ in 1:(1 << n)]
        d[1] = x
        return d
    end
    return todense(x)
end

"Keep only the grade-`G` part of a dense vector (Multivector order)."
function project_grade(d, n::Int, G::Int)
    out = Any[zero(c) for c in d]
    for B in Leibniz.indexbasis(n, G)
        i = Leibniz.basisindex(n, B)
        out[i] = d[i]
    end
    return out
end

# Oracle generator for the JuliaBase test suites.
#
#   julia --startup-file=no --project=oracle Tests/JuliaBase/gen_golden.jl golden Tests/JuliaBase
#       writes the committed goldens (float_show.json, num.json, range.json, show.json, math.json,
#       trig.json)
#   julia --startup-file=no --project=oracle Tests/JuliaBase/gen_golden.jl math Tests/JuliaBase
#       rewrites only math.json (it has its own seed)
#   julia --startup-file=no --project=oracle Tests/JuliaBase/gen_golden.jl trig Tests/JuliaBase
#       rewrites only trig.json (Julia's own trigonometric, hyperbolic and ComplexF64 functions)
#   julia --startup-file=no --project=oracle Tests/JuliaBase/gen_golden.jl fuzz PREFIX N SEED
#       writes large TSV fuzz files PREFIX_{f64,f32,opts,num,range,math,trig}.tsv (not committed); run
#       them with Tests.JuliaBase.fuzzAll (see Tests/JuliaBase.lean)
#   julia --startup-file=no --project=oracle Tests/JuliaBase/gen_golden.jl fuzzmath PREFIX N SEED
#       writes only PREFIX_math.tsv
#   julia --startup-file=no --project=oracle Tests/JuliaBase/gen_golden.jl fuzztrig PREFIX N SEED
#       writes only PREFIX_trig.tsv
#
# Floats are exchanged as the hex of their bit pattern so they round-trip exactly.

using Random
import JSON

hex(x::Float64) = string(reinterpret(UInt64, x), base = 16)
hex(x::Float32) = string(reinterpret(UInt32, x), base = 16)
cshow(x) = sprint(show, x; context = :compact => true)

nudge(x, s) = (for _ in 1:abs(s); x = s > 0 ? nextfloat(x) : prevfloat(x); end; x)

# ---------------------------------------------------------------- float samples

function sample64(rng)
    k = rand(rng, 1:10)
    if k <= 3
        return reinterpret(Float64, rand(rng, UInt64))
    elseif k == 4   # short decimals
        nd = rand(rng, 1:17)
        d = rand(rng, 1:9) * 10^(nd-1) + (nd > 1 ? rand(rng, 0:10^(nd-1)-1) : 0)
        x = something(tryparse(Float64, string(d) * "e" * string(rand(rng, -340:310))), 1.0)
        return rand(rng, Bool) ? -x : x
    elseif k == 5   # near the layout thresholds
        base = rand(rng, (1e-4, 1e-5, 1e6, 999999.0, 999999.5, 999999.4, 99999.95, 1e5, 1e-3,
                          1.0, 10.0, 1e16, 1e15, 9.999995e5, 9.9999949e5, 123456.789, 0.1, 0.3))
        x = nudge(base, rand(rng, -5:5))
        return rand(rng, Bool) ? -x : x
    elseif k == 6   # integers
        x = Float64(rand(rng, 0:2^rand(rng, 1:60)))
        return rand(rng, Bool) ? -x : x
    elseif k == 7   # subnormals
        return reinterpret(Float64, rand(rng, UInt64(1):UInt64(2)^rand(rng, 1:52)))
    elseif k == 8   # moderate values with a few decimals (compact-sensitive)
        x = round(rand(rng) * 10.0^rand(rng, -5:8), digits = rand(rng, 1:9))
        return rand(rng, Bool) ? -x : x
    elseif k == 9   # powers of 10 and 2, nudged
        x = rand(rng, Bool) ? 10.0^rand(rng, -320:308) : 2.0^rand(rng, -1074:1023)
        return nudge(x, rand(rng, -2:2))
    else            # log-uniform
        return exp(rand(rng) * 1400 - 700) * (rand(rng, Bool) ? -1 : 1)
    end
end

function sample32(rng)
    k = rand(rng, 1:6)
    if k <= 2
        return reinterpret(Float32, rand(rng, UInt32))
    elseif k == 3
        return Float32(sample64(rng))
    elseif k == 4
        nd = rand(rng, 1:9)
        d = rand(rng, 1:9) * 10^(nd-1) + (nd > 1 ? rand(rng, 0:10^(nd-1)-1) : 0)
        return something(tryparse(Float32, string(d) * "e" * string(rand(rng, -48:38))), 1f0)
    elseif k == 5
        return reinterpret(Float32, rand(rng, UInt32(1):UInt32(2)^rand(rng, 1:23)))
    else
        return Float32(round(rand(rng) * 10.0^rand(rng, -5:8), digits = rand(rng, 1:7)))
    end
end

# "ordinary" operands for arithmetic: mostly moderate magnitudes, sometimes extreme/special
function operand(rng)
    k = rand(rng, 1:12)
    k <= 5 && return (rand(rng) - 0.5) * 10.0^rand(rng, -3:3)
    k <= 7 && return sample64(rng)
    k == 8 && return Float64(rand(rng, -20:20))
    k == 9 && return rand(rng, (0.0, -0.0, Inf, -Inf, NaN, floatmax(), -floatmax(), floatmin(), 5e-324, -5e-324))
    k == 10 && return (rand(rng) - 0.5) * 10.0^rand(rng, -310:308)
    k == 11 && return rand(rng, -10:10) + rand(rng, (0.5, -0.5, 0.25, 0.0))
    return (rand(rng) - 0.5) * 2.0^rand(rng, -1074:1023)
end

const fixed64 = Float64[0.0, -0.0, NaN, -NaN, Inf, -Inf, 1/3, 1e-4, 1e-5, 999999.0, 1e6, 1234567.0,
    123456.789, 0.1+0.2, floatmax(), -floatmax(), floatmin(), nextfloat(0.0), prevfloat(floatmin()),
    100.0, 1.0, 2.0^53, 2.0^53+2, 2.0^63, 1e23, 5e-324, 9.999995e5, 999999.5, 0.30000000000000004,
    1e15, 1e16, 1e17, 12345.6, 123456.0, 999999.9, -2.5, 0.5, 1e-300, 7.0e-10]
const fixed32 = Float32[0, -0f0, NaN32, Inf32, -Inf32, 1.5f0, 1f-5, 1/3, floatmax(Float32),
    floatmin(Float32), nextfloat(0f0), 1f10, 16777216f0, 1f6, 999999f0, 123456.79f0]

f64rows(xs) = [[hex(x), repr(x), cshow(x)] for x in xs]
f32rows(xs) = [[hex(x), repr(x), cshow(x), string(x)] for x in xs]

# Ryu.writeshortest with random keyword options (plus, space, hash, precision, expchar, padexp,
# decchar, typed, compact): row = [hex(x), flags..., result]
function opts_case(rng)
    x = rand(rng) < 0.8 ? sample64(rng) : Float64(sample32(rng))
    f32 = rand(rng) < 0.3
    plus, space, hash, padexp, typed, compact = rand(rng, Bool, 6)
    prec = rand(rng) < 0.5 ? -1 : rand(rng, 0:22)
    expchar = rand(rng, (UInt8('e'), UInt8('E'), UInt8('f')))
    decchar = rand(rng, (UInt8('.'), UInt8(',')))
    y = f32 ? Float32(x) : x
    s = Base.Ryu.writeshortest(y, plus, space, hash, prec, expchar, padexp, decchar, typed, compact)
    [f32 ? "f32" : "f64", hex(y), string(plus), string(space), string(hash), string(prec), string(Char(expchar)),
     string(padexp), string(Char(decchar)), string(typed), string(compact), s]
end

# ---------------------------------------------------------------- numeric ops

const BINOPS = Dict("hypot" => hypot, "rem" => rem, "mod" => mod, "fld" => fld, "cld" => cld,
                    "div" => div, "max" => max, "min" => min)
const UNOPS = Dict("cbrt" => cbrt, "round" => round, "sign" => sign, "trunc" => trunc,
                   "nextfloat" => nextfloat, "prevfloat" => prevfloat)

function binop_case(rng, name)
    x, y = operand(rng), operand(rng)
    if name == "hypot" && rand(rng, Bool)
        y = x * (rand(rng) + 0.5) * 10.0^rand(rng, -3:3)   # comparable magnitudes
    elseif name in ("rem", "mod", "fld", "cld", "div") && rand(rng, Bool)
        y = (rand(rng) + 0.1) * 10.0^rand(rng, -2:2) * rand(rng, (1, -1))
    end
    r = try BINOPS[name](x, y) catch; nothing end
    r === nothing && return nothing
    [name, hex(x), hex(y), hex(r)]
end

function unop_case(rng, name)
    x = operand(rng)
    name == "round" && rand(rng, Bool) && (x = rand(rng, -1000:1000) / 2)
    [name, hex(x), hex(UNOPS[name](x))]
end

function approx_case(rng)
    x = operand(rng)
    δ = rand(rng, (0.0, 1e-16, 1e-12, 1e-9, 1.4e-8, 1.5e-8, 1e-7, 1e-3)) * (rand(rng) + 0.5)
    y = rand(rng) < 0.1 ? operand(rng) : x * (1 + δ * rand(rng, (1, -1)))
    kind = rand(rng, 1:4)
    if kind == 1
        return ["default", hex(x), hex(y), "", "", string(isapprox(x, y))]
    elseif kind == 2
        a = rand(rng, (1e-12, 1e-8, 1e-3, 1.0))
        return ["atol", hex(x), hex(y), hex(a), "", string(isapprox(x, y; atol = a))]
    elseif kind == 3
        t = rand(rng, (1e-12, 1e-9, 1e-6, 1e-3))
        return ["rtol", hex(x), hex(y), "", hex(t), string(isapprox(x, y; rtol = t))]
    else
        return ["nans", hex(x), hex(y), "", "", string(isapprox(x, y; nans = true))]
    end
end

function complex_case(rng)
    a, b, c, d = operand(rng), operand(rng), operand(rng), operand(rng)
    if rand(rng, Bool)
        a, b, c, d = (rand(rng, 4) .- 0.5) .* 10.0 .^ rand(rng, -3:3, 4)
    end
    k = rand(rng, 1:4)
    z, w = complex(a, b), complex(c, d)
    r = k == 1 ? z / w : k == 2 ? inv(z) : k == 3 ? z * w : complex(abs(z), abs2(z))
    [("div", "inv", "mul", "abs")[k], hex(a), hex(b), hex(c), hex(d), hex(real(r)), hex(imag(r))]
end

# ---------------------------------------------------------------- ranges

function endpoint(rng)
    k = rand(rng, 1:8)
    k == 1 && return Float64(rand(rng, -10:10))
    k == 2 && return rand(rng, -20:20) / rand(rng, (2, 3, 4, 5, 7, 10, 100, 1000))
    k == 3 && return rand(rng, -4:4) * π / rand(rng, 1:4)
    k == 4 && return (rand(rng) - 0.5) * 10.0^rand(rng, -3:3)
    k == 5 && return round((rand(rng) - 0.5) * 100, digits = rand(rng, 1:3))
    k == 6 && return 0.0
    k == 7 && return rand(rng, (0.1, 0.2, 0.3, 1/3, 2/3, 0.7, 1.1, 2π, π/2, -π/2, ℯ))
    return (rand(rng) - 0.5) * 10.0^rand(rng, -300:300)
end

rangehex(r) = join((hex(Float64(x)) for x in r), ",")

function range_case(rng, maxn = 500)
    try
        return range_case_(rng, maxn)
    catch
        return nothing
    end
end

function range_case_(rng, maxn)
    k = rand(rng, 1:12)
    n = rand(rng) < 0.9 ? rand(rng, 0:40) : rand(rng, 41:maxn)
    a, b = endpoint(rng), endpoint(rng)
    (rand(rng) < 0.05 || n == 1) && (b = a)
    if k <= 3
        return ["range", hex(a), hex(b), string(n), rangehex(range(a, b, length = n))]
    elseif k == 4
        return ["linrange", hex(a), hex(b), string(n), rangehex(LinRange(a, b, n))]
    elseif k == 5
        ia, ib = rand(rng, -50:50), rand(rng, -50:50)
        n == 1 && (ib = ia)
        return ["rangeint", string(ia), string(ib), string(n), rangehex(range(ia, ib, length = n))]
    elseif k <= 7
        st = rand(rng) < 0.7 ? rand(rng, (0.1, 0.2, 0.25, 0.5, 1/3, 0.05, 1.0, -0.1, -0.5, π/8)) : endpoint(rng)
        (st == 0 || !isfinite(st)) && (st = 0.1)
        b = a + st * rand(rng, 0:60) * (rand(rng) < 0.8 ? 1 : 0.97)
        r = a:st:b
        length(r) > 2000 && return nothing
        return ["colon", hex(a), hex(st), hex(b), rangehex(r)]
    elseif k == 8
        st = rand(rng, (0.1, 0.2, 0.25, 1/3, -0.1, π/4))
        return ["rangestep", hex(a), hex(st), string(n), rangehex(range(a; step = st, length = n))]
    elseif k == 9
        n < 2 && (n = 2)
        r = range(a, b, length = n)
        x = rand(rng, (2.0, 0.5, 3.0, π, -1.5, 0.1))
        op = rand(rng, ("mul", "bmul", "bdiv", "badd", "div"))
        rr = op == "mul" ? x * r : op == "bmul" ? x .* r : op == "bdiv" ? r ./ x : op == "badd" ? r .+ x : r / x
        return [op, hex(a), hex(b), string(n), hex(x), rangehex(rr)]
    elseif k == 10
        a32, b32 = Float32(a), Float32(b)
        rand(rng, Bool) && (b32 = nextfloat(b32))   # contourf: range(Float32(lo), nextfloat(Float32(hi)), n)
        n == 1 && (b32 = a32)
        return ["range32", hex(a32), hex(b32), string(n), join((hex(x) for x in range(a32, b32, length = n)), ",")]
    else
        a32, b32 = Float32(a), Float32(b)
        n == 1 && (b32 = a32)
        return ["linrange32", hex(a32), hex(b32), string(n), join((hex(x) for x in LinRange(a32, b32, n)), ",")]
    end
end

# ---------------------------------------------------------------- show of other types

# (id, value) pairs; Tests/JuliaBase/Show.lean builds the same values from the ids
const SHOW_VALUES = Any[
    ("int_0", 0), ("int_1", 1), ("int_m3", -3), ("int_max", typemax(Int)), ("int_min", typemin(Int)),
    ("bool_t", true), ("bool_f", false),
    ("rat_1_3", 1//3), ("rat_m1_3", -1//3), ("rat_0", 0//1), ("rat_2", 2//1),
    ("ci_1_2", 1 + 2im), ("ci_1_m2", 1 - 2im), ("ci_0_0", 0 + 0im), ("ci_m1_m2", -1 - 2im),
    ("cf_1_2", 1.0 + 2.0im), ("cf_15_m25", 1.5 - 2.5im), ("cf_1_m0", complex(1.0, -0.0)),
    ("cf_m0_0", complex(-0.0, 0.0)), ("cf_1_nan", complex(1.0, NaN)), ("cf_1_minf", complex(1.0, -Inf)),
    ("cf_inf_inf", complex(Inf, Inf)), ("cf_third", complex(1/3, 2/3)), ("cf32_15_2", complex(1.5f0, 2f0)),
    ("cr_half_third", complex(1//2, 1//3)),
    ("u8_3", 0x03), ("u16_3", 0x0003), ("u32_3", 0x00000003), ("u64_42", UInt64(42)),
    ("cb_im", im), ("cb_tt", complex(true, true)),
    ("f32_15", 1.5f0), ("f32_nan", NaN32), ("f32_minf", -Inf32)]

function show_cases()
    [Dict("id" => id, "show" => repr(v), "compact" => cshow(v), "print" => string(v),
          "pcompact" => sprint(print, v; context = :compact => true)) for (id, v) in SHOW_VALUES]
end

# ---------------------------------------------------------------- Julia's own math (math.json)
#
# Julia's pure-Julia kernels (base/special/{exp,log,pow}.jl, intfuncs.jl, reduce.jl, parse,
# floatfuncs.jl rounding) and the exact IEEE toolkit. Rows are tagged by the first field:
#   u64/u32   name x r        exp exp2 exp10 log log2 log10 log1p expm1 (Float64 / Float32)
#   powf64/powf32  x y r      x^y, same float type
#   powi64/powi32  x n r      x^n, n::Int
#   lit64/lit32    x k r      Base.literal_pow(^, x, Val(k))
#   pbs64          x p r      Base.power_by_squaring(x, p)
#   sum            n xs... r  sum(::Vector{Float64}) of explicit values
#   sumgen         n seed r   sum of the Wilkinson generator vector (see sumvec)
#   parse          s r|ERR    tryparse(Float64, s)
#   rdig/rsig      x d r      round(x, digits = d) / round(x, sigdigits = d)
#   hidigit        x h        Base.hidigit(x, 10)
#   eps64/eps32    x r        eps(x)
#   exponent64/32  x e        exponent(x)
#   rat64/rat32    p q r      p/q correctly rounded (Float64(BigFloat(p)/BigFloat(q)) at 4096 bits)
#   colon32        a st b xs  collect(a:st:b) for Float32
#   f16            p q bits str   Float16(p//q) correctly rounded, and string(Float16) of it

hex16(x::Float16) = string(reinterpret(UInt16, x), base = 16)

const EXPLIM = Dict("exp" => (709.7827128933841, -745.1332191019412, 708.3964185322641),
                    "exp2" => (1024.0, -1075.0, 1022.0),
                    "exp10" => (308.25471555991675, -323.60724533877976, 307.6526555685887),
                    "expm1" => (709.7827128933845, -37.42994775023705, 0.22314355131420976))
const EXPLIM32 = Dict("exp" => (88.72284f0, -103.97208f0, 87.33655f0),
                      "exp2" => (128f0, -150f0, 126.00001f0),
                      "exp10" => (38.53184f0, -45.1545f0, 37.92978f0),
                      "expm1" => (88.72284f0, -17.32868f0, 0.22314355f0))
const UNARY = Dict("exp" => exp, "exp2" => exp2, "exp10" => exp10, "log" => log, "log2" => log2,
                   "log10" => log10, "log1p" => log1p, "expm1" => expm1)
const UNAMES = sort(collect(keys(UNARY)))

function exp_arg(rng, name)
    mx, mn, sub = EXPLIM[name]
    k = rand(rng, 1:9)
    k == 1 && return (2rand(rng) - 1) * 1.05 * max(-mn, mx)
    k == 2 && return (2rand(rng) - 1) * 50.0
    k == 3 && return (2rand(rng) - 1)
    k == 4 && return nudge(rand(rng, (mx, mn, sub, -sub, -0.2876820724517809)), rand(rng, -40:40))
    k == 5 && return (2rand(rng) - 1) * 10.0^rand(rng, -20:0)
    k == 6 && return rand(rng, (0.0, -0.0, Inf, -Inf, NaN, 1.0, -1.0, 0.5, 2.0, 10.0, 1e-300, 5e-324))
    k == 7 && return Float64(rand(rng, -1100:1100)) / rand(rng, (1, 2, 4, 256, 512))
    k == 8 && return (2rand(rng) - 1) * 0.3
    return operand(rng)
end

function log_arg(rng, name)
    if name == "log1p"
        k = rand(rng, 1:7)
        k == 1 && return (2rand(rng) - 1) * 10.0^rand(rng, -20:-1)
        k == 2 && return nudge(rand(rng, (1.1102230246251565e-16, -1.1102230246251565e-16, -0.06058693718652422,
                                         0.06449445891785943, -1.0, 0.0)), rand(rng, -5:5))
        k == 3 && return rand(rng) * 2 - 1
        k == 4 && return exp(rand(rng) * 1400 - 700)
        k == 5 && return rand(rng, (0.0, -0.0, Inf, NaN, 1.0, -0.5, 1e-310, -1.0))
        k == 6 && return -rand(rng)
        return abs(operand(rng))
    end
    k = rand(rng, 1:8)
    k <= 2 && return reinterpret(Float64, rand(rng, UInt64) >> 1)
    k == 3 && return 1 + (2rand(rng) - 1) * 0.1
    k == 4 && return nudge(rand(rng, (0.9394130628134757, 1.0644944589178595, 1.0, floatmin(), 5e-324, floatmax())),
                           rand(rng, -5:5))
    k == 5 && return exp(rand(rng) * 1400 - 700)
    k == 6 && return rand(rng, (0.0, -0.0, Inf, NaN, 1.0, 2.0, 10.0, 0.5, 1e-310))
    k == 7 && return Float64(rand(rng, 1:10^6)) / rand(rng, (1, 10, 1000))
    return abs(operand(rng))
end

unary_arg(rng, name) = name in ("exp", "exp2", "exp10", "expm1") ? exp_arg(rng, name) : log_arg(rng, name)

function unary32_arg(rng, name)
    if name in ("exp", "exp2", "exp10", "expm1")
        mx, mn, sub = EXPLIM32[name]
        k = rand(rng, 1:5)
        k == 1 && return Float32((2rand(rng) - 1) * 1.05 * max(-mn, mx))
        k == 2 && return nudge(rand(rng, (mx, mn, sub, -sub, -0.2876821f0)), rand(rng, -40:40))
        k == 3 && return Float32((2rand(rng) - 1) * 10.0^rand(rng, -10:0))
        k == 4 && return rand(rng, (0f0, -0f0, Inf32, -Inf32, NaN32, 1f0, -1f0))
        return sample32(rng)
    end
    x = Float32(log_arg(rng, name))
    rand(rng) < 0.2 && (x = abs(sample32(rng)))
    rand(rng) < 0.1 && (x = nudge(rand(rng, (0.939413f0, 1.0644945f0, 1f0, -0.06058694f0, 0.06449446f0,
                                            5.9604645f-8, floatmin(Float32))), rand(rng, -3:3)))
    return x
end

function pow_base(rng)
    k = rand(rng, 1:9)
    k <= 2 && return exp(rand(rng) * 60 - 30)
    k == 3 && return Float64(rand(rng, 2:43)) * rand(rng, (1, -1))
    k == 4 && return 1 + (2rand(rng) - 1) * 10.0^rand(rng, -16:-1)
    k == 5 && return rand(rng, (0.0, -0.0, Inf, -Inf, NaN, 1.0, -1.0, 5e-324, 1e-310, floatmax()))
    k == 6 && return -exp(rand(rng) * 20 - 10)
    k == 7 && return exp(rand(rng) * 1400 - 700)
    return operand(rng)
end

function pow_exp(rng)
    k = rand(rng, 1:9)
    k <= 2 && return rand(rng, (0.5, -0.5, 1.5, -1.5, 2.5, 1/3, -1/3, 0.25, 3.5, -2.5, 0.1, 0.9))
    k == 3 && return Float64(rand(rng, -40:40))
    k == 4 && return (2rand(rng) - 1) * 10
    k == 5 && return Float64(rand(rng, (-1, 1)) * rand(rng, 24577:10^7))
    k == 6 && return rand(rng, (0.0, -0.0, Inf, -Inf, NaN, 1e20, -1e20, 7e18, 1e300))
    k == 7 && return (2rand(rng) - 1) * 10.0^rand(rng, 2:6)
    k == 8 && return Float64(rand(rng, -5000:30000)) + rand(rng, (0.0, 0.5))
    return operand(rng)
end

function pow_int(rng)
    k = rand(rng, 1:6)
    k <= 3 && return rand(rng, -40:40)
    k == 4 && return rand(rng, -5000:30000)
    k == 5 && return rand(rng, (-1, 1)) * rand(rng, 24577:10^9)
    return rand(rng, (-1, 1)) * rand(rng, 2^52:2^62)
end

# the Wilkinson sum vector: integers scaled by powers of two (Lean rebuilds it exactly)
sumvec(n, s) = [Float64(Int64((UInt64(i) * 0x9E3779B1 + UInt64(s)) % UInt64(2)^32) - 2^31) *
                2.0^(Int((UInt64(i) * UInt64(s) + 7) % 61) - 91) for i in 1:n]

function parse_str(rng)
    k = rand(rng, 1:6)
    if k <= 3
        d = join(rand(rng, '0':'9', rand(rng, 1:25)))
        return string(rand(rng) < 0.3 ? "-" : "", d[1:min(end, rand(rng, 1:length(d)))], ".", d, "e",
                      rand(rng, -340:320))
    elseif k == 4
        return repr(sample64(rng))
    elseif k == 5
        return string(rand(rng, 0:10^rand(rng, 1:18)))
    else
        return rand(rng, ("0", "-0", "1", "+1.5", ".5", "5.", "-.5e-3", "1E+2", "inf", "-Inf", "NaN", "Infinity",
                          "-infinity", "nan", "1e", ".", "e5", "", "1.5.2", "--1", "1e-400", "1e400", "2e-324",
                          "2.4703282292062328e-324", "2.4703282292062327e-324", "  3.25  ", "4.9e-324",
                          "1.7976931348623158e308", "1.7976931348623159e308", "0.1", "0.30000000000000004"))
    end
end

rat_part(rng) = rand(rng) < 0.5 ? BigInt(rand(rng, 1:10^6)) : rand(rng, BigInt(1):BigInt(2)^rand(rng, 1:1100))
exactquot(::Type{T}, p, q) where {T} = setprecision(BigFloat, 4096) do
    T(BigFloat(p) / BigFloat(q))
end

function colon32_case(rng)
    a = Float32(rand(rng, (0, 0.1, 0.5, 1, -3, 100, 1e-3, -1.5, 0.2, 2, 5)) + rand(rng, (0, 0, 0.25, -0.7, 1/3)))
    st = Float32(rand(rng, (0.1, 0.2, 0.25, 0.5, 1/3, 1, 7.5, 1e-3, -0.1, -0.5, 0.7, 0.3)))
    b = a + st * Float32(rand(rng, 0:60)) * (rand(rng) < 0.8 ? 1f0 : 0.97f0)
    r = try a:st:b catch; return nothing end
    ["colon32", hex(a), hex(st), hex(b), join((hex(x) for x in r), ",")]
end

function math_case(rng)
    k = rand(rng, 1:20)
    if k <= 5
        name = rand(rng, UNAMES)
        x = unary_arg(rng, name)
        r = try UNARY[name](x) catch; return nothing end
        return ["u64", name, hex(x), hex(r)]
    elseif k <= 7
        name = rand(rng, UNAMES)
        x = unary32_arg(rng, name)
        r = try UNARY[name](x) catch; return nothing end
        return ["u32", name, hex(x), hex(r)]
    elseif k <= 9
        x, y = pow_base(rng), pow_exp(rng)
        r = try x^y catch; return nothing end
        return ["powf64", hex(x), hex(y), hex(r)]
    elseif k == 10
        x, n = pow_base(rng), pow_int(rng)
        r = try x^n catch; return nothing end
        return ["powi64", hex(x), string(n), hex(r)]
    elseif k == 11
        x, y = Float32(pow_base(rng)), Float32(pow_exp(rng))
        r = try x^y catch; return nothing end
        return ["powf32", hex(x), hex(y), hex(r)]
    elseif k == 12
        x, n = Float32(pow_base(rng)), pow_int(rng)
        r = try x^n catch; return nothing end
        return ["powi32", hex(x), string(n), hex(r)]
    elseif k == 13
        f32 = rand(rng, Bool)
        x = f32 ? Float32(pow_base(rng)) : pow_base(rng)
        p = rand(rng, -4:12)
        r = Base.literal_pow(^, x, Val(p))
        return [f32 ? "lit32" : "lit64", hex(x), string(p), hex(r)]
    elseif k == 14
        x, p = pow_base(rng), rand(rng) < 0.8 ? rand(rng, 0:70) : rand(rng, 71:5000)
        return ["pbs64", hex(x), string(p), hex(Base.power_by_squaring(x, p))]
    elseif k == 15
        if rand(rng, Bool)
            n = rand(rng) < 0.7 ? rand(rng, 0:70) : rand(rng, 71:300)
            v = Float64[rand(rng) < 0.9 ? (2rand(rng) - 1) * 2.0^rand(rng, -40:40) : operand(rng) for _ in 1:n]
            return vcat(["sum", string(n)], hex.(v), [hex(sum(v))])
        else
            n, s = rand(rng, 1:5000), rand(rng, UInt32)
            return ["sumgen", string(n), string(Int(s)), hex(sum(sumvec(n, s)))]
        end
    elseif k == 16
        s = parse_str(rng)
        r = tryparse(Float64, s)
        return ["parse", s, r === nothing ? "ERR" : hex(r)]
    elseif k == 17
        x = rand(rng) < 0.8 ? exp10(rand(rng) * 40 - 20) * rand(rng, (1, -1)) : operand(rng)
        if rand(rng, Bool)
            d = rand(rng) < 0.9 ? rand(rng, -10:20) : rand(rng, (-320, -309, -308, 300, 308, 309, 320, 400))
            return ["rdig", hex(x), string(d), hex(round(x, digits = d))]
        elseif rand(rng, Bool)
            n = rand(rng, 1:17)
            return ["rsig", hex(x), string(n), hex(round(x, sigdigits = n))]
        else
            isfinite(x) || (x = 1.0)
            return ["hidigit", hex(x), string(Base.hidigit(x, 10))]
        end
    elseif k == 18
        j = rand(rng, 1:5)
        if j == 1
            x = rand(rng) < 0.3 ? sample64(rng) : operand(rng)
            return ["eps64", hex(x), hex(eps(x))]
        elseif j == 2
            x = sample32(rng)
            return ["eps32", hex(x), hex(eps(x))]
        elseif j == 3
            x = rand(rng, Bool) ? sample64(rng) : Float64(sample32(rng))
            (isfinite(x) && x != 0) || (x = 1.0)
            return rand(rng, Bool) ? ["exponent64", hex(x), string(exponent(x))] :
                   (y = Float32(x); (isfinite(y) && y != 0) || (y = 1f0); ["exponent32", hex(y), string(exponent(y))])
        else
            p, q = rat_part(rng) * rand(rng, (1, -1)), rat_part(rng)
            rand(rng) < 0.05 && (p = big(0))
            f32 = j == 5
            r = f32 ? exactquot(Float32, p, q) : exactquot(Float64, p, q)
            return [f32 ? "rat32" : "rat64", string(p), string(q), hex(r)]
        end
    elseif k == 19
        return colon32_case(rng)
    else
        p, q = rand(rng) < 0.5 ? (rand(rng, 0:10^5), rand(rng, 1:10^5)) : (100 * rand(rng, 0:40), 2^rand(rng, 1:45) - 1)
        x = exactquot(Float16, p, q)
        return ["f16", string(p), string(q), hex16(x), string(x)]
    end
end

math_rows(rng, n) = (rows = Any[]; while length(rows) < n; c = math_case(rng); c === nothing || push!(rows, c); end; rows)

# `string(x)` of every nonnegative finite Float16, in bit order (x = reinterpret(Float16, i - 1)):
# Float16 printing is checked exhaustively
f16all() = [string(reinterpret(Float16, u)) for u in UInt16(0):UInt16(0x7bff)]

# ---------------------------------------------------------------- trigonometry (trig.json)

const TRIG = Dict("sin" => sin, "cos" => cos, "tan" => tan, "asin" => asin, "acos" => acos,
                  "atan" => atan, "sinh" => sinh, "cosh" => cosh, "tanh" => tanh, "asinh" => asinh,
                  "acosh" => acosh, "atanh" => atanh, "sinpi" => sinpi, "cospi" => cospi)
const TNAMES = sort(collect(keys(TRIG)))

# arguments that reach every branch: reduction boundaries (multiples of π/2, Payne–Hanek up to
# floatmax), the kernels' thresholds, domain edges and special values
function trig_arg(rng, name)
    k = rand(rng, 1:10)
    sg = rand(rng, Bool) ? -1.0 : 1.0
    special = (0.0, -0.0, Inf, -Inf, NaN, floatmax(), -floatmax(), 5e-324, -5e-324, 1e-300, 1.0, -1.0)
    if name in ("sin", "cos", "tan")
        k <= 3 && return (2rand(rng) - 1) * 10
        k == 4 && return sg * exp(rand(rng) * 60 - 30)
        k == 5 && return sg * exp(rand(rng) * 709)
        k == 6 && return nudge(sg * rand(rng, 1:2^rand(rng, 1:30)) * (pi / 2), rand(rng, -3:3))
        k == 7 && return nudge(sg * rand(rng, (pi/4, 3pi/4, 5pi/4, 7pi/4, 9pi/4, 2.0^20 * pi/2,
                                                 sqrt(eps()), sqrt(eps() / 2), sqrt(eps()) / 2)), rand(rng, -3:3))
        k == 8 && return rand(rng, special)
        k == 9 && return sg * reinterpret(Float64, rand(rng, UInt64) >> 1)
        return operand(rng)
    elseif name in ("asin", "acos", "atanh")
        k <= 4 && return 2rand(rng) - 1
        k == 5 && return nudge(sg, rand(rng, -60:0))
        k == 6 && return nudge(sg * rand(rng, (0.5, 0.975, 2.0^-26, 2.0^-57, sqrt(eps()))), rand(rng, -3:3))
        k == 7 && return sg * exp(-rand(rng) * 90)
        k == 8 && return rand(rng, (0.0, -0.0, NaN, 1.0, -1.0, 0.5, -0.5, 5e-324))
        return (2rand(rng) - 1) * 10.0^rand(rng, -20:0)
    elseif name == "atan"
        k <= 3 && return sg * exp(rand(rng) * 80 - 40)
        k == 4 && return (2rand(rng) - 1) * 3
        k == 5 && return nudge(sg * rand(rng, (7/16, 11/16, 19/16, 39/16, 2.0^66, 2.0^-27)), rand(rng, -3:3))
        k == 6 && return rand(rng, special)
        return operand(rng)
    elseif name in ("sinh", "cosh", "tanh")
        k <= 3 && return (2rand(rng) - 1) * 25
        k == 4 && return sg * exp(-rand(rng) * 40)
        k == 5 && return nudge(sg * rand(rng, (2.1, 1.0, 0.5, 22.0, 709.7822265633563, 3.0, 9.0, 88.72283, 18.0 / 2,
                                                 1.3862944 / 2)), rand(rng, -3:3))
        k == 6 && return sg * (700 + rand(rng) * 20)
        k == 7 && return rand(rng, special)
        return operand(rng)
    elseif name == "asinh"
        k <= 4 && return sg * exp(rand(rng) * 100 - 50)
        k == 5 && return nudge(sg * rand(rng, (2.0, 2.0^28, 2.0^-28)), rand(rng, -3:3))
        k == 6 && return rand(rng, special)
        return operand(rng)
    elseif name == "acosh"
        k <= 3 && return 1 + exp(rand(rng) * 40 - 38)
        k <= 5 && return 1 + 2rand(rng)
        k == 6 && return exp(rand(rng) * 700)
        k == 7 && return nudge(rand(rng, (1.0, 2.0, 2.0^28)), rand(rng, 0:3))
        k == 8 && return rand(rng, (1.0, Inf, NaN, floatmax()))
        return abs(operand(rng)) + 1
    else  # sinpi, cospi
        k <= 3 && return (2rand(rng) - 1) * 10
        k == 4 && return nudge(sg * rand(rng, 0:40) / rand(rng, (2, 4)), rand(rng, -3:3))
        k == 5 && return sg * exp(rand(rng) * 40)
        k == 6 && return nudge(sg * rand(rng, (2.0^52, 2.0^53, 2.0^60)), rand(rng, -3:3))
        k == 7 && return rand(rng, special)
        return operand(rng)
    end
end

function trig_arg32(rng, name)
    r = rand(rng)
    r < 0.15 && return sample32(rng)
    if r < 0.25 && name in ("sin", "cos", "tan")
        return nudge(Float32(rand(rng, (pi/4, 2.0^28 * pi/2, sqrt(eps(Float32)), 2.0^-12))) *
                     (rand(rng, Bool) ? -1f0 : 1f0), rand(rng, -3:3))
    end
    return Float32(trig_arg(rng, name))
end

# a complex operand: moderate, tiny, huge or special parts, often on an axis
function carg(rng)
    part() = (k = rand(rng, 1:10);
              k <= 5 ? (rand(rng) - 0.5) * 10.0^rand(rng, -3:3) :
              k == 6 ? Float64(rand(rng, -3:3)) :
              k == 7 ? rand(rng, (0.0, -0.0, Inf, -Inf, NaN, 1.0, -1.0)) :
              k == 8 ? (rand(rng) - 0.5) * 10.0^rand(rng, 100:308) :
              k == 9 ? (rand(rng) - 0.5) * 10.0^rand(rng, -320:-100) : operand(rng))
    a, b = part(), part()
    k = rand(rng, 1:8)
    k == 1 && (b = rand(rng, (0.0, -0.0)))
    k == 2 && (a = rand(rng, (0.0, -0.0)))
    return complex(a, b)
end

const CUNARY = Dict("exp" => exp, "expm1" => expm1, "log" => log, "log1p" => log1p, "sqrt" => sqrt,
                    "sin" => sin, "cos" => cos, "tan" => tan, "sinh" => sinh, "cosh" => cosh,
                    "tanh" => tanh, "asin" => asin, "acos" => acos, "atan" => atan, "asinh" => asinh,
                    "acosh" => acosh, "atanh" => atanh)
const CNAMES = sort(collect(keys(CUNARY)))

function trig_case(rng)
    k = rand(rng, 1:20)
    if k <= 7
        name = rand(rng, TNAMES)
        x = trig_arg(rng, name)
        r = try TRIG[name](x) catch; return nothing end
        return ["t64", name, hex(x), hex(r)]
    elseif k <= 9
        name = rand(rng, TNAMES)
        x = trig_arg32(rng, name)
        r = try TRIG[name](x) catch; return nothing end
        return ["t32", name, hex(x), hex(r)]
    elseif k == 10
        f32 = rand(rng) < 0.3
        x = f32 ? trig_arg32(rng, "sin") : trig_arg(rng, "sin")
        s, c = try sincos(x) catch; return nothing end
        return [f32 ? "sincos32" : "sincos64", hex(x), hex(s), hex(c)]
    elseif k == 11
        x = trig_arg(rng, "sinpi")
        s, c = try sincospi(x) catch; return nothing end
        return ["sincospi64", hex(x), hex(s), hex(c)]
    elseif k <= 13
        f32 = rand(rng) < 0.3
        y, x = operand(rng), operand(rng)
        j = rand(rng, 1:5)
        j == 1 && (y = x * 10.0^rand(rng, (-25, -20, -18, -17, 17, 18, 20, 25)) * (rand(rng, Bool) ? 1 : -1))
        j == 2 && (x = rand(rng, (0.0, -0.0, Inf, -Inf, 1.0, NaN)))
        j == 3 && (y = rand(rng, (0.0, -0.0, Inf, -Inf, NaN)))
        if f32
            y32, x32 = Float32(y), Float32(x)
            j == 1 && rand(rng, Bool) && (y32 = x32 * 1f8)
            return ["atan2_32", hex(y32), hex(x32), hex(atan(y32, x32))]
        end
        return ["atan2_64", hex(y), hex(x), hex(atan(y, x))]
    elseif k <= 18
        name = rand(rng, CNAMES)
        z = carg(rng)
        r = try CUNARY[name](z) catch; return nothing end
        return ["c64", name, hex(real(z)), hex(imag(z)), hex(real(r)), hex(imag(r))]
    elseif k == 19
        θ = trig_arg(rng, "sin")
        r = try cis(θ) catch; return nothing end
        return ["cis", hex(θ), hex(real(r)), hex(imag(r))]
    else
        z = carg(rng)
        j = rand(rng, 1:4)
        p = j == 1 ? complex(rand(rng, (0.5, -0.5, 1/3, 2.5, -1.5, 0.1, 3.0, -2.0)), rand(rng, (0.0, -0.0))) :
            j == 2 ? complex(Float64(rand(rng, -6:6)), 0.0) :
            j == 3 ? complex((rand(rng) - 0.5) * 8, 0.0) : carg(rng)
        j == 3 && (z = complex(-abs(real(z)), rand(rng, (0.0, -0.0))))  # negative real base, real power
        r = try z^p catch; return nothing end
        return ["cpow", hex(real(z)), hex(imag(z)), hex(real(p)), hex(imag(p)), hex(real(r)), hex(imag(r))]
    end
end

trig_rows(rng, n) = (rows = Any[]; while length(rows) < n; c = trig_case(rng); c === nothing || push!(rows, c); end; rows)

function trig_golden(dir)
    rng = Random.Xoshiro(20260927)
    open(joinpath(dir, "trig.json"), "w") do io
        JSON.print(io, Dict("meta" => Dict("julia" => string(VERSION), "seed" => 20260927),
            "cases" => trig_rows(rng, 9000)))
    end
end

function trig_fuzz(prefix, n, seed)
    rng = Random.Xoshiro(seed + 2)
    open(prefix * "_trig.tsv", "w") do io
        for row in trig_rows(rng, n)
            println(io, join(row, '\t'))
        end
    end
end

# ---------------------------------------------------------------- drivers

function golden(dir)
    rng = Random.Xoshiro(20260924)
    f64 = vcat(fixed64, [sample64(rng) for _ in 1:1600])
    f32 = vcat(fixed32, [sample32(rng) for _ in 1:400])
    open(joinpath(dir, "float_show.json"), "w") do io
        JSON.print(io, Dict("meta" => Dict("julia" => string(VERSION), "seed" => 20260924),
            "f64" => f64rows(f64), "f32" => f32rows(f32), "opts" => [opts_case(rng) for _ in 1:400]))
    end
    binops = Any[]
    for name in sort(collect(keys(BINOPS))), _ in 1:120
        c = binop_case(rng, name); c === nothing || push!(binops, c)
    end
    unops = Any[unop_case(rng, name) for name in sort(collect(keys(UNOPS))) for _ in 1:80]
    approx = Any[approx_case(rng) for _ in 1:300]
    cplx = Any[complex_case(rng) for _ in 1:300]
    ints = Any[]
    for _ in 1:200
        x, y = rand(rng, -100:100), rand(rng, [-13:-1; 1:13])
        push!(ints, [x, y, div(x, y), rem(x, y), fld(x, y), mod(x, y), cld(x, y)])
    end
    open(joinpath(dir, "num.json"), "w") do io
        JSON.print(io, Dict("meta" => Dict("julia" => string(VERSION)), "binop" => binops,
            "unop" => unops, "isapprox" => approx, "complex" => cplx, "int" => ints))
    end
    ranges = Any[]
    while length(ranges) < 400
        c = range_case(rng, 80); c === nothing || push!(ranges, c)
    end
    open(joinpath(dir, "range.json"), "w") do io
        JSON.print(io, Dict("meta" => Dict("julia" => string(VERSION)), "cases" => ranges))
    end
    open(joinpath(dir, "show.json"), "w") do io
        JSON.print(io, Dict("meta" => Dict("julia" => string(VERSION)), "cases" => show_cases()))
    end
    math_golden(dir)
    trig_golden(dir)
end

# math.json has its own seed so the older goldens keep their random streams
function math_golden(dir)
    rng = Random.Xoshiro(20260925)
    open(joinpath(dir, "math.json"), "w") do io
        cases = math_rows(rng, 6000)
        # later additions draw from their own streams so `cases` stays reproducible
        rng2 = Random.Xoshiro(20260926)
        cbrt32 = [[hex(x), hex(cbrt(x))] for x in vcat(Float32[0, -0f0, Inf32, -Inf32, NaN32, 8, -27, 1f-45],
                                                        [sample32(rng2) for _ in 1:2000])]
        JSON.print(io, Dict("meta" => Dict("julia" => string(VERSION), "seed" => 20260925),
            "cases" => cases, "float16" => f16all(), "cbrt32" => cbrt32))
    end
end

function fuzz(prefix, n, seed)
    rng = Random.Xoshiro(seed)
    open(prefix * "_f64.tsv", "w") do io
        for x in Iterators.flatten((fixed64, (sample64(rng) for _ in 1:n)))
            println(io, join(f64rows([x])[1], '\t'))
        end
    end
    open(prefix * "_f32.tsv", "w") do io
        for x in Iterators.flatten((fixed32, (sample32(rng) for _ in 1:(n ÷ 4))))
            println(io, join(f32rows([x])[1], '\t'))
        end
    end
    open(prefix * "_opts.tsv", "w") do io
        for _ in 1:(n ÷ 4)
            println(io, join(opts_case(rng), '\t'))
        end
    end
    names = sort(collect(keys(BINOPS)))
    unames = sort(collect(keys(UNOPS)))
    open(prefix * "_num.tsv", "w") do io
        for _ in 1:n
            k = rand(rng, 1:10)
            c = k <= 5 ? binop_case(rng, rand(rng, names)) :
                k <= 7 ? unop_case(rng, rand(rng, unames)) :
                k <= 8 ? approx_case(rng) : complex_case(rng)
            c === nothing || println(io, (k <= 5 ? "bin\t" : k <= 7 ? "un\t" : k <= 8 ? "approx\t" : "cplx\t") * join(c, '\t'))
        end
    end
    open(prefix * "_range.tsv", "w") do io
        m = 0
        while m < n ÷ 10
            c = range_case(rng)
            c === nothing && continue
            println(io, join(c, '\t'))
            m += 1
        end
    end
    math_fuzz(prefix, n, seed)
    trig_fuzz(prefix, n, seed)
end

function math_fuzz(prefix, n, seed)
    rng = Random.Xoshiro(seed + 1)
    open(prefix * "_math.tsv", "w") do io
        for row in math_rows(rng, n)
            println(io, join(row, '\t'))
        end
    end
end

if ARGS[1] == "golden"
    golden(ARGS[2])
elseif ARGS[1] == "math"
    math_golden(ARGS[2])
elseif ARGS[1] == "fuzz"
    fuzz(ARGS[2], parse(Int, ARGS[3]), parse(Int, ARGS[4]))
elseif ARGS[1] == "fuzzmath"
    math_fuzz(ARGS[2], parse(Int, ARGS[3]), parse(Int, ARGS[4]))
elseif ARGS[1] == "trig"
    trig_golden(ARGS[2])
elseif ARGS[1] == "fuzztrig"
    trig_fuzz(ARGS[2], parse(Int, ARGS[3]), parse(Int, ARGS[4]))
else
    error("usage: gen_golden.jl golden DIR | math DIR | trig DIR | fuzz PREFIX N SEED | fuzzmath PREFIX N SEED | fuzztrig PREFIX N SEED")
end

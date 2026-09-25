# Oracle generator for the JuliaBase test suites.
#
#   julia --startup-file=no --project=oracle Tests/JuliaBase/gen_golden.jl golden Tests/JuliaBase
#       writes the committed goldens (float_show.json, num.json, range.json, show.json)
#   julia --startup-file=no --project=oracle Tests/JuliaBase/gen_golden.jl fuzz PREFIX N SEED
#       writes large TSV fuzz files PREFIX_{f64,f32,num,range}.tsv (not committed); run them with
#       Tests.JuliaBase.fuzzAll (see Tests/JuliaBase.lean).
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
    k = rand(rng, 1:10)
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
    else
        n < 2 && (n = 2)
        r = range(a, b, length = n)
        x = rand(rng, (2.0, 0.5, 3.0, π, -1.5, 0.1))
        op = rand(rng, ("mul", "bmul", "bdiv", "badd", "div"))
        rr = op == "mul" ? x * r : op == "bmul" ? x .* r : op == "bdiv" ? r ./ x : op == "badd" ? r .+ x : r / x
        return [op, hex(a), hex(b), string(n), hex(x), rangehex(rr)]
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

# ---------------------------------------------------------------- drivers

function golden(dir)
    rng = Random.Xoshiro(20260924)
    f64 = vcat(fixed64, [sample64(rng) for _ in 1:1600])
    f32 = vcat(fixed32, [sample32(rng) for _ in 1:400])
    open(joinpath(dir, "float_show.json"), "w") do io
        JSON.print(io, Dict("meta" => Dict("julia" => string(VERSION), "seed" => 20260924),
            "f64" => f64rows(f64), "f32" => f32rows(f32)))
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
end

if ARGS[1] == "golden"
    golden(ARGS[2])
elseif ARGS[1] == "fuzz"
    fuzz(ARGS[2], parse(Int, ARGS[3]), parse(Int, ARGS[4]))
else
    error("usage: gen_golden.jl golden DIR | fuzz PREFIX N SEED")
end

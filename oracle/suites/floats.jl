# oracle/suites/floats.jl: Julia's number display, the single biggest display risk
# (grassmann-types.md §5.5, DESIGN.md §6). About 20000 Float64 values given by their exact IEEE
# bit patterns, with `show` (shortest round-trip, Ryu `writeshortest`) and compact `show`
# (`:compact => true`, 6 significant digits), plus Int64, Rational{Int64}, Complex and Bool samples.

shards() = ["all"]

bits_hex(x::Float64) = string(reinterpret(UInt64, x); base = 16, pad = 16)
compact_show(x) = sprint(show, x; context = :compact => true)

"Deduplicate by bit pattern, keeping first occurrence."
function dedupe(xs)
    seen = Set{UInt64}()
    out = Float64[]
    for x in xs
        b = reinterpret(UInt64, x)
        b in seen && continue
        push!(seen, b)
        push!(out, x)
    end
    return out
end

function float_samples(rng)
    xs = Float64[]
    fb(u) = reinterpret(Float64, UInt64(u))
    # specials and famous values
    append!(xs, [0.0, -0.0, NaN, -NaN, Inf, -Inf, 1.0, -1.0, 0.5, 2.0, 10.0, 0.1, 0.2, 0.3, 0.1 + 0.2,
                 1 / 3, 2 / 3, float(π), float(ℯ), sqrt(2.0), eps(), floatmin(Float64), floatmax(Float64),
                 -floatmin(Float64), -floatmax(Float64), nextfloat(0.0), -nextfloat(0.0),
                 prevfloat(floatmin(Float64)), nextfloat(floatmin(Float64)), prevfloat(floatmax(Float64)),
                 fb(0x7ff8000000000001), fb(0xfff8000000000000), fb(0x7ff0000000000001), fb(0x7fffffffffffffff),
                 2.2250738585072011e-308, 2.2250738585072014e-308, 4.35, 2.675, 1.005, 100.0, 1e23, 8.41e21,
                 9007199254740993.0, 2.0^53, 2.0^53 + 2, 2.0^63, 2.0^64, 1e15, 1e16, 1e17, 123456.0,
                 1234567.0, 12345678.0, 123456.789, 12345.6789, 99999.5, 999999.4, 999999.5, 999999.9,
                 1e5, 1e6, 1e6 - 1, 1e6 - 0.5, 1e-4, 1e-5, 9.999e-5, 9.9999999e-5, 1.234e-5, 1e-7, 1e10,
                 1e-10, 1e20, 1e-20, 5e-324, 5.0e-301, 1.7976931348623157e308, 0.30000000000000004,
                 2.220446049250313e-16, 3.14159265, 0.0714286, 0.93224, -0.617273, 0.70369, 1e300, 1e-300])
    # powers of ten and their neighbours
    for k in -323:308
        x = parse(Float64, "1e$k")
        append!(xs, [x, nextfloat(x), prevfloat(x), -x])
    end
    # powers of two
    for k in -1074:1023
        push!(xs, ldexp(1.0, k))
    end
    # decade boundaries of the decimal/exponent switch, both forms
    for e in -8:8, m in (0.99999949, 0.9999995, 0.99999951, 0.999999, 1.0000005, 1.000005, 9.9999995, 9.999995, 1.2345675, 5.0000005)
        x = m * 10.0^e
        append!(xs, [x, nextfloat(x), prevfloat(x)])
    end
    # halfway cases for the 6-significant-digit compact rounding: 7-digit decimals ending in 5
    for _ in 1:2500
        d = rand(rng, 1000000:9999999)
        d = 10 * (d ÷ 10) + 5
        e = rand(rng, -12:12)
        s = string(d)
        push!(xs, (rand(rng, Bool) ? -1 : 1) * parse(Float64, s[1] * "." * s[2:end] * "e$e"))
    end
    # short decimals (what users type)
    for _ in 1:2500
        k = rand(rng, 0:9)
        push!(xs, (rand(rng, Bool) ? -1 : 1) * parse(Float64, string(rand(rng, 1:999999)) * "e-$k"))
    end
    # integers as floats
    for _ in 1:600
        push!(xs, float(rand(rng, -10^8:10^8)))
    end
    # random bit patterns (all exponents, incl. NaN payloads and subnormals)
    for _ in 1:5000
        push!(xs, reinterpret(Float64, rand(rng, UInt64)))
    end
    # subnormals
    for _ in 1:600
        push!(xs, reinterpret(Float64, rand(rng, UInt64) & 0x800fffffffffffff))
    end
    # log-uniform magnitudes
    for _ in 1:3000
        push!(xs, (rand(rng, Bool) ? -1 : 1) * 10.0^(60 * rand(rng) - 30))
    end
    # Gaussian values rounded to a few digits (typical coefficients)
    for _ in 1:1000
        push!(xs, round(randn(rng); digits = rand(rng, 1:8)))
    end
    return dedupe(xs)
end

function build(sh, defects)
    rng = rng_for("floats", sh)
    top = Obj("meta" => meta_obj("floats", sh; seed_key = seedkey("floats", sh), seed = string(fnv1a(seedkey("floats", sh)))))
    top["encoding"] = Obj(
        "Float64" => "value: 16 lowercase hex digits of the IEEE-754 bit pattern",
        "Int64" => "value: decimal string",
        "Rational{Int64}" => "value: [numerator, denominator] decimal strings",
        "Complex{Int64}" => "value: [re, im] decimal strings",
        "Complex{Float64}" => "value: [re, im] hex bit patterns",
        "Bool" => "value: \"true\"/\"false\"")
    top["fields"] = Obj("show" => "sprint(show, x)  (= repr(x) = string(x) for these types)",
                        "compact" => "sprint(show, x; context = :compact => true)")
    cl = CaseLog()
    for x in float_samples(rng)
        addcase!(cl, Obj("T" => "Float64", "value" => bits_hex(x), "show" => sprint(show, x), "compact" => compact_show(x)))
    end
    ints = Int64[0, 1, -1, 2, -2, 9, 10, -10, 100, 123456789, -987654321, typemax(Int64), typemin(Int64)]
    append!(ints, rand(rng, -10^6:10^6, 40))
    append!(ints, rand(rng, typemin(Int64):typemax(Int64), 20))
    for x in ints
        addcase!(cl, Obj("T" => "Int64", "value" => string(x), "show" => sprint(show, x), "compact" => compact_show(x)))
    end
    rats = Rational{Int64}[1 // 2, -1 // 2, 0 // 1, 3 // 1, -7 // 3, 123 // 456, 1 // 1000000, typemax(Int64) // 1, -5 // 7]
    append!(rats, [rand(rng, -50:50) // rand(rng, 1:60) for _ in 1:30])
    for x in rats
        addcase!(cl, Obj("T" => "Rational{Int64}", "value" => Any[string(numerator(x)), string(denominator(x))],
                          "show" => sprint(show, x), "compact" => compact_show(x)))
    end
    cis = Complex{Int64}[1 + 2im, -1 - 2im, 0 + 0im, 0 - 1im, 3 + 0im, -5 + 7im, 0 + 1im]
    append!(cis, [Complex(rand(rng, -9:9), rand(rng, -9:9)) for _ in 1:20])
    for x in cis
        addcase!(cl, Obj("T" => "Complex{Int64}", "value" => Any[string(real(x)), string(imag(x))],
                          "show" => sprint(show, x), "compact" => compact_show(x)))
    end
    cfs = ComplexF64[1.5 - 2.5im, 0.1 + 0.2im, complex(NaN, Inf), complex(-0.0, -0.0), complex(1 / 3, 2 / 3),
                     complex(1e-5, 1e6), complex(1.0, -0.0), complex(-Inf, NaN), complex(123456.789, -1e-20)]
    append!(cfs, [complex(round(randn(rng); digits = 3), round(randn(rng); digits = 5)) for _ in 1:20])
    append!(cfs, [complex(reinterpret(Float64, rand(rng, UInt64)), reinterpret(Float64, rand(rng, UInt64))) for _ in 1:20])
    for x in cfs
        addcase!(cl, Obj("T" => "Complex{Float64}", "value" => Any[bits_hex(real(x)), bits_hex(imag(x))],
                          "show" => sprint(show, x), "compact" => compact_show(x)))
    end
    for x in (true, false)
        addcase!(cl, Obj("T" => "Bool", "value" => string(x), "show" => sprint(show, x), "compact" => compact_show(x)))
    end
    top["cases"] = cl.cases
    return retag!(top, defects)
end

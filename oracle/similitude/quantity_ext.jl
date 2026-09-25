# Golden generator for the rest of Similitude's quantity algebra: literal and
# rational powers, `Quantity * ConvertUnit`, the quotient of quantities of two
# systems (a `ConvertUnit`), products of conversion factors, a dimensionless
# quantity plus a `Constant`, and logarithmic quantities (`log`, `log2`,
# `log10`, `logdb`, their sums, scalings and `exp`), plus `neper`, `bel`,
# `decibel` in every system.
#   julia --startup-file=no --project=oracle oracle/similitude/quantity_ext.jl
# Writes oracle/golden/similitude/quantity_ext.json.
using Similitude, Random
const S = Similitude
const US = S.UnitSystems
const FC = US.FieldConstants
include(joinpath(@__DIR__, "..", "unitsystems", "jsonw.jl"))
const OUT = joinpath(@__DIR__, "..", "golden", "similitude")
mkpath(OUT)
Random.seed!(20260925)

showstr(x) = try sprint(show, x) catch; "ERROR" end
h(x::Real) = "0x" * string(reinterpret(UInt64, Float64(x)), base = 16, pad = 16)
num(x::Integer) = ["I", string(x)]
num(x::Rational) = ["R", string(numerator(x), "/", denominator(x))]
num(x::AbstractFloat) = ["F", h(x)]

const systems = [s for s in US.Systems]
const convs = [u for u in US.Convert]

pw = Any[]
for i in 1:300
    u = rand(convs); d = S.evaldim(u)
    s = rand(systems); U = getfield(S, s)
    x = rand((2, 3, 0.5, 2.5, 1//3, 4.0))
    q = U(x, d)
    y = rand((1, 2, 0.25))
    b = S.English(y, d)
    push!(pw, Dict("sys" => string(s), "q" => string(u), "x" => num(x), "y" => num(y),
        "show" => showstr(q), "pow_m2" => showstr(q^-2), "pow_m1" => showstr(q^-1), "pow3" => showstr(q^3),
        "pow_half" => showstr(q^(1//2)), "pow_third" => showstr(q^(1//3)), "pow_m3half" => showstr(q^(-3//2)),
        "times_conv" => showstr(q * d(U, S.English)), "quotient" => showstr(q / b),
        "conv_sq" => showstr(d(U, S.English) * d(U, S.English)), "conv_div" => showstr(d(U, S.English) / S.length(U, S.English))))
end

dl = Any[]
for s in systems, u in convs
    U = getfield(S, s); d = S.evaldim(u)
    U(d) == S.𝟙 || continue
    rand() < 0.15 || continue
    q = U(2.5, d)
    push!(dl, Dict("sys" => string(s), "q" => string(u), "add" => showstr(q + FC.Constant(1.5)),
        "radd" => showstr(FC.Constant(1.5) + q), "sub" => showstr(q - FC.Constant(1.5))))
end

lg = Any[]
for i in 1:150
    u = rand(convs); d = S.evaldim(u)
    s = rand(systems); U = getfield(S, s)
    x = rand((2.0, 0.5, 10.0, 3.75))
    q = U(x, d)
    l = log(q)
    push!(lg, Dict("sys" => string(s), "q" => string(u), "x" => num(x),
        "log" => showstr(l), "log2" => showstr(log2(q)), "log10" => showstr(log10(q)),
        "logdb" => showstr(S.logdb(q)), "add" => showstr(l + l), "sub" => showstr(l - l),
        "mul2" => showstr(l * 2), "div2" => showstr(l / 2), "exp" => showstr(exp(l)),
        "exp10" => showstr(exp10(log10(q)))))
end

nb = Any[]
for s in systems
    U = getfield(S, s)
    push!(nb, [string(s), showstr(S.neper(U)), showstr(S.bel(U)), showstr(S.decibel(U)),
        showstr(exp(S.neper(U))), showstr(exp10(S.bel(U)))])
end

# `display(U)` of every system: the defining constants as quantities (`Similitude.jl:103-126`)
function capture_display(x)
    io = IOBuffer()
    old = stdout
    rd, wr = redirect_stdout()
    t = @async read(rd, String)
    try
        display(x)
    finally
        redirect_stdout(old)
        close(wr)
    end
    fetch(t)
end
dsp = Any[[string(s), capture_display(getfield(S, s))] for s in systems]

writejson(joinpath(OUT, "quantity_ext.json"), Dict("julia" => string(VERSION), "powers" => pw,
    "dimensionless" => dl, "logs" => lg, "neper" => nb, "display" => dsp))
println("wrote quantity_ext.json")

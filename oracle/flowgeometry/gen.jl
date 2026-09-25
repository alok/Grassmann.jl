# Golden generator for FlowGeometry.jl (profiles, airfoils, the NACA grammar, meshes).
#
#   julia --startup-file=no --project=oracle oracle/flowgeometry/gen.jl [path/to/FlowGeometry.jl]
#
# FlowGeometry is not in the oracle environment; its dependencies (Grassmann, Cartan,
# LinearAlgebra) are, so the package source is `include`d from a checkout (default
# ~/chakravala/FlowGeometry.jl, v0.1.5 = commit 395ab65). Julia 1.13 has package extensions, so
# the `Requires` branch of the package is not taken.
#
# Writes oracle/golden/flowgeometry/*.json. Floats are IEEE bit patterns ("0x…"); complex vectors
# and homogeneous points are flattened (re, im, re, im, … and 1, x, y, 1, x, y, …); a Julia
# exception is {"E": "<Type>: <message>"}; integers are JSON numbers.
#
# Shims (oracle/flowgeometry/defects.toml): `TorusTopology` is imported into FlowGeometry (FG-B1,
# `complex(::Airfoil)` throws without it). Keys ending in `_patched` record Julia's value of the
# evident intent of a broken method (FG-B2 British, FG-B6 SymmetricArc/DoubleArc `interval`,
# FG-B7 `initedges`, FG-B8 `addbound`), computed by patched copies installed below; the
# unpatched call's error is recorded next to it.
using Grassmann, Cartan, LinearAlgebra, Random
const SRC = length(ARGS) ≥ 1 ? ARGS[1] : joinpath(homedir(), "chakravala", "FlowGeometry.jl")
include(joinpath(SRC, "src", "FlowGeometry.jl"))
using .FlowGeometry
const F = FlowGeometry
isdefined(F, :TorusTopology) || Core.eval(F, :(const TorusTopology = Cartan.TorusTopology))
include(joinpath(@__DIR__, "..", "unitsystems", "jsonw.jl"))
const OUT = joinpath(@__DIR__, "..", "golden", "flowgeometry")
mkpath(OUT)
const fib = Cartan.fiber

hx(x::Real) = "0x" * string(reinterpret(UInt64, Float64(x)), base = 16, pad = 16)
errstr(e) = (s = sprint(showerror, e); string(nameof(typeof(e)), ": ", first(s, 160)))
fixtype(s) = replace(s, "Main.FlowGeometry." => "")
typestr(x) = fixtype(string(typeof(x)))
enc(x::Bool) = x
enc(x::Integer) = x
enc(x::AbstractFloat) = hx(x)
enc(x::Real) = hx(x)
# complex vectors and vectors of chains are flattened
flat(x::Complex) = [hx(real(x)), hx(imag(x))]
flat(x::Real) = [hx(x)]
flat(x::Grassmann.Chain) = [hx(y) for y in Grassmann.value(x)]
flat(x::Values) = [hx(y) for y in x]
flatv(v) = reduce(vcat, [flat(y) for y in v]; init = String[])
ints(v) = [Int(y) for y in v]
macro safe(ex)
    quote
        try
            $(esc(ex))
        catch e
            e isa InterruptException && rethrow()
            Dict("E" => errstr(e))
        end
    end
end
save(name, data) = (writejson(joinpath(OUT, name * ".json"), data);
    println("wrote ", name, " (", filesize(joinpath(OUT, name * ".json")), " bytes)"))
gitrev = try strip(read(`git -C $SRC rev-parse --short HEAD`, String)) catch; "unknown" end
meta = Dict("julia" => string(VERSION), "flowgeometry" => "0.1.5 @ " * gitrev,
    "grassmann" => string(pkgversion(Grassmann)), "cartan" => string(pkgversion(Cartan)))
Random.seed!(20260925)

# ------------------------------------------------------------------------------------------
# Patched intents (recorded under `*_patched` keys only)
# ------------------------------------------------------------------------------------------
# FG-B2: British multiplies a Vector by a TensorField; broadcast the product instead.
brit_upper(x, yc, dyc, yt) = F.upper(x + im*yc, TensorField(base(yt), (im .* cis.(atan.(collect(dyc)))) .* fib(yt)))
brit_lower(x, yc, dyc, yt) = F.lower(x + im*yc, TensorField(base(yt), (im .* cis.(atan.(collect(dyc)))) .* fib(yt)))
brit_upper(n::F.British, c = 1, x0 = 0) = brit_upper(F.getprofiles(n, c, x0)...)
brit_lower(n::F.British, c = 1, x0 = 0) = brit_lower(F.getprofiles(n, c, x0)...)
# FG-B6: SymmetricArc/DoubleArc/British have no `interval`; use the (upper) profile's.
patched_interval(n::SymmetricArc, c = 1, x0 = 0) = interval(n.s, c, x0)
patched_interval(n::DoubleArc, c = 1, x0 = 0) = interval(n.u, c, x0)
patched_interval(n::F.British, c = 1, x0 = 0) = interval(n.c, c, x0)
patched_interval(n, c = 1, x0 = 0) = interval(n, c, x0)
patched_upperlower(n::F.British) = (brit_upper(n), brit_lower(n))
patched_upperlower(n) = upperlower(n)
function patched_complex(N)
    U, L = patched_upperlower(N)
    TensorField(F.doubleinterval(patched_interval(N)), [fib(U); reverse(fib(L))[2:end]])
end

# ------------------------------------------------------------------------------------------
# Profiles
# ------------------------------------------------------------------------------------------
xfix = vcat([-0.1, -1e-9, -0.0], collect(range(0.0, 1.0, length = 101)),
    [0.0125, 0.003, 0.87437, 0.87, 0.9, 0.8, 0.5000000000000001, 1.0 - 1e-8, 1.0 - 1e-7, 1e-7, 1e-8, 1.0 + 1e-9, 1.1, 2.0])
xs = vcat(xfix, rand(400), rand(20) .* 1e-6)
xsc = [0.5, 0.75, 1.0, 1.5, 2.0, 2.5, 0.4, 1.23456789]
profs = Any[
    FlatPlate{5}(), FlatPlate{2}(),
    ParabolicArc{6,5}(), ParabolicArc{10,5}(), ParabolicArc{5}(), ParabolicArc{2.5,7}(),
    CircularArc{6,5}(), CircularArc{10,5}(), CircularArc{2,5}(), CircularArc{21}(), CircularArc{7.5,6}(),
    ClarkY{12,5}(), ClarkY{6,5}(), ClarkY{12,0.0,5}(), ClarkY{15,0.5,5}(), ClarkY{12.5,5}(), ClarkY{12,150}(),
    Thickness{12,5}(), Thickness{12,4,5}(), Thickness{9,2,0.1,5}(), Thickness{15,5,5}(), Thickness{10.5,3,0.2,6}(),
    Modified{12,5}(), Modified{12,63,5}(), Modified{12,64,5}(), Modified{12,33,5}(), Modified{12,34,5}(),
    Modified{10,93,5}(), Modified{12,65,0.5,5}(), Modified{6,12,5}(), Modified{5,12,5}(), Modified{8.25,63.5,5}(),
    Modified{15,95,5}(), Modified{12,64,150}(),
    NACA4{24,5}(), NACA4{0,5}(), NACA4{44,5}(), NACA4{64,5}(), NACA4{25,5}(), NACA4{65,5}(), NACA4{99,6}(),
    NACA4{24,150}(),
    NACA5{210,5}(), NACA5{220,5}(), NACA5{230,5}(), NACA5{240,5}(), NACA5{250,5}(), NACA5{430,5}(),
    NACA5{221,5}(), NACA5{231,5}(), NACA5{241,5}(), NACA5{251,5}(), NACA5{230,150}(),
    NACA6{2,5}(), NACA6{4,5}(), NACA6{0,5}(), NACA6{2.5,6}(), NACA6{3,9}(),
    NACA6{5}(Values(0.5, 1.0), Values(0.1, 0.2)), NACA6{5}(Values(0.8), Values(0.3)),
    NACA6{7}(Values(0.3, 0.6, 1.0), Values(0.05, 0.1, 0.25)),
    NACA6A{2,5}(), NACA6A{0,5}(), NACA6A{4,6}()]
plist = Any[]
for p in profs
    d = Dict{String,Any}("type" => typestr(p))
    d["y"] = [@safe(hx(p(x))) for x in xs]
    d["dy"] = [@safe(hx(profileslope(p, x))) for x in xs]
    d["angle"] = [@safe(hx(profileangle(p, x, 1, 0))) for x in xs]
    d["y_c2_x0h"] = [@safe(hx(profile(p, x, 2.0, 0.5))) for x in xsc]
    d["dy_c2_x0h"] = [@safe(hx(profileslope(p, x, 2.0, 0.5))) for x in xsc]
    d["angle_c2_x0h"] = [@safe(hx(profileangle(p, x, 2.0, 0.5))) for x in xsc]
    d["y_c3_x0m1"] = [@safe(hx(profile(p, x, 3, -1))) for x in xsc]
    d["adjoint"] = [@safe(hx((p')(x))) for x in xsc]
    d["field"] = @safe(flatv(fib(profile(p))))
    d["slopefield"] = @safe(flatv(fib(profileslope(p))))
    d["anglefield"] = @safe(flatv(fib(profileangle(p))))
    d["interval"] = repr(interval(p))
    d["interval_c2_x01"] = repr(interval(p, 2, 1))
    d["interval_vals"] = flatv(collect(interval(p, 2.5, -0.5)))
    d["points"] = @safe(flatv(F.points(p)))
    d["points_c2_x01"] = @safe(flatv(F.points(p, 2, 1)))
    d["initpoints"] = @safe(flatv(F.initpoints(p)))
    d["chord"] = flatv(collect(chord(p)))
    push!(plist, d)
end
save("profiles", Dict("meta" => meta, "x" => flatv(xs), "xsc" => flatv(xsc), "profiles" => plist))

# ------------------------------------------------------------------------------------------
# Internals: the precomputed coefficients (localise errors before the profiles)
# ------------------------------------------------------------------------------------------
internals = Dict{String,Any}()
internals["clarky"] = [Dict("te" => hx(te), "a" => flatv([F.clarky(te)])) for te in (0.0021, 0.0, 0.005, 0.0012, 0.001)]
internals["clarky5"] = [Dict("te" => hx(te), "x" => hx(x), "a" => @safe(flatv([F.clarky(te, x)])))
    for (te, x) in ((0.0012, 0.3), (0.0012, 0.4), (0.002, 0.2), (0.001, 0.5), (0.0009, 0.6), (0.0015, 0.5), (0.00105, 0.3))]
internals["tailslope"] = [[hx(x), hx(F.tailslope(x))] for x in (0.2, 0.3, 0.4, 0.5, 0.6, 0.45, 0.35, 0.635)]
internals["riegel"] = [[hx(x), hx(F.riegel(x))] for x in (0.2, 0.3, 0.4, 0.5, 0.6)]
internals["radius"] = [[hx(t), hx(F.radius(t))] for t in (0.06, 0.12, 0.2, 0.2/3, 0.2*9/6, 0.2*6sqrt(3)/6)]
modlist = [(12, 63, 0.2), (12, 64, 0.2), (12, 33, 0.2), (10, 93, 0.2), (6, 12, 0.2), (5, 12, 0.2), (12, 65, 0.5),
    (8.25, 63.5, 0.2), (15, 95, 0.2), (12, 34, 0.2)]
internals["modified"] = [begin
        M = Modified{t,m,te,5}()
        tip = F.modified(M)
        a, d = F.modified(tip...)
        Dict("type" => typestr(M), "params" => [hx(tip[1]), hx(tip[2]), hx(tip[3]), hx(tip[4])],
             "a" => flatv([a]), "d" => flatv([d]))
    end for (t, m, te) in modlist]
internals["naca4"] = [begin
        m, p = F.naca4(n)
        f, r = F.naca4(m, p)
        Dict("n" => n, "m" => hx(m), "p" => hx(p), "front" => flatv([f]), "rear" => flatv([r]))
    end for n in (0, 24, 44, 64, 25, 12, 65, 99, 10)]
internals["naca5"] = [Dict("n" => n, "decode" => @safe([hx(y) for y in F.naca5(n)]))
    for n in (210, 220, 230, 240, 250, 430, 221, 231, 241, 251, 110, 999, 232)]
internals["naca6"] = [begin
        n = NACA6{9}(Values(a...), Values(cl...))
        Cla, aa, h, g = F.naca6(n)
        Dict("a" => flatv(collect(a)), "cl" => flatv(collect(cl)), "cla" => flatv(collect(Cla)), "h" => flatv(collect(h)),
             "g" => flatv(collect(g)), "type" => typestr(n))
    end for (a, cl) in (((0.8,), (0.1,)), ((0.5, 1.0), (0.1, 0.2)), ((1.0,), (0.2,)), ((0.3, 0.6, 1.0), (0.05, 0.1, 0.25)))]
save("internals", Dict("meta" => meta, "internals" => internals))

# ------------------------------------------------------------------------------------------
# The NACA grammar (types only)
# ------------------------------------------------------------------------------------------
nacaparse(s) = eval(Meta.parse("F.@NACA_str " * repr(s)))
fixed_strings = ["0006", "0012", "0015", "2412", "2415", "4412", "4415", "6409", "6511", "0012-64", "0012-34",
    "2412-34", "4412-63", "23012", "23015", "23112", "24012-34", "16-212", "16-(2)(12)", "16-009", "16-012",
    "65A012", "65A010", "64A210", "63A415", "2412.5", "abc", "12345", "x2412y", "2412-6", "2412-", "24120",
    "241.12", "0008.25-63.5", "16-2.5(12)", "16-2.512", "16-(2.5)(12.25)", "1-212", "6A012", "65A(1)(12)",
    "NACA 2412", "", "2412-34.5", "230", "23012-", "23012-6", "010", "0010", "01012", "16-2(12", "16-(2)12",
    "64A2.10", "9999", "99999", "00000", "1611-12", "16-2", "6XA012", "12-345", "2 412", "24-12", "16--212"]
digits(k) = join(rand('0':'9', k))
function randgrammar()
    r = rand()
    s = if r < 0.2
        digits(4)
    elseif r < 0.35
        digits(2) * rand(["0", "1"]) * digits(2)
    elseif r < 0.45
        digits(4) * "-" * digits(2)
    elseif r < 0.55
        "1" * digits(1) * "-" * digits(1) * digits(2)
    elseif r < 0.65
        "6" * digits(1) * "A" * digits(1) * digits(2)
    elseif r < 0.72
        "1" * digits(1) * "-(" * digits(1) * ")(" * digits(2) * ")"
    elseif r < 0.8
        digits(4) * "." * digits(rand(1:3))
    else
        join(rand(['0':'9'..., '-', '.', '(', ')', 'A'], rand(3:9)))
    end
    return s
end
strings = vcat(fixed_strings, [randgrammar() for _ in 1:400])
parses = [begin
        d = Dict{String,Any}("s" => s)
        try
            d["type"] = typestr(nacaparse(s))
        catch e
            d["E"] = errstr(e isa LoadError ? e.error : e)
        end
        d
    end for s in strings]
save("parse", Dict("meta" => meta, "cases" => parses))

# ------------------------------------------------------------------------------------------
# Airfoils
# ------------------------------------------------------------------------------------------
function airfoil_record(name, a)
    d = Dict{String,Any}("name" => name, "type" => typestr(a), "p" => typeof(a).parameters[end])
    d["interval"] = @safe(repr(interval(a)))
    d["interval_patched"] = @safe(repr(patched_interval(a)))
    for (c, x0, tag) in ((1, 0, ""), (2, 1, "_c2_x01"), (0.5, -0.25, "_ch_x0q"))
        u = @safe(F.upper(a, c, x0)); l = @safe(F.lower(a, c, x0))
        d["upper" * tag] = u isa Dict ? u : flatv(fib(u))
        d["lower" * tag] = l isa Dict ? l : flatv(fib(l))
        u isa Dict || (d["upper_base" * tag] = repr(Cartan.points(u)))
        l isa Dict || (d["lower_base" * tag] = repr(Cartan.points(l)))
        if a isa F.British
            d["upper" * tag * "_patched"] = flatv(fib(brit_upper(a, c, x0)))
            d["lower" * tag * "_patched"] = flatv(fib(brit_lower(a, c, x0)))
        end
    end
    cx = @safe(complex(a))
    d["complex"] = cx isa Dict ? cx : flatv(fib(cx))
    cx isa Dict || (d["complex_base"] = repr(Cartan.points(cx)))
    pc = @safe(patched_complex(a))
    d["complex_patched"] = pc isa Dict ? pc : flatv(fib(pc))
    pc isa Dict || (d["complex_base_patched"] = repr(Cartan.points(pc)))
    d["points"] = @safe(flatv(F.points(a)))
    return d
end
nacas = ["0006", "0012", "2412", "2415", "4412", "6409", "6511", "0012-64", "2412-34", "4412-63", "23012",
    "24012-34", "16-212", "16-012", "64A210", "2412.5", "0008.25-63.5"]
alist = Any[]
for s in nacas
    push!(alist, airfoil_record(s, nacaparse(s)))
end
save("airfoils", Dict("meta" => meta, "airfoils" => alist))

small = Any[("American(NACA4{24,9},ClarkY{12,9})", American(NACA4{24,9}(), ClarkY{12,9}())),
    ("American(NACA4{0,9},Modified{12,64,9})", American(NACA4{0,9}(), Modified{12,64,9}())),
    ("American(NACA6{2,9},ClarkY{12,9})", American(NACA6{2,9}(), ClarkY{12,9}())),
    ("American(NACA5{230,9},Thickness{12,9})", American(NACA5{230,9}(), Thickness{12,9}())),
    ("American(CircularArc{4,9},ClarkY{9,9})", American(CircularArc{4,9}(), ClarkY{9,9}())),
    ("American(NACA6A{2,9},Modified{12,9})", American(NACA6A{2,9}(), Modified{12,9}())),
    ("British(NACA5{230,9},ClarkY{12,9})", F.British(NACA5{230,9}(), ClarkY{12,9}())),
    ("British(NACA4{24,9},Modified{12,64,9})", F.British(NACA4{24,9}(), Modified{12,64,9}())),
    ("SymmetricArc(CircularArc{6,9})", SymmetricArc(CircularArc{6,9}())),
    ("SymmetricArc(ClarkY{12,9})", SymmetricArc(ClarkY{12,9}())),
    ("SymmetricArc(FlatPlate{9})", SymmetricArc(FlatPlate{9}())),
    ("DoubleArc(CircularArc{6,9},ParabolicArc{4,9})", DoubleArc(CircularArc{6,9}(), ParabolicArc{4,9}())),
    ("DoubleArc(CircularArc{6,9},ParabolicArc{4,5})", DoubleArc(CircularArc{6,9}(), ParabolicArc{4,5}())),
    ("American(UpperArc(American(NACA4{24,9},ClarkY{12,9})),ClarkY{6,9})",
        American(UpperArc(American(NACA4{24,9}(), ClarkY{12,9}())), ClarkY{6,9}())),
    ("SymmetricArc(UpperArc(American(NACA4{24,9},ClarkY{12,9})))",
        SymmetricArc(UpperArc(American(NACA4{24,9}(), ClarkY{12,9}())))),
    ("SymmetricArc(LowerArc(SymmetricArc(CircularArc{6,9})))",
        SymmetricArc(LowerArc(SymmetricArc(CircularArc{6,9}()))))]
slist = Any[]
for (k, a) in small
    push!(slist, airfoil_record(k, a))
end
jlist = Any[]
for (R, f, g, b, p) in ((1.1, 0.1, 0.1, 1.0, 5), (1.1, 0.1, 0.0, 1.0, 9), (1.2, 0.15, 0.05, 1.0, 17), (1.0, 0.0, 0.0, 1.0, 5),
        (1.1, 0.1, 0, 1, 5), (1.3, -0.2, -0.1, 1.1, 7), (1.1, 0.1, 0.1, 1.0, 75))
    j = F.joukowski(R, f, g, b, p)
    push!(jlist, Dict("type" => typestr(j), "interval" => repr(interval(j)), "complex" => flatv(fib(complex(j))),
        "complex_base" => repr(Cartan.points(complex(j))), "points" => flatv(F.points(j))))
end
# UpperArc / LowerArc as profiles
arcs = Any[UpperArc(American(NACA4{24,9}(), ClarkY{12,9}())), LowerArc(American(NACA4{24,9}(), ClarkY{12,9}())),
    UpperArc(SymmetricArc(CircularArc{6,9}())), LowerArc(DoubleArc(CircularArc{6,9}(), ParabolicArc{4,7}())),
    UpperArc(American(NACA4{24,5}(), ClarkY{12,5}()))]
arclist = Any[]
for U in arcs
    d = Dict{String,Any}("type" => typestr(U))
    d["interval"] = flatv(fib(interval(U)))
    d["interval_c2_x01"] = flatv(fib(interval(U, 2, 1)))
    d["field"] = flatv(fib(profile(U)))
    d["slopefield"] = @safe(flatv(fib(profileslope(U))))
    d["upper"] = flatv(fib(upper(U)))
    d["lower"] = flatv(fib(lower(U)))
    d["upper_c2_x01"] = flatv(fib(upper(U, 2, 1)))
    d["eval"] = @safe(hx(U(0.5)))
    push!(arclist, d)
end
save("small", Dict("meta" => meta, "airfoils" => slist, "joukowski" => jlist, "arcs" => arclist))

# ------------------------------------------------------------------------------------------
# Meshes and point utilities
# ------------------------------------------------------------------------------------------
md = Dict{String,Any}()
md["rectangletriangle"] = [Dict("m" => m, "tris" => [ints(F.rectangletriangle(i, m)) for i in 1:2(m-1)*4]) for m in (3, 4, 7)]
md["rectangletriangles"] = [Dict("m" => m, "JL" => JL, "tris" => [ints(t) for t in F.rectangletriangles(m, JL)])
    for (m, JL) in ((3, 3), (4, 3), (3, 5), (6, 4))]
md["rectanglebounds"] = [Dict("n" => n, "JL" => JL, "edges" => [ints(t) for t in F.rectanglebounds(n, JL)])
    for (n, JL) in ((3, 3), (4, 3), (3, 5), (6, 4), (2, 2))]
md["FittedPoint"] = [Dict("k" => k, "JL" => JL, "pt" => flatv([F.FittedPoint(k, JL)])) for (k, JL) in ((1, 3), (5, 3), (9, 3), (52, 51), (2601, 51))]
md["RakichNewton"] = [Dict("D" => hx(D), "JL" => JL, "dy" => hx(dy), "k" => hx(F.RakichNewton(D, JL, dy)))
    for (D, JL, dy) in ((50, 51, 6e-3), (50, 51, 0.1), (10, 21, 0.01), (49.9, 26, 0.006), (50, 5, 0.1), (50.0, 51, 0.006),
        (49.99999999999999, 11, 0.006), (1, 3, 0.2))]
md["RakichLine"] = [Dict("y" => hx(y), "D" => hx(D), "JL" => JL, "dy" => hx(dy), "v" => flatv(F.RakichLine(y, D, JL, dy)))
    for (y, D, JL, dy) in ((0, 50, 5, 0.1), (0, 50, 51, 0.006), (-0.0, 50, 6, 0.25), (0.03, 50, 11, 0.006))]
md["Rakich"] = [Dict("k" => hx(k), "j" => j, "y0" => hx(y0), "D" => hx(D), "JL" => JL, "v" => hx(F.Rakich(k, j, y0, D, JL)))
    for (k, j, y0, D, JL) in ((1.0, 3, 0, 50, 5), (7.157340807983087, 20, 0.01, 50, 51), (2.5, 1, 0.3, 10, 7))]
md["RakichPlate"] = [Dict("type" => typestr(P), "D" => D, "JL" => JL, "v" => flatv(F.RakichPlate(P, D, JL)))
    for (P, D, JL) in ((CircularArc{6,5}(), 50, 11), (CircularArc{6,21}(), 50, 51), (CircularArc{6,61}(), 50, 101),
        (ClarkY{12,9}(), 20, 17))]
md["rakichpoints"] = [Dict("type" => typestr(P), "D" => D, "n" => n, "JL" => JL,
        "v" => flatv(collect(Cartan.points(F.rakichpoints(P, D, n, JL)))))
    for (P, D, n, JL) in ((CircularArc{6,5}(), 50, 11, 5), (CircularArc{6,21}(), 50, 51, 51), (CircularArc{10,9}(), 30, 21, 9))]
pt, pe = F.initrakich()
md["initrakich"] = Dict("points" => flatv(collect(Cartan.fullpoints(pt))),
    "tris" => [ints(t) for t in Cartan.topology(pt)], "bounds" => [ints(t) for t in Cartan.topology(pe)],
    "nodes_tris" => length(pt), "nodes_bounds" => length(pe))
md["rectangle"] = [Dict("args" => flatv([a...]), "v" => flatv(F.rectangle(a...))) for a in ((-1.0, 2.0, -1.0, 1.0), (0.0, 1.0, 0.0, 1.0))]
md["square"] = [Dict("args" => flatv([a...]), "v" => flatv(F.square(a...))) for a in ((1.0,), (-0.5, 2.0))]
md["box"] = [Dict("args" => flatv([a...]), "v" => flatv(F.box(a...))) for a in ((0.0, 1.0, 0.0, 2.0, 0.0, 3.0),)]
md["cube"] = [Dict("args" => flatv([a...]), "v" => flatv(F.cube(a...))) for a in ((1.0,), (-2.0, 0.5))]
md["icosahedron"] = [Dict("a" => hx(a), "v" => flatv(F.icosahedron(a))) for a in (1.0, 0.5, 2.0)]
md["icosahedron_ab"] = [Dict("a" => hx(a), "b" => hx(b), "v" => flatv(F.icosahedron(a, b))) for (a, b) in ((1.0, 2.0),)]
md["sphere"] = [Dict("r" => hx(r), "v" => flatv(F.sphere(r))) for r in (1.0, 2.0, 0.75)]
md["circlemid"] = [Dict("x" => flatv([x]), "r" => hx(r), "v" => flatv([F.circlemid(x, r)]))
    for (x, r) in ((Chain{Submanifold(ℝ^4),1}(2.0, 1.0, 1.0, 0.0), 1.0), (Chain{Submanifold(ℝ^4),1}(2.0, 0.3, -0.7, 1.1), 2.5),
        (Chain{Submanifold(ℝ^4),1}(2.0, 0.0, 0.0, 1e-3), 1.0))]
md["rectcirc"] = [Dict("n" => n, "args" => flatv([a...]), "c" => flatv([c]), "v" => flatv(F.rectcirc(n, a..., c)))
    for (n, a, c) in ((4, (-1.0, 2.0, -1.0, 1.0), Chain{Submanifold(ℝ^3),1}(1.0, 0.0, 0.0)),
        (6, (-1.5, 3.5, -1.5, 1.5), Chain{Submanifold(ℝ^3),1}(1.0, 0.0, 0.0)),
        (5, (-1.0, 3.0, -2.0, 1.0), Chain{Submanifold(ℝ^3),1}(1.0, 0.5, -0.25)),
        (2, (-1.0, 1.0, -1.0, 1.0), Chain{Submanifold(ℝ^3),1}(1.0, 0.0, 0.0)),
        (9, (-1.5, 3.5, -1.5, 1.5), Chain{Submanifold(ℝ^3),1}(1.0, 0.5, 0.0)))]
# edges
md["edgeslist"] = [Dict("n" => n, "edges" => [ints(e) for e in F.edgeslist(Cartan.PointCloud(F.points(ClarkY{12,n}())))]) for n in (5, 2)]
# FG-B8: `edgeslist!` pushes Chains into the PointArray of Coordinates (convert error); the intent
# (append the points, return the closed loop over the new indices) on a plain vector:
function edgeslist_patched!(pts::Vector, r)
    l, n = length(pts), length(r)
    append!(pts, r)
    Values{2,Int}.(l+1:l+n, l .+ [2:n; 1])
end
md["edgeslist!"] = @safe(F.edgeslist!(Cartan.PointCloud(F.points(ClarkY{12,5}())), F.rectangle(-1.0, 2.0, -1.0, 1.0)))
let pts = collect(F.points(ClarkY{12,5}()))
    e = edgeslist_patched!(pts, F.rectangle(-1.0, 2.0, -1.0, 1.0))
    md["edgeslist!_patched"] = Dict("edges" => [ints(x) for x in e], "points" => flatv(pts))
end
md["airfoiledges"] = [Dict("name" => s, "edges" => [ints(e) for e in F.airfoiledges(nacaparse(s))]) for s in ("2412",)]
md["addbound"] = @safe(F.addbound(F.airfoiledges(nacaparse("2412"))))
let N = American(NACA4{24,9}(), ClarkY{12,9}())
    pts = collect(F.points(N)); e = F.edgeslist(Cartan.PointCloud(F.points(N)))
    ee = [e; edgeslist_patched!(pts, F.rectangle(-1.5, 3.5, -1.5, 1.5))]
    md["addbound_patched"] = Dict("edges" => [ints(x) for x in ee], "points" => flatv(pts))
end
md["initedges"] = @safe(F.initedges(ClarkY{12,5}()))
let ie = Cartan.initedges(collect(interval(ClarkY{12,5}())))
    md["initedges_patched"] = Dict("points" => flatv(collect(Cartan.fullpoints(ie))), "edges" => [ints(t) for t in Cartan.topology(ie)])
end
md["chord"] = flatv(collect(F.chord(5)))
md["interval"] = [Dict("p" => p, "c" => hx(c), "x0" => hx(x0), "repr" => repr(interval(p, c, x0)), "v" => flatv(collect(interval(p, c, x0))))
    for (p, c, x0) in ((5, 2, 1), (150, 1, 0), (7, 3.5, -1.25), (2, 1, 0), (11, 0.3, 0.1))]
md["interval150_1_4"] = flatv(collect(interval(150))[1:4])
md["doubleinterval"] = [Dict("p" => p, "repr" => repr(F.doubleinterval(interval(p))), "v" => flatv(collect(F.doubleinterval(interval(p)))))
    for p in (5, 150, 9)]
# convex hull
hullsets = Any[F.rectangle(-1.0, 1.0, -1.0, 1.0),
    [Chain{Submanifold(ℝ^3),1}(1.0, Float64(i), Float64(j)) for i in 0:3 for j in 0:3],
    [Chain{Submanifold(ℝ^3),1}(1.0, randn(), randn()) for _ in 1:25],
    [Chain{Submanifold(ℝ^3),1}(1.0, cos(2π*k/12), sin(2π*k/12)) for k in 0:11],
    F.points(American(NACA4{24,9}(), ClarkY{12,9}()))]
md["convhull"] = [Dict("points" => flatv(P), "edges" => [ints(e) for e in F.convhull(Cartan.PointCloud(P))],
        "edges_r" => [ints(e) for e in F.convhull(Cartan.PointCloud(P), 1.5)]) for P in hullsets]
# decsg geometry matrix (the data passed to MATLAB's decsg, FlowGeometry.jl:282-289)
md["decsg"] = [begin
        N = nacaparse(s); pts = typeof(N).parameters[end]
        P = fib(complex(N))[1:end-1]
        x1, x2, x3, x4 = -1.5, 3.5, 3.5, -1.5; y1, y2, y3, y4 = 1.5, 1.5, -1.5, -1.5
        R = [[3, 4, x1, x2, x3, x4, y1, y2, y3, y4]; zeros(2pts - 8)]
        A = [[2, pts]; [real.(P); imag.(P)]]
        Dict("name" => s, "R" => flatv(Float64.(R)), "A" => flatv(Float64.(A)))
    end for s in ("2412", "0012")]
save("mesh", Dict("meta" => meta, "mesh" => md))

# ------------------------------------------------------------------------------------------
# Sphere subdivision (the icosahedron faces, then two levels)
# ------------------------------------------------------------------------------------------
ico_faces = [(1, 2, 3)]  # placeholder, replaced by the convex hull faces below
let V = F.icosahedron(1.0)
    pts = [Grassmann.value(v)[2:4] for v in V]
    faces = Tuple{Int,Int,Int}[]
    for i in 1:12, j in i+1:12, k in j+1:12
        a, b, c = pts[i], pts[j], pts[k]
        n = cross(b - a, c - a)
        d = dot(n, a)
        s = [dot(n, q) - d for q in pts]
        if all(x -> x ≤ 1e-9, s) || all(x -> x ≥ -1e-9, s)
            # orient outward
            push!(faces, dot(n, a) > 0 ? (i, j, k) : (i, k, j))
        end
    end
    global ico_faces = faces
end
sph = Dict{String,Any}("faces" => [collect(f) for f in ico_faces])
for r in (1.0, 2.0)
    P = Cartan.PointCloud(F.sphere(r))
    fac = P(SimplexTopology([Values(f...) for f in ico_faces], 12))
    s1 = F.sphere(fac, r)
    # `sphere` appends to the shared point vector in place: snapshot level 1 before level 2
    l1 = flatv(collect(Cartan.fullpoints(s1)))
    s2 = F.sphere(s1, r)
    sph["r=$(r)"] = Dict("level1_points" => l1,
        "level1_faces" => [ints(t) for t in Cartan.topology(s1)],
        "level2_points" => flatv(collect(Cartan.fullpoints(s2))), "level2_faces" => [ints(t) for t in Cartan.topology(s2)])
end
save("sphere", Dict("meta" => meta, "sphere" => sph))

# ------------------------------------------------------------------------------------------
# Wing surfaces
# ------------------------------------------------------------------------------------------
wl = Any[]
for (name, N, λ, σ) in (("American(NACA4{24,9},ClarkY{12,9})", American(NACA4{24,9}(), ClarkY{12,9}()), 0.7, 0.5),
        ("American(NACA4{24,9},ClarkY{12,9}) λ=0.4 σ=0.2", American(NACA4{24,9}(), ClarkY{12,9}()), 0.4, 0.2),
        ("American(NACA4{44,21},Modified{12,64,21})", American(NACA4{44,21}(), Modified{12,64,21}()), 0.7, 0.5))
    w = F.wing(N, λ, σ)
    push!(wl, Dict("name" => name, "lambda" => hx(λ), "sigma" => hx(σ), "size" => collect(size(fib(w))),
        "fiber" => flatv(vec(fib(w))), "base" => repr(Cartan.points(w))))
end
w = F.wing(nacaparse("6511"))
push!(wl, Dict("name" => "6511", "lambda" => hx(0.7), "sigma" => hx(0.5), "size" => collect(size(fib(w))),
    "checksum" => hx(sum(x -> sum(Grassmann.value(x)), fib(w))), "corner" => flatv([fib(w)[1, 1], fib(w)[end, end], fib(w)[75, 150]]),
    "base" => repr(Cartan.points(w))))
save("wing", Dict("meta" => meta, "wings" => wl))

# Show strings of homogeneous points (Grassmann's printer)
save("show", Dict("meta" => meta, "points" => [string(x) for x in F.points(ClarkY{12,5}())],
    "airfoil" => [string(x) for x in F.points(American(NACA4{24,5}(), ClarkY{12,5}()))]))

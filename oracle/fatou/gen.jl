# Oracle generator for Fatou.jl (port-notes/fatou.md §9).
#
#   julia --startup-file=no --project=<env with Fatou 1.2.4 + JSON> oracle/fatou/gen.jl
#
# Writes oracle/golden/fatou/:
#   complex.json      Julia ComplexF64 primitives on random/special operands (hex bits)
#   grids.json        Rectangle sizes and the exact grid axes x' .+ im*y
#   points.json       the per-pixel kernel Fatou.orbit(K, z0) for a catalog of maps
#   sets.json         metadata, titles and statistics of every raster below
#   <name>.iter.u16 / .mix.f64 / .zre.f64 / .zim.f64
#                     reduced-resolution rasters, raw little-endian, row-major, row 1 = top
#   orbits.json       real_orb cobweb data and orbit-plot strings
#   schemes.json      ColorSchemes stops and the (C::ColorScheme)(K) functor output
#
# README examples are dumped at reduced resolution; their full-resolution iteration
# histograms and FNV-1a hashes go into sets.json so the Lean tests can recompute them.
# `Compute` prints `@time` lines on stdout; they are harmless.

using Fatou, JSON, Random
const CS = Fatou.ColorSchemes

const OUT = joinpath(@__DIR__, "..", "golden", "fatou")
mkpath(OUT)
Random.seed!(0xFA70)

hex(x::Float64) = string(reinterpret(UInt64, x), base = 16, pad = 16)
hexs(v) = [hex(Float64(x)) for x in v]
hexc(z) = [hex(real(z)), hex(imag(z))]
rowmajor(M) = vec(permutedims(M))
function fnv1a(bytes::AbstractVector{UInt8})
    h = 0xcbf29ce484222325
    for b in bytes
        h = (h ⊻ b) * 0x100000001b3
    end
    string(h, base = 16, pad = 16)
end
fnvf(v) = fnv1a(reinterpret(UInt8, htol.(collect(Float64, v))))
fnvu16(M) = fnv1a(reinterpret(UInt8, htol.(rowmajor(M))))
writejson(name, x) = open(io -> JSON.print(io, x), joinpath(OUT, name), "w")

# ---------------------------------------------------------------- complex primitives
function randmag()
    r = rand()
    r < 0.05 ? 0.0 : r < 0.1 ? -0.0 : r < 0.8 ? (rand() - 0.5) * 8 :
        (rand(Bool) ? 1 : -1) * 10.0^(rand() * 40 - 20)
end
specials = [0.0, -0.0, 1.0, -1.0, 0.5, 2.0, 1e-300, 1e300, 3.0e-320, Inf, -Inf, NaN]
zs = ComplexF64[]
for _ in 1:600
    push!(zs, complex(randmag(), randmag()))
end
for a in specials, b in specials
    push!(zs, complex(a, b))
end
lp(z, ::Val{k}) where {k} = Base.literal_pow(^, z, Val(k))
cases = Any[]
for i in eachindex(zs)
    z = zs[i]
    w = zs[mod1(i * 7 + 3, length(zs))]
    x = real(zs[mod1(i * 13 + 5, length(zs))])
    push!(cases, Dict(
        "z" => hexc(z), "w" => hexc(w), "x" => hex(x),
        "mul" => hexc(z * w), "div" => hexc(z / w), "inv" => hexc(inv(z)),
        "add" => hexc(z + w), "sub" => hexc(z - w),
        "addx" => hexc(z + x), "subx" => hexc(z - x), "xsub" => hexc(x - z),
        "mulx" => hexc(x * z), "divx" => hexc(z / x), "xdiv" => hexc(x / z),
        "abs" => hex(abs(z)), "abs2" => hex(abs2(z)), "angle" => hex(angle(z)),
        "exp" => hexc(exp(z)), "sin" => hexc(sin(z)), "cos" => hexc(cos(z)),
        "sinh" => hexc(sinh(z)), "cosh" => hexc(cosh(z)),
        "log" => hexc(log(z)), "sqrt" => hexc(sqrt(z)),
        "plane" => hexc(Fatou.plane(z)), "disk" => hexc(Fatou.disk(z)),
        "lit" => [hexc(lp(z, Val(k))) for k in -3:12],
        "pow" => [hexc(z^k) for k in -3:12],
    ))
end
writejson("complex.json", Dict("litpow_range" => [-3, 12], "cases" => cases))
println("complex.json: ", length(cases), " cases")

# ---------------------------------------------------------------- grids
function gridcase(∂, n)
    R = Fatou.Rectangle(∂, n)
    rows, cols = Int.(size(R))
    G = Fatou.fatou(R).Ω
    gx = real.(G[1, :]); gy = imag.(G[:, 1])
    # the grid is separable: check it before recording only the axes
    @assert all(real.(G) .=== repeat(gx', rows, 1))
    @assert all(imag.(G) .=== repeat(gy, 1, cols))
    d = Dict("bounds" => hexs(R.∂), "n" => n, "rows" => rows, "cols" => cols,
             "fnvx" => fnvf(gx), "fnvy" => fnvf(gy))
    if rows * cols ≤ 64 * 64
        d["gx"] = hexs(gx); d["gy"] = hexs(gy)
    end
    d
end
grids = Any[]
for (∂, n) in [(π / 2, 176), ([-1.5, 1.5, -1, 1], 1501), ([-1.91, 0.51, -1.21, 1.21], 800),
               (π / 2, 800), ([-2π / 3, -π / 3, -π / 6, π / 6], 500), ([-1.25, 1.5], 147),
               ([-2.0, 0.5, -1.25, 1.25], 1000), ([-1.5, 1.5, -1, 1], 151), ([-2, 2], 41),
               ([-2π / 3, 0, -π / 3, π / 3], 1501), (2π, 800), ([0.5, 2], 500),
               ([-0.5, 0.5, -1, 0], 800), (π / 2.4, 800)]
    push!(grids, gridcase(∂, n))
end
decimal() = round((rand() - 0.5) * 8, digits = rand(1:4))
for _ in 1:250
    kind = rand(1:4)
    a, b, c, d = kind == 1 ? (decimal(), decimal(), decimal(), decimal()) :
                 kind == 2 ? Tuple(rand(-7:7, 4) .* π ./ rand(1:8, 4)) :
                 kind == 3 ? Tuple((rand(4) .- 0.5) .* 10) :
                 (0.0, rand(1:5) * 1.0, -rand() * 3, rand() * 3)
    a == b && (b = a + 1); c == d && (d = c + 1)
    a > b && ((a, b) = (b, a)); c > d && ((c, d) = (d, c))
    n = rand([2, 3, 5, 10, 17, 41, 64, 100, 176, 257])
    rows = round((d - c) / (b - a) * n)
    (2 ≤ rows ≤ 4000) || continue
    push!(grids, gridcase([a, b, c, d], n))
end
# ties in the row count (rounded half to even)
for (∂, n) in [([0.0, 2, 0, 1], 5), ([0.0, 2, 0, 1], 7), ([0.0, 4, 0, 1], 10), ([0.0, 4, 0, 1], 6),
               ([0.0, 2, 0, 1], 9), ([0.0, 1, 0, 2.5], 3)]
    push!(grids, gridcase(∂, n))
end
writejson("grids.json", Dict("cases" => grids))
println("grids.json: ", length(grids), " cases")

# ---------------------------------------------------------------- the catalog
const c₀ = -0.06 + 0.67im
# name => (n -> Define, tier, reduced n, full-resolution n or 0)
catalog = [
    "readme_filled_julia" => (n -> juliafill(:(z^2 + $c₀), ∂ = [-1.5, 1.5, -1, 1], N = 80, n = n,
                                             cmap = "gnuplot", iter = true), "exact", 151, 1501),
    "readme_mandelbrot" => (n -> mandelbrot(:(z^2 + c), n = n, N = 20, ∂ = [-1.91, 0.51, -1.21, 1.21],
                                            cmap = "gist_earth"), "exact", 100, 800),
    "readme_newton" => (n -> newton(:(z^3 - 1), n = n, ϵ = 0.1, N = 25, iter = true, cmap = "jet"),
                        "exact", 100, 800),
    "readme_gen_newton" => (n -> newton(:(sin(z) - 1), m = 1 - 1im, ∂ = [-2π / 3, -π / 3, -π / 6, π / 6],
                                        n = n, N = 33, iter = true, ϵ = 0.05, cmap = "cubehelix"),
                            "transcendental", 100, 500),
    "default_newton" => (n -> newton(:(z^3 - 1), n = n), "exact", 41, 176),
    "default_mandelbrot" => (n -> mandelbrot(:(z^2 + c), n = n), "exact", 41, 176),
    "default_juliafill" => (n -> juliafill(:(z^2 - 0.06 + 0.67im), n = n), "exact", 41, 176),
    "plane_juliafill" => (n -> juliafill(:(z^2 - 0.06 + 0.67im), n = n, plane = true), "exact", 41, 0),
    "disk_juliafill" => (n -> juliafill(:(z^2 - 0.06 + 0.67im), n = n, disk = true), "exact", 41, 0),
    "p_juliafill" => (n -> juliafill(:(z^2 - 0.06 + 0.67im), n = n, p = 0.3), "transcendental", 41, 0),
    "cubic_mandelbrot" => (n -> mandelbrot(:(z^3 + c), n = n, N = 30, ∂ = [-1.5, 1.5]), "exact", 41, 0),
    "seed_mandelbrot" => (n -> mandelbrot(:(z^2 + c), n = n, N = 25, seed = 0.1 + 0.1im,
                                          ∂ = [-2, 1, -1.5, 1.5]), "exact", 41, 0),
    "basilica_iter" => (n -> juliafill(:(z^2 - 1), ∂ = [-2, 2], iter = true, n = n), "exact", 41, 0),
    "affine_juliafill" => (n -> juliafill(:(3z + 2), ∂ = [-π, π], n = n), "exact", 41, 0),
    "newton_m2" => (n -> newton(:(z^3 - 1), m = 2, n = n, N = 37, ϵ = 0.27, iter = true), "exact", 41, 0),
    "newton_mhalf" => (n -> newton(:(z^3 - 1), m = -0.5, n = n, N = 10), "exact", 41, 0),
    "newton_cubic5" => (n -> newton(:(z^3 - 2z - 5), n = n), "exact", 41, 0),
    "newton_zim" => (n -> newton(:(z^2 - im), m = -0.5 + 2im, n = n, N = 10), "exact", 41, 0),
    "newton_octic" => (n -> newton(:(z^8 - 15z^4 - 16), m = 1.5, ∂ = [-2π / 3, 0, -π / 3, π / 3], n = n,
                                   N = 17), "exact", 41, 0),
    "cos_juliafill" => (n -> juliafill(:(cos(z)), ∂ = [0.5, 2], n = n), "transcendental", 41, 0),
    "newton_exp" => (n -> newton(:(exp(z) + 1), ∂ = 2π, n = n, N = 27, iter = true), "transcendental", 41, 0),
]
defineof(name) = (e = first(v for (k, v) in catalog if k == name); e[1](e[3]))

latexE(K) = Fatou.rdpm(Fatou.Algebra.latex(K.E))
function pytitle(S)
    K = S.meta
    text, t = "f:z\\mapsto $(latexE(K)),\\,", Fatou.LaTeXString(Fatou.typeplot(S))
    K.newt ? String(Fatou.latexstring("$text m = $(K.m), ") * t) : String(Fatou.latexstring(text) * t)
end
const YLABEL = String(Fatou.L"Fatou\,set:\," * Fatou.L"z\,↦\,z-m\,×\,f(z)\,/\,f\,'(z)")

function stats(S)
    it = S.iter
    N = Int(S.meta.N)
    hist = [count(==(k), it) for k in 0:N]
    mix = S.mix
    ok = filter(!isnan, mix)
    Dict("rows" => size(it, 1), "cols" => size(it, 2), "sum" => sum(Int, it), "max" => Int(maximum(it)),
         "hist" => hist, "fnv" => fnvu16(it), "mixnan" => count(isnan, mix),
         "mixmin" => hex(minimum(ok)), "mixmax" => hex(maximum(ok)), "mixsum" => hex(sum(ok)))
end

function writeraster(name, S)
    write(joinpath(OUT, "$name.iter.u16"), htol.(rowmajor(S.iter)))
    write(joinpath(OUT, "$name.mix.f64"), htol.(rowmajor(S.mix)))
    write(joinpath(OUT, "$name.zre.f64"), htol.(rowmajor(real.(S.set.Ω))))
    write(joinpath(OUT, "$name.zim.f64"), htol.(rowmajor(imag.(S.set.Ω))))
end

function meta(name, K, S, tier)
    Dict("name" => name, "tier" => tier, "E" => string(K.E),
         "F" => K.newt ? string(Fatou.newton_raphson(K.E, K.m)) : string(K.E),
         "latex" => latexE(K), "bounds" => hexs(K.Ω.∂), "n" => Int(K.Ω.n),
         "rows" => size(S.iter, 1), "cols" => size(S.iter, 2), "N" => Int(K.N), "eps" => hex(K.ϵ),
         "iter" => K.iter, "p" => hex(K.p), "newt" => K.newt, "m" => string(K.m),
         "mandel" => K.mandel, "seed" => hexc(K.seed), "plane" => K.plane, "disk" => K.disk,
         "cmap" => K.cmap, "title" => String(S), "typeplot" => Fatou.typeplot(S),
         "pytitle" => pytitle(S), "ylabel" => K.newt ? YLABEL : "",
         "basin0" => String(basin(K, 0)), "basin1" => String(basin(K, 1)),
         "basin1body" => K.newt ? Fatou.nL(K.E, K.m, 1) : Fatou.jL(K.E, 1),
         "stats" => stats(S))
end

sets = Any[]
for (name, (mk, tier, n, full)) in catalog
    K = mk(n)
    S = fatou(K)
    writeraster(name, S)
    d = meta(name, K, S, tier)
    if full > 0
        d["full"] = stats(fatou(mk(full)))
    end
    push!(sets, d)
    println("set ", name, " ", size(S.iter))
end

# chaining: fatou(K2, fatou(K1)) continues from K1's final iterates
K1 = juliafill(:(z^2 - 0.06 + 0.67im), n = 41, N = 5)
K2 = mandelbrot(:(z^2 + c), n = 41, N = 10)
S12 = fatou(K2, fatou(K1))
writeraster("chain", S12)
d = meta("chain", K2, S12, "exact"); d["bounds_used"] = hexs(Fatou.bounds(S12))
push!(sets, d)
# re-running a set from its own final iterates: fatou(fatou(K))
S11 = fatou(fatou(K1))
writeraster("refatou", S11)
d = meta("refatou", K1, S11, "exact")
push!(sets, d)
writejson("sets.json", Dict("sets" => sets))

# ---------------------------------------------------------------- per-pixel kernel
points = Any[]
for (name, (mk, tier, n, _)) in catalog
    K = mk(n)
    ∂ = K.Ω.∂
    z0s = ComplexF64[complex(∂[1] + rand() * (∂[2] - ∂[1]), ∂[3] + rand() * (∂[4] - ∂[3])) for _ in 1:150]
    append!(z0s, ComplexF64[0, -2, 1, -1, 0.25, 1im, -1im, 2.1, 0.3 + 0.7im, -0.75 + 0.1im, 1 + 1im])
    res = Any[]
    for z0 in z0s
        n, z = Fatou.orbit(K, z0)
        push!(res, Dict("z0" => hexc(z0), "n" => Int(n), "z" => hexc(z),
                        "mix" => hex(K.C(z, float(n / K.N), K.p))))
    end
    push!(points, Dict("name" => name, "tier" => tier, "points" => res))
end
writejson("points.json", Dict("maps" => points))
println("points.json written")

# ---------------------------------------------------------------- orbits
function orbitcase(name, K, tier; latex = nothing)
    bi = K.x0 === nothing ? Matrix(K.Ω.∂[1:2]') : Matrix([K.Ω.∂[1:2]..., K.x0]')
    f = z -> K.F(z, 0)
    x, N, N2, orb, bis = Fatou.real_orb(K.E, f, convert(Array{Float64}, bi), K.orbit, K.depth, Int(K.Ω.n))
    d = 1.07
    ylim = (minimum([d * minimum(N[:, 2]), 0]), maximum([d * maximum(N[:, 2]), 0]))
    fune = latex === nothing ? latexE(K) : latex  # REDUCE hangs on `%`
    funt = K.orbit ≠ 0 ? ", IC: \$ x_0 = $(bis[3])\$, \$ n\\in0:$(K.orbit)\$" : ""
    legend = vcat([Fatou.L"$y=x$", Fatou.L"$\phi(x)$", Fatou.L"(x_n,\phi(x_n))"],
                  [Fatou.latexstring("\\phi^{$x}(x)") for x ∈ 2:K.depth],
                  K.orbit ≠ 0 ? [Fatou.latexstring("\\phi(x_{0:$(K.orbit)})")] : [])
    Dict("name" => name, "tier" => tier, "E" => string(K.E), "latex" => fune,
         "a" => hex(bi[1]), "b" => hex(bi[2]), "x0" => K.x0 === nothing ? nothing : hex(Float64(K.x0)),
         "orbit" => K.orbit, "depth" => K.depth, "incr" => Int(K.Ω.n),
         "x" => hexs(x), "comps" => [hexs(N[:, t]) for t in 1:size(N, 2)], "N2" => hexs(N2),
         "cobx" => hexs(orb[:, 1]), "coby" => hexs(orb[:, 2]), "bis" => hexs(bis),
         "ylim" => hexs(ylim), "tseries" => K.orbit ≠ 0 ? hexs(range(bi[1], stop = bi[2], length = length(N2))) : String[],
         "unicode_title" => "z ↦ $(K.E)" * (K.orbit ≠ 0 ? ", IC: z₀ = $(bis[3]), n∈0:$(K.orbit)" : ""),
         "latex_title" => String(Fatou.latexstring("\$ x \\mapsto $fune\$$funt")),
         "latex_legend" => String.(legend))
end
orbits = [
    orbitcase("readme_orbit", juliafill(:(z^2 - 0.67), ∂ = [-1.25, 1.5], x0 = 1.25, orbit = 17, depth = 3,
                                        n = 147), "exact"),
    orbitcase("noorbit", juliafill(:(z^2 - 0.67), ∂ = [-1.25, 1.5]), "exact"),
    orbitcase("newton_orbit", newton(:(z^3 - 1), ∂ = [0.4, 2.5], x0 = 2.1, orbit = 4, depth = 2, n = 42),
              "exact"),
    orbitcase("basilica_orbit", juliafill(:(z^2 - 1), ∂ = [-2, 2], x0 = 0, orbit = 10, depth = 5), "exact"),
    orbitcase("quadratic_orbit", juliafill(:((-3 / 2) * z^2 + 5z / 2 + 1), ∂ = [-0.7, 2.5], x0 = 0.001,
                                           orbit = 37, depth = 3), "exact"),
    orbitcase("doubling_orbit", juliafill(:(2z % 1), ∂ = [0, 1], x0 = 0.3, orbit = 70, depth = 3), "exact",
              latex = "2 z \\bmod 1"),
    orbitcase("hump_orbit", juliafill(:(z * exp(1.5 * (1 - z^2 / 50))), ∂ = [0, 15], x0 = 1, orbit = 24),
              "transcendental"),
    orbitcase("cos_orbit", juliafill(:(cos(z)), ∂ = [0, 2], x0 = 1.7, orbit = 17, depth = 3), "transcendental"),
]
writejson("orbits.json", Dict("orbits" => orbits))
println("orbits.json written")

# ---------------------------------------------------------------- ColorSchemes
schemes = Dict{String,Any}()
for s in ["jet", "balance", "gnuplot", "cubehelix", "RdGy"]
    C = getproperty(CS, Symbol(s))
    schemes[s] = [hex(Float64(getfield(c, f))) for c in C.colors for f in (:r, :g, :b)]
end
functor = Any[]
for (name, s) in [("readme_newton", "jet"), ("default_juliafill", "balance"),
                  ("readme_mandelbrot", "gnuplot"), ("newton_m2", "RdGy"), ("readme_gen_newton", "cubehelix")]
    S = fatou(defineof(name))
    H = getproperty(CS, Symbol(s))(S)
    vals = [Float64(getfield(c, f)) for c in rowmajor(H) for f in (:r, :g, :b)]
    push!(functor, Dict("set" => name, "scheme" => s, "fnv" => fnvf(vals), "rgb" => hexs(vals[1:min(end, 600)])))
end
writejson("schemes.json", Dict("schemes" => schemes, "functor" => functor))
println("schemes.json written")

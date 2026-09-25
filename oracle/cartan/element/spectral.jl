# Goldens for Cartan's spectral tools (Cartan.jl src/spectral.jl, ext/FFTWExt.jl,
# ext/ToeplitzMatricesExt.jl): frequency axes, wavenumbers, periodic calculus, Toeplitz
# matrices, Chebyshev collocation, Clenshaw–Curtis, Lagrange/sinc resampling, Fourier series,
# Laplace transforms.
#
#   julia --startup-file=no --project=<oracle env + FFTW + ToeplitzMatrices> oracle/cartan/element/spectral.jl
#
# Writes oracle/golden/cartan/element/spectral.json.
include(joinpath(@__DIR__, "common.jl"))
using Grassmann, Cartan, FFTW, ToeplitzMatrices, LinearAlgebra

out = Dict{String,Any}("meta" => Dict("julia" => string(VERSION), "cartan" => string(pkgversion(Cartan))))
C = Cartan

# 1. frequency axes and wavenumbers
out["fftspaceN"] = Dict(string(N) => hxs(C.fftspace(N)) for N in 1:12)
out["rfftspaceN"] = Dict(string(N) => hxs(C.rfftspace(N)) for N in 1:12)
out["r2rspaceNk"] = Dict("$(N),$(k)" => hxs(C.r2rspace(N, k, 1)) for N in 2:9 for k in (5, 6, 9, 10))
let rs = Dict("0:0.5:3.5" => 0:0.5:3.5, "range(-pi,pi,9)" => range(-π, π, length = 9), "0.3:0.2:7.1" => 0.3:0.2:7.1)
    out["axes"] = Dict(k => Dict("fft" => hxs(C.fftspace(r).f), "rfft" => hxs(C.rfftspace(r).f),
        "r2r" => hxs(C.r2rspace(r).f), "r2r9" => hxs(C.r2rspace(r, 9).f), "r2r5" => hxs(C.r2rspace(r, 5).f))
        for (k, r) in rs)
end
out["fftwavenumber"] = Dict(string(N) => collect(C.fftwavenumber(N)) for N in 1:10)
out["rfftwavenumber"] = Dict(string(N) => collect(C.rfftwavenumber(N)) for N in 1:10)

# 2. Toeplitz and impulses
out["toeplitz1"] = hxs(C.toeplitz1(8)); out["toeplitz2"] = hxs(C.toeplitz2(8))
out["toeplitz1_7"] = hxs(C.toeplitz1(7))
out["derivetoeplitz4"] = hxs(Matrix(derivetoeplitz(4)))
out["spectral_sum_impulse"] = hxs(C.spectral_sum_impulse(8))

# 3. periodic calculus on the N = 8 grid 0:2π/8:7·2π/8 and an odd grid
let x = 0:2π/8:7*2π/8, t = TensorField(x)
    s = sin(t)
    f = fft(s)
    out["grid8"] = Dict("x" => hxs(x), "sin" => hxs(fiber(s)), "fft" => hxc(fiber(f)), "fftaxis" => hxs(points(f)),
        "dct" => hxs(fiber(dct(s))), "dctaxis" => hxs(points(dct(s))),
        "dst" => hxs(fiber(C.dst(s))), "dstaxis" => hxs(points(C.dst(s))),
        "idst" => hxs(fiber(C.idst(C.dst(s)))),
        "rfft" => hxc(fiber(rfft(s))), "irfft" => hxs(fiber(irfft(rfft(s)))),
        "gradient_impulse" => hxs(fiber(C.gradient_impulse(t))),
        "convolve" => hxs(fiber(C.convolve(s, s))),
        "integral_fft" => hxs(fiber(C.integral_fft(cos(t) + 1))),
        "integral_rfft" => hxs(fiber(C.integral_rfft(cos(t) + 1))),
        "integrate_fft" => hx(C.integrate_fft(cos(t) + 1)),
        "gradient_fft" => hxs(fiber(C.gradient_fft(sin(3t)))),
        "gradient_rfft" => hxs(fiber(C.gradient_rfft(sin(3t)))),
        "flt" => hxc(fiber(C.flt(s, 0.5))), "iflt" => hxc(fiber(C.iflt(C.flt(s, 0.5), 0.5))))
end
let x = 0:2π/7:6*2π/7, t = TensorField(x)
    out["grid7"] = Dict("gradient_fft_sin3" => hxs(fiber(C.gradient_fft(sin(3t)))),
        "gradient_fft_sin1" => hxs(fiber(C.gradient_fft(sin(t)))))
end

# 4. Chebyshev
out["chebyshev5"] = hxs(C.points(C.Chebyshev(5)))
out["chebyshev_range"] = hxs(C.points(C.Chebyshev(0:0.5:2)))
out["unitpoints"] = hxs(C.unitpoints(C.Chebyshev(0:0.5:2)))
out["chebmatrix"] = Dict(string(N) => hxs(C.ChebyshevMatrix(N)) for N in 2:9)
out["chebvector"] = Dict(string(N) => hxs(C.ChebyshevVector(N)) for N in 3:9)
out["chebfft9"] = hxc(C.chebyshevfft(collect(C.points(C.Chebyshev(9))) .^ 3))
let xs = collect(C.points(C.Chebyshev(9)))
    out["gradcheb9"] = Dict("x3" => hxs(fiber(C.gradient_chebyshevfft(TensorField(xs, xs .^ 3)))),
        "x5" => hxs(fiber(C.gradient_chebyshevfft(TensorField(xs, xs .^ 5 .- 2xs)))))
end
out["clenshawcurtis"] = Dict(string(n) => hxs(C.clenshawcurtis(n)) for n in 3:12)

# 5. Lagrange and sinc resampling
let x = 0:0.25:1, t = TensorField(x, x .^ 3 .- x)
    out["lagrange"] = Dict("w" => hxs(C.lagrangeweights(collect(x))),
        "at" => hxs([C.lagrangepolynomial(t, q) for q in (0.3, 0.5, -0.1, 1.2, 0.25)]),
        "resample9" => hxs(fiber(C.resample_lagrange(t, 9))),
        "roots03" => hx(C.rootspolynomial(collect(x), 0.3)),
        "sinc9" => hxs(fiber(C.resample_sinc(t, 9))))
    y = randfloats(7, UInt64(0x1a9), -1.0, 1.0)
    xr = sort(randfloats(7, UInt64(0x1aa), 0.0, 2.0))
    out["lagrange_rand"] = Dict("x" => hxs(xr), "y" => hxs(y), "w" => hxs(C.lagrangeweights(xr)),
        "at" => hxs([C.lagrangepolynomial(C.LagrangeWeights(xr), y, q) for q in (0.1, 0.77, 1.5, 2.1)]))
end

# 6. Fourier series
let x = 0:π/64:π, t = TensorField(x)
    g = cos(2t) + 0.5
    c = C.FourierCosine(g, 5)
    out["series"] = Dict("cos" => hxs(fiber(c)), "sin" => hxs(fiber(C.FourierSine(sin(3t), 5))),
        "cos2" => hxs(fiber(C.FourierCosine(2, TensorField(0:0.25:1)))))
end

save("spectral", out)

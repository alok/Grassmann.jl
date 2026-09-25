# Goldens for Cartan.Spectral.FFT against FFTW (fft, bfft, ifft, rfft, irfft, brfft, the r2r
# kinds, dct/idct), for lengths covering radix 2, mixed radix and Bluestein.
#
#   julia --startup-file=no --project=<oracle env + FFTW> oracle/cartan/element/fft.jl
#
# FFTW is not in oracle/Project.toml (Cartan's FFTWExt is a weak dependency); run this in a copy
# of the oracle environment with FFTW added. Writes oracle/golden/cartan/element/fft.json.
include(joinpath(@__DIR__, "common.jl"))
using FFTW

Ns = [1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 15, 16, 17, 31, 32, 33, 64, 100, 127, 128, 243]
cases = Dict{String,Any}[]
for N in Ns
    x = randfloats(N, UInt64(0xf0f0 + N), -1.0, 1.0)
    y = randfloats(N, UInt64(0x0f0f + N), -1.0, 1.0)
    z = complex.(x, y)
    c = Dict{String,Any}("N" => N, "x" => hxs(x), "y" => hxs(y),
        "fft" => hxc(fft(z)), "bfft" => hxc(bfft(z)), "ifft" => hxc(ifft(z)),
        "rfft" => hxc(rfft(x)), "irfft" => hxs(irfft(rfft(x), N)), "brfft" => hxs(brfft(rfft(y), N)),
        "dct" => hxs(dct(x)), "idct" => hxs(idct(x)))
    r2rs = Dict{String,Any}()
    for k in 0:10
        (k == 3 && N < 2) && continue
        r2rs[string(k)] = @safe hxs(FFTW.r2r(x, k))
    end
    c["r2r"] = r2rs
    push!(cases, c)
end
save("fft", Dict("meta" => Dict("julia" => string(VERSION), "fftw" => string(pkgversion(FFTW))),
    "cases" => cases))

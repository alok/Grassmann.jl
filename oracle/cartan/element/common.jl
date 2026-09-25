# Shared helpers of the Cartan element/spectral/solver/operator golden generators
# (oracle/cartan/element/*.jl). Floats are IEEE bit patterns ("0x…"); a Julia exception is
# {"E": "<Type>: …"}; arrays are column-major; indices are 1-based as in Julia.
using JSON

const OUT = joinpath(@__DIR__, "..", "..", "golden", "cartan", "element")
mkpath(OUT)
save(name, data) = (open(io -> JSON.print(io, data), joinpath(OUT, name * ".json"), "w");
    println("wrote ", name, " (", filesize(joinpath(OUT, name * ".json")), " bytes)"))

hx(x::Real) = "0x" * string(reinterpret(UInt64, Float64(x)), base = 16, pad = 16)
hxs(xs) = [hx(x) for x in vec(collect(xs))]
hxc(xs) = reduce(vcat, [[hx(real(z)), hx(imag(z))] for z in vec(collect(xs))]; init = String[])
errstr(e) = (s = sprint(showerror, e); string(nameof(typeof(e)), ": ", first(s, 160)))
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

"`n` floats uniform in `[lo, hi)` from SplitMix64 seeded with `seed` (the Lean
`Tests.Util.Random`/`Bench.randFloats` sequence)."
function splitmix64(s::UInt64)
    s += 0x9e3779b97f4a7c15
    z = s
    z = (z ⊻ (z >> 30)) * 0xbf58476d1ce4e5b9
    z = (z ⊻ (z >> 27)) * 0x94d049bb133111eb
    (z ⊻ (z >> 31), s)
end
function randfloats(n::Integer, seed::UInt64, lo::Float64 = 0.0, hi::Float64 = 1.0)
    out = Vector{Float64}(undef, n)
    s = seed
    for i in 1:n
        z, s = splitmix64(s)
        out[i] = lo + (hi - lo) * (Float64(z >> 11) * 0x1.0p-53)
    end
    out
end

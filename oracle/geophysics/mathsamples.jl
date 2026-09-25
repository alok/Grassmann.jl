# Large sweep of Julia's own elementary functions, to validate `JuliaBase.F64` (`JuliaBase.Trig`, `JuliaBase.Math`) bit for bit.
#
#   julia --startup-file=no oracle/geophysics/mathsamples.jl /tmp/geo_math.txt
#   lake env lean --run oracle/geophysics/MathSweep.lean /tmp/geo_math.txt
#
# One line per sample: `<fn> <x bits> [<y bits>] <result bits…>` (decimal UInt64). The committed
# regression sample is `oracle/golden/geophysics/math.json` (written by gen.jl); this sweep is not
# committed. Last run (Julia 1.13.0, aarch64): 1.4M values, 0 mismatches.
using Random
Random.seed!(20260924)
const N = 100_000
out = length(ARGS) ≥ 1 ? ARGS[1] : "geo_math.txt"
b(x) = reinterpret(UInt64, Float64(x))
open(out, "w") do io
    for _ in 1:N
        x = rand() * 100 - 50
        println(io, "exp ", b(x), " ", b(exp(x)))
    end
    for _ in 1:N
        x = rand() * 4; y = rand() * 120 - 60
        println(io, "pow ", b(x), " ", b(y), " ", b(x^y))
    end
    for _ in 1:N
        x = exp(rand() * 20 - 10); y = rand() * 4 - 2
        println(io, "pow ", b(x), " ", b(y), " ", b(x^y))
    end
    for _ in 1:N
        x = rand() * 4; n = Float64(rand(-60:60))
        println(io, "pow ", b(x), " ", b(n), " ", b(x^n))
    end
    for _ in 1:N
        x = rand() * 20 - 10
        println(io, "trig ", b(x), " ", b(sin(x)), " ", b(cos(x)), " ", b(tan(x)))
    end
    for _ in 1:N
        x = (rand() < 0.5 ? -1 : 1) * exp(rand() * 80 - 20)   # up to e^60: Payne-Hanek reduction
        println(io, "trig ", b(x), " ", b(sin(x)), " ", b(cos(x)), " ", b(tan(x)))
    end
    for _ in 1:N
        x = (rand() < 0.5 ? -1 : 1) * exp(rand() * 60 - 30)
        println(io, "atan ", b(x), " ", b(atan(x)))
    end
    for _ in 1:N
        x = rand() * 2 - 1
        println(io, "arc ", b(x), " ", b(asin(x)), " ", b(atanh(x)), " ", b(log1p(x)))
    end
end

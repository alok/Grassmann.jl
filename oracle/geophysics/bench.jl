# Julia side of Tests/Geophysics/Bench.lean: ns per evaluation on the same grids.
#   julia --startup-file=no --project=oracle oracle/geophysics/bench.jl [path/to/Geophysics.jl]
using UnitSystems, StaticVectors
const SRC = length(ARGS) ≥ 1 ? ARGS[1] : joinpath(homedir(), "chakravala", "Geophysics.jl")
include(joinpath(SRC, "src", "Geophysics.jl"))
using .Geophysics
const G = Geophysics

function loop(f, W, hs)
    s = 0.0
    for h in hs
        s += f(h, W)
    end
    s
end
function loopP(P, xs)
    s = 0.0
    for x in xs
        s += gravity(x, P)
    end
    s
end
hs = [-2000.0 + i * 0.8 for i in 0:999_999]
for f in (G.temperature, G.pressure, G.density, G.sonicspeed, G.viscosity, G.kinematic)
    loop(f, Earth1959, hs[1:10])
    t = @elapsed s = loop(f, Earth1959, hs)
    println("  ", f, ": ", t * 1e3, " ns/eval (checksum ", s, ")")
end
xs = [i * 1.5e-6 for i in 0:999_999]
loopP(Earth, xs[1:10])
t = @elapsed s = loopP(Earth, xs)
println("  gravity(ϕ, Earth): ", t * 1e3, " ns/eval (checksum ", s, ")")

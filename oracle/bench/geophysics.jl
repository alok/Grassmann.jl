# Julia twin of Bench/Geophysics.lean (`geophysics` suite). Geophysics.jl is included from its
# source (`$CHAKRAVALA/Geophysics.jl`, default ~/chakravala), as in oracle/geophysics/gen.jl.
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "harness.jl"))
using .BenchHarness
using UnitSystems, StaticVectors
if !isdefined(Main, :Geophysics)
    include(joinpath(get(ENV, "CHAKRAVALA", joinpath(homedir(), "chakravala")), "Geophysics.jl", "src", "Geophysics.jl"))
end
using .Geophysics

function geo_loop(f::F, W, hs::Vector{Float64}) where {F}
    s = 0.0
    for h in hs
        s += f(h, W)
    end
    s
end
function geo_loopf(f::F, xs::Vector{Float64}) where {F}
    s = 0.0
    for x in xs
        s += f(x)
    end
    s
end
geo_pow(x) = x^-5.25
geo_gravity(ϕ) = Geophysics.gravity(ϕ, Geophysics.Earth)

function suite_geophysics(ctx)
    n = sized(ctx, 100000, 1000)
    p = "n=$n"
    G = Geophysics
    hs = [-2000.0 + i * 0.8 for i in 0:n-1]
    for (name, f) in (("temperature", G.temperature), ("pressure", G.pressure), ("density", G.density),
                      ("sonicspeed", G.sonicspeed), ("viscosity", G.viscosity), ("kinematic", G.kinematic))
        bench!(ctx, name; ops = n, param = p) do i
            geo_loop(f, G.Earth1959, blackbox(i, hs))
        end
    end
    xs = [0.5 + i * 1.0e-6 for i in 0:n-1]
    bench!(i -> geo_loopf(geo_pow, blackbox(i, xs)), ctx, "pow_neg5.25"; ops = n, param = p)
    ϕs = [i * 1.5e-5 for i in 0:n-1]
    bench!(i -> geo_loopf(geo_gravity, blackbox(i, ϕs)), ctx, "gravity"; ops = n, param = p)
end

register!("geophysics", suite_geophysics)
(abspath(PROGRAM_FILE) == @__FILE__) && main_suites(["geophysics" => suite_geophysics])

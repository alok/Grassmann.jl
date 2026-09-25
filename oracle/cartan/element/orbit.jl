# Goldens for orbits of field maps (AbstractAnalysis `orbit`, `orbiterror`, `orbithold` with the
# field metric `supnorm(a, b) = supnorm(a - b)`, Cartan.jl src/Cartan.jl:37, 513) and for
# reparametrization `TensorField(a, b)` (C6, Cartan.jl:115).
#
#   julia --startup-file=no --project=oracle oracle/cartan/element/orbit.jl
#
# Writes oracle/golden/cartan/element/orbit.json.
include(joinpath(@__DIR__, "common.jl"))
using Grassmann, Cartan
import AbstractAnalysis

lim(L) = Dict("n" => length(L), "r" => hx(AbstractAnalysis.residual(L)),
    "last" => hxs(fiber(last(L))), "first" => hxs(fiber(first(L))))

t = TensorField(0:0.25:1)
# `Limit(v0::T, v::T, …)` needs the iterates to keep the start's type: start from a materialized
# field (a range-valued `t` becomes a vector-valued field after one step)
s = sin(t)
f(u) = 0.5 * u + s
out = Dict{String,Any}()
out["orbit_eps"] = @safe lim(orbit(f, s, 1e-12))
out["orbit_n"] = @safe lim(orbit(f, s, 7))
out["orbiterror"] = @safe begin
    L, tr = orbiterror(f, s, 1e-10)
    merge(lim(L), Dict("trace" => hxs(tr)))
end
g(x, u) = 0.25 * u + x
out["orbithold"] = @safe lim(orbithold(g, t, 1:9))
# reparametrization: a non-range and a range-valued parameter
a = t * t
out["reparam_points"] = @safe hxs(collect(Float64, points(TensorField(a, sin(t)))))
out["reparam_fiber"] = @safe hxs(fiber(TensorField(a, sin(t))))
b = 2 * t
out["reparam_range_points"] = @safe hxs(collect(Float64, points(TensorField(b, cos(t)))))
out["reparam_range_isrange"] = @safe (points(TensorField(b, cos(t))) isa AbstractRange)
save("orbit", out)

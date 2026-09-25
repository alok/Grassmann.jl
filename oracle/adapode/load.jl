# Load Adapode.jl *master* (the registered 0.3.13 predates Flow/FlowIntegral and grid.jl) on top of
# the registered Grassmann/Cartan/MeshTopology, with the oracle patches that make the adaptive
# integrators well defined (docs/port-notes/adapode.md §9.1). Included by gen.jl and bench.jl.
#
#   ADAPODE_SRC  path of Adapode.jl/src/Adapode.jl (default: ~/chakravala/Adapode.jl checkout)
using Grassmann, Cartan, LinearAlgebra, SparseArrays
import MeshTopology

# patch 0: MeshTopology 0.1.0 refers to Cartan/Grassmann names it does not import (port notes §7)
for s in (:fibertype, :fiber, :base, :points, :fullpoints)
    isdefined(MeshTopology, s) || Core.eval(MeshTopology, :($s(x) = $(getfield(Cartan, s))(x)))
end
Core.eval(MeshTopology, :(const Grassmann = $(Grassmann)))

const ADAPODE_SRC = get(ENV, "ADAPODE_SRC", joinpath(homedir(), "chakravala", "Adapode.jl", "src", "Adapode.jl"))
include(ADAPODE_SRC)
using .Adapode

# patch 1 (defect B1): the adaptive integrators assign `t ↦ x` into a trajectory whose base is a
# `Vector{Float64}` of times, but Cartan's `setindex!` stores only the fiber, so the times stay
# uninitialized and the loop exits at random. Store the time too.
function Base.setindex!(m::TensorField{B,F,1,<:Cartan.GridBundle{1,<:Any,<:Cartan.PointArray{<:Any,<:Any,1,<:Vector}}} where {B,F}, s::LocalTensor, i::Int)
    points(m)[i] = Real(point(s))
    setindex!(fiber(m), fiber(s), i)
    return s
end

# patch 2 (defect B1b): the bootstrap of the adaptive multistep method assigns only fibers.
function Adapode.initsteps!(x::TensorField, f::Function, fx, t, B::Val=Val(4))
    m = length(fx) - 2
    xi = Adapode.extract(x, t.i)
    for j ∈ 1:m
        @inbounds fx[j] = Adapode.localfiber(f(xi))
        xi = (Adapode.point(xi) + step(t)) ↦ Adapode.explicit(xi, f, step(t), B)
        x[t.i+j] = xi
    end
    t.s = 1 + m
    t.i += m
end

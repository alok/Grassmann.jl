# Julia side of the Adapode ODE benchmarks (docs/PERF.md; Lean side: Bench/Adapode/Lorenz.lean).
#
#   julia --startup-file=no --project=<env with Grassmann 0.8.46, Cartan 0.4.16> oracle/adapode/bench.jl
#
# The same integrations as `lake exe bench Adapode`: wall time of the whole `odesolve` (trajectory
# included), best of 7 after a warm-up, one thread. Adapode.jl master with the load.jl patches (the
# adaptive integrators need them to terminate reproducibly, defect B1).
include(joinpath(@__DIR__, "load.jl"))

Lorenz(σ, r, b) = x -> Chain(σ * (x[2] - x[1]), x[1] * (r - x[3]) - x[2], x[1] * x[2] - b * x[3])
const V3 = Submanifold(3)

function timed(name, f)
    f()
    best = minimum(@elapsed(f()) for _ in 1:7)
    s = f()
    n = s isa LocalTensor ? 1 : length(s)
    println(rpad(name, 46), round(best * 1e3, digits = 3), " ms   (points ", n, ")")
    best
end

function main()
    x0 = Chain(10.0, 10.0, 10.0)
    L = Lorenz(10.0, 28.0, 8 / 3)
    h = 2.0^-15
    T = 2π
    println("Lorenz(10,28,8/3), x0 = (10,10,10), t ∈ [0, 2π], h = 2^-15")
    ic = InitialCondition(L, x0, T)
    timed("RK4 skip 1", () -> odesolve(ic, ExplicitIntegrator{4}(h)))
    timed("RK4 skip 0", () -> odesolve(ic, ExplicitIntegrator{4}(h, 0)))
    timed("ABM4 skip 1", () -> odesolve(ic, MultistepIntegrator{4}(h)))
    timed("Heun skip 1", () -> odesolve(ic, EulerHeunIntegrator(h)))
    timed("Dormand-Prince adaptive, tol 10", () -> odesolve(ic, ExplicitAdaptor{5}(10)))
    timed("ABM4 adaptive, tol 10", () -> odesolve(ic, MultistepAdaptor{4}(10)))
    println("Lorenz, 10^6 RK4 steps (t ∈ [0, 10^6·2^-15])")
    ic6 = InitialCondition(L, x0, 1e6 * h)
    timed("RK4 skip 1", () -> odesolve(ic6, ExplicitIntegrator{4}(h)))
    timed("RK4 skip 0", () -> odesolve(ic6, ExplicitIntegrator{4}(h, 0)))
    println("x' = Bx on multivectors of ℝ3 (B = v₁₂ + v₂₃/2), t ∈ [0, 2π], h = 2^-15")
    B = Multivector{V3}(Values(0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.5, 0.0))
    m0 = Multivector{V3}(Values(1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0))
    icm = InitialCondition(x -> B * fiber(x), m0, T)
    timed("RK4 skip 1", () -> odesolve(icm, ExplicitIntegrator{4}(h)))
end
main()

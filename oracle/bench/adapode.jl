# Julia twin of Bench/Adapode.lean (`adapode` suite): whole `odesolve` calls, trajectory included.
# Adapode.jl master is loaded through oracle/adapode/load.jl (ADAPODE_SRC), whose patches touch
# Cartan methods, so scripts/bench/run.py runs this suite in its own Julia process.
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "harness.jl"))
using .BenchHarness
isdefined(Main, :Adapode) || include(joinpath(@__DIR__, "..", "adapode", "load.jl"))

adapode_lorenz(σ, r, b) = x -> Chain(σ * (x[2] - x[1]), x[1] * (r - x[3]) - x[2], x[1] * x[2] - b * x[3])

"Number of points plus the sum of the last state's coordinates (the Lean check)."
adapode_check(s::LocalTensor) = 1.0 + sum(Grassmann.value(fiber(s)))
adapode_check(s) = Float64(length(s)) + sum(Grassmann.value(fiber(s)[end]))

function suite_adapode(ctx)
    sm = ctx.cfg.smoke
    h = 2.0^-15
    T = sm ? 0.01 : 2π
    T6 = sm ? 0.01 : 1e6 * h
    L = adapode_lorenz(10.0, 28.0, 8 / 3)
    x0 = Chain(10.0, 10.0, 10.0)
    p = sm ? "t∈[0,0.01]" : "t∈[0,2π]"
    solve(t, I) = i -> adapode_check(odesolve(InitialCondition(L, blackbox(i, x0), t), I))
    rk4 = ExplicitIntegrator{4}(h)
    bench!(solve(T, rk4), ctx, "lorenz_rk4"; param = p)
    bench!(solve(T, rk4), ctx, "lorenz_rk4_alloc"; param = p)
    bench!(solve(T, ExplicitIntegrator{4}(h, 0)), ctx, "lorenz_rk4_final"; param = p)
    bench!(solve(T, MultistepIntegrator{4}(h)), ctx, "lorenz_abm4"; param = p)
    bench!(solve(T, MultistepIntegrator{4}(h)), ctx, "lorenz_abm4_alloc"; param = p)
    bench!(solve(T, EulerHeunIntegrator(h)), ctx, "lorenz_heun"; param = p)
    bench!(solve(T, ExplicitAdaptor{5}(10)), ctx, "lorenz_dp_adaptive"; param = p * " tol 10")
    bench!(solve(T, ExplicitAdaptor{5}(10)), ctx, "lorenz_dp_adaptive_alloc"; param = p * " tol 10")
    bench!(solve(T, MultistepAdaptor{4}(10)), ctx, "lorenz_abm4_adaptive"; param = p * " tol 10")
    p6 = sm ? "t∈[0,0.01]" : "10⁶ steps"
    bench!(solve(T6, rk4), ctx, "lorenz_rk4_1e6"; param = p6)
    bench!(solve(T6, ExplicitIntegrator{4}(h, 0)), ctx, "lorenz_rk4_final_1e6"; param = p6)
    V3 = Submanifold(3)
    B = Multivector{V3}(Values(0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.5, 0.0))
    m0 = Multivector{V3}(Values(1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0))
    bench!(ctx, "multivector_rk4"; param = p) do i
        adapode_check(odesolve(InitialCondition(x -> B * fiber(x), blackbox(i, m0), T), rk4))
    end
end

register!("adapode", suite_adapode)
(abspath(PROGRAM_FILE) == @__FILE__) && main_suites(["adapode" => suite_adapode])

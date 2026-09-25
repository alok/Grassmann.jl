import Bench.Harness
import Bench.Adapode.Lorenz

/-!
# `adapode`: ODE integrators

Julia twin: `oracle/bench/adapode.jl` (Adapode.jl master through `oracle/adapode/load.jl`, in its
own Julia process because the loader patches Cartan methods). One operation is one whole
`odesolve`, trajectory included: Lorenz `(10, 28, 8/3)` from `(10, 10, 10)` over `[0, 2π]` with
`h = 2^-15` (205 888 points; smoke: `[0, 0.01]`) under RK4, RK4 final state only, ABM4 and Heun;
adaptive Dormand–Prince (`ExplicitAdaptor{5}(10)`) and adaptive ABM4 (`MultistepAdaptor{4}(10)`)
with Julia's end of integration (`compat`), so both sides take the same steps; RK4 over `10⁶`
steps; and `x' = Bx` on multivectors of `ℝ3` (the generated `ℝ3` product kernel).

Lean runs Lorenz in two forms: `Flow.into` (`*` cases: the system writes into the scratch state,
no allocation per step) and `Flow.of` (`*_alloc`: Julia's form, a new `Chain` per evaluation).
Both are compared with the same Julia solve. The check is the number of points plus the sum of
the last state's coordinates, equal on both sides.
-/

namespace Bench.Adapode

open _root_.Adapode Grassmann DirectSum StaticVectors Bench

/-- The suite. -/
def suite : Suite := ⟨"adapode", do
  let sm ← smoke
  let h := Tol.toStep 15
  let T := if sm then 0.01 else twoPi
  let T6 := if sm then 0.01 else 1e6 * h
  let rk4 : Integrator := .explicit ({ tol := h } : ExplicitIntegrator 4)
  let rk4f : Integrator := .explicit ({ tol := h, skip := 0 } : ExplicitIntegrator 4)
  let abm4 : Integrator := .multistep ({ tol := h } : MultistepIntegrator 4)
  let heun : Integrator := .eulerHeun { tol := h }
  let dp : Integrator := .explicitAdaptor ({ tol := Tol.toStep 10, compat := true } : ExplicitAdaptor 5)
  let abma : Integrator := .multistepAdaptor ({ tol := Tol.toStep 10, compat := true } : MultistepAdaptor 4)
  let σ := 10
  let ρ := 28
  let β : Float := 8 / 3
  let p := if sm then "t∈[0,0.01]" else "t∈[0,2π]"
  bench "lorenz_rk4" (param := p) fun s => lorenzInPlace σ ρ β (start s) T rk4
  bench "lorenz_rk4_alloc" (param := p) fun s => lorenzAlloc σ ρ β (start s) T rk4
  bench "lorenz_rk4_final" (param := p) fun s => lorenzInPlace σ ρ β (start s) T rk4f
  bench "lorenz_abm4" (param := p) fun s => lorenzInPlace σ ρ β (start s) T abm4
  bench "lorenz_abm4_alloc" (param := p) fun s => lorenzAlloc σ ρ β (start s) T abm4
  bench "lorenz_heun" (param := p) fun s => lorenzInPlace σ ρ β (start s) T heun
  bench "lorenz_dp_adaptive" (param := p ++ " tol 10") fun s => lorenzInPlace σ ρ β (start s) T dp
  bench "lorenz_dp_adaptive_alloc" (param := p ++ " tol 10") fun s => lorenzAlloc σ ρ β (start s) T dp
  bench "lorenz_abm4_adaptive" (param := p ++ " tol 10") fun s => lorenzInPlace σ ρ β (start s) T abma
  let p6 := if sm then "t∈[0,0.01]" else "10⁶ steps"
  bench "lorenz_rk4_1e6" (param := p6) fun s => lorenzInPlace σ ρ β (start s) T6 rk4
  bench "lorenz_rk4_final_1e6" (param := p6) fun s => lorenzInPlace σ ρ β (start s) T6 rk4f
  let B : Multivector ℝ3 Float := ⟨Values.ofFn fun i => [0, 0, 0, 0, 1, 0, 0.5, 0].getD i.1 0⟩
  let mv (s : Nat) : Multivector ℝ3 Float :=
    ⟨Values.ofFn fun i => [1 + s.toUInt64.toFloat * 0, 1, 0, 0, 0, 0, 0, 0].getD i.1 0⟩
  bench "multivector_rk4" (param := p) fun s => spinSolve B (mv s) T rk4⟩

end Bench.Adapode

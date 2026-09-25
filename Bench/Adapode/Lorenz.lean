import Adapode
import Grassmann.Kernel.Generated.R3

/-!
# ODE benchmarks: Lorenz and a multivector flow (`lake exe bench Adapode`)

The integrations of `oracle/adapode/bench.jl`, timed the same way (best of `reps` runs after a
warm-up, wall time of the whole `odesolve`, trajectory included):

* Lorenz `(10, 28, 8/3)` from `(10, 10, 10)` over `[0, 2π]` with `h = 2^-15` (205 888 points):
  RK4 (Julia's `odesolve(f, x0)`), RK4 final state only, ABM4, Heun; and RK4 over `10⁶` steps
  (`t ∈ [0, 10⁶·2^-15]`);
* adaptive Dormand–Prince (`ExplicitAdaptor{5}(10)`) and adaptive ABM4 (`MultistepAdaptor{4}(10)`),
  with Julia's end of integration (`compat`), so both sides take the same steps;
* the multivector flow `x' = Bx` in `ℝ3` (four geometric products per RK4 step, the generated
  `ℝ3` kernel).

Lorenz runs in two forms: `Flow.into` with `lorenzInto` (the system writes into the scratch state:
no allocation per step) and `Flow.of` with `lorenz` (Julia's form: a new `Chain` per evaluation).
Inputs reach the solver as run-time arguments (`@[noinline]`), so no solve is a closed term.
-/

namespace Bench.Adapode

open _root_.Adapode Grassmann DirectSum StaticVectors

/-- A checksum of a result (keeps the whole solve live): the number of points plus the last state. -/
def checksum {σ : Type} [OdeState σ] (r : Result σ) : Float :=
  let n := match r with
    | .final .. => 1
    | .path s => s.length
  r.lastFlat.foldl (· + ·) n.toUInt64.toFloat

/-- Lorenz with the in-place system. -/
@[noinline] def lorenzInPlace (σ ρ β : Float) (x0 : Chain ℝ3 1 Float) (tmax : Float) (I : Integrator) : Float :=
  checksum (odesolve ⟨.into (fun _ x o => lorenzInto σ ρ β x o) tmax, x0, 0⟩ I)

/-- Lorenz with Julia's allocating system. -/
@[noinline] def lorenzAlloc (σ ρ β : Float) (x0 : Chain ℝ3 1 Float) (tmax : Float) (I : Integrator) : Float :=
  checksum (odesolve ⟨.of (lorenz σ ρ β) tmax, x0, 0⟩ I)

/-- `x' = Bx` on multivectors of `ℝ3`. -/
@[noinline] def spinSolve (B x0 : Multivector ℝ3 Float) (tmax : Float) (I : Integrator) : Float :=
  checksum (odesolve ⟨.of (fun x => B * x) tmax, x0, 0⟩ I)

/-- Time one run (ms). -/
@[noinline] def measure (run : Nat → Float) (salt : Nat) : IO (Float × Float) := do
  let t0 ← IO.monoNanosNow
  let s ← IO.lazyPure fun _ => run salt
  let t1 ← IO.monoNanosNow
  return ((t1 - t0).toFloat / 1e6, s)

/-- Warm up, then print the best of `reps` runs. -/
def timed (name : String) (reps : Nat) (run : Nat → Float) : IO Float := do
  let _ ← measure run 0
  let mut best := 1.0e30
  let mut sum := 0.0
  for r in [0:reps] do
    let (t, s) ← measure run (r + 1)
    best := min best t
    sum := s
  IO.println s!"  {name.pushn ' ' (44 - name.length)} {JuliaBase.F64.showCompact best} ms   (checksum {JuliaBase.F64.showCompact sum})"
  return best

/-- `x₀ = (10, 10, 10)`, perturbed by `salt · 0` so that the compiler cannot share runs. -/
def start (salt : Nat) : Chain ℝ3 1 Float :=
  let z := salt.toUInt64.toFloat * 0
  vec3 (10 + z) (10 + z) (10 + z)

/-- Run the ODE benchmarks (`smoke`: one short run of each). -/
def run (smoke : Bool := false) : IO Unit := do
  let reps := if smoke then 1 else 7
  let h := Tol.toStep 15
  let T := if smoke then 0.01 else twoPi
  let T6 := if smoke then 0.01 else 1e6 * h
  let rk4 : Integrator := .explicit ({ tol := h } : ExplicitIntegrator 4)
  let rk4f : Integrator := .explicit ({ tol := h, skip := 0 } : ExplicitIntegrator 4)
  let abm4 : Integrator := .multistep ({ tol := h } : MultistepIntegrator 4)
  let heun : Integrator := .eulerHeun { tol := h }
  let dp : Integrator := .explicitAdaptor ({ tol := Tol.toStep 10, compat := true } : ExplicitAdaptor 5)
  let abma : Integrator := .multistepAdaptor ({ tol := Tol.toStep 10, compat := true } : MultistepAdaptor 4)
  let σ := 10
  let ρ := 28
  let β : Float := 8 / 3
  IO.println "Lorenz(10,28,8/3), x0 = (10,10,10), t ∈ [0, 2π], h = 2^-15 (205888 points)"
  let _ ← timed "RK4 skip 1 (in place)" reps fun s => lorenzInPlace σ ρ β (start s) T rk4
  let _ ← timed "RK4 skip 1 (allocating system)" reps fun s => lorenzAlloc σ ρ β (start s) T rk4
  let _ ← timed "RK4 skip 0 (in place)" reps fun s => lorenzInPlace σ ρ β (start s) T rk4f
  let _ ← timed "ABM4 skip 1 (in place)" reps fun s => lorenzInPlace σ ρ β (start s) T abm4
  let _ ← timed "ABM4 skip 1 (allocating system)" reps fun s => lorenzAlloc σ ρ β (start s) T abm4
  let _ ← timed "Heun skip 1 (in place)" reps fun s => lorenzInPlace σ ρ β (start s) T heun
  let _ ← timed "Dormand-Prince adaptive, tol 10 (in place)" reps fun s => lorenzInPlace σ ρ β (start s) T dp
  let _ ← timed "Dormand-Prince adaptive (allocating)" reps fun s => lorenzAlloc σ ρ β (start s) T dp
  let _ ← timed "ABM4 adaptive, tol 10 (in place)" reps fun s => lorenzInPlace σ ρ β (start s) T abma
  IO.println "Lorenz, 10^6 RK4 steps (t ∈ [0, 10^6·2^-15])"
  let _ ← timed "RK4 skip 1 (in place)" reps fun s => lorenzInPlace σ ρ β (start s) T6 rk4
  let _ ← timed "RK4 skip 0 (in place)" reps fun s => lorenzInPlace σ ρ β (start s) T6 rk4f
  IO.println "x' = Bx on multivectors of ℝ3 (B = v₁₂ + v₂₃/2), t ∈ [0, 2π], h = 2^-15"
  let B : Multivector ℝ3 Float := ⟨Values.ofFn fun i => [0, 0, 0, 0, 1, 0, 0.5, 0].getD i.1 0⟩
  let mv (s : Nat) : Multivector ℝ3 Float :=
    ⟨Values.ofFn fun i => [1 + s.toUInt64.toFloat * 0, 1, 0, 0, 0, 0, 0, 0].getD i.1 0⟩
  let _ ← timed "RK4 skip 1" reps fun s => spinSolve B (mv s) T rk4

end Bench.Adapode

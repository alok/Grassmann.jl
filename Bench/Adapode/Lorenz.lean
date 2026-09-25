import Adapode
import Grassmann.Kernel.Generated.R3

/-!
# ODE benchmark kernels: Lorenz and a multivector flow

The solves timed by the `adapode` suite (`Bench/Adapode.lean`, Julia twin
`oracle/bench/adapode.jl`); each returns a checksum of the whole result:

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

/-- `x₀ = (10, 10, 10)`, perturbed by `salt · 0` so that the compiler cannot share runs. -/
def start (salt : Nat) : Chain ℝ3 1 Float :=
  let z := salt.toUInt64.toFloat * 0
  vec3 (10 + z) (10 + z) (10 + z)

end Bench.Adapode

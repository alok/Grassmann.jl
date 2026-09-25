import Tests.Adapode.Common
import Grassmann.Kernel.Generated.R3

/-!
# The test problems of `oracle/adapode/gen.jl`, and integrators built from golden records

| golden name | system | state |
|---|---|---|
| `lorenz` | Lorenz `(10(y-x), x(28-z)-y, xy-(8/3)z)` | `Chain ℝ3 1`, `x₀ = (10,10,10)` |
| `osc` | damped oscillator `(v, -x - 0.1v)` | `Chain ℝ2 1`, `x₀ = (1, 0)` |
| `nonauto` | `x' = x cos t + t` (reads the time; Julia's `cos`) | `Chain ℝ1 1`, `x₀ = 1` |
| `spin` | `x' = B x`, `B = v₁₂ + 0.5v₂₃` (geometric product) | `Multivector ℝ3`, `x₀ = 1 + v₁` |
-/

open Lean Tests.Small JuliaBase Adapode Grassmann DirectSum StaticVectors Cartan

namespace Tests.AdapodeTests

/-- A vector of `V` from a list of coefficients (zeros if the length is wrong). -/
def chainOf {V : TensorBundle} (xs : List Float) : Chain V 1 Float :=
  Chain.ofFn fun i => xs.getD i.1 0

/-- The Lorenz system of the goldens (Julia `Chain(10.0(x[2]-x[1]), x[1]*(28.0-x[3])-x[2],
x[1]*x[2]-(8/3)*x[3])`). -/
def lorenzFn (x : Chain ℝ3 1 Float) : Chain ℝ3 1 Float :=
  vec3 (10.0 * (comp x 1 - comp x 0)) (comp x 0 * (28.0 - comp x 2) - comp x 1)
    (comp x 0 * comp x 1 - (8 / 3) * comp x 2)

/-- `Flow(lorenz)` (duration 2π). -/
def lorenzFlow : Flow (Chain ℝ3 1 Float) := .of lorenzFn

/-- The damped oscillator (Julia `Chain(x[2], -x[1]-0.1x[2])`). -/
def oscFlow : Flow (Chain ℝ2 1 Float) :=
  .of fun x => chainOf [comp x 1, -comp x 0 - 0.1 * comp x 1]

/-- The non-autonomous scalar problem (Julia `Chain(x[1]*cos(point(x))+point(x))`). -/
def nonautoFlow : Flow (Chain ℝ1 1 Float) :=
  .ofTime fun t x => chainOf [comp x 0 * F64.cos t + t]

/-- `B = v₁₂ + 0.5v₂₃` as a multivector. -/
def bspin : Multivector ℝ3 Float := ⟨Values.ofFn fun i => [0, 0, 0, 0, 1, 0, 0.5, 0].getD i.1 0⟩

/-- The rotation generator `x' = B x` on multivectors. -/
def spinFlow : Flow (Multivector ℝ3 Float) := .of fun x => bspin * x

/-- `1 + v₁`. -/
def spinStart : Multivector ℝ3 Float := ⟨Values.ofFn fun i => [1, 1, 0, 0, 0, 0, 0, 0].getD i.1 0⟩

/-- The integrator of a golden record: `method` (`RK`, `Heun`, `ABM`, `RKA`, `ABMA`), `order`, step
`h`, `skip` and `compat`. -/
def mkIntegrator (method : String) (o : Nat) (h : Float) (skip : Nat) (compat : Bool) : Option Integrator :=
  match method with
  | "RK" => if hv : 1 ≤ o ∧ o ≤ 4 then some (.explicit ({ tol := h, skip, valid := hv } : ExplicitIntegrator o)) else none
  | "Heun" => some (.eulerHeun { tol := h, skip, compat })
  | "ABM" =>
    if hv : 1 ≤ o ∧ o ≤ 5 then some (.multistep ({ tol := h, skip, compat, valid := hv } : MultistepIntegrator o))
    else none
  | "RKA" =>
    if hv : 1 ≤ o ∧ o ≤ 5 then some (.explicitAdaptor ({ tol := h, skip, compat, valid := hv } : ExplicitAdaptor o))
    else none
  | "ABMA" =>
    if hv : 1 ≤ o ∧ o ≤ 5 then some (.multistepAdaptor ({ tol := h, skip, compat, valid := hv } : MultistepAdaptor o))
    else none
  | _ => none

/-- The times of a solution (`n` points). -/
def timesOf {σ : Type} (s : Solution σ) : FloatArray :=
  (List.range s.length).foldl (fun a i => a.push (s.timeAt i)) .empty

/-- Run a golden problem with an integrator from time `0` to `tmax`: `(times, flat states)` (one
point for `skip = 0`). -/
def runProblem (problem : String) (I : Integrator) (tmax : Float) : Option (FloatArray × FloatArray) :=
  let out {σ : Type} [OdeState σ] (r : Result σ) : FloatArray × FloatArray :=
    match r with
    | .final t x => (FloatArray.empty.push t, toFlat x)
    | .path s => (timesOf s, s.data)
  match problem with
  | "lorenz" => some (out (odesolve ⟨lorenzFlow.withDuration tmax, chaosStart, 0⟩ I))
  | "osc" => some (out (odesolve ⟨oscFlow.withDuration tmax, chainOf [1, 0], 0⟩ I))
  | "nonauto" => some (out (odesolve ⟨nonautoFlow.withDuration tmax, chainOf [1], 0⟩ I))
  | "spin" => some (out (odesolve ⟨spinFlow.withDuration tmax, spinStart, 0⟩ I))
  | _ => none

end Tests.AdapodeTests

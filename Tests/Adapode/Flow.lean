import Tests.Adapode.Chaos

/-!
# The flow API against Julia (`flow.json`)

Lorenz flows over `t ∈ [0, 1]` with `h = 2^-11`: `Flow(f, t)(x0, i)` for RK1–4, the default
integrator of a flow (Julia's `MultistepIntegrator{4}(2^-11, 0)`, whose B3 result is reproduced by
`compat` and fixed by default), `integrator(Φ)`, a negative duration, a start `t0 ↦ x0` (B5: Julia
integrates over `[0, t0 + T]`), `FlowIntegral`; a flow applied to a field of states (a state that is
a whole `TensorField`), a field-valued system, and the flow of a vector field sampled on a grid
(Julia `exp(X)`, through Cartan's multilinear interpolation).
-/

open Lean Tests.Small JuliaBase Adapode Grassmann DirectSum StaticVectors Cartan

namespace Tests.AdapodeTests.FlowTests

/-- `Flow(lorenz, 1.0)`. -/
def L1 : Flow (Chain ℝ3 1 Float) := lorenzFlow.withDuration 1

/-- RK`o` with `h = 2^-11`, final state. -/
def rk (o : Nat) (h : 1 ≤ o ∧ o ≤ 4 := by decide) (step : Float := Tol.toStep 11) : Integrator :=
  .explicit ({ tol := step, skip := 0, valid := h } : ExplicitIntegrator o)

/-- Compare a final `t ↦ x` with a golden `{t, x}`. -/
def checkFinal {σ : Type} [OdeState σ] (label : String) (r : Result σ) (g : Json) : TestM Unit := do
  let (ts, xs) := Chaos.flatOf r
  checkBits s!"{label} t" ts (FloatArray.empty.push (← gFloatAt g "t"))
  checkBits s!"{label} x" xs (← gFloatsAt g "x")

/-- The starting field of `field_flow`: `(10 + t, 10 - t, 10 + 2t)` over `0:0.5:1.5`. -/
def fieldStart : TensorField (GridBundle.ofAxis (Axis.colon 0 0.5 1.5)) (Chain ℝ3 1 Float) :=
  TensorField.ofAxisFn (Axis.colon 0 0.5 1.5) fun t => vec3 (10 + t) (10 - t) (10 + 2 * t)

/-- The vector field `(x, y) ↦ (-y, x)` on the grid `(-2:0.5:2)²`. -/
def rotField :=
  TensorField.ofSpaceFn (ProductSpace.ofAxes #v[Axis.colon (-2) 0.5 2, Axis.colon (-2) 0.5 2])
    fun p => (chainOf [-(p.get! 1), p.get! 0] : Chain ℝ2 1 Float)

/-- Run the flow checks. -/
def run : TestM Unit := do
  let j ← load "flow"
  checkFinal "Flow RK1" (L1.apply chaosStart (rk 1)) (← jField j "RK1_skip0")
  checkFinal "Flow RK2" (L1.apply chaosStart (rk 2)) (← jField j "RK2_skip0")
  checkFinal "Flow RK3" (L1.apply chaosStart (rk 3)) (← jField j "RK3_skip0")
  checkFinal "Flow RK4" (L1.apply chaosStart (rk 4)) (← jField j "RK4_skip0")
  checkFinal "Flow integrator(Φ)" (L1.apply chaosStart L1.integrator) (← jField j "integrator_default")
  -- Julia's default Flow call (B3 as it runs)
  checkFinal "Flow default compat" (L1.apply chaosStart
    (.multistep ({ tol := Tol.toStep 11, skip := 0, compat := true } : MultistepIntegrator 4)))
    (← jField j "default_ASIS")
  -- fixed: the default is the final state of the ABM4 trajectory
  let abm := (L1.apply chaosStart (.multistep (MultistepIntegrator.new 4 11))).lastFlat
  checkBits "Flow default = ABM4 trajectory end" (L1.apply chaosStart).lastFlat abm
  checkFinal "Flow backward" ((lorenzFlow.withDuration (-0.5)).apply chaosStart (rk 4)) (← jField j "backward")
  -- B5: Julia integrates t0 ↦ x0 over [0, t0 + T] …
  let g15 ← jField j "from0_to_1.5"
  checkFinal "Flow [0, 1.5]" ((lorenzFlow.withDuration 1.5).apply chaosStart (rk 4)) g15
  checkBits "Flow(t0 ↦ x0) as Julia runs it" (← gFloatsAt (← jField j "localtensor_ASIS") "x") (← gFloatsAt g15 "x")
  -- … the port over [t0, t0 + T]: an autonomous flow gives the state of [0, T] at time t0 + T
  let r := L1.applyLocal ⟨0.5, chaosStart⟩ (rk 4)
  checkBits "Flow(t0 ↦ x0) state" r.lastFlat (L1.apply chaosStart (rk 4)).lastFlat
  checkEq "Flow(t0 ↦ x0) time" r.lastTime 1.5
  -- FlowIntegral(f, 1.0): RK4 2^-11, full trajectory
  let fi := FlowIntegral.of L1
  let gi ← jField j "FlowIntegral"
  match fi.apply chaosStart with
  | .path s =>
    checkEq "FlowIntegral n" s.length (← gNat gi "n")
    checkBits "FlowIntegral last" (s.flatAt (s.length - 1)) (← gFloatsAt gi "last")
    checkEq "FlowIntegral digest" (digest (timesOf s) s.data) (← gStr gi "digest")
  | .final .. => check "FlowIntegral path" false
  checkEq "FlowIntegral applyAll" ((fi.applyAll #[chaosStart, chaosStart]).map (·.lastFlat.toList)).size 2
  -- a flow applied to a field of states
  let gf ← jField j "field_flow"
  checkBits "field x0" fieldStart.data (← gFloatsAt gf "x0")
  let rf := (lorenzFlow.withDuration 0.25).onField fieldStart (rk 4 (step := Tol.toStep 8))
  checkFinal "field flow" rf gf
  -- a field-valued system on a field state
  let fsys : Flow (TensorField (GridBundle.ofAxis (Axis.colon 0 0.5 1.5)) (Chain ℝ3 1 Float)) :=
    .of (fun X => X.map fun c => vec3 (-comp c 1) (comp c 0) (0.1 * comp c 2)) 1
  checkFinal "field system" (odesolve ⟨fsys, fieldStart, 0⟩ (rk 4 (step := Tol.toStep 6))) (← jField j "field_system")
  -- the flow of a vector field sampled on a grid
  checkFinal "exp(vector field)" ((vectorFieldExp rotField).apply (chainOf [1, 0.25]) (rk 4 (step := Tol.toStep 6)))
    (← jField j "vectorfield_exp")
  checkFinal "Flow(vector field) RK2" ((Flow.ofField rotField 1).apply (chainOf [1, 0.25]) (rk 2 (step := Tol.toStep 5)))
    (← jField j "vectorfield_rk2")

end Tests.AdapodeTests.FlowTests

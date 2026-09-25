import Tests.Adapode.Flow

/-!
# Properties of the ODE port beyond the goldens

* The fixed semantics of Julia's defective paths are consistent with the paths Julia gets right:
  `skip = k` stores every `k`-th state of `skip = 1` (RK4, Heun, ABM4; B4, B7), `skip = 0` returns
  the last state of `skip = 1` (ABM4, B3; Heun, which Julia cannot run).
* The default end rule of the adaptive integrators (B2 fixed) ends exactly at `tmax` with every
  accepted point kept, and matches the analytic solution of the damped oscillator; Julia's rule
  (`compat`) stops Runge–Kutta pairs short of `tmax - hmax`.
* The corrected Fehlberg and Cash–Karp pairs (B10) converge at orders 5 and 4 as fixed-step
  methods, Julia's tables at order 1.
* A flow of a field of states (`skip = 1`, the trajectory over `base ⊕ time`) agrees point by point
  with the flows of the individual states, and its last slice with the `skip = 0` flow.
* The multivector problem `x' = Bx` follows `exp(tB) x₀`; a `FlowApprox` system receives the step;
  the `Result`/`Solution` accessors and `TensorField` packaging agree with the flat data.
-/

open Lean Tests.Small JuliaBase Adapode Grassmann DirectSum StaticVectors Cartan

namespace Tests.AdapodeTests.Props

/-- The flat trajectory of a result. -/
def flat {σ : Type} [OdeState σ] (r : Result σ) : FloatArray × FloatArray := Chaos.flatOf r

/-- Lorenz from `x₀ = (10,10,10)` over `[0, 1]` with step `2^-8`. -/
def lz (I : Integrator) : FloatArray × FloatArray := flat (odesolve ⟨lorenzFlow.withDuration 1, chaosStart, 0⟩ I)

/-- `h = 2^-8`. -/
def h8 : Float := Tol.toStep 8

/-- Stride and final-state consistency of the fixed semantics. -/
def runSkips : TestM Unit := do
  let (t1, x1) := lz (.explicit ({ tol := h8 } : ExplicitIntegrator 4))
  let (t4, x4) := lz (.explicit ({ tol := h8, skip := 4 } : ExplicitIntegrator 4))
  checkBits "RK4 skip 4 = every 4th of skip 1" x4 (every x1 3 4)
  checkBits "RK4 skip 4 times" t4 (every t1 1 4)
  let (_, h1) := lz (.eulerHeun { tol := h8 })
  let (_, h4) := lz (.eulerHeun { tol := h8, skip := 4 })
  checkBits "Heun skip 4 = every 4th of skip 1 (B7 fixed)" h4 (every h1 3 4)
  let (th0, h0) := lz (.eulerHeun { tol := h8, skip := 0 })
  checkBits "Heun skip 0 = last of skip 1" h0 (sub h1 (h1.size - 3) 3)
  checkEq "Heun skip 0 time" (th0.get! 0) 1
  let (_, a1) := lz (.multistep ({ tol := h8 } : MultistepIntegrator 4))
  let (_, a4) := lz (.multistep ({ tol := h8, skip := 4 } : MultistepIntegrator 4))
  checkBits "ABM4 skip 4 = every 4th of skip 1 (B4 fixed)" a4 (every a1 3 4)
  let (ta0, a0) := lz (.multistep ({ tol := h8, skip := 0 } : MultistepIntegrator 4))
  checkBits "ABM4 skip 0 = last of skip 1 (B3 fixed)" a0 (sub a1 (a1.size - 3) 3)
  checkEq "ABM4 skip 0 time" (ta0.get! 0) 1
  -- a run shorter than the bootstrap is all RK4
  let (_, r5) := flat (odesolve ⟨lorenzFlow.withDuration (2 * h8), chaosStart, 0⟩
    (.multistep ({ tol := h8 } : MultistepIntegrator 5)))
  let (_, r4) := flat (odesolve ⟨lorenzFlow.withDuration (2 * h8), chaosStart, 0⟩
    (.explicit ({ tol := h8 } : ExplicitIntegrator 4)))
  checkBits "ABM5 over two steps = RK4" r5 r4
  -- the in-place and the allocating Lorenz give the same bits
  let (_, p1) := flat (odesolve ⟨(Flow.into fun _ x o => lorenzInto 10 28 (8 / 3) x o).withDuration 1, chaosStart, 0⟩
    (.explicit ({ tol := h8 } : ExplicitIntegrator 4)))
  checkBits "lorenzInto = lorenz" p1 x1

/-- The damped oscillator `x'' + 0.1x' + x = 0`, `x(0) = 1`, `x'(0) = 0`, at time `t`. -/
def oscExact (t : Float) : Float × Float :=
  let ω := Float.sqrt (1 - 0.0025)
  let e := Float.exp (-0.05 * t)
  (e * (Float.cos (ω * t) + (0.05 / ω) * Float.sin (ω * t)), -e * Float.sin (ω * t) / ω)

/-- An adaptive integrator with `h₀ = 2^-7` (corrected tables). -/
def adaptive (method : String) (o : Nat) (compat : Bool) : Integrator :=
  if hv : 1 ≤ o ∧ o ≤ 5 then
    if method == "RKA" then
      .explicitAdaptor ({ tol := Tol.toStep 7, fixed := true, compat, valid := hv } : ExplicitAdaptor o)
    else .multistepAdaptor ({ tol := Tol.toStep 7, compat, valid := hv } : MultistepAdaptor o)
  else .default

/-- The end of the adaptive integrations. -/
def runAdaptiveEnd : TestM Unit := do
  let (xe, ve) := oscExact 1
  for (method, o, tol) in [("RKA", 1, 1e-3), ("RKA", 2, 1e-5), ("RKA", 3, 1e-5), ("RKA", 4, 1e-5),
      ("RKA", 5, 1e-5), ("ABMA", 1, 1e-3), ("ABMA", 2, 1e-5), ("ABMA", 3, 1e-5), ("ABMA", 4, 1e-5),
      ("ABMA", 5, 1e-5)] do
    let label := s!"osc {method}{o} exact end"
    match odesolve ⟨oscFlow.withDuration 1, chainOf [1, 0], 0⟩ (adaptive method o false) with
    | .path s =>
      let n := s.length
      checkEq s!"{label}: last time is tmax" (s.timeAt (n - 1)) 1
      let ts := timesOf s
      check s!"{label}: times increase" ((List.range (n - 1)).all fun i => ts.get! i < ts.get! (i + 1))
      let x := s.flatAt (n - 1)
      check s!"{label}: accuracy" ((x.get! 0 - xe).abs ≤ tol && (x.get! 1 - ve).abs ≤ tol) fun _ =>
        s!"x = {fmt (x.get! 0)}, {fmt (x.get! 1)} vs {fmt xe}, {fmt ve}"
    | .final .. => check label false
    -- Julia's rule stops short of tmax - hmax (Runge–Kutta; an ABM bootstrap of o - 1 RK4 steps
    -- runs past the test and may even reach tmax)
    if method == "RKA" then
      match odesolve ⟨oscFlow.withDuration 1, chainOf [1, 0], 0⟩ (adaptive method o true) with
      | .path s => check s!"osc {method}{o} compat end" (s.lastTime < 1 - Tol.toStep 7) fun _ => fmt s.lastTime
      | .final .. => check "compat path" false

/-- Global error of a fixed-step method with the advancing weights of `T` on the oscillator. -/
def oscError (T : Tableau) (h : Float) : Float :=
  let d := 2
  have hd : d = OdeState.dim (Chain ℝ2 1 Float) := by decide
  let x0 : Chain ℝ2 1 Float := chainOf [1, 0]
  let f := flatSystem d hd x0 oscFlow.f
  let r := rkSolve f id T false d (toFlat x0) 0 h 1 0 0
  let (xe, ve) := oscExact r.t
  (r.x.get! 0 - xe).abs + (r.x.get! 1 - ve).abs

/-- Empirical orders of the corrected and of Julia's Fehlberg and Cash–Karp weights. -/
def runOrders : TestM Unit := do
  let order (T : Tableau) : Float :=
    Float.log (oscError T (Tol.toStep 4) / oscError T (Tol.toStep 5)) / Float.log 2
  let fF := order (CBA.fixed 3)
  let fJ := order (CBA 3)
  let cF := order (CBA.fixed 4)
  let cJ := order (CBA 4)
  let dp := order (CBA 5)
  check "Fehlberg fixed order 5" (fF > 4.5) fun _ => fmt fF
  check "Fehlberg as in Julia order 1" (fJ < 1.5) fun _ => fmt fJ
  check "Cash-Karp fixed order 4" (cF > 3.5 && cF < 4.6) fun _ => fmt cF
  check "Cash-Karp as in Julia order 1" (cJ < 1.5) fun _ => fmt cJ
  check "Dormand-Prince order 5" (dp > 4.5) fun _ => fmt dp

/-- Flows of fields of states. -/
def runFieldFlow : TestM Unit := do
  let Φ := lorenzFlow.withDuration 0.25
  let I1 := Integrator.explicit ({ tol := h8 } : ExplicitIntegrator 4)
  let I0 := Integrator.explicit ({ tol := h8, skip := 0 } : ExplicitIntegrator 4)
  match Φ.onField FlowTests.fieldStart I1 with
  | .path s =>
    let n := s.length
    checkEq "field trajectory points" n 65
    checkEq "field trajectory data" s.data.size (3 * 4 * 65)
    checkBits "field trajectory last slice = skip 0" (s.flatAt (n - 1)) (Φ.onField FlowTests.fieldStart I0).lastFlat
    -- point p of the field follows the flow of its own initial state
    for p in [0, 1, 2, 3] do
      let x0 := FlowTests.fieldStart.get p
      match Φ.apply x0 I1 with
      | .path sp =>
        let mine := (List.range n).foldl (fun a i => (sub s.data (i * 12 + 3 * p) 3).foldl (·.push ·) a) FloatArray.empty
        checkBits s!"field point {p} = its own flow" mine sp.data
      | .final .. => check "point path" false
    -- the trajectory as a field over base ⊕ time
    let F := s.field
    checkEq "field over base ⊕ time" F.length (4 * 65)
    checkBits "field over base ⊕ time data" F.data s.data
  | .final .. => check "field path" false

/-- The remaining API. -/
def runApi : TestM Unit := do
  checkEq "Tol exponent" (Tol.toStep 15).toBits 0x3F00000000000000
  checkEq "Tol step" (Tol.toStep (.step 0.1)) 0.1
  let t := TimeStep.check { h := -1e-20, hmin := 1e-16, hmax := 1e-4, emin := 0, emax := 1, e := 0, i := 0 }
  checkEq "checkstep! clamps up with the sign" t.h (-1e-16)
  checkEq "checkstep! i ≥ 1" t.i 1
  checkEq "checkstep! clamps down" (TimeStep.check { t with h := 0.5 }).h 1e-4
  -- x' = Bx with B = v₁₂ + v₂₃/2 is a rotation: x(t) = exp(tB) x₀
  let r := odesolve ⟨spinFlow.withDuration 1, spinStart, 0⟩ (.explicit ({ tol := h8 } : ExplicitIntegrator 4))
  let x := r.lastFlat
  -- exp(tB) acts on the vector part as the rotation generated by (e₁ → e₂, e₂ → -e₁ + e₃/2 …):
  -- compare with the RK4 solution of the same linear system at a smaller step
  let r' := odesolve ⟨spinFlow.withDuration 1, spinStart, 0⟩ (.explicit ({ tol := Tol.toStep 10 } : ExplicitIntegrator 4))
  checkClose "spin converges" x r'.lastFlat 1e-9 1e-12
  -- |x| is conserved by a rotation of the vector and scalar parts (B² < 0 on this subspace)
  let nrm (a : FloatArray) := a.foldl (fun s c => s + c * c) 0
  check "spin conserves |x|²" ((nrm x - 2).abs < 1e-9) fun _ => fmt (nrm x)
  -- FlowApprox systems receive the step
  let fa : Flow (Chain ℝ1 1 Float) := FlowApprox (fun _ x h => chainOf [comp x 0 * h]) 1
  let fc : Flow (Chain ℝ1 1 Float) := .of (fun x => chainOf [comp x 0 * Tol.toStep 6]) 1
  checkBits "FlowApprox receives h" (fa.apply (chainOf [1]) (.explicit ({ tol := Tol.toStep 6, skip := 0 } : ExplicitIntegrator 4))).lastFlat
    (fc.apply (chainOf [1]) (.explicit ({ tol := Tol.toStep 6, skip := 0 } : ExplicitIntegrator 4))).lastFlat
  -- accessors
  match odesolve ⟨lorenzFlow.withDuration 1, chaosStart, 0⟩ (.explicit ({ tol := h8, skip := 16 } : ExplicitIntegrator 4)) with
  | .path s =>
    let F := s.field
    checkEq "Solution.field length" F.length s.length
    checkBits "Solution.stateAt = field fiber" (toFlat (s.stateAt 5)) (toFlat (F.get 5))
    checkEq "Solution.timeAt" (s.timeAt 5) (5 * 16 * h8)
    checkEq "Result.localTensor time" (Result.path s).localTensor.base 1
  | .final .. => check "path" false
  let it := lorenzFlow.withDuration 0.25 |>.iterate chaosStart 3
  checkEq "Flow.iterate size" it.size 3
  checkBits "Flow.iterate second" (toFlat it[1]!) ((lorenzFlow.withDuration 0.25).apply chaosStart (FlowTests.rk 4)).lastFlat
  -- geosolve keeps the positions of the phase trajectory
  let ic := geodesic halfPlane (chainOf [1, 1]) (chainOf [1, 2]) 1
  let I := Integrator.explicit ({ tol := Tol.toStep 7 } : ExplicitIntegrator 4)
  match odesolve ic I with
  | .path s =>
    let g := geosolve ic I
    checkBits "geosolve = positions" (sub g.data (7 * 2) 2) (sub s.data (7 * 4) 2)
  | .final .. => check "geodesic path" false

/-- Run the property checks. -/
def run : TestM Unit := do
  runSkips
  runAdaptiveEnd
  runOrders
  runFieldFlow
  runApi

end Tests.AdapodeTests.Props

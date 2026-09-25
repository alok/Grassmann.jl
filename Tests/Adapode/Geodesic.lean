import Tests.Adapode.Chaos

/-!
# Geodesics and leapfrog against Julia (`geodesic.json`, `leapfrog.json`, `runtests.json`)

* The five geodesics of the upper half plane of the README, `geosolve(halfplane, x0, v0, 10π, 7)`
  (RK4, `h = 2^-7`, 4022 points): count, last time, every 64-th position, the last one, and the whole
  curve (`digest`); the end point also lies on the analytic semicircle.
* `LeapIntegrator{1}` and `{2}` on `u' = K u` / `u'' = -K u` (`K = tridiag(-1, 2, -1)`) for a state
  that is a `TensorField` over `1:3`: every stored state and the time axis.
* `test/runtests.jl`: `odesolve(Lorenz, x0, 2π, 7, Val(k), Val(4))` for `k = 0 … 4` (the adaptive
  ones with Julia's end of integration, `compat`).
-/

open Lean Tests.Small JuliaBase Adapode Grassmann DirectSum StaticVectors Cartan

namespace Tests.AdapodeTests.Geodesics

/-- `10π` (Julia `10pi`). -/
def tenPi : Float := 10 * piF

/-- The geodesic checks. -/
def runGeodesics : TestM Unit := do
  let j ← load "geodesic"
  for c in ← gArr j "cases" do
    let x0 ← gFloatsAt c "x0"
    let v0 ← gFloatsAt c "v0"
    let label := s!"geodesic x0={x0.toList.map fmt} v0={v0.toList.map fmt}"
    let s := geosolveCode halfPlane (chainOf x0.toList) (chainOf v0.toList) tenPi 7
    let n ← gNat c "n"
    checkEq s!"{label} n" s.length n
    checkFloat s!"{label} tlast" s.lastTime (← jField c "tlast")
    checkBits s!"{label} every 64" (every s.data 2 64) (← gFloatsAt c "every64")
    checkBits s!"{label} last" (s.flatAt (n - 1)) (← gFloatsAt c "last")
    checkEq s!"{label} digest" (digest (timesOf s) s.data) (← gStr c "digest")
    let xe ← gFloatAt c "analytic_endpoint_x"
    -- the curve approaches the real axis at the semicircle's end point
    let xl := (s.flatAt (n - 1)).get! 0
    check s!"{label} analytic end" ((xl - xe).abs < 3e-5) fun _ => s!"{fmt xl} vs {fmt xe}"

/-- `-(K v)` with `K = tridiag(-1, 2, -1)` (Julia `-(K*collect(localfiber(v)))`: each row summed
left to right, then negated). -/
def leapK (v : FloatArray) : FloatArray :=
  let row (a b c : Float) : Float := -((a * v.get! 0 + b * v.get! 1) + c * v.get! 2)
  ⟨#[row 2 (-1) 0, row (-1) 2 (-1), row 0 (-1) 2]⟩

/-- The state space of the leapfrog test: a field over the integers `1:3`. -/
abbrev LeapBase := GridBundle.ofAxis (Axis.unitRange 1 3)

/-- A field over `1:3` from three floats. -/
def leapField (xs : FloatArray) : TensorField LeapBase Float := TensorField.ofFn LeapBase fun i => xs.get! i

/-- The leapfrog checks. -/
def runLeap : TestM Unit := do
  let j ← load "leapfrog"
  let u0 := leapField (← gFloatsAt j "u0")
  let u1 := leapField (← gFloatsAt j "u1")
  let fp : Flow (TensorField LeapBase Float) := .of fun v => leapField (leapK v.data)
  for c in ← gArr j "cases" do
    let o ← gNat c "order"
    let dt ← gFloatAt c "dt"
    let tmax ← gFloatAt c "tmax"
    let gap ← gNat c "gap"
    let label := s!"Leap{o} dt={fmt dt} tmax={fmt tmax} gap={gap}"
    let ic := LeapCondition.ofStep (fp.withDuration tmax) u0 u1 dt
    let s := if o == 1 then leapsolve ic ({ skip := gap } : LeapIntegrator 1)
      else leapsolve ic ({ skip := gap } : LeapIntegrator 2)
    let data ← gFloatsAt c "data"
    checkBits s!"{label} data" s.data data
    -- Julia labels the `nplots + 1` stored states with the range `t₁ : dt·gap : t₁ + tmax`, which is
    -- one point short when `tmax/(dt·gap)` rounds up (B8: `size` then disagrees with the data);
    -- the port's axis has one time per state and agrees with Julia's range where it exists
    checkEq s!"{label} one time per state" s.length (data.size / 3)
    let jt ← gFloatsAt c "times"
    let size ← (← gArr c "size").mapM jNat
    checkEq s!"{label} Julia size = its range" size[1]! jt.size
    checkBits s!"{label} times" (sub (timesOf s) 0 jt.size) jt

/-- The `test/runtests.jl` checks. -/
def runRuntests : TestM Unit := do
  let j ← load "runtests"
  for c in ← gArr j "cases" do
    let k ← gNat c "k"
    let I := match k with
      | 0 => Integrator.eulerHeun { tol := Tol.toStep 7 }
      | 1 => .explicit ({ tol := Tol.toStep 7 } : ExplicitIntegrator 4)
      | 2 => .explicitAdaptor ({ tol := Tol.toStep 7, compat := true } : ExplicitAdaptor 4)
      | 3 => .multistep ({ tol := Tol.toStep 7 } : MultistepIntegrator 4)
      | _ => .multistepAdaptor ({ tol := Tol.toStep 7, compat := true } : MultistepAdaptor 4)
    let (ts, xs) := Chaos.flatOf (odesolve ⟨lorenzFlow, chaosStart, 0⟩ I)
    let n ← gNat c "n"
    let label := s!"runtests k={k}"
    checkEq s!"{label} n" ts.size n
    checkFloat s!"{label} tlast" (ts.get! (n - 1)) (← jField c "tlast")
    checkBits s!"{label} last" (sub xs ((n - 1) * 3) 3) (← gFloatsAt c "last")
    checkEq s!"{label} digest" (digest ts xs) (← gStr c "digest")
  -- `odesolve(f, x0, tmax, tol, m, o)` builds the same integrators (without Julia's B2)
  checkBits "odesolveCode RK4" (odesolveCode lorenzFn chaosStart twoPi 7 1 4).lastFlat
    (odesolve ⟨lorenzFlow, chaosStart, 0⟩ (.explicit ({ tol := Tol.toStep 7 } : ExplicitIntegrator 4))).lastFlat

/-- Run the geodesic, leapfrog and runtests checks. -/
def run : TestM Unit := do
  runGeodesics
  runLeap
  runRuntests

end Tests.AdapodeTests.Geodesics

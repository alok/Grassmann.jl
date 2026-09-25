import Adapode.ODE.Adaptive

/-!
# Leapfrog and Störmer–Verlet (`LeapIntegrator{o}`)

Julia's `odesolve(ic::LeapCondition, I::LeapIntegrator, bc)` (`src/Adapode.jl:648-675`), with two
consecutive states `vold` (at `t₀`) and `v` (at `t₁`), `dt = t₁ - t₀`:

```
LeapIntegrator{1}:  v' = vold - (2dt) fprime(v)                 (u' = -fprime(u))
LeapIntegrator{2}:  v' = (2v - vold) + dt² fprime(v)            (u'' = fprime(u))
```

`gap = I.skip` steps are taken per stored state, `nplots = round(tmax/(dt·gap))` states are stored
after the initial `v`, and the step is recomputed as `dt = (dt·gap)/gap`. `bc` is applied to both
initial states and after every step. Julia labels the output with the range
`t₁ : dt·gap : t₁ + tmax`, whose length can differ from `nplots + 1` when the division rounds up
(B8); here the time axis has exactly `nplots + 1` points `t₁ + j·dt·gap` (Julia's
`range(t₁; step, length)`), which is Julia's range whenever that has the right length.
-/

namespace Adapode

open JuliaBase Cartan

/-- The leapfrog loop: `m` steps remain in the current gap, `j` states are stored; `(vold, v)` are
the last two states, `w` scratch for the next one. -/
@[specialize] def leapRun (f : FlatSystem) (bc : FloatArray → FloatArray) (order2 : Bool) (d gap : Nat)
    (dt t1 tplot : Float) :
    (fuel m j : Nat) → (t : Float) → (vold v w kb out : FloatArray) → FlatRun
  | 0, _, _, t, _, v, _, _, out => ⟨t, v, out⟩
  | fuel + 1, m, j, t, vold, v, w, kb, out =>
    let kb := f dt t v kb
    let w := bc (if order2 then leap2Loop dt vold v kb d 0 w else leap1Loop dt vold kb d 0 w)
    let t := t + dt
    if m ≤ 1 then
      let out := copyInto out (j * d) d w
      leapRun f bc order2 d gap dt t1 tplot fuel gap (j + 1) t v w vold kb out
    else leapRun f bc order2 d gap dt t1 tplot fuel (m - 1) j t v w vold kb out
where
  /-- `w[j] := vold[j] - (2dt) K[j]` (Julia `localfiber(vold) - 2dt*fprime(v)`). -/
  leap1Loop (dt : Float) (vold K : FloatArray) : (n j : Nat) → FloatArray → FloatArray
    | 0, _, w => w
    | n + 1, j, w => leap1Loop dt vold K n (j + 1) (w.set! j (vold.get! j - (f64! 2 * dt) * K.get! j))
  /-- `w[j] := (2 v[j] - vold[j]) + dt² K[j]` (Julia `2localfiber(v) - localfiber(vold) + dt^2*fprime(v)`). -/
  leap2Loop (dt : Float) (vold v K : FloatArray) : (n j : Nat) → FloatArray → FloatArray
    | 0, _, w => w
    | n + 1, j, w =>
      leap2Loop dt vold v K n (j + 1) (w.set! j ((f64! 2 * v.get! j - vold.get! j) + (dt * dt) * K.get! j))

/-- The time axis of a leapfrog run: Julia's `t₁ : dt·gap : t₁ + tmax` when it has the `nplots + 1`
points of the data, else (B8) `nplots + 1` points `t₁ + j·(dt·gap)` (`range(t₁; step, length)`). -/
def leapAxis (t1 step tmax : Float) (nplots : Nat) : Axis :=
  let r := JuliaBase.colon t1 step (t1 + tmax)
  if r.len == nplots + 1 then .stepLen r else .stepLen (JuliaBase.rangeStep t1 step (nplots + 1))

/-- Leapfrog (`order2 = false`) or Störmer–Verlet (`order2 = true`) from `(t0, x0)`, `(t1, x1)` over
`tmax` with `gap` steps per stored state: the stored states (`nplots + 1`, the first `bc(x1)`) and
their time axis. -/
@[inline] def leapSolve (f : FlatSystem) (bc : FloatArray → FloatArray) (order2 : Bool) (d gap : Nat)
    (x0 x1 : FloatArray) (t0 t1 tmax : Float) : FlatRun × Axis :=
  let vold := bc (copyInto (zeros d) 0 d x0)
  let v := bc (copyInto (zeros d) 0 d x1)
  let gapF := gap.toUInt64.toFloat
  let tplot := (t1 - t0) * gapF
  let nplots := (roundSteps (tmax / tplot)).toNat
  let dt := tplot / gapF
  let out := copyInto (zeros ((nplots + 1) * d)) 0 d v
  let run := if nplots == 0 || gap == 0 then ⟨t1, v, out⟩ else
    leapRun f bc order2 d gap dt t1 tplot (nplots * gap) gap 1 t1 vold v (zeros d) (zeros d) out
  (run, leapAxis t1 (dt * gapF) tmax nplots)

end Adapode

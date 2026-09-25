import Adapode.ODE.Flow

/-!
# Fixed-step explicit integration: Runge–Kutta and Heun

Julia's `ExplicitIntegrator{o}` and `EulerHeunIntegrator` drivers (`odesolve`,
`src/Adapode.jl:483-520`) on flat states (`Adapode.ODE.State`).

**One step** (`butcher` + `explicit`, `Adapode.jl:234-293`): with stage rows `aₗ` and weights `b`,

```
K₀ = f(t ↦ x)
Kₗ = f((t + h·sum(aₗ)) ↦ (x + weights(h*aₗ, K₀ … K_{l-1})))      l = 1 … s-1
x' = x + weights(h*b, K₀ … K_{s-1})
```

and Heun's (`heun`, `Adapode.jl:243-246`) is `x + (h K₀ + h f((t+h) ↦ (x + h K₀)))/2`.
Order 1 (`explicit(x,f,h,Val(1)) = x + h f(x)`) is the generic step with `CB[1]` (`h·1 = h`).

**Output** (`initsteps`, `Adapode.jl:332-340`):

* `skip = 0`: `n = round((tmax - t₀)/h)` steps (ties to even) of `sign(n)·h` (so a negative duration
  integrates backwards), the time accumulated by addition; the result is the final `t ↦ x`.
* `skip = 1`: the grid `t₀:h:tmax` (Julia's `StepRangeLen`, `JuliaBase.colon`); point `i` is one
  step from point `i-1` at its grid time.
* `skip = k`: the grid `t₀:(h·k):tmax`; each stored point is `k` steps of `h` from the previous
  one, the inner times accumulated from its grid time.

`bc` (Julia's boundary hook, default `identity`) is applied to the initial state and after every
step.

**The loop** is one tail-recursive function over (point, inner step, stage) with the stage
workspace in flat arrays, so a step allocates nothing (a loop returning several arrays would box
them into a tuple per step).
-/

namespace Adapode

open JuliaBase Cartan

/-- The result of a flat integration: the final time and state, and the trajectory buffer (`n·d`
floats, point-major; empty when nothing is stored). -/
structure FlatRun where
  /-- Final time. -/
  t : Float
  /-- Final state. -/
  x : FloatArray
  /-- Stored states. -/
  out : FloatArray
  deriving Inhabited

/-- Julia's output grid `tmin:h*skip:tmax` (`initsteps`, `Adapode.jl:335`), bit-exact
(`JuliaBase.colon`). -/
def outputGrid (t0 h tmax : Float) (skip : Nat) : StepRangeLen :=
  JuliaBase.colon t0 (h * skip.toUInt64.toFloat) tmax

/-- Julia `Int(round(x))` for step counts: round half to even. -/
@[inline] def roundSteps (x : Float) : Int := F64.roundInt x

/-- The explicit Runge–Kutta / Heun machine: stage `l` of inner step `inner` of segment `seg`
(segment `seg` goes from stored point `seg` to `seg + 1`, `k` inner steps each). Stage workspace:
`ks` (stage derivatives, stage-major), `kb` (the system's scratch output), `y` (stage state).
`heun` selects Heun's final combination (the tableau is then `a = [[1]]`). -/
@[specialize] def rkRun (f : FlatSystem) (bc : FloatArray → FloatArray)
    (a c b : FloatArray) (s d : Nat) (heun : Bool) (h : Float) (r : StepRangeLen) (k nseg : Nat)
    (store : Bool) :
    (fuel seg inner l : Nat) → (t : Float) → (x y kb ks out : FloatArray) → FlatRun
  | 0, _, _, _, t, x, _, _, _, out => ⟨t, x, out⟩
  | fuel + 1, seg, inner, l, t, x, y, kb, ks, out =>
    if l == 0 then
      let kb := f h t x kb
      rkRun f bc a c b s d heun h r k nseg store fuel seg inner 1 t x y kb (copyInto ks 0 d kb) out
    else if l < s then
      let y := if heun then eulerLoop h ks 0 x d 0 y else comb h a (l * (l - 1) / 2) ks x d l y
      let kb := f h (t + h * c.get! l) y kb
      rkRun f bc a c b s d heun h r k nseg store fuel seg inner (l + 1) t x y kb
        (copyInto ks (l * d) d kb) out
    else
      let x' := bc (if heun then heunLoop h ks x d d 0 y else comb h b 0 ks x d s y)
      let t := t + h
      if inner ≤ 1 then
        let out := if store then copyInto out ((seg + 1) * d) d x' else out
        if seg + 1 < nseg then
          rkRun f bc a c b s d heun h r k nseg store fuel (seg + 1) k 0 (Axis.stepLenGet r (seg + 1))
            x' x kb ks out
        else ⟨t, x', out⟩
      else rkRun f bc a c b s d heun h r k nseg store fuel seg (inner - 1) 0 t x' x kb ks out

/-- Heun's method as a tableau for `rkRun` (`a = [[1]]`, stage time `t + h`). -/
def heunTableau : Tableau := .ofQ heunEuler

/-- Fixed-step explicit integration of `d`-dimensional flat states from `(t0, x0)` to `tmax` with
step `h` and stride `skip` (see the module doc): the final state, and for `skip ≥ 1` the stored
states on `outputGrid t0 h tmax skip`. `inner` is the number of steps per stored point for
`skip ≥ 1` (Julia: `skip`; Heun as Julia runs it, B7: `1`). -/
@[inline] def rkSolve (f : FlatSystem) (bc : FloatArray → FloatArray) (T : Tableau) (heun : Bool)
    (d : Nat) (x0 : FloatArray) (t0 h tmax : Float) (skip inner : Nat) : FlatRun :=
  let s := T.s
  let x := bc (copyInto (zeros d) 0 d x0)
  if skip == 0 then
    let n := roundSteps ((tmax - t0) / h)
    let steps := n.natAbs
    let hs := if n < 0 then -h else if n > 0 then h else 0
    if steps == 0 then ⟨t0, x, .empty⟩
    else
      rkRun f bc T.a T.c T.b s d heun hs default steps 1 false (steps * (s + 1) + 1) 0 steps 0 t0 x
        (zeros d) (zeros d) (zeros (s * d)) .empty
  else
    let r := outputGrid t0 h tmax skip
    let n := r.len
    let out := copyInto (zeros (n * d)) 0 d x
    if n ≤ 1 then ⟨t0, x, out⟩
    else
      rkRun f bc T.a T.c T.b s d heun h r inner (n - 1) true ((n - 1) * inner * (s + 1) + 1) 0 inner 0
        (Axis.stepLenGet r 0) x (zeros d) (zeros d) (zeros (s * d)) out

end Adapode

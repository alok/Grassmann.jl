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

**The loops** are single tail-recursive functions (Runge–Kutta over point, inner step and stage;
Heun over point and inner step) with the stage workspace in flat arrays, so a step allocates
nothing with an in-place system (a loop returning several arrays would box them into a tuple per
step). Heun writes its two derivatives into their own buffers; Runge–Kutta copies each derivative
into the stage-major workspace that the unrolled combinations (`linComb`) read. The grid times
are Julia's range elements (`rangeAt`), computed with the index conversion in `Float`.
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

/-- The explicit Runge–Kutta machine: stage `l` of inner step `inner` of segment `seg` (segment
`seg` goes from stored point `seg` to `seg + 1`, `k` inner steps each). Stage workspace: `ks`
(stage derivatives, stage-major), `kb` (the system's scratch output), `y` (stage state). The grid
time of point `i` is `rangeAt r offF i`. -/
@[specialize] def rkRun (f : FlatSystem) (bc : FloatArray → FloatArray)
    (a c b : FloatArray) (s d : Nat) (h : Float) (r : StepRangeLen) (offF : Float) (k nseg : Nat)
    (store : Bool) :
    (fuel seg inner l : Nat) → (t : Float) → (x y kb ks out : FloatArray) → FlatRun
  | 0, _, _, _, t, x, _, _, _, out => ⟨t, x, out⟩
  | fuel + 1, seg, inner, l, t, x, y, kb, ks, out =>
    if l == 0 then
      let kb := f h t x kb
      rkRun f bc a c b s d h r offF k nseg store fuel seg inner 1 t x y kb (copyInto ks 0 d kb) out
    else if l < s then
      let y := comb h a (l * (l - 1) / 2) ks x d l y
      let kb := f h (t + h * c.get! l) y kb
      rkRun f bc a c b s d h r offF k nseg store fuel seg inner (l + 1) t x y kb
        (copyInto ks (l * d) d kb) out
    else
      let x' := bc (comb h b 0 ks x d s y)
      let t := t + h
      if inner ≤ 1 then
        let out := if store then copyInto out ((seg + 1) * d) d x' else out
        if seg + 1 < nseg then
          rkRun f bc a c b s d h r offF k nseg store fuel (seg + 1) k 0 (rangeAt r offF (seg + 1))
            x' x kb ks out
        else ⟨t, x', out⟩
      else rkRun f bc a c b s d h r offF k nseg store fuel seg (inner - 1) 0 t x' x kb ks out

/-- Heun's machine (`heun`, `Adapode.jl:243-246`), one step per iteration: `K₁ = f(t ↦ x)`,
`K₂ = f((t+h) ↦ (x + hK₁))`, `x' = x + (hK₁ + hK₂)/2`. Each derivative is written into its own
buffer (no copies). -/
@[specialize] def heunRun (f : FlatSystem) (bc : FloatArray → FloatArray) (d : Nat) (h : Float)
    (r : StepRangeLen) (offF : Float) (k nseg : Nat) (store : Bool) :
    (fuel seg inner : Nat) → (t : Float) → (x y k1 k2 out : FloatArray) → FlatRun
  | 0, _, _, t, x, _, _, _, out => ⟨t, x, out⟩
  | fuel + 1, seg, inner, t, x, y, k1, k2, out =>
    let k1 := f h t x k1
    let y := eulerLoop h k1 0 x d 0 y
    let k2 := f h (t + h) y k2
    let x' := bc (heunLoop h k1 k2 x d 0 y)
    let t := t + h
    if inner ≤ 1 then
      let out := if store then copyInto out ((seg + 1) * d) d x' else out
      if seg + 1 < nseg then
        heunRun f bc d h r offF k nseg store fuel (seg + 1) k (rangeAt r offF (seg + 1)) x' x k1 k2 out
      else ⟨t, x', out⟩
    else heunRun f bc d h r offF k nseg store fuel seg (inner - 1) t x' x k1 k2 out

/-- The step count of Julia's `skip = 0` path: `n = round((tmax - t₀)/h)` (ties to even), taken as
`|n|` steps of `sign(n)·h`. -/
@[inline] def finalSteps (t0 h tmax : Float) : Nat × Float :=
  let n := roundSteps ((tmax - t0) / h)
  (n.natAbs, if n < 0 then -h else if n > 0 then h else 0)

/-- Fixed-step explicit Runge–Kutta integration with the tableau `T` of `d`-dimensional flat states
from `(t0, x0)` to `tmax` with step `h` and stride `skip` (see the module doc): the final state,
and for `skip ≥ 1` the stored states on `outputGrid t0 h tmax skip`, `inner` steps per stored
point. -/
@[inline] def rkSolve (f : FlatSystem) (bc : FloatArray → FloatArray) (T : Tableau) (d : Nat)
    (x0 : FloatArray) (t0 h tmax : Float) (skip inner : Nat) : FlatRun :=
  let s := T.s
  let x := bc (copyInto (zeros d) 0 d x0)
  if skip == 0 then
    let (steps, hs) := finalSteps t0 h tmax
    if steps == 0 then ⟨t0, x, .empty⟩
    else
      rkRun f bc T.a T.c T.b s d hs default 0 steps 1 false (steps * (s + 1) + 1) 0 steps 0 t0 x
        (zeros d) (zeros d) (zeros (s * d)) .empty
  else
    let r := outputGrid t0 h tmax skip
    let offF := rangeOffset r
    let n := r.len
    let out := copyInto (zeros (n * d)) 0 d x
    if n ≤ 1 then ⟨t0, x, out⟩
    else
      rkRun f bc T.a T.c T.b s d h r offF inner (n - 1) true ((n - 1) * inner * (s + 1) + 1) 0 inner 0
        (rangeAt r offF 0) x (zeros d) (zeros d) (zeros (s * d)) out

/-- Fixed-step Heun integration (as `rkSolve`; `inner` is `skip`, or `1` for Julia's B7). -/
@[inline] def heunSolve (f : FlatSystem) (bc : FloatArray → FloatArray) (d : Nat) (x0 : FloatArray)
    (t0 h tmax : Float) (skip inner : Nat) : FlatRun :=
  let x := bc (copyInto (zeros d) 0 d x0)
  if skip == 0 then
    let (steps, hs) := finalSteps t0 h tmax
    if steps == 0 then ⟨t0, x, .empty⟩
    else
      heunRun f bc d hs default 0 steps 1 false (steps + 1) 0 steps t0 x (zeros d) (zeros d) (zeros d)
        .empty
  else
    let r := outputGrid t0 h tmax skip
    let offF := rangeOffset r
    let n := r.len
    let out := copyInto (zeros (n * d)) 0 d x
    if n ≤ 1 then ⟨t0, x, out⟩
    else
      heunRun f bc d h r offF inner (n - 1) true ((n - 1) * inner + 1) 0 inner (rangeAt r offF 0) x
        (zeros d) (zeros d) (zeros d) out

end Adapode

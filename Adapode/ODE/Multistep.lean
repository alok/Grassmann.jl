import Adapode.ODE.Explicit

/-!
# Fixed-step Adams–Bashforth–Moulton (`MultistepIntegrator{o}`)

Julia's `odesolve(ic, ::MultistepIntegrator{o})` (`src/Adapode.jl:529-562`), with
`predictcorrect` (306-320), `multistep!` (298-305) and the bootstrap `initsteps!` (378-398).

**PECE of order `o`** with a ring of `o + 1` derivative slots `F` and a 1-based slot pointer `s`:

```
F[s] = f(tᵢ ↦ xᵢ)
p    = xᵢ + weights(h*CAB[o], F[ring(s)])     -- the o newest slots ending at s, oldest first
s    = s mod (o+1) + 1
F[s] = f((tᵢ+h) ↦ p)
xᵢ₊₁ = bc(xᵢ + weights(h*CAM[o], F[ring(s)]))
```

`F[s]` (the derivative at the predictor) is overwritten by `f(xᵢ₊₁)` at the next step. Order 1 is
Julia's special case `x + h f((t+h) ↦ (x + h f(t ↦ x)))` (Euler predictor, one backward-Euler
correction). For `o ≥ 2` the first `o - 1` states come from **RK4** whatever `o` is
(`initsteps!` uses `CB[4]`), with the bootstrap times accumulated by addition from `t₀` and no `bc`;
the derivative at each bootstrap state fills `F[1 … o-1]` (it is the first RK4 stage, evaluated
once here, twice in Julia: same values). Then `s = o`.

**Times.** For `skip = 1` the multistep steps read the grid time of the current point (as
`extract(x, t.i)` does); inside `skip = k` segments and for `skip = 0` times accumulate by
addition (`skip = 0` steps with `sign(n)·h`).

**Julia defects** (port notes B3, B4): with `skip = 0` Julia computes the bootstrap history but
restarts from `x₀` with the clock at `t₀ + (o-1)h` (`abmCompatFinal` reproduces it for
`compat := true`); with `skip > 1` it returns uninitialized states. Here both return the states of
the `skip = 1` recursion.
-/

namespace Adapode

open JuliaBase Cartan

/-- The Adams–Bashforth–Moulton machine. Phases `0 … 4`: an RK4 bootstrap step (stages `0 … 3`,
then the new state; `boot` bootstrap steps remain); phase `5`: one predictor–corrector step.
`gridTimes`: the multistep steps take the grid time of the segment's first point (`skip = 1`). -/
@[specialize] def abmRun (f : FlatSystem) (bc : FloatArray → FloatArray)
    (a4 c4 b4 cab cam : FloatArray) (o d : Nat) (h : Float) (r : StepRangeLen) (offF : Float)
    (k nseg : Nat) (store : Bool) :
    (fuel seg inner phase boot s : Nat) → (t : Float) → (x y kb ks F out : FloatArray) → FlatRun
  | 0, _, _, _, _, _, t, x, _, _, _, _, out => ⟨t, x, out⟩
  | fuel + 1, seg, inner, phase, boot, s, t, x, y, kb, ks, F, out =>
    if phase < 5 then
      if phase == 0 then
        let kb := f h t x kb
        let ks := copyInto ks 0 d kb
        let F := copyInto F ((o - 1 - boot) * d) d kb
        abmRun f bc a4 c4 b4 cab cam o d h r offF k nseg store fuel seg inner 1 boot s t x y kb ks F out
      else if phase < 4 then
        let y := comb h a4 (phase * (phase - 1) / 2) ks x d phase y
        let kb := f h (t + h * c4.get! phase) y kb
        abmRun f bc a4 c4 b4 cab cam o d h r offF k nseg store fuel seg inner (phase + 1) boot s t x y kb
          (copyInto ks (phase * d) d kb) F out
      else
        -- a bootstrap state (Julia `initsteps!`: no `bc`)
        let x' := comb h b4 0 ks x d 4 y
        let t := t + h
        let boot := boot - 1
        let phase' := if boot == 0 then 5 else 0
        let s := if boot == 0 then o else s
        if inner ≤ 1 then
          let out := if store then copyInto out ((seg + 1) * d) d x' else out
          if seg + 1 < nseg then
            abmRun f bc a4 c4 b4 cab cam o d h r offF k nseg store fuel (seg + 1) k phase' boot s t x' x kb
              ks F out
          else ⟨t, x', out⟩
        else
          abmRun f bc a4 c4 b4 cab cam o d h r offF k nseg store fuel seg (inner - 1) phase' boot s t x' x
            kb ks F out
    else
      -- one predictor–corrector step (order 1 through the same ring: `CAB[1] = CAM[1] = (1)`, and
      -- `(h·1)·K = h·K`, Julia's special case bit for bit)
      let t := if store && inner == k then rangeAt r offF seg else t
      let kb := f h t x kb
      let F := copyInto F ((s - 1) * d) d kb
      let y := adamsComb h cab F x o s d y
      let s := s % (o + 1) + 1
      let kb := f h (t + h) y kb
      let F := copyInto F ((s - 1) * d) d kb
      let x' := bc (adamsComb h cam F x o s d y)
      let t := t + h
      if inner ≤ 1 then
        let out := if store then copyInto out ((seg + 1) * d) d x' else out
        if seg + 1 < nseg then
          abmRun f bc a4 c4 b4 cab cam o d h r offF k nseg store fuel (seg + 1) k 5 boot s t x' x kb ks
            F out
        else ⟨t, x', out⟩
      else
        abmRun f bc a4 c4 b4 cab cam o d h r offF k nseg store fuel seg (inner - 1) 5 boot s t x' x kb ks F
          out

/-- Fixed-step ABM of order `o` (`1 ≤ o ≤ 5`) from `(t0, x0)` to `tmax` with step `h` and stride
`skip` (module doc). -/
@[inline] def abmSolve (f : FlatSystem) (bc : FloatArray → FloatArray) (o d : Nat) (x0 : FloatArray)
    (t0 h tmax : Float) (skip : Nat) : FlatRun :=
  let T := CB 4
  let x := bc (copyInto (zeros d) 0 d x0)
  let boot0 := if o ≤ 1 then 0 else o - 1
  let run (hs : Float) (r : StepRangeLen) (k nseg : Nat) (store : Bool) (t : Float) (out : FloatArray) :=
    let boot := Nat.min boot0 (k * nseg)
    abmRun f bc T.a T.c T.b (CAB o) (CAM o) o d hs r (rangeOffset r) k nseg store (5 * boot + k * nseg + 1) 0 k
      (if boot == 0 then 5 else 0) boot (if boot == 0 then o else 0) t x (zeros d) (zeros d)
      (zeros (4 * d)) (zeros ((o + 1) * d)) out
  if skip == 0 then
    let n := roundSteps ((tmax - t0) / h)
    let steps := n.natAbs
    let hs := if n < 0 then -h else if n > 0 then h else 0
    if steps == 0 then ⟨t0, x, .empty⟩ else run hs default steps 1 false t0 .empty
  else
    let r := outputGrid t0 h tmax skip
    let n := r.len
    let out := copyInto (zeros (n * d)) 0 d x
    if n ≤ 1 then ⟨t0, x, out⟩ else run h r skip (n - 1) true (rangeAt r (rangeOffset r) 0) out

/-- One RK4 step with allocation (for the compatibility path below). -/
@[specialize] def rk4Once (f : FlatSystem) (d : Nat) (h t : Float) (x : FloatArray) : FloatArray :=
  let T := CB 4
  (rkRun f id T.a T.c T.b T.s d h default 0 1 1 false (T.s + 2) 0 1 0 t
    (copyInto (zeros d) 0 d x) (zeros d) (zeros d) (zeros (T.s * d)) .empty).x

/-- The PECE steps of `abmCompatFinal`: `m` steps of `+h` from `(t, x)` with the ring `F` at slot
`s`; each result is labelled `lb + sh`, and the next step starts at that label. -/
@[specialize] def abmCompatLoop (f : FlatSystem) (bc : FloatArray → FloatArray) (o d : Nat)
    (h sh : Float) : (m s : Nat) → (t lb : Float) → (x F : FloatArray) → Float × FloatArray
  | 0, _, t, _, x, _ => (t, x)
  | m + 1, s, t, lb, x, F =>
    let lb := lb + sh
    if o == 1 then
      let k1 := f h t x (zeros d)
      let p := eulerLoop h k1 0 x d 0 (zeros d)
      let k2 := f h (t + h) p (zeros d)
      abmCompatLoop f bc o d h sh m s lb lb (bc (eulerLoop h k2 0 x d 0 (zeros d))) F
    else
      let F := copyInto F ((s - 1) * d) d (f h t x (zeros d))
      let p := adamsComb h (CAB o) F x o s d (zeros d)
      let s := s % (o + 1) + 1
      let F := copyInto F ((s - 1) * d) d (f h (t + h) p (zeros d))
      let c := adamsComb h (CAM o) F x o s d (zeros d)
      abmCompatLoop f bc o d h sh m s lb lb (bc c) F

/-- The RK4 bootstrap history of `abmCompatFinal`: `F[j] = f(tⱼ ↦ xⱼ)` along RK4 steps of `+h`
from `(t, x)`; the states themselves are dropped. -/
@[specialize] def abmCompatBoot (f : FlatSystem) (o d : Nat) (h : Float) :
    (j : Nat) → (t : Float) → (x F : FloatArray) → FloatArray
  | 0, _, _, F => F
  | j + 1, t, x, F =>
    let F := copyInto F ((o - 1 - (j + 1)) * d) d (f h t x (zeros d))
    abmCompatBoot f o d h j (t + h) (rk4Once f d h t x) F

/-- Julia's `skip = 0` multistep path as it runs (B3, `Adapode.jl:533-543` with the `LocalTensor`
`initsteps!`, 378-387): the RK4 bootstrap fills `F[1 … o-1]` from `(t₀, x₀)` but its states are
discarded; the multistep recursion starts again at `(t₀, x₀)`, always with the step `+h`, and its
`j`-th result is labelled `t₀ + (o-1)·sign(n)·h + j·sign(n)·h` (the next step starting at that
label). Julia gives `(t₀, x₀)` when `|n| < o`. -/
@[specialize] def abmCompatFinal (f : FlatSystem) (bc : FloatArray → FloatArray) (o d : Nat)
    (x0 : FloatArray) (t0 h tmax : Float) : Float × FloatArray :=
  let x := bc (copyInto (zeros d) 0 d x0)
  let n := roundSteps ((tmax - t0) / h)
  let sn : Int := if n < 0 then -1 else if n > 0 then 1 else 0
  let sh := Float.ofInt sn * h
  if n.natAbs < o then (t0, x)
  else
    let F := if o ≤ 1 then zeros ((o + 1) * d) else abmCompatBoot f o d h (o - 1) t0 x (zeros ((o + 1) * d))
    let pxi := t0 + Float.ofInt ((Int.ofNat o - 1) * sn) * h
    abmCompatLoop f bc o d h sh (n.natAbs + 1 - o) o t0 pxi x F

end Adapode

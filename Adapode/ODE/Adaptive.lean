import Adapode.ODE.Multistep

/-!
# Adaptive integration: embedded Runge–Kutta pairs and adaptive ABM

Julia's `ExplicitAdaptor{o}` and `MultistepAdaptor{o}` (`odesolve`, `src/Adapode.jl:521-528,
563-571`), driven by `timeloop!` (677-694) with the `TimeStep` controller (114-137) and stepped by
`explicit!` (427-435) and `predictcorrect!` (437-469). Port notes §4.3-4.4.

**Controller** (`timeloop!(x, t, tmax, Val(m))`, `m = 1` for Runge–Kutta, `m = o` for ABM), before
each step, with `e` the last error estimate:

```
e < emin  ⇒  h *= 2;  i -= ⌊m/2⌋;  s = 0         (grow; ABM drops ⌊o/2⌋ points)
e > emax  ⇒  h /= 2;  i -= ⌈m/2⌉;  s = 0         (reject; ABM drops ⌈o/2⌉ points)
s == 0    ⇒  clamp |h| into [hmin, hmax], i ≥ 1   (Runge–Kutta: every step)
```

(`e` starts at `(emin + emax)/2`). An embedded pair estimates `e = max |h (db · K)|` (absolute), the
multistep method `e = max |(c - p)/c|` (relative); an ABM whose history was invalidated (`s = 0`)
rebuilds it with `o - 1` RK4 steps at the new `h` (storing their points) before the next
predictor–corrector step.

**End of integration.** Julia stops once `d = tmax - tᵢ ≤ hmax`, without a last step, and then
truncates the output to `i - 1` points when the preallocated array is longer than `i` (B2): the
result ends in `[tmax - 2hmax, tmax - hmax)`. `compat := true` reproduces that, bit for bit with
the (time-storing) oracle, including the preallocation bookkeeping (`n = round((tmax - t₀)/h/skip)
+ 1` points, grown by `10000` as `resize!` does). The default ends exactly at `tmax`: the step
that would pass it is shortened to land on `tmax` (Runge–Kutta: an ordinary step of the pair, which
may still be rejected; ABM: one RK4 step), every accepted point is kept, and a step at `hmin` is
accepted rather than rejected forever. Both integrate forward (`tmax > t₀`; Julia's controller
takes `log2` of the step).
-/

namespace Adapode

open JuliaBase Cartan

/-- The result of an adaptive integration: `len` points, times `T` and flat states `X` (possibly
longer; the first `len` points are the result). -/
structure AdaptiveRun where
  /-- Number of points. -/
  len : Nat
  /-- Times. -/
  T : FloatArray
  /-- States, point-major. -/
  X : FloatArray
  deriving Inhabited

/-- Write the time of point `i` (overwrite, or append the next point). -/
@[inline] def writeTime (T : FloatArray) (i : Nat) (v : Float) : FloatArray :=
  if i < T.size then T.set! i v else T.push v

/-- Write the state of point `i` (overwrite, or append the next point). -/
@[inline] def writePoint (X : FloatArray) (i d : Nat) (x : FloatArray) : FloatArray :=
  if (i + 1) * d ≤ X.size then copyInto X (i * d) d x else appendLoop x d 0 X

/-- Julia `checkstep!` on the step: clamp `|h|` into `[hmin, hmax]` keeping its sign. -/
@[inline] def clampStep (h hmin hmax : Float) : Float :=
  let h := if h.abs < hmin then F64.copysign hmin h else h
  if h.abs > hmax then F64.copysign hmax h else h

/-- Julia `truncate!(x, t.i-1)` at the end (B2): `i - 1` points (1-based `i`) when the array holds
more than `i`, else all of them. Here `i` is 0-based. -/
@[inline] def compatLength (i cap : Nat) : Nat := if cap > i + 1 then i else i + 1

/-- Julia's preallocated length `Int(round((tmax - tmin)/h/skip)) + 1` (`initsteps`,
`Adapode.jl:334`). -/
@[inline] def initialCapacity (t0 h tmax : Float) (skip : Nat) : Nat :=
  (roundSteps ((tmax - t0) / h / skip.toUInt64.toFloat) + 1).toNat

/-! ## Embedded Runge–Kutta pairs -/

/-- The adaptive Runge–Kutta machine: phase `0` is the controller (`timeloop!`), phases `1 … s`
the stages, phase `s + 1` the new point and its error (`explicit!`). `i` is the 0-based index of
the current point (`x`, `t`), `cap` Julia's allocated length, `final` (default end rule) marks a
step shortened onto `tmax`. -/
@[specialize] def rkaRun (f : FlatSystem) (a c b db zero : FloatArray) (s d : Nat)
    (tmax hmin hmax emin emax : Float) (compat : Bool) :
    (fuel phase i cap : Nat) → (h e t : Float) → (final : Bool) → (x y kb ks z T X : FloatArray) →
      AdaptiveRun
  | 0, _, i, _, _, _, _, _, _, _, _, _, _, T, X => ⟨i + 1, T, X⟩
  | fuel + 1, phase, i, cap, h, e, t, final, x, y, kb, ks, z, T, X =>
    if phase == 0 then
      let h := if e < emin then h * f64! 2 else h
      let reject := e > emax && (compat || h.abs > hmin)
      let h := if reject then h / f64! 2 else h
      let i := if reject then i - 1 else i
      let h := clampStep h hmin hmax
      let x := if reject then loadFrom x X (i * d) d else x
      let t := if reject then T.get! i else t
      if compat then
        let dd := tmax - t
        let h := if dd ≤ h then dd else h
        if dd ≤ hmax then ⟨compatLength i cap, T, X⟩
        else
          let cap := if cap < i + 2 then i + 1 + 10000 else cap
          rkaRun f a c b db zero s d tmax hmin hmax emin emax compat fuel 1 i cap h e t final x y kb ks z T X
      else if final && !reject then ⟨i + 1, T, X⟩
      else
        let dd := tmax - t
        if dd ≤ 0 then ⟨i + 1, T, X⟩
        else
          let final := dd ≤ h
          let h := if final then dd else h
          rkaRun f a c b db zero s d tmax hmin hmax emin emax compat fuel 1 i cap h e t final x y kb ks z T X
    else if phase ≤ s then
      let l := phase - 1
      if l == 0 then
        let kb := f h t x kb
        rkaRun f a c b db zero s d tmax hmin hmax emin emax compat fuel 2 i cap h e t final x y kb
          (copyInto ks 0 d kb) z T X
      else
        let y := comb h a (l * (l - 1) / 2) ks x d l y
        let kb := f h (t + h * c.get! l) y kb
        rkaRun f a c b db zero s d tmax hmin hmax emin emax compat fuel (phase + 1) i cap h e t final x y kb
          (copyInto ks (l * d) d kb) z T X
    else
      let (e, z) := errEmbedded h db ks zero d s z
      let y := comb h b 0 ks x d s y
      let tn := if final then tmax else t + h
      let T := writeTime T (i + 1) tn
      let X := writePoint X (i + 1) d y
      rkaRun f a c b db zero s d tmax hmin hmax emin emax compat fuel 0 (i + 1) cap h e tn final y x kb ks z T X

/-- Adaptive Runge–Kutta with the pair `tab` from `(t0, x0)` towards `tmax`, initial step `h0`
(Julia `ExplicitAdaptor{o}(h0, skip)`; `skip` only sizes Julia's preallocation). -/
@[inline] def rkaSolve (f : FlatSystem) (tab : Tableau) (d : Nat) (x0 : FloatArray)
    (t0 h0 tmax : Float) (skip : Nat) (compat : Bool) : AdaptiveRun :=
  let ts := TimeStep.new h0 skip
  let x := copyInto (zeros d) 0 d x0
  let s := tab.s
  rkaRun f tab.a tab.c tab.b tab.db (zeros d) s d tmax ts.hmin ts.hmax ts.emin ts.emax compat (2 ^ 60) 0 0
    (initialCapacity t0 ts.h tmax skip) ts.h ts.e t0 false x (zeros d) (zeros d) (zeros (s * d)) (zeros d)
    (FloatArray.empty.push t0) (copyInto (zeros d) 0 d x0)

/-! ## Adaptive Adams–Bashforth–Moulton -/

/-- The adaptive ABM machine: phase `0` controller (`timeloop!` at `Val(o)`), phases `1 … 5` an
RK4 bootstrap step (stages, then the stored point; `boot` steps remain), `6` predictor, `7`
corrector and the new point (`predictcorrect!`). `s` is the 1-based ring slot (`0`: history
invalid). -/
@[specialize] def abmaRun (f : FlatSystem) (a4 c4 b4 cab cam : FloatArray) (o d : Nat)
    (tmax hmin hmax emin emax : Float) (compat : Bool) :
    (fuel phase i cap s boot : Nat) → (h e t : Float) → (final : Bool) →
      (x y z kb ks F T X : FloatArray) → AdaptiveRun
  | 0, _, i, _, _, _, _, _, _, _, _, _, _, _, _, _, T, X => ⟨i + 1, T, X⟩
  | fuel + 1, phase, i, cap, s, boot, h, e, t, final, x, y, z, kb, ks, F, T, X =>
    if phase == 0 then
      let grow := e < emin
      let h := if grow then h * f64! 2 else h
      let i := if grow then i - o / 2 else i
      let s := if grow then 0 else s
      let reject := e > emax && (compat || h.abs > hmin)
      let h := if reject then h / f64! 2 else h
      let i := if reject then i - (o + 1) / 2 else i
      let s := if reject then 0 else s
      let h := if s == 0 then clampStep h hmin hmax else h
      let moved := grow || reject
      let x := if moved then loadFrom x X (i * d) d else x
      let t := if moved then T.get! i else t
      let dd := tmax - t
      if compat then
        let h := if dd ≤ h then dd else h
        if dd ≤ hmax then ⟨compatLength i cap, T, X⟩
        else if o == 1 then
          abmaRun f a4 c4 b4 cab cam o d tmax hmin hmax emin emax compat fuel 6 i cap s boot h e t final
            x y z kb ks F T X
        else
          let cap := if cap < i + o + 2 then i + 1 + o + 10000 else cap
          if s == 0 then
            abmaRun f a4 c4 b4 cab cam o d tmax hmin hmax emin emax compat fuel 1 i cap s (o - 1) h e t
              final x y z kb ks F T X
          else
            abmaRun f a4 c4 b4 cab cam o d tmax hmin hmax emin emax compat fuel 6 i cap s boot h e t
              final x y z kb ks F T X
      else if dd ≤ 0 then ⟨i + 1, T, X⟩
      else if dd ≤ h then
        -- the last step: one RK4 step onto tmax
        abmaRun f a4 c4 b4 cab cam o d tmax hmin hmax emin emax compat fuel 1 i cap s 1 dd e t true
          x y z kb ks F T X
      else if o == 1 || s != 0 then
        abmaRun f a4 c4 b4 cab cam o d tmax hmin hmax emin emax compat fuel 6 i cap s boot h e t final
          x y z kb ks F T X
      else
        abmaRun f a4 c4 b4 cab cam o d tmax hmin hmax emin emax compat fuel 1 i cap s (o - 1) h e t
          final x y z kb ks F T X
    else if phase ≤ 5 then
      if phase == 1 then
        -- a bootstrap step; by default a step that would pass `tmax` is shortened onto it
        let dd := tmax - t
        let final := final || (!compat && dd ≤ h)
        let h := if !compat && dd ≤ h then dd else h
        let kb := f h t x kb
        let F := copyInto F ((o - 1 - boot) * d) d kb
        abmaRun f a4 c4 b4 cab cam o d tmax hmin hmax emin emax compat fuel 2 i cap s boot h e t final
          x y z kb (copyInto ks 0 d kb) F T X
      else if phase ≤ 4 then
        let l := phase - 1
        let y := comb h a4 (l * (l - 1) / 2) ks x d l y
        let kb := f h (t + h * c4.get! l) y kb
        abmaRun f a4 c4 b4 cab cam o d tmax hmin hmax emin emax compat fuel (phase + 1) i cap s boot h
          e t final x y z kb (copyInto ks (l * d) d kb) F T X
      else
        let y := comb h b4 0 ks x d 4 y
        let tn := if final then tmax else t + h
        let T := writeTime T (i + 1) tn
        let X := writePoint X (i + 1) d y
        if final then ⟨i + 2, T, X⟩
        else
          let boot := boot - 1
          if boot == 0 then
            abmaRun f a4 c4 b4 cab cam o d tmax hmin hmax emin emax compat fuel 6 (i + 1) cap o 0 h e tn
              final y x z kb ks F T X
          else
            abmaRun f a4 c4 b4 cab cam o d tmax hmin hmax emin emax compat fuel 1 (i + 1) cap s boot h e
              tn final y x z kb ks F T X
    else if phase == 6 then
      let kb := f h t x kb
      if o == 1 then
        abmaRun f a4 c4 b4 cab cam o d tmax hmin hmax emin emax compat fuel 7 i cap s boot h e t final
          x (eulerLoop h kb 0 x d 0 y) z kb ks F T X
      else
        let F := copyInto F ((s - 1) * d) d kb
        let y := adamsComb h cab F x o s d y
        abmaRun f a4 c4 b4 cab cam o d tmax hmin hmax emin emax compat fuel 7 i cap (s % (o + 1) + 1)
          boot h e t final x y z kb ks F T X
    else
      let kb := f h (t + h) y kb
      let tn := t + h
      let F := if o == 1 then F else copyInto F ((s - 1) * d) d kb
      -- the corrector into `z`, its gap to the predictor in `y`, then `z` is the new point
      let z := if o == 1 then eulerLoop h kb 0 x d 0 z else adamsComb h cam F x o s d z
      let e := relGapLoop z y d 0 0
      let cap := if o == 1 && cap < i + 3 then i + 2 + 10000 else cap
      let T := writeTime T (i + 1) tn
      let X := writePoint X (i + 1) d z
      abmaRun f a4 c4 b4 cab cam o d tmax hmin hmax emin emax compat fuel 0 (i + 1) cap s boot h e tn
        final z x y kb ks F T X

/-- Adaptive ABM of order `o` from `(t0, x0)` towards `tmax`, initial step `h0` (Julia
`MultistepAdaptor{o}(h0, skip)`). -/
@[inline] def abmaSolve (f : FlatSystem) (o d : Nat) (x0 : FloatArray) (t0 h0 tmax : Float)
    (skip : Nat) (compat : Bool) : AdaptiveRun :=
  let ts := TimeStep.new h0 skip
  let T4 := CB 4
  abmaRun f T4.a T4.c T4.b (CAB o) (CAM o) o d tmax ts.hmin ts.hmax ts.emin ts.emax compat (2 ^ 60) 0 0
    (initialCapacity t0 ts.h tmax skip) 0 0 ts.h ts.e t0 false (copyInto (zeros d) 0 d x0) (zeros d)
    (zeros d) (zeros d) (zeros (4 * d)) (zeros ((o + 1) * d)) (FloatArray.empty.push t0) (copyInto (zeros d) 0 d x0)

end Adapode

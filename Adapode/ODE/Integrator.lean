import Adapode.ODE.State

/-!
# Integrators and the time-step controller (`src/Adapode.jl:44-137`)

Julia's integrators are types carrying the step, the output stride and an unused `geo` flag
(`Adapode.jl:54-86`):

| Julia | Lean | method |
|---|---|---|
| `EulerHeunIntegrator(tol, skip)` | `EulerHeunIntegrator` | Heun's improved Euler |
| `ExplicitIntegrator{o}(tol, skip)`, `o ∈ 1:4` | `ExplicitIntegrator o` | explicit Runge–Kutta `CB[o]` |
| `ExplicitAdaptor{o}(tol, skip)`, `o ∈ 1:5` | `ExplicitAdaptor o` | embedded pair `CBA[o]` with step control |
| `MultistepIntegrator{o}(tol, skip)`, `o ∈ 1:5` | `MultistepIntegrator o` | Adams–Bashforth–Moulton PECE of order `o` |
| `MultistepAdaptor{o}(tol, skip)`, `o ∈ 1:5` | `MultistepAdaptor o` | the same with step control |
| `LeapIntegrator{o}(skip)`, `o ∈ 1:2` | `LeapIntegrator o` | leapfrog / Störmer–Verlet |
| `AbstractIntegrator` (`integrator`) | `Integrator` | any of the first five |

The order `o` is a type index, as in Julia, with its range as an erased proof field.

**`tol` is the step, not a tolerance** (port notes §2.2): `X{o}(tol::Int)` means `h = 2^-tol`
(`Adapode.jl:105-112`), `X{o}(tol::Float64)` is `h` itself; `Tol` keeps both spellings
(`(15 : Tol)` and `((2^-11 : Float) : Tol)`). `skip` is the output stride: `0` returns only the final
`t ↦ x`, `1` the whole trajectory, `k` every `k`-th state. The adaptive controller also derives
its bounds from `tol` (`TimeStep`, below).

**Julia defects** (port notes §8.6; `oracle/adapode/defects.toml`). The integrators implement the
intended semantics; `compat := true` reproduces Julia's behaviour where it is deterministic and the
goldens record it:

* B2 (adaptive): Julia stops once `tmax - t ≤ hmax` and then drops the last accepted point. Fixed:
  the last step lands on `tmax` and every accepted point is kept; `compat` reproduces the truncation
  (including its dependence on the preallocated length).
* B3 (`MultistepIntegrator`, `skip = 0`): Julia discards the bootstrapped states and restarts the
  multistep recursion from `x₀` with a shifted clock. Fixed: the final state of the same recursion
  as `skip = 1`; `compat` reproduces the discarded bootstrap.
* B4 (`MultistepIntegrator`, `skip > 1`): Julia returns uninitialized states. Fixed: every `skip`-th
  state of the `skip = 1` recursion (not reproducible, no `compat`).
* B7 (`EulerHeunIntegrator`, `skip > 1`): Julia takes one step of `h` per stored point of a grid of
  spacing `h·skip`. Fixed: `skip` steps per stored point; `compat` reproduces the single step.
  (Julia also throws for `skip = 0`; here it returns the final state.)
* B10: the Fehlberg and Cash–Karp tables have typos (`Adapode.Constants`); `ExplicitAdaptor`
  uses Julia's tables unless `fixed := true`.
* B20: `AbstractIntegrator()` with no arguments throws (its default is a type). `Integrator.default`
  is the intended `ExplicitIntegrator{4}(2^-15)`.
-/

namespace Adapode

open JuliaBase

/-- Julia's `tol` argument (`Adapode.jl:105-112`): an `Int` is the exponent of the step `2^-tol`,
a `Float64` is the step itself. -/
inductive Tol where
  /-- `tol::Int`: the step `2^-n`. -/
  | exp (n : Nat)
  /-- `tol::Float64`: the step. -/
  | step (h : Float)
  deriving Inhabited

instance {n : Nat} : OfNat Tol n := ⟨.exp n⟩
instance : Coe Float Tol := ⟨.step⟩

/-- The step `h` of a `Tol` (Julia `2.0^-tol`, exact). -/
def Tol.toStep : Tol → Float
  | .exp n => Float.scaleB 1 (-(n : Int))
  | .step h => h

/-- Julia `EulerHeunIntegrator(tol, skip)` (`Adapode.jl:54-58, 105-106`). -/
structure EulerHeunIntegrator where
  /-- The step `h`. -/
  tol : Float
  /-- Output stride (`0`: final state only). -/
  skip : Nat := 1
  /-- Reproduce Julia's single step per stored point for `skip > 1` (B7). -/
  compat : Bool := false
  deriving Inhabited

/-- Julia `ExplicitIntegrator{o}(tol, skip)` (`Adapode.jl:60-64`): `CB[o]` with a fixed step. -/
structure ExplicitIntegrator (o : Nat) where
  /-- The step `h`. -/
  tol : Float
  /-- Output stride (`0`: final state only). -/
  skip : Nat := 1
  /-- `o ∈ 1:4`. -/
  valid : 1 ≤ o ∧ o ≤ 4 := by decide

/-- Julia `ExplicitAdaptor{o}(tol, skip)` (`Adapode.jl:66-70`): the embedded pair `CBA[o]` with
Adapode's step control. -/
structure ExplicitAdaptor (o : Nat) where
  /-- The initial (and, above `1e-4`, maximal) step. -/
  tol : Float
  /-- Julia's stride; it only sets the preallocated length that `compat` truncation depends on. -/
  skip : Nat := 1
  /-- Reproduce Julia's end of integration (B2). -/
  compat : Bool := false
  /-- Use the corrected Fehlberg and Cash–Karp tables (B10). -/
  fixed : Bool := false
  /-- `o ∈ 1:5`. -/
  valid : 1 ≤ o ∧ o ≤ 5 := by decide

/-- Julia `MultistepIntegrator{o}(tol, skip)` (`Adapode.jl:72-76`): Adams–Bashforth–Moulton PECE
of order `o`, bootstrapped by RK4. -/
structure MultistepIntegrator (o : Nat) where
  /-- The step `h`. -/
  tol : Float
  /-- Output stride (`0`: final state only). -/
  skip : Nat := 1
  /-- Reproduce Julia's `skip = 0` path, which discards the bootstrap (B3). -/
  compat : Bool := false
  /-- `o ∈ 1:5`. -/
  valid : 1 ≤ o ∧ o ≤ 5 := by decide

/-- Julia `MultistepAdaptor{o}(tol, skip)` (`Adapode.jl:78-82`): adaptive PECE. -/
structure MultistepAdaptor (o : Nat) where
  /-- The initial (and, above `1e-4`, maximal) step. -/
  tol : Float
  /-- Julia's stride; it only sets the preallocated length that `compat` truncation depends on. -/
  skip : Nat := 1
  /-- Reproduce Julia's end of integration (B2). -/
  compat : Bool := false
  /-- `o ∈ 1:5`. -/
  valid : 1 ≤ o ∧ o ≤ 5 := by decide

/-- Julia `LeapIntegrator{o}(skip)` (`Adapode.jl:84-86, 104`): `o = 1` leapfrog for `u' = -f(u)`,
`o = 2` Störmer–Verlet for `u'' = f(u)`; `skip` steps per stored state. -/
structure LeapIntegrator (o : Nat) where
  /-- Steps per stored state (Julia `plotgap`). -/
  skip : Nat := 1
  /-- `o ∈ 1:2`. -/
  valid : 1 ≤ o ∧ o ≤ 2 := by decide

namespace EulerHeunIntegrator
/-- Julia `EulerHeunIntegrator(tol, skip=1)`. -/
def new (tol : Tol) (skip : Nat := 1) : EulerHeunIntegrator := { tol := tol.toStep, skip }
end EulerHeunIntegrator

namespace ExplicitIntegrator
/-- Julia `ExplicitIntegrator{o}(tol, skip=1)`. -/
def new (o : Nat) (tol : Tol) (skip : Nat := 1) (h : 1 ≤ o ∧ o ≤ 4 := by decide) :
    ExplicitIntegrator o := { tol := tol.toStep, skip, valid := h }
end ExplicitIntegrator

namespace ExplicitAdaptor
/-- Julia `ExplicitAdaptor{o}(tol, skip=1)`. -/
def new (o : Nat) (tol : Tol) (skip : Nat := 1) (h : 1 ≤ o ∧ o ≤ 5 := by decide) :
    ExplicitAdaptor o := { tol := tol.toStep, skip, valid := h }
end ExplicitAdaptor

namespace MultistepIntegrator
/-- Julia `MultistepIntegrator{o}(tol, skip=1)`. -/
def new (o : Nat) (tol : Tol) (skip : Nat := 1) (h : 1 ≤ o ∧ o ≤ 5 := by decide) :
    MultistepIntegrator o := { tol := tol.toStep, skip, valid := h }
end MultistepIntegrator

namespace MultistepAdaptor
/-- Julia `MultistepAdaptor{o}(tol, skip=1)`. -/
def new (o : Nat) (tol : Tol) (skip : Nat := 1) (h : 1 ≤ o ∧ o ≤ 5 := by decide) :
    MultistepAdaptor o := { tol := tol.toStep, skip, valid := h }
end MultistepAdaptor

/-- Julia `AbstractIntegrator` (`integrator`, `Adapode.jl:48-52`): any of the integrators of an
`InitialCondition`. -/
inductive Integrator where
  /-- `EulerHeunIntegrator`. -/
  | eulerHeun (i : EulerHeunIntegrator)
  /-- `ExplicitIntegrator{o}`. -/
  | explicit {o : Nat} (i : ExplicitIntegrator o)
  /-- `ExplicitAdaptor{o}`. -/
  | explicitAdaptor {o : Nat} (i : ExplicitAdaptor o)
  /-- `MultistepIntegrator{o}`. -/
  | multistep {o : Nat} (i : MultistepIntegrator o)
  /-- `MultistepAdaptor{o}`. -/
  | multistepAdaptor {o : Nat} (i : MultistepAdaptor o)

instance : Coe EulerHeunIntegrator Integrator := ⟨.eulerHeun⟩
instance {o : Nat} : CoeOut (ExplicitIntegrator o) Integrator := ⟨.explicit⟩
instance {o : Nat} : CoeOut (ExplicitAdaptor o) Integrator := ⟨.explicitAdaptor⟩
instance {o : Nat} : CoeOut (MultistepIntegrator o) Integrator := ⟨.multistep⟩
instance {o : Nat} : CoeOut (MultistepAdaptor o) Integrator := ⟨.multistepAdaptor⟩

namespace Integrator

/-- Julia `AbstractIntegrator(tol, m, o=4)` (`Adapode.jl:89-102`): `m = 0` Heun, `1` explicit RK,
`2` adaptive RK, `3` multistep, `4` adaptive multistep; `none` where Julia returns `nothing` or
fails on the order. -/
def ofCode (tol : Tol) (m : Nat) (o : Nat := 4) : Option Integrator :=
  let h := tol.toStep
  match m with
  | 0 => some (.eulerHeun { tol := h })
  | 1 => if hv : 1 ≤ o ∧ o ≤ 4 then some (.explicit ({ tol := h, valid := hv } : ExplicitIntegrator o)) else none
  | 2 => if hv : 1 ≤ o ∧ o ≤ 5 then some (.explicitAdaptor ({ tol := h, valid := hv } : ExplicitAdaptor o)) else none
  | 3 => if hv : 1 ≤ o ∧ o ≤ 5 then some (.multistep ({ tol := h, valid := hv } : MultistepIntegrator o)) else none
  | 4 => if hv : 1 ≤ o ∧ o ≤ 5 then some (.multistepAdaptor ({ tol := h, valid := hv } : MultistepAdaptor o)) else none
  | _ => none

/-- The intended default of Julia's `AbstractIntegrator(tol=15, int=ExplicitIntegrator{4})`
(`Adapode.jl:88`, which throws, B20): RK4 with `h = 2^-15`. -/
def default : Integrator := .explicit ({ tol := Tol.toStep 15 } : ExplicitIntegrator 4)

/-- The step (Julia `I.tol`). -/
def tol : Integrator → Float
  | eulerHeun i => i.tol
  | explicit i => i.tol
  | explicitAdaptor i => i.tol
  | multistep i => i.tol
  | multistepAdaptor i => i.tol

/-- The output stride (Julia `I.skip`). -/
def skip : Integrator → Nat
  | eulerHeun i => i.skip
  | explicit i => i.skip
  | explicitAdaptor i => i.skip
  | multistep i => i.skip
  | multistepAdaptor i => i.skip

end Integrator

/-! ## The time-step controller -/

/-- Julia `TimeStep{T}` (`Adapode.jl:114-137`): the controller state of the adaptive integrators.
`e` is the last error estimate, `i` the 1-based index of the current point, `s` the ring slot of an
adaptive multistep method (`0`: history invalid, bootstrap next). The error window `[emin, emax]`
is tied to the step: `emin = 10^(log₂ h - 3)`, `emax = 10^(log₂ h)` (a base-2 step against base-10
thresholds: `[1e-10, 1e-7]` for `h = 2^-7`). -/
structure TimeStep where
  /-- The step. -/
  h : Float
  /-- Julia's `skip` (only used for the preallocated length). -/
  skip : Nat := 1
  /-- Smallest step. -/
  hmin : Float
  /-- Largest step (`h₀` above `1e-4`, else `1e-4`: the step never grows past a large `h₀`). -/
  hmax : Float
  /-- Double the step below this error. -/
  emin : Float
  /-- Halve the step (and reject) above this error. -/
  emax : Float
  /-- The last error estimate. -/
  e : Float
  /-- The 1-based index of the current point. -/
  i : Nat := 1
  /-- The ring slot of an adaptive multistep method (`0`: rebuild the history). -/
  s : Nat := 0
  deriving Inhabited, Repr

namespace TimeStep

/-- Julia `checkstep!` (`Adapode.jl:132-137`): clamp `|h|` into `[hmin, hmax]` keeping its sign,
and `i ≥ 1`. -/
@[inline] def check (t : TimeStep) : TimeStep :=
  let h := if t.h.abs < t.hmin then F64.copysign t.hmin t.h else t.h
  let h := if h.abs > t.hmax then F64.copysign t.hmax h else h
  { t with h, i := if t.i < 1 then 1 else t.i }

/-- Julia `TimeStep(h, skip=1)` (`Adapode.jl:124-126`) with its defaults `hmin = 1e-16`,
`hmax = h > 1e-4 ? h : 1e-4`, `emin = 10^(log2(h)-3)`, `emax = 10^log2(h)`, `e = (emin+emax)/2`,
`i = 1`, `s = 0`, then `checkstep!`. -/
def new (h : Float) (skip : Nat := 1) : TimeStep :=
  let emin := F64.pow (f64! 10) (F64.log2 h - f64! 3)
  let emax := F64.pow (f64! 10) (F64.log2 h)
  check { h, skip, hmin := f64! 1e-16, hmax := if h > f64! 1e-4 then h else f64! 1e-4,
          emin, emax, e := (emin + emax) / f64! 2 }

end TimeStep

end Adapode

import Adapode.ODE.Integrator

/-!
# Flows and initial conditions (`src/Adapode.jl:139-220, 609-646`)

Julia's `Flow{F,N}` pairs a system `f` with a duration `t` (`Adapode.jl:143-157`). The system
receives the local tensor `t ↦ x` (time and state) and returns the derivative; a `FlowApprox`
(`N = 2`) system also receives the step, `f(x, h)`. An `InitialCondition` adds the starting state
(`Adapode.jl:205-219`), a `LeapCondition` two consecutive states for the leapfrog methods
(`Adapode.jl:626-646`).

Here a system is stored in the one form every integrator calls, `f h t x out`: the step `h`
(read only by `FlowApprox` systems), the time `t`, the state `x`, and a scratch state `out` of
the same size that the system may overwrite and return (destination passing: then an evaluation
allocates nothing) or ignore. The constructors cover Julia's spellings:

| Julia system | Lean |
|---|---|
| `x -> Chain(…)` (autonomous) | `Flow.of f` with `f : σ → σ` |
| `x -> …point(x)…` (reads the time) | `Flow.ofTime f` with `f : Float → σ → σ`, or `Flow.ofLocal` on a `LocalTensor` |
| `FlowApprox(f, t)`, `f(x, h)` | `FlowApprox f t` with `f : Float → σ → Float → σ` |
| (none: in-place for speed) | `Flow.into f` with `f : Float → σ → σ → σ` writing into its last argument |

**Speed.** The integrators are specialized on the system: build the `Flow` where it is used or
bind it with `@[inline] def`/`abbrev`, so that the stepping loop compiles against the system's
code (docs/PERF.md, "Fatou"): a system hidden behind an opaque definition is called as a closure,
which boxes the time on every call.
-/

namespace Adapode

open JuliaBase Cartan

/-- Julia `2π` (`Float64(2π)`), the default duration (`Adapode.jl:154, 213`). -/
def twoPi : Float := f64! 6.283185307179586

/-- Julia `Flow{F,N}` (`Adapode.jl:143-148`): the system `f` (in the form `f h t x out`) over the
duration `t`. -/
structure Flow (σ : Type) where
  /-- The system: `f h t x out` is the derivative at `t ↦ x` (written into, or instead of, `out`). -/
  f : Float → Float → σ → σ → σ
  /-- Julia `duration(Φ)`. -/
  t : Float := twoPi

namespace Flow

variable {σ : Type}

/-- Julia `Flow(f, t)` of an autonomous system `x -> …` (`Adapode.jl:153-155`). -/
@[inline] def of (f : σ → σ) (t : Float := twoPi) : Flow σ := ⟨fun _ _ x _ => f x, t⟩

/-- Julia `Flow(f, t)` of a system reading the time (`point(x)`). -/
@[inline] def ofTime (f : Float → σ → σ) (t : Float := twoPi) : Flow σ := ⟨fun _ s x _ => f s x, t⟩

/-- Julia `Flow(f, t)` of a system on the local tensor `t ↦ x`. -/
@[inline] def ofLocal (f : LocalTensor Float σ → σ) (t : Float := twoPi) : Flow σ :=
  ⟨fun _ s x _ => f ⟨s, x⟩, t⟩

/-- A system in destination-passing form `f t x out` (no allocation per evaluation when `f` writes
into `out`). -/
@[inline] def into (f : Float → σ → σ → σ) (t : Float := twoPi) : Flow σ := ⟨fun _ s x o => f s x o, t⟩

/-- Julia `system(Φ)` (`Adapode.jl:156`), in the integrators' form. -/
@[inline] def system (Φ : Flow σ) : Float → Float → σ → σ → σ := Φ.f

/-- Julia `duration(Φ)` (`Adapode.jl:157`). -/
@[inline] def duration (Φ : Flow σ) : Float := Φ.t

/-- Julia `integrator(::Flow) = ExplicitIntegrator{4}(2^-11, 0)` (`Adapode.jl:158`): RK4 with
`h = 2^-11`, final state only. -/
def integrator (_ : Flow σ) : Integrator :=
  .explicit ({ tol := Tol.toStep 11, skip := 0 } : ExplicitIntegrator 4)

/-- The same flow over another duration. -/
@[inline] def withDuration (Φ : Flow σ) (t : Float) : Flow σ := { Φ with t }

end Flow

/-- Julia `FlowApprox(f, t)` (`Adapode.jl:150-151`): a system `f(x, h)` that also reads the step
(passed the full step `h` at every stage, as Julia's `butcher` does). -/
@[inline] def FlowApprox {σ : Type} (f : Float → σ → Float → σ) (t : Float := twoPi) : Flow σ :=
  ⟨fun h s x _ => f s x h, t⟩

/-- Julia `InitialCondition{L,X}` (`Adapode.jl:205-219`; `IC`): a flow and a starting state. A plain
Julia `x0` starts at time `0` (`init`, `Adapode.jl:471-476`); a `LocalTensor` keeps its time
(`t0`). -/
structure InitialCondition (σ : Type) where
  /-- Julia `LieGroup(ic)`. -/
  flow : Flow σ
  /-- Julia `parameter(ic)`. -/
  x0 : σ
  /-- The starting time. -/
  t0 : Float := 0

/-- Julia `IC = InitialCondition` (`Adapode.jl:211`). -/
abbrev IC := InitialCondition

namespace InitialCondition

variable {σ : Type}

/-- Julia `InitialCondition(f, x0, tmax=2π)` of an autonomous system (`Adapode.jl:212-213`). -/
@[inline] def of (f : σ → σ) (x0 : σ) (tmax : Float := twoPi) : InitialCondition σ :=
  ⟨.of f tmax, x0, 0⟩

/-- Julia `InitialCondition(f, x0, tmax)` of a system reading the time. -/
@[inline] def ofTime (f : Float → σ → σ) (x0 : σ) (tmax : Float := twoPi) : InitialCondition σ :=
  ⟨.ofTime f tmax, x0, 0⟩

/-- Julia `InitialCondition(Φ, t0 ↦ x0)`: start at the local tensor's time. -/
@[inline] def ofLocalTensor (Φ : Flow σ) (x : LocalTensor Float σ) : InitialCondition σ :=
  ⟨Φ, x.fiber, x.base⟩

/-- Julia `LieGroup(ic)`. -/
@[inline] def lieGroup (ic : InitialCondition σ) : Flow σ := ic.flow
/-- Julia `system(ic)`. -/
@[inline] def system (ic : InitialCondition σ) : Float → Float → σ → σ → σ := ic.flow.f
/-- Julia `duration(ic)`. -/
@[inline] def duration (ic : InitialCondition σ) : Float := ic.flow.t
/-- Julia `parameter(ic)`. -/
@[inline] def parameter (ic : InitialCondition σ) : σ := ic.x0
/-- Julia `integrator(ic) = integrator(LieGroup(ic))`: RK4, `h = 2^-11`, final state. -/
def integrator (ic : InitialCondition σ) : Integrator := ic.flow.integrator

end InitialCondition

/-- Julia `FlowIntegral{F,I,N}` (`Adapode.jl:179-203`): a flow with its integrator. -/
structure FlowIntegral (σ : Type) where
  /-- Julia `Flow(Φ)`. -/
  flow : Flow σ
  /-- Julia `integrator(Φ)`. -/
  integrator : Integrator

namespace FlowIntegral

variable {σ : Type}

/-- Julia `FlowIntegral(f, tmax, i=ExplicitIntegrator{4}(2^-11))` (`Adapode.jl:185-186`): RK4 at
`h = 2^-11`, full trajectory. -/
@[inline] def of (Φ : Flow σ)
    (i : Integrator := .explicit ({ tol := Tol.toStep 11 } : ExplicitIntegrator 4)) : FlowIntegral σ :=
  ⟨Φ, i⟩

end FlowIntegral

/-- Julia `LeapCondition{L,X,Y}` (`Adapode.jl:626-646`): the system `fprime` over a duration, and
two consecutive states `x0` (previous, at time `t0`) and `x1` (current, at `t1`); Julia
`step(ic) = t1 - t0`. -/
structure LeapCondition (σ : Type) where
  /-- Julia `LieGroup(ic)`: `fprime` and the duration. -/
  flow : Flow σ
  /-- Julia `parameter(ic)`: the previous state. -/
  x0 : σ
  /-- Its time. -/
  t0 : Float
  /-- Julia `leap(ic)`: the current state. -/
  x1 : σ
  /-- Its time. -/
  t1 : Float

namespace LeapCondition

variable {σ : Type}

/-- Julia `LeapCondition(f, x0, x1, dt, tmax=2π)` (`Adapode.jl:636-637`): `x0` at `-dt`, `x1` at `0`. -/
@[inline] def ofStep (Φ : Flow σ) (x0 x1 : σ) (dt : Float) : LeapCondition σ :=
  ⟨Φ, x0, -dt, x1, 0⟩

/-- Julia `step(ic) = point(leap(ic)) - point(parameter(ic))` (`Adapode.jl:644`). -/
@[inline] def step (ic : LeapCondition σ) : Float := ic.t1 - ic.t0

/-- Julia `duration(ic)`. -/
@[inline] def duration (ic : LeapCondition σ) : Float := ic.flow.t

end LeapCondition

end Adapode

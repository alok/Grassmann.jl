import Adapode.ODE.Geodesic

/-!
# `odesolve` and the flow API (`src/Adapode.jl:161-203, 478-622, 655-675`)

The typed front end: it views the state `x₀ : σ` as `d = dim σ` floats, runs the flat machines of
`Adapode.ODE.Explicit`/`Multistep`/`Adaptive`/`Leapfrog` specialized on the system, and packages
the result as Julia does:

| Julia | Lean |
|---|---|
| `odesolve(ic, I)` with `I.skip = 0` | `Result.final t x` (Julia `t ↦ x`) |
| `odesolve(ic, I)` otherwise | `Result.path s`, `s : Solution σ`; `s.field` is the `TensorField` over the time points (over `base(x₀) ⊕ time` for a field state, `OdePath`) |
| `odesolve(ic)` | `odesolve ic ic.integrator` (RK4, `h = 2^-11`, final state) |
| `odesolve(f, x0, tmax=2π, tol=15, M=Val(1), B=Val(4))` | `odesolveCode` (RK4, `h = 2^-15`, full trajectory by default) |
| `(I::AbstractIntegrator)(ic)` | `odesolve ic I` |
| `(Φ::Flow)(x0, i)`, `(Φ::Flow)(t0 ↦ x0, i)`, `(Φ::Flow)(x0, n, i)` | `Flow.apply`, `Flow.applyLocal`, `Flow.iterate` |
| `(Φ::Flow)(x0::TensorField, i)` (a flow applied to a field of states) | `Flow.onField` |
| `(Φ::FlowIntegral)(x0)`, `(Φ::FlowIntegral)(xs::Vector)` | `FlowIntegral.apply`, `FlowIntegral.applyAll` |
| `odesolve(ic::LeapCondition, I::LeapIntegrator, bc)` | `leapsolve` |
| `geosolve(ic, I)`, `geosolve(Γ, x0, v0, tmax, tol, m, o)` | `geosolve`, `geosolveCode` |
| `Base.exp(X::TensorField)` (the flow of a vector field for time 1) | `Flow.ofField`, `vectorFieldExp` |

**Julia defects fixed here** (port notes §8.6): `Flow(t0 ↦ x0)` integrates over `[t0, t0 + T]`
(Julia: `[0, t0 + T]`, B5); `Flow(x0, n, i)` iterates with the integrator `i` (Julia: always the
default, B6); `FlowIntegral` on a vector of states works (Julia: `typoef`, undefined `n`, B20). The
default integrator of `Flow(x0)` is Julia's `MultistepIntegrator{4}(2^-11, 0)`, with B3 fixed.
-/

namespace Adapode

open JuliaBase Grassmann DirectSum StaticVectors Cartan

/-! ## Results -/

/-- A trajectory: the states (`dim` floats each, point-major) at the time points `times` (Julia's
`TensorField` over the time grid, before choosing its fiber type). -/
structure Solution (σ : Type) where
  /-- The time points (a range for fixed-step methods, explicit for adaptive ones). -/
  times : Axis
  /-- The states, flat. -/
  data : FloatArray
  /-- Floats per state. -/
  dim : Nat
  deriving Inhabited

/-- Julia `odesolve`'s result: `t ↦ x` when `skip = 0`, a trajectory otherwise. -/
inductive Result (σ : Type) where
  /-- Julia `LocalTensor(t ↦ x)`. -/
  | final (t : Float) (x : σ)
  /-- Julia's trajectory `TensorField`. -/
  | path (s : Solution σ)

/-- The trajectory type of a state type (Julia `initsteps`, `Adapode.jl:337-339`): a field of states
over the time axis, or for a field state the field over `base(x₀) ⊕ time` with time last. -/
class OdePath (σ : Type) where
  /-- The trajectory over the time points `ax`. -/
  Path : Axis → Type
  /-- Package flat states at the time points `ax`. -/
  mkPath : (ax : Axis) → FloatArray → Path ax

/-- Vector states: `TensorField(t, x)` over the time axis. -/
instance (priority := low) {σ : Type} [FlatFiber σ] : OdePath σ where
  Path ax := TensorField (GridBundle.ofAxis ax) σ
  mkPath ax data := (TensorField.ofFlat? (GridBundle.ofAxis ax) data).getD default

/-- Field states: `TensorField(base(x₀) × t, x)` (Julia `ndims(f0) > 0 ? base(f0)×t : t`). -/
instance {M : Type} [FrameBundle M] {m : M} {F : Type} [FlatFiber F] : OdePath (TensorField m F) where
  Path ax := TensorField (FiberProductBundle.ofBase m ax) F
  mkPath ax data := (TensorField.ofFlat? (FiberProductBundle.ofBase m ax) data).getD default

namespace Solution

variable {σ : Type}

/-- Julia `length(sol)`: the number of time points. -/
def length (s : Solution σ) : Nat := if s.dim == 0 then s.times.length else s.data.size / s.dim

/-- The time of point `i` (0-based; Julia `points(sol)[i+1]`). -/
def timeAt (s : Solution σ) (i : Nat) : Float := s.times.get i

/-- The flat state of point `i` (a copy). -/
def flatAt (s : Solution σ) (i : Nat) : FloatArray := slice s.data (i * s.dim) s.dim

/-- The state of point `i` (0-based; Julia `fiber(sol)[i+1]`). -/
def stateAt [OdeState σ] [Inhabited σ] (s : Solution σ) (i : Nat) : σ :=
  let a := s.flatAt i
  if h : a.size = OdeState.dim σ then OdeState.ofFlat a h else default

/-- The last state (Julia `fiber(sol)[end]`). -/
def last [OdeState σ] [Inhabited σ] (s : Solution σ) : σ := s.stateAt (s.length - 1)

/-- The last time (Julia `points(sol)[end]`). -/
def lastTime (s : Solution σ) : Float := s.timeAt (s.length - 1)

/-- The trajectory as a Cartan `TensorField` over its time points (`OdePath`). -/
def field [OdePath σ] (s : Solution σ) : OdePath.Path σ s.times := OdePath.mkPath s.times s.data

end Solution

namespace Result

variable {σ : Type}

/-- The trajectory, if any. -/
def path? : Result σ → Option (Solution σ)
  | .final .. => none
  | .path s => some s

/-- The final time. -/
def lastTime : Result σ → Float
  | .final t _ => t
  | .path s => s.lastTime

/-- The final state. -/
def last [OdeState σ] [Inhabited σ] : Result σ → σ
  | .final _ x => x
  | .path s => s.last

/-- The final state, flat. -/
def lastFlat [OdeState σ] : Result σ → FloatArray
  | .final _ x => toFlat x
  | .path s => s.flatAt (s.length - 1)

/-- Julia `t ↦ x` of the final state. -/
def localTensor [OdeState σ] [Inhabited σ] (r : Result σ) : LocalTensor Float σ := ⟨r.lastTime, r.last⟩

end Result

/-! ## `odesolve` -/

section Solve

variable {σ : Type} [OdeState σ]

/-- The boundary hook as a flat map (`fallback` for arrays of the wrong size, which never occur). -/
@[inline] def flatHook (d : Nat) (hd : d = OdeState.dim σ) (fallback : σ) (bc : σ → σ) :
    FloatArray → FloatArray :=
  fun a => toFlat (bc (OdeState.wrap d hd a fallback))

/-- Package a fixed-step run. -/
@[inline] def fixedResult (d : Nat) (hd : d = OdeState.dim σ) (x0 : σ) (t0 h tmax : Float) (skip : Nat)
    (r : FlatRun) : Result σ :=
  if skip == 0 then .final r.t (OdeState.wrap d hd r.x x0)
  else .path ⟨.stepLen (outputGrid t0 h tmax skip), r.out, d⟩

/-- Package an adaptive run. -/
@[inline] def adaptiveResult (d : Nat) (r : AdaptiveRun) : Result σ :=
  .path ⟨.explicit (slice r.T 0 r.len), slice r.X 0 (r.len * d), d⟩

/-- Julia `odesolve(ic, I, bc=identity)` (`Adapode.jl:483-571`): integrate `ic` from its time `t0`
to the time `ic.flow.t` (Julia's `duration`, an end time) with `I`. `bc` is applied to the initial
state and after every fixed step (Julia has no `bc` for the adaptive integrators, and none is
applied there). -/
@[inline] def odesolve (ic : InitialCondition σ) (I : Integrator) (bc : σ → σ := id) : Result σ :=
  let x0 := ic.x0
  let d := (toFlat x0).size
  have hd : d = OdeState.dim σ := OdeState.size_toFlat x0
  let f := flatSystem d hd x0 ic.flow.f
  let B := flatHook d hd x0 bc
  let t0 := ic.t0
  let T := ic.flow.t
  let xf := toFlat x0
  match I with
  | .eulerHeun i =>
    fixedResult d hd x0 t0 i.tol T i.skip
      (rkSolve f B heunTableau true d xf t0 i.tol T i.skip (if i.compat then 1 else i.skip))
  | .explicit (o := o) i =>
    fixedResult d hd x0 t0 i.tol T i.skip (rkSolve f B (CB o) false d xf t0 i.tol T i.skip i.skip)
  | .explicitAdaptor (o := o) i =>
    adaptiveResult d (rkaSolve f (if i.fixed then CBA.fixed o else CBA o) d xf t0 i.tol T i.skip i.compat)
  | .multistep (o := o) i =>
    if i.skip == 0 && i.compat then
      let (t, x) := abmCompatFinal f B o d xf t0 i.tol T
      .final t (OdeState.wrap d hd x x0)
    else fixedResult d hd x0 t0 i.tol T i.skip (abmSolve f B o d xf t0 i.tol T i.skip)
  | .multistepAdaptor (o := o) i => adaptiveResult d (abmaSolve f o d xf t0 i.tol T i.skip i.compat)

/-- Julia `odesolve(ic) = odesolve(ic, integrator(ic))` (`Adapode.jl:478`): RK4 at `h = 2^-11`,
final state. -/
@[inline] def odesolveDefault (ic : InitialCondition σ) : Result σ := odesolve ic ic.integrator

/-- Julia `odesolve(f, x0, tmax=2π, tol=15, M=Val(1), B=Val(4))` (`Adapode.jl:479-482`): the
integrator `AbstractIntegrator(tol, m, o)` (`m = 0` Heun, `1` RK, `2` adaptive RK, `3` ABM, `4`
adaptive ABM), full trajectory; RK4 at `h = 2^-15` over `[0, 2π]` by default. An invalid `(m, o)`
(Julia: `nothing`, then a `MethodError`) falls back to that default. -/
@[inline] def odesolveCode (f : σ → σ) (x0 : σ) (tmax : Float := twoPi) (tol : Tol := 15)
    (m : Nat := 1) (o : Nat := 4) : Result σ :=
  odesolve (.of f x0 tmax) ((Integrator.ofCode tol m o).getD .default)

end Solve

/-! ## Flows -/

namespace Flow

variable {σ : Type} [OdeState σ]

/-- Julia's default integrator of `(Φ::Flow)(x0)` (`Adapode.jl:161`): `MultistepIntegrator{4}(2^-11, 0)`. -/
def applyDefault : Integrator := .multistep ({ tol := Tol.toStep 11, skip := 0 } : MultistepIntegrator 4)

/-- Julia `(Φ::Flow)(x0, i=MultistepIntegrator{4}(2^-11,0))` (`Adapode.jl:161`): integrate `x0`
from time `0` to `duration(Φ)`. -/
@[inline] def apply (Φ : Flow σ) (x0 : σ) (I : Integrator := applyDefault) : Result σ :=
  odesolve ⟨Φ, x0, 0⟩ I

/-- Julia `(Φ::Flow)(t0 ↦ x0, i=integrator(Φ))` (`Adapode.jl:162`), fixed (B5): integrate over
`[t0, t0 + duration(Φ)]` (Julia integrates `x0` from `0` to `t0 + duration(Φ)`). -/
@[inline] def applyLocal (Φ : Flow σ) (x : LocalTensor Float σ) (I : Integrator := Φ.integrator) :
    Result σ :=
  odesolve ⟨Φ.withDuration (x.base + Φ.t), x.fiber, x.base⟩ I

/-- Julia `(Φ::Flow)(x0, n, i)` (`Adapode.jl:164-171`), fixed (B6): `n` states, each the flow of the
previous one under the integrator `I` (the final states; the first is `x0`). -/
def iterate [Inhabited σ] (Φ : Flow σ) (x0 : σ) (n : Nat) (I : Integrator := Φ.integrator) : Array σ :=
  go (n - 1) x0 (#[x0])
where
  /-- `k` more states after `x`. -/
  go : Nat → σ → Array σ → Array σ
    | 0, _, acc => acc
    | k + 1, x, acc => let y := (Φ.apply x I).last; go k y (acc.push y)

end Flow

namespace FlowIntegral

variable {σ : Type} [OdeState σ]

/-- Julia `(Φ::FlowIntegral)(x0) = Flow(Φ)(x0, integrator(Φ))` (`Adapode.jl:193`). -/
@[inline] def apply (Φ : FlowIntegral σ) (x0 : σ) : Result σ := Φ.flow.apply x0 Φ.integrator

/-- Julia `(Φ::FlowIntegral)(x0::Vector{<:Chain})` (`Adapode.jl:195-203`, which throws, B20): the
result for every initial state. -/
def applyAll (Φ : FlowIntegral σ) (xs : Array σ) : Array (Result σ) := xs.map Φ.apply

end FlowIntegral

/-! ## Flows of fields of states -/

section Pointwise

variable {F : Type} [FlatFiber F] [OdeState F]

/-- Apply a fiber system at every point of a flat field `X` (`w` floats per point), writing into
`out`. -/
@[specialize] def pointwiseLoop (f : Float → Float → F → F → F) (h t : Float) (w : Nat)
    (hw : w = OdeState.dim F) (fallback : F) (X : FloatArray) :
    (n p : Nat) → (scratch out : FloatArray) → FloatArray
  | 0, _, _, out => out
  | n + 1, p, scratch, out =>
    let r := toFlat (f h t (OdeState.wrap w hw (slice X (p * w) w) fallback)
      (OdeState.wrap w hw scratch fallback))
    pointwiseLoop f h t w hw fallback X n (p + 1) r (copyInto out (p * w) w r)

/-- The flow of a system on fibers, acting pointwise on fields over `m` (Julia
`(Φ::Flow)(x0::TensorField)`, `Adapode.jl:174-177`: the system
`t -> TensorField(base(fiber(t)), Φ.f.(fiber(fiber(t))))`). `fallback` is any fiber value. -/
@[inline] def Flow.pointwise {M : Type} [FrameBundle M] {m : M} (Φ : Flow F) (fallback : F) :
    Flow (TensorField m F) :=
  ⟨fun h t X out =>
    let w := (toFlat fallback).size
    have hw : w = OdeState.dim F := OdeState.size_toFlat fallback
    let data := pointwiseLoop Φ.f h t w hw fallback X.data (card m) 0 (zeros w) out.data
    if hs : data.size = FlatFiber.width F * card m then ⟨data, hs, none⟩ else X, Φ.t⟩

/-- Julia `(Φ::Flow)(x0::TensorField, i=integrator(Φ))` (`Adapode.jl:174-177`): flow every point
of the field `x0` (the state is the whole field). -/
@[inline] def Flow.onField [Inhabited F] {M : Type} [FrameBundle M] {m : M} (Φ : Flow F)
    (x0 : TensorField m F) (I : Integrator := Φ.integrator) : Result (TensorField m F) :=
  odesolve ⟨Φ.pointwise (x0.get 0), x0, 0⟩ I

end Pointwise

/-! ## Vector fields as systems -/

/-- The system of a vector field sampled on a grid, evaluated by Cartan's multilinear
interpolation at the state's coordinates (Julia `f(x)` for `f::TensorField`, `heun`'s and
`butcher`'s `TensorField` methods). -/
@[inline] def Flow.ofField {N : Nat} {P G : Type} {b : GridBundle N P G} {V : TensorBundle}
    (X : TensorField b (Chain V 1 Float)) (t : Float := twoPi) : Flow (Chain V 1 Float) :=
  .of (fun x => X.eval (Vector.ofFn fun a => x.v.get! a.1)) t

/-- Julia `Base.exp(X::TensorField{B,<:Chain{V,1}}) = Flow(X, 1.0)` (`Adapode.jl:159`). -/
@[inline] def vectorFieldExp {N : Nat} {P G : Type} {b : GridBundle N P G} {V : TensorBundle}
    (X : TensorField b (Chain V 1 Float)) : Flow (Chain V 1 Float) := Flow.ofField X 1

/-! ## Leapfrog -/

/-- Julia `odesolve(ic::LeapCondition, I::LeapIntegrator{o}, bc=identity)` (`Adapode.jl:655-675`):
the `nplots + 1` stored states and their time axis (module doc of `Adapode.ODE.Leapfrog`). -/
@[inline] def leapsolve {σ : Type} [OdeState σ] {o : Nat} (ic : LeapCondition σ) (I : LeapIntegrator o)
    (bc : σ → σ := id) : Solution σ :=
  let x0 := ic.x1
  let d := (toFlat x0).size
  have hd : d = OdeState.dim σ := OdeState.size_toFlat x0
  let (r, ax) := leapSolve (flatSystem d hd x0 ic.flow.f) (flatHook d hd x0 bc) (o == 2) d I.skip
    (toFlat ic.x0) (toFlat ic.x1) ic.t0 ic.t1 ic.flow.t
  ⟨ax, r.out, d⟩

/-! ## Geodesics -/

/-- The first `n` of every `2n` floats of `data`, for the points `p, p+1, …` (`k` of them). -/
def positionsLoop (data : FloatArray) (n : Nat) : (k p : Nat) → FloatArray → FloatArray
  | 0, _, out => out
  | k + 1, p, out => positionsLoop data n k (p + 1) (copyInto out (p * n) n (slice data (2 * n * p) n))

/-- Julia `geosolve(ic, i=integrator(ic))` (`Adapode.jl:617-618`): the positions of the geodesic
(`getindex.(odesolve(ic, i), 1)`), a curve over the time points. -/
def geosolve {V : TensorBundle} (ic : InitialCondition (Phase V)) (I : Integrator) :
    Solution (Chain V 1 Float) :=
  let n := Leibniz.binomial V.n 1
  match odesolve ic I with
  | .final t x => ⟨.explicit (FloatArray.empty.push t), slice x.data 0 n, n⟩
  | .path s =>
    let len := s.length
    ⟨s.times, positionsLoop s.data n len 0 (zeros (len * n)), n⟩

/-- Julia `geosolve(Γ, x0, v0, tmax=2π, tol=15, M=Val(1), B=Val(4))` (`Adapode.jl:619-622`). -/
def geosolveCode {V : TensorBundle} (Γ : Chain V 1 Float → Christoffel) (x0 v0 : Chain V 1 Float)
    (tmax : Float := twoPi) (tol : Tol := 15) (m : Nat := 1) (o : Nat := 4) :
    Solution (Chain V 1 Float) :=
  geosolve (geodesic Γ x0 v0 tmax) ((Integrator.ofCode tol m o).getD .default)

end Adapode

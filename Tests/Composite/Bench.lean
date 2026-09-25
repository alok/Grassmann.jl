/-
Micro-benchmarks of `Grassmann.Composite` (ns per call over a sweep of arguments, the
result folded into an accumulator), with the matching Julia loops in the module
docstring of each case (`oracle` environment, Julia 1.13, Grassmann 0.8.46):

```julia
using Grassmann; @basis S"+++"
f(n) = (s = 0.0; for i in 1:n; x = 1e-7i; s += value(exp(Couple{V,v12}(0.1, x)))[2]; end; s)
f(10); @elapsed f(10^7)
```
-/
import Grassmann.Composite

namespace Tests.Composite.Bench

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase Composite

/-- Euclidean 3-space. -/
abbrev E3 : TensorBundle := S!"+++"

/-- `∑ f(i·dx)` for `i < n` (tail-recursive, unboxed). -/
@[specialize] def sweep (f : Float → Float) (dx : Float) : Nat → Float → Float → Float
  | 0, _, acc => acc
  | k + 1, x, acc => sweep f dx k (x + dx) (acc + f x)

/-- Time `n` calls; prints ns per call and the checksum. -/
def time (name : String) (n : Nat) (run : Unit → Float) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let s := run ()
  let t1 ← IO.monoNanosNow
  IO.println s!"  {name}: {F64.showCompact ((t1 - t0).toFloat / n.toFloat)} ns/op (checksum {F64.showCompact s})"

/-- The bivector `0.3v₁₂ + 0.2v₁₃ + 0.4v₂₃`. -/
def biv0 : Chain E3 2 Float := (Chain.ofList? [0.3, 0.2, 0.4]).get!

/-- The quaternion `1 + 0.3v₁₂ + 0.2v₁₃ + 0.4v₂₃`. -/
def quat0 : Spinor E3 Float := (Half.ofList? [1.0, 0.3, 0.2, 0.4]).get!

/-- The multivector with coefficients `0.1·(1, 2, …, 8)`. -/
def mv0 : Multivector E3 Float := (Multivector.ofList? [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8]).get!

/-- The quaternion `1 + x·(0.3v₁₂ + 0.2v₁₃ + 0.4v₂₃)` (one `map` of a stored vector). -/
@[inline] def quat (x : Float) : Spinor E3 Float := Half.addScalar (1.0 - x) ⟨quat0.v.map (· * x)⟩

/-- The bivector chain `x·(0.3v₁₂ + 0.2v₁₃ + 0.4v₂₃)`. -/
@[inline] def biv (x : Float) : Chain E3 2 Float := ⟨biv0.v.map (· * x)⟩

/-- A dense multivector depending on `x`. -/
@[inline] def mvx (x : Float) : Multivector E3 Float := ⟨mv0.v.map (· * x)⟩

/-- Run the benchmarks (`smoke`: few iterations). -/
def run (smoke : Bool := false) : IO Unit := do
  let n := if smoke then 1000 else 1000000
  let dx := 1.0 / n.toFloat
  IO.println s!"composite ({n} calls each, ℝ3)"
  time "input: biv x (one map, baseline)" n fun _ => sweep (fun x => getD (biv x).v 1) dx n 0 0
  time "input: quat x (map + addScalar, baseline)" n fun _ => sweep (fun x => getD (quat x).v 1) dx n 0 0
  time "Couple.exp (rotor, closed form)" n fun _ =>
    sweep (fun x => (Couple.exp (⟨3, 0.1, x⟩ : Couple E3 Float)).im) dx n 0 0
  time "Single.exp (bivector term)" n fun _ =>
    sweep (fun x => (Single.exp (⟨3, x⟩ : Single E3 2 Float)).im) dx n 0 0
  time "Couple.log (complex)" n fun _ =>
    sweep (fun x => (Couple.log (⟨3, 1.0, x⟩ : Couple E3 Float)).im) dx n 0 0
  time "Couple.sqrt (complex)" n fun _ =>
    sweep (fun x => (Couple.sqrt (⟨3, 1.0, x⟩ : Couple E3 Float)).im) dx n 0 0
  time "Couple.cosh (hyperbolic, series)" n fun _ =>
    sweep (fun x => (Couple.cosh (⟨1, 0.5, x⟩ : Couple E3 Float)).im) dx n 0 0
  time "Chain.expEven (bivector, closed form)" n fun _ =>
    sweep (fun x => getD (biv x).expEven.v 1) dx n 0 0
  time "Chain.exp (bivector → Multivector)" n fun _ =>
    sweep (fun x => getD (biv x).exp.v 4) dx n 0 0
  time "Half.exp (quaternion, closed form)" n fun _ =>
    sweep (fun x => getD (quat x).exp.v 1) dx n 0 0
  time "Half.log (quaternion, polar)" n fun _ =>
    sweep (fun x => getD (quat x).log.v 1) dx n 0 0
  time "Half.sqrt (quaternion, polar)" n fun _ =>
    sweep (fun x => getD (quat x).sqrt.v 1) dx n 0 0
  let m := n / 10
  time "Multivector.exp (dense, series)" m fun _ =>
    sweep (fun x => getD (mvx x).exp.v 3) (1.0 / m.toFloat) m 0 0
  time "Chain.cos (bivector, series)" m fun _ =>
    sweep (fun x => getD (biv x).cos.v 0) (1.0 / m.toFloat) m 0 0

end Tests.Composite.Bench

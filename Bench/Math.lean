import JuliaBase

/-!
# Scalar kernel benchmarks

Throughput of Julia's own kernels (`JuliaBase.Math`) against the platform `libm` that Lean's
`Float.exp`/`Float.log`/`Float.pow` call: ns per call over a sweep of arguments, the result
folded into an accumulator so nothing is dead code.
-/

namespace Bench.Math

open JuliaBase

/-- `∑ f(x₀ + i·dx)` for `i < n` (tail-recursive, unboxed Floats). -/
@[specialize] def sweep (f : Float → Float) (x dx : Float) : Nat → Float → Float
  | 0, acc => acc
  | k + 1, acc => sweep f (x + dx) dx k (acc + f x)

/-- `∑ f(x₀ + i·dx, y)` for `i < n`. -/
@[specialize] def sweep2 (f : Float → Float → Float) (x dx y : Float) : Nat → Float → Float
  | 0, acc => acc
  | k + 1, acc => sweep2 f (x + dx) dx y k (acc + f x y)

/-- Time `n` calls; returns ns per call (and prints the checksum so the loop is kept). -/
def time (name : String) (n : Nat) (run : Unit → Float) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let s := run ()
  let t1 ← IO.monoNanosNow
  let ns := (t1 - t0).toFloat / n.toFloat
  IO.println s!"  {name}: {F64.showCompact ns} ns/op (checksum {F64.showCompact s})"

/-- Run the suite; `smoke` uses few iterations. -/
def run (smoke : Bool) : IO Unit := do
  let n := if smoke then 10000 else 10000000
  IO.println s!"math ({n} calls each)"
  let dx := 1400.0 / n.toFloat
  time "Float.exp (libm)" n fun _ => sweep Float.exp (-700.0) dx n 0
  time "F64.exp (Julia)" n fun _ => sweep F64.exp (-700.0) dx n 0
  let lx := 1.0e6 / n.toFloat
  time "Float.log (libm)" n fun _ => sweep Float.log 1.0e-3 lx n 0
  time "F64.log (Julia)" n fun _ => sweep F64.log 1.0e-3 lx n 0
  time "F64.expm1 (Julia)" n fun _ => sweep F64.expm1 (-2.0) (4.0 / n.toFloat) n 0
  time "F64.log1p (Julia)" n fun _ => sweep F64.log1p (-0.5) (4.0 / n.toFloat) n 0
  let px := 100.0 / n.toFloat
  time "Float.pow x 2.5 (libm)" n fun _ => sweep2 Float.pow 1.0e-3 px 2.5 n 0
  time "F64.pow x 2.5 (Julia)" n fun _ => sweep2 F64.pow 1.0e-3 px 2.5 n 0
  time "F64.powInt x 7 (pow_body)" n fun _ => sweep (fun x => F64.powInt x 7) 1.0e-3 px n 0
  -- trigonometric and hyperbolic functions (`JuliaBase.Trig`, `JuliaBase.Hyperbolic`)
  let tx := 20.0 / n.toFloat
  time "Float.sin (libm)" n fun _ => sweep Float.sin (-10.0) tx n 0
  time "F64.sin (Julia)" n fun _ => sweep F64.sin (-10.0) tx n 0
  time "Float.cos (libm)" n fun _ => sweep Float.cos (-10.0) tx n 0
  time "F64.cos (Julia)" n fun _ => sweep F64.cos (-10.0) tx n 0
  time "Float.tan (libm)" n fun _ => sweep Float.tan (-10.0) tx n 0
  time "F64.tan (Julia)" n fun _ => sweep F64.tan (-10.0) tx n 0
  time "F64.sin, |x| ~ 1e10 (Payne-Hanek)" n fun _ => sweep F64.sin 1.0e10 (1.0e10 / n.toFloat) n 0
  let ax := 2.0 / n.toFloat
  time "Float.asin (libm)" n fun _ => sweep Float.asin (-1.0) ax n 0
  time "F64.asin (Julia)" n fun _ => sweep F64.asin (-1.0) ax n 0
  time "Float.atan (libm)" n fun _ => sweep Float.atan (-10.0) tx n 0
  time "F64.atan (Julia)" n fun _ => sweep F64.atan (-10.0) tx n 0
  time "Float.atan2 y 0.7 (libm)" n fun _ => sweep2 Float.atan2 (-10.0) tx 0.7 n 0
  time "F64.atan2 y 0.7 (Julia)" n fun _ => sweep2 F64.atan2 (-10.0) tx 0.7 n 0
  time "Float.sinh (libm)" n fun _ => sweep Float.sinh (-10.0) tx n 0
  time "F64.sinh (Julia)" n fun _ => sweep F64.sinh (-10.0) tx n 0
  time "Float.tanh (libm)" n fun _ => sweep Float.tanh (-10.0) tx n 0
  time "F64.tanh (Julia)" n fun _ => sweep F64.tanh (-10.0) tx n 0
  time "F64.sinpi (Julia)" n fun _ => sweep F64.sinpi (-10.0) tx n 0
  -- `ComplexF64` (Julia's algorithms on Julia's kernels)
  time "ComplexF64.div" n fun _ => sweep (fun x => (ComplexF64.div ⟨x, 1.5⟩ ⟨0.5, x⟩).re) (-10.0) tx n 0
  time "ComplexF64.exp" n fun _ => sweep (fun x => (ComplexF64.exp ⟨0.1 * x, x⟩).re) (-10.0) tx n 0
  time "ComplexF64.sin" n fun _ => sweep (fun x => (ComplexF64.sin ⟨x, 0.1 * x⟩).re) (-10.0) tx n 0

end Bench.Math

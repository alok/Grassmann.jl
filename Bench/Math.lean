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

end Bench.Math

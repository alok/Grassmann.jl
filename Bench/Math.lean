import Bench.Harness
import JuliaBase

/-!
# `math`: Julia's scalar kernels (`JuliaBase.Math`)

ns per call of Julia's own `exp`/`log`/`expm1`/`log1p`/`^` as ported to Lean, over a sweep of
`n = 10⁴` arguments folded into a sum (`sweep`), against the same loop in Julia
(`oracle/bench/math.jl`). The `*_libm` cases are Lean-only references: the platform `libm`
that `Float.exp`/`Float.log`/`Float.pow` call.

Both languages generate the arguments by repeated addition from the same start and step, so
the sums (the checks) agree bit for bit when the kernels do.
-/

namespace Bench.Math

open JuliaBase Bench

/-- `∑ f(x₀ + i·dx)` for `i < n` (tail-recursive, unboxed Floats). -/
@[specialize] def sweep (f : Float → Float) (x dx : Float) : Nat → Float → Float
  | 0, acc => acc
  | k + 1, acc => sweep f (x + dx) dx k (acc + f x)

/-- `∑ f(x₀ + i·dx, y)` for `i < n`. -/
@[specialize] def sweep2 (f : Float → Float → Float) (x dx y : Float) : Nat → Float → Float
  | 0, acc => acc
  | k + 1, acc => sweep2 f (x + dx) dx y k (acc + f x y)

/-- `x ^ 7` by Julia's `pow_body` (a top-level function so its literal is hoisted). -/
def pow7 (x : Float) : Float := F64.powInt x 7

/-- The suite. -/
def suite : Suite := ⟨"math", do
  let n := 10000
  let p := s!"n={n}"
  let n' := n.toUInt64.toFloat
  let ex := 1400.0 / n'
  bench "exp" (ops := n) (param := p) fun i => sweep F64.exp (blackBox i (-700.0)) ex n 0
  bench "exp_libm" (ops := n) (param := p) fun i => sweep Float.exp (blackBox i (-700.0)) ex n 0
  let lx := 1.0e6 / n'
  bench "log" (ops := n) (param := p) fun i => sweep F64.log (blackBox i 1.0e-3) lx n 0
  bench "log_libm" (ops := n) (param := p) fun i => sweep Float.log (blackBox i 1.0e-3) lx n 0
  bench "expm1" (ops := n) (param := p) fun i => sweep F64.expm1 (blackBox i (-2.0)) (4.0 / n') n 0
  bench "log1p" (ops := n) (param := p) fun i => sweep F64.log1p (blackBox i (-0.5)) (4.0 / n') n 0
  let px := 100.0 / n'
  bench "pow_2.5" (ops := n) (param := p) fun i => sweep2 F64.pow (blackBox i 1.0e-3) px 2.5 n 0
  bench "pow_2.5_libm" (ops := n) (param := p) fun i => sweep2 Float.pow (blackBox i 1.0e-3) px 2.5 n 0
  bench "pow_int7" (ops := n) (param := p) fun i => sweep pow7 (blackBox i 1.0e-3) px n 0⟩

end Bench.Math

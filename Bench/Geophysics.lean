import Bench.Harness
import Geophysics

/-!
# `geophysics`: standard-atmosphere profiles

Julia twin: `oracle/bench/geophysics.jl` (Geophysics.jl included from its source, as in the
oracle). ns per evaluation of the `Earth1959` altitude functions over a grid of `n = 10⁵`
geopotential altitudes (−2 km … 78 km, step 0.8 m), Somigliana gravity over latitudes, and the
Julia elementary functions Geophysics ports (`JMath`) against libm (`*_libm`, Lean-only).
Replaces `Tests/Geophysics/Bench.lean` (previous reference numbers: temperature 3.6, pressure
15.2, density 14.5, sonicspeed 189, viscosity 54.9, kinematic 74.9, gravity 3.0 ns in Julia).
-/

namespace Bench.Geophysics

open _root_.Geophysics Bench

/-- Sum an operation of a column over a grid. -/
def loop (C : Column 11) (o : Op) (hs : FloatArray) (i : Nat) (acc : Float) : Float :=
  if h : i < hs.size then loop C o hs (i + 1) (acc + C.eval o (hs[i]'h)) else acc
termination_by hs.size - i

/-- Sum a scalar function over a grid. -/
@[specialize] def loopF (f : Float → Float) (hs : FloatArray) (i : Nat) (acc : Float) : Float :=
  if h : i < hs.size then loopF f hs (i + 1) (acc + f (hs[i]'h)) else acc
termination_by hs.size - i

/-- `x^-5.25` with Julia's `^`. -/ def fPow (x : Float) : Float := JMath.pow x (-5.25)
/-- `x^-5.25` with libm. -/ def fLibPow (x : Float) : Float := Float.pow x (-5.25)
/-- Somigliana gravity on Earth. -/ def fGravity (ϕ : Float) : Float := Earth.gravity ϕ

/-- `n` points `a + i·d` (as Julia's comprehension `a + i * d`). -/
def grid (n : Nat) (a d : Float) : FloatArray :=
  (List.range n).foldl (fun acc i => acc.push (a + i.toUInt64.toFloat * d)) (FloatArray.emptyWithCapacity n)

/-- The suite. -/
def suite : Suite := ⟨"geophysics", do
  let n ← size 100000 1000
  let p := s!"n={n}"
  let C := Earth1959.native
  let hs := grid n (-2000.0) 0.8
  for o in [Op.temperature, .pressure, .density, .sonicspeed, .viscosity, .kinematic] do
    bench o.name (ops := n) (param := p) fun s => loop (blackBox s C) o hs 0 0.0
  let xs := grid n 0.5 1.0e-6
  bench "jmath_pow" (ops := n) (param := p) fun s => loopF fPow (blackBox s xs) 0 0.0
  bench "pow_libm" (ops := n) (param := p) fun s => loopF fLibPow (blackBox s xs) 0 0.0
  bench "jmath_exp" (ops := n) (param := p) fun s => loopF JMath.exp (blackBox s xs) 0 0.0
  bench "exp_libm" (ops := n) (param := p) fun s => loopF Float.exp (blackBox s xs) 0 0.0
  bench "jmath_sin" (ops := n) (param := p) fun s => loopF JMath.sin (blackBox s xs) 0 0.0
  bench "sin_libm" (ops := n) (param := p) fun s => loopF Float.sin (blackBox s xs) 0 0.0
  bench "jmath_atan" (ops := n) (param := p) fun s => loopF JMath.atan (blackBox s xs) 0 0.0
  let ϕs := grid n 0.0 1.5e-5
  bench "gravity" (ops := n) (param := p) fun s => loopF fGravity (blackBox s ϕs) 0 0.0⟩

end Bench.Geophysics

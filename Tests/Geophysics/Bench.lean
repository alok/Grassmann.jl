import Geophysics

/-!
# Geophysics micro-benchmarks

`Tests.GeophysicsBench.run` times the altitude functions of `Earth1959` on a
10⁶-point grid (−2 km … 798 km), Julia's elementary functions and Somigliana
gravity, printing ns per evaluation; it checks nothing and returns `(0, 0)`.
Julia reference (same grids, `oracle/geophysics/bench.jl`): temperature 3.6,
pressure 15.2, density 14.5, sonicspeed 189, viscosity 54.9, kinematic 74.9,
`gravity(ϕ, Earth)` 3.0 ns.

Each timed loop's result feeds the second clock read, so the pure computation
cannot float past it; the element functions are top-level definitions so their
literals are hoisted constants.
-/

namespace Tests.GeophysicsBench

open Geophysics

/-- Sum an operation of a column over a grid. -/
def loop (C : Column 11) (o : Op) (hs : FloatArray) (i : Nat) (acc : Float) : Float :=
  if h : i < hs.size then loop C o hs (i + 1) (acc + C.eval o (hs[i]'h)) else acc
termination_by hs.size - i

/-- Sum a scalar function over a grid. -/
def loopF (f : Float → Float) (hs : FloatArray) (i : Nat) (acc : Float) : Float :=
  if h : i < hs.size then loopF f hs (i + 1) (acc + f (hs[i]'h)) else acc
termination_by hs.size - i

/-- `x^-5.25` with Julia's `^`. -/ def fPow (x : Float) : Float := JMath.pow x (-5.25)
/-- `x^-5.25` with libm. -/ def fLibPow (x : Float) : Float := Float.pow x (-5.25)
/-- Somigliana gravity on Earth. -/ def fGravity (ϕ : Float) : Float := Earth.gravity ϕ

/-- `n` evenly spaced points from `a` with step `d`. -/
def grid (n : Nat) (a d : Float) : FloatArray :=
  (List.range n).foldl (fun acc i => acc.push (a + i.toFloat * d)) (FloatArray.emptyWithCapacity n)

/-- Time `f` and print ns per evaluation. -/
def time (name : String) (n : Nat) (f : Unit → Float) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let s := f ()
  let t1 ← if s.isNaN then IO.monoNanosNow else IO.monoNanosNow
  IO.println s!"  {name}: {(t1 - t0).toFloat / n.toFloat} ns/eval (checksum {s})"

/-- Run the benchmarks. -/
def run : IO (Nat × Nat) := do
  let C := Earth1959.native
  let n := 1000000
  let hs := grid n (-2000.0) 0.8
  for o in [Op.temperature, .pressure, .density, .sonicspeed, .viscosity, .kinematic] do
    time o.name n fun _ => loop C o hs 0 0.0
  let xs := grid n 0.5 1.0e-6
  for (nm, f) in [("JMath.pow", fPow), ("libm pow", fLibPow), ("JMath.exp", JMath.exp),
      ("libm exp", Float.exp), ("JMath.sin", JMath.sin), ("libm sin", Float.sin),
      ("JMath.atan", JMath.atan)] do
    time nm n fun _ => loopF f xs 0 0.0
  let ϕs := grid n 0.0 1.5e-6
  time "Earth.gravity ϕ" n fun _ => loopF fGravity ϕs 0 0.0
  return (0, 0)

end Tests.GeophysicsBench

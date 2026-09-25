/-
A tiny test harness shared by the AbstractTensors suites: a pass/fail
counter that prints failures, and bitwise/ulp float comparisons.
-/
import StaticVectors

namespace Tests.AbstractTensors

open StaticVectors

/-- Pass/fail tally of one suite. -/
structure Tally where
  /-- Number of passing checks. -/
  passed : Nat := 0
  /-- Number of failing checks. -/
  failed : Nat := 0

/-- A test monad: a tally in `IO`. -/
abbrev TestM := StateT Tally IO

/-- Record one check; print a line on failure. -/
def check (ok : Bool) (msg : Unit → String) : TestM Unit := do
  if ok then modify fun t => { t with passed := t.passed + 1 }
  else
    modify fun t => { t with failed := t.failed + 1 }
    IO.println s!"  FAIL {msg ()}"

/-- Run a suite, printing its summary; returns `(passed, failed)`. -/
def runSuite (name : String) (m : TestM Unit) : IO (Nat × Nat) := do
  let ((), t) ← m.run {}
  IO.println s!"{name}: {t.passed} passed, {t.failed} failed"
  return (t.passed, t.failed)

/-- A float from its IEEE bits. -/
@[inline] def fb (b : UInt64) : Float := Float.ofBits b

/-- Julia-style hex rendering of a float's bits, with its value. -/
def showF (x : Float) : String := s!"{x} (0x{String.ofList (Nat.toDigits 16 x.toBits.toNat)})"

/-- Bitwise equality up to the NaN payload (`±0` distinguished). -/
@[inline] def same (x y : Float) : Bool := Julia.sameBits x y

/-- Within `k` ulps (NaNs equal to each other only). -/
@[inline] def ulpClose (k : Nat) (x y : Float) : Bool := Julia.ulpDist x y ≤ k

/-- Close in the relative sense `|x - y| ≤ rtol·max(|x|,|y|) + atol`, or bitwise equal. -/
@[inline] def relClose (rtol atol : Float) (x y : Float) : Bool :=
  same x y || (x - y).abs ≤ rtol * Julia.max x.abs y.abs + atol

end Tests.AbstractTensors

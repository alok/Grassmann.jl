import Tests.Geophysics.Common
import Tests.Geophysics.Math
import Tests.Geophysics.Planets
import Tests.Geophysics.Gases
import Tests.Geophysics.Weather
import Tests.Geophysics.Display

/-!
# Geophysics test aggregator

`Tests.Geophysics.run` returns `(passed, failed)` over the Geophysics goldens
(`oracle/golden/geophysics/`, written by `oracle/geophysics/gen.jl`). Every
float must match Julia bit for bit.
-/

namespace Tests.Geophysics

open Tests.GeophysicsTests _root_.Geophysics

/-- Run all Geophysics suites; returns `(passed, failed)`. -/
def run : IO (Nat × Nat) := do
  IO.println "Geophysics"
  let mut pass := 0
  let mut fail := 0
  let suites : List (IO Tally) :=
    [mathSuite, unitsSuite, planetsSuite, gasesSuite, fluidSuite, displaySuite, customSuite] ++
      weathers.map (weatherSuite ·.1)
  for suite in suites do
    let t0 ← IO.monoMsNow
    let t ← suite
    let t1 ← IO.monoMsNow
    let (p, f) ← ({ t with s := { t.s with name := s!"{t.s.name} ({t1 - t0} ms)" } } : Tally).report
    pass := pass + p
    fail := fail + f
  return (pass, fail)

end Tests.Geophysics

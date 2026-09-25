import Tests.Geophysics.Weather
import Tests.Geophysics.Gases

/-!
# Display goldens

Julia's `show` of every gas, mixture and planet, `display` of the 14 atmosphere
tables and `show` of fluid states (`display.json`; weather displays are checked
per weather).
-/

namespace Tests.GeophysicsTests

open Lean Tests.Units Geophysics UnitSystems

/-- The 14 atmosphere tables with their Julia names. -/
def tables : List (String × Σ n, Atmosphere n) :=
  [("US22", ⟨_, US22⟩), ("US25", ⟨_, US25⟩), ("US56", ⟨_, US56⟩), ("US59", ⟨_, US59⟩),
   ("US62", ⟨_, US62⟩), ("US66", ⟨_, US66⟩), ("US76", ⟨_, US76⟩), ("US22E", ⟨_, US22E⟩),
   ("US25E", ⟨_, US25E⟩), ("US56E", ⟨_, US56E⟩), ("US59E", ⟨_, US59E⟩), ("US62E", ⟨_, US62E⟩),
   ("US66E", ⟨_, US66E⟩), ("US76E", ⟨_, US76E⟩)]

/-- `display.json`. -/
def displaySuite : IO Tally := do
  let j ← load "display"
  let mut t := Tally.new "display"
  for (nm, ⟨_, A⟩) in tables do
    t := t.string A.display (fld (fld j "atmospheres") nm) fun _ => s!"display({nm})"
  for (nm, M) in moles ++ [("Nested", (nested : Mole))] do
    t := t.string M.jshow (fld (fld j "moles") nm) fun _ => s!"show({nm})"
  for (nm, P) in planets do
    t := t.string P.jshow (fld (fld j "planets") nm) fun _ => s!"show({nm})"
  let st := fld j "states"
  t := t.string ((Air : Mole).state 288.15 101325.0).jshow (fld st "Air") fun _ => "show(Air(288.15))"
  t := t.string ((N2 : Mole).state 500.0 2116.2 .English).jshow (fld st "N2_English")
    fun _ => "show(N2(500, 2116.2, English))"
  t := t.string (Earth1959.state 1000.0).jshow (fld st "Earth1959_1000") fun _ => "show(Earth1959(1000))"
  return t

end Tests.GeophysicsTests

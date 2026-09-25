import Tests.UnitSystems.Common

/-!
# UnitSystems: display

`display(U)` of every system, `display(Universe)`, and alias names, against
`oracle/golden/unitsystems/systems.json`.
-/

namespace Tests.UnitSystemsTests

open Lean Tests.Units FieldConstants UnitSystems

/-- `display(U)` of every system, `display(Universe)`, and alias names. -/
def displaySuite : IO (Suite × Suite) := do
  let j ← loadJson "unitsystems/systems.json"
  let mut s : Suite := { name := "display" }
  for r in arr (fld j "systems") do
    let nm := str (fld r "name")
    let some u := Sys.ofName? nm | continue
    let got := u.display
    s := s.check (got == str (fld r "display")) fun _ =>
      s!"display {nm}:\n{got}\nwant\n{str (fld r "display")}"
  let cpl := (Metric Num).C
  s := s.check (cpl.display == str (fld (fld j "coupling") "display")) fun _ =>
    s!"coupling display: {cpl.display}"
  match fld j "aliases" with
  | .obj kvs =>
    for (k, v) in kvs.toList do
      s := s.check (((Sys.ofName? k).map Sys.name) == some (str v)) fun _ => s!"alias {k}"
  | _ => pure ()
  return (s, { name := "display (no bit-exact part)" })

end Tests.UnitSystemsTests

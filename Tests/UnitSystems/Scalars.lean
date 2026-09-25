import Tests.UnitSystems.Common

/-!
# UnitSystems: one-argument functions and module constants

Against `oracle/golden/unitsystems/{scalars,constants}.json`: every constant,
physics quantity, standardized unit and prefix of every one of the 48 systems
(`f(U)`), and the module-level constants.
-/

namespace Tests.UnitSystemsTests

open Lean Tests.Units FieldConstants UnitSystems

/-- One-argument functions × 48 systems. -/
def scalarsSuite : IO (Suite × Suite) := do
  let j ← loadJson "unitsystems/scalars.json"
  let mut s : Suite := { name := "scalars" }
  let mut e : Suite := { name := "scalars (bit-exact)" }
  let funs := fld j "functions"
  let systems := Sys.all.map (·.sys Num)
  let fns : List (String × (UnitSystem Num → Num)) :=
    scalarFunctions ++ [("sackurtetrode", fun U => sackurtetrode U)]
  for (nm, f) in fns do
    let row := arr (fld funs nm)
    s := s.check (row.size == 48) fun _ => s!"no golden for {nm}"
    for (u, U, g) in Sys.all.zip (systems.zip row.toList) |>.map (fun (a, b, c) => (a, b, c)) do
      (s, e) := checkNum s e (f U) (gnum g) fun _ => s!"{nm}({u.name})"
  return (s, e)

/-- Module-level constants. -/
def constantsSuite : IO (Suite × Suite) := do
  let j ← loadJson "unitsystems/constants.json"
  let mut s : Suite := { name := "module constants" }
  let mut e : Suite := { name := "module constants (bit-exact)" }
  let cs := fld j "constants"
  for (nm, x) in moduleConstants do
    let g := fld cs nm
    s := s.check (!g.isNull) fun _ => s!"no golden for {nm}"
    (s, e) := checkNum s e x (gnum g) fun _ => nm
  for (nm, x) in irrationalConstants do
    (s, e) := checkNum s e (.p (.float x)) (gnum (fld cs nm)) fun _ => nm
  return (s, e)

end Tests.UnitSystemsTests

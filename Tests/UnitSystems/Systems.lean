import Tests.UnitSystems.Common

/-!
# UnitSystems: named systems and conversion factors

Against `oracle/golden/unitsystems/{systems,conversions}.json`
(`oracle/unitsystems/systems.jl`): the eleven parameters of all 48 systems, and
31 027 conversion factors `q(U,S)` (every quantity to and from Metric for every
system, plus 20 000 random pairs), `q(U)` for all 131 × 48, and 3000 value
conversions `q(v,U,S)`, `q(v,U)`.
-/

namespace Tests.UnitSystemsTests

open Lean Tests.Units FieldConstants UnitSystems

/-- The eleven parameters of a system in Julia's `slots` order. -/
def params (U : UnitSystem Num) : List Num :=
  [U.kB, U.ħ, U.c, U.μ₀, U.mₑ, U.Mᵤ, U.Kcd, U.θ, U.lam, U.αL, U.g₀]

/-- Named systems: parameters, name, `isrationalized`. -/
def systemsSuite : IO (Suite × Suite) := do
  let j ← loadJson "unitsystems/systems.json"
  let mut s : Suite := { name := "systems" }
  let mut e : Suite := { name := "systems (bit-exact)" }
  let rows := arr (fld j "systems")
  s := s.check (rows.size == 48) fun _ => s!"{rows.size} systems"
  for r in rows do
    let nm := str (fld r "name")
    match Sys.ofName? nm with
    | none => s := s.check false fun _ => s!"unknown system {nm}"
    | some u =>
      let U := u.sys Num
      s := s.check (u.name == str (fld r "show")) fun _ => s!"name {u.name} vs {str (fld r "show")}"
      let ps := (arr (fld r "params")).toList
      for (i, x, g) in (List.range 11).zip ((params U).zip ps) |>.map (fun (i, x, g) => (i, x, g)) do
        (s, e) := checkNum s e x (gnum g) fun _ => s!"{nm} slot {i}"
      let rat := (fld r "isrationalized").getBool?.toOption.getD false
      s := s.check (isrationalized U == rat) fun _ => s!"{nm} isrationalized"
  return (s, e)

/-- Conversion factors and value conversions. -/
def conversionsSuite : IO (Suite × Suite) := do
  let j ← loadJson "unitsystems/conversions.json"
  let mut s : Suite := { name := "conversions" }
  let mut e : Suite := { name := "conversions (bit-exact)" }
  let sysOf (nm : String) : UnitSystem Num := (sysOf! nm).sys Num
  for r in arr (fld j "factors") do
    let qn := str (idx r 0)
    match Conv.ofName? qn with
    | none => s := s.check false fun _ => s!"unknown quantity {qn}"
    | some q =>
      let x := q.factor (sysOf (str (idx r 1))) (sysOf (str (idx r 2)))
      (s, e) := checkNum s e x (gnum (idx r 3)) fun _ => s!"{qn}({str (idx r 1)},{str (idx r 2)})"
  -- q(U) = q(Natural, U)
  let onearg := fld j "onearg"
  for q in Conv.all do
    let row := arr (fld onearg q.name)
    for (u, g) in Sys.all.zip row.toList do
      (s, e) := checkNum s e (q.natural (u.sys Num)) (gnum g) fun _ => s!"{q.name}({u.name})"
  -- q(v, U, S) with a plain value v, and q(v, U) = q(v, U, Metric)
  for r in arr (fld j "values") do
    let some q := Conv.ofName? (str (idx r 0)) | continue
    let U := sysOf (str (idx r 1))
    let S := sysOf (str (idx r 2))
    let v : Num := match gnum (idx r 3) with
      | .int n => .p (.int (Int64.ofInt n))
      | .float x => .p (.float x)
      | .err _ => .p (.int 0)
    (s, e) := checkNum s e (q.convert v U S) (gnum (idx r 4)) fun _ =>
      s!"{q.name}({v},{str (idx r 1)},{str (idx r 2)})"
    (s, e) := checkNum s e (q.convert v U (Metric Num)) (gnum (idx r 5)) fun _ =>
      s!"{q.name}({v},{str (idx r 1)})"
  return (s, e)

end Tests.UnitSystemsTests

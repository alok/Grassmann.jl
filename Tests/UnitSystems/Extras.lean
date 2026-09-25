import Tests.UnitSystems.Common
import Tests.UnitSystems.Systems

/-!
# UnitSystems: perturbed couplings and constructors

Against `oracle/golden/unitsystems/extras.json` (`oracle/unitsystems/extras.jl`):
30 `Coupling`-aware constants of all 48 systems evaluated with a perturbed
universe (this is what exposes the value-dispatch overrides), and the
`MetricSystem`/`ConventionalSystem`/`EntropySystem`/`AstronomicalSystem`/
`ElectricSystem`/`GaussSystem`/`RankineSystem` constructors on random arguments.
-/

namespace Tests.UnitSystemsTests

open Lean Tests.Units FieldConstants UnitSystems

/-- A plain Julia number from a golden. -/
def plainOf (j : Json) : Num :=
  match gnum j with
  | .int n => .p (.int (Int64.ofInt n))
  | .float x => .p (.float x)
  | .err _ => .p (.int 0)

/-- A `Constant` from a golden float argument. -/
def constOf (j : Json) : Num := .c (.float ((j.getNum?.toOption.map (·.toFloat)).getD 0.0))

/-- Coupling-aware constants with a perturbed universe. -/
def couplingSuite : IO (Suite × Suite) := do
  let j ← loadJson "unitsystems/extras.json"
  let mut s : Suite := { name := "perturbed coupling" }
  let mut e : Suite := { name := "perturbed coupling (bit-exact)" }
  let cs := (arr (fld j "coupling")).map plainOf
  let C : Coupling Num := ⟨cs[0]!, cs[1]!, cs[2]!, cs[3]!, cs[4]!⟩
  let fns : List (String × (UnitSystem Num → Num)) :=
    [("planckmass", fun U => planckmass U C), ("planck", fun U => planckC U C),
     ("gravitation", fun U => gravitation U C), ("elementarycharge", fun U => elementarycharge U C),
     ("dalton", fun U => dalton U C), ("protonmass", fun U => protonmass U C),
     ("einstein", fun U => einstein U C), ("molargas", fun U => molargas U C),
     ("stefan", fun U => stefan U C), ("radiationdensity", fun U => radiationdensity U C),
     ("vacuumpermittivity", fun U => vacuumpermittivity U C),
     ("electrostatic", fun U => electrostatic U C), ("biotsavart", fun U => biotsavart U C),
     ("vacuumimpedance", fun U => vacuumimpedance U C), ("faraday", fun U => faraday U C),
     ("josephson", fun U => josephson U C), ("magneticfluxquantum", fun U => magneticfluxquantum U C),
     ("klitzing", fun U => klitzing U C), ("conductancequantum", fun U => conductancequantum U C),
     ("hartree", fun U => hartree U C), ("rydberg", fun U => rydberg U C), ("bohr", fun U => bohr U C),
     ("electronradius", fun U => electronradius U C), ("magneton", fun U => magneton U C),
     ("avogadro", fun U => avogadro U C), ("cosmological", fun U => cosmological U C),
     ("electronmass", fun U => electronmassC U C), ("lightspeed", fun U => lightspeedC U C),
     ("planckreduced", fun U => planckreducedC U C), ("vacuumpermeability", fun U => vacuumpermeabilityC U C)]
  let coupled := fld j "coupled"
  for (nm, f) in fns do
    let row := arr (fld coupled nm)
    for (u, g) in Sys.all.zip row.toList do
      (s, e) := checkNum s e (f (u.sys Num)) (gnum g) fun _ => s!"{nm}({u.name}, C)"
  return (s, e)

/-- Constructors on random arguments. -/
def constructorsSuite : IO (Suite × Suite) := do
  let j ← loadJson "unitsystems/extras.json"
  let mut s : Suite := { name := "constructors" }
  let mut e : Suite := { name := "constructors (bit-exact)" }
  for r in arr (fld j "constructors") do
    let ctor := str (fld r "ctor")
    let a := (arr (fld r "args")).map constOf
    let B := (sysOf! (str (fld r "base"))).sys Num
    let U? : Option (UnitSystem Num) := match ctor with
      | "MetricSystem" => some (MetricSystem Num a[0]! a[1]! a[2]! a[3]! a[4]!)
      | "ConventionalSystem" => some (ConventionalSystem Num a[0]! a[1]!)
      | "EntropySystem" => some (EntropySystem B a[0]! a[1]! a[2]! a[3]!)
      | "AstronomicalSystem" => some (AstronomicalSystem B a[0]! a[1]! a[2]!)
      | "ElectricSystem" => some (ElectricSystem B a[0]! a[1]!)
      | "GaussSystem" => some (GaussSystem B a[0]! a[1]! (some a[2]!))
      | "RankineSystem" => some (RankineSystem Num B a[0]! a[1]! a[2]!)
      | _ => none
    match U? with
    | none => s := s.check false fun _ => s!"unknown constructor {ctor}"
    | some U =>
      for (i, x, g) in (List.range 11).zip ((params U).zip (arr (fld r "out")).toList) |>.map (fun (i, x, g) => (i, x, g)) do
        (s, e) := checkNum s e x (gnum g) fun _ => s!"{ctor}({str (fld r "base")}) slot {i}"
  -- rescaled systems and their names
  for r in arr (fld j "rescale") do
    let a := (arr (fld r "args")).map plainOf
    let B := (sysOf! (str (fld r "base"))).sys Num
    let U := B.rescale a[0]! a[1]! a[2]! a[3]! a[4]!
    for (i, x, g) in (List.range 11).zip ((params U).zip (arr (fld r "out")).toList) |>.map (fun (i, x, g) => (i, x, g)) do
      (s, e) := checkNum s e x (gnum g) fun _ => s!"rescale {str (fld r "base")} slot {i}"
    s := s.check (U.unitname == str (fld r "name")) fun _ => s!"rescale name {U.unitname}"
  for (u : Sys) in Sys.all do
    s := s.check ((u.sys Num).unitname == u.name) fun _ => s!"unitname {u.name}"
    s := s.check ((u.sys Num).displayAny == u.display) fun _ => s!"displayAny {u.name}"
  -- conversion helpers
  for r in arr (fld j "helpers") do
    let f := str (idx r 0)
    let x := plainOf (idx r 1)
    let sn := str (idx r 3)
    let U? : Option (UnitSystem Num) := if sn == "" then none else some ((sysOf! sn).sys Num)
    let got : Option Num := match f, U? with
      | "kilograms", none => some (kilograms x) | "kilograms", some U => some (kilograms x U)
      | "slugs", none => some (slugs x) | "slugs", some U => some (slugs x U)
      | "feet", none => some (feet x) | "feet", some U => some (feet x U)
      | "meters", none => some (meters x) | "meters", some U => some (meters x U)
      | "moles", none => some (moles x) | "moles", some U => some (moles x U)
      | "molecules", none => some (molecules x) | "molecules", some U => some (molecules x U)
      | _, _ => none
    match got with
    | some y => (s, e) := checkNum s e y (gnum (idx r 2)) fun _ => s!"{f}({x}, {sn})"
    | none => s := s.check false fun _ => s!"unknown helper {f}"
  return (s, e)

end Tests.UnitSystemsTests

import Tests.Geophysics.Common

/-!
# Gas, mixture and fluid-state goldens

`gases.json`: 11 gases, 5 mixtures and a nested mixture; their parameters and
the ten temperature functions on an 82-point temperature grid in five unit
systems, plus the Einstein function. `fluidstate.json`: 72 fluid states and all
their derived properties in their own units, English and British.
-/

namespace Tests.GeophysicsTests

open Lean Tests.Units Geophysics UnitSystems

/-- The nested mixture of the goldens: `0.5Nitrox + 0.25N₂ + 0.25(0.5Ar + 0.5CO₂)`. -/
def nested : Mixture := 0.5 * Nitrox + 0.25 * N2 + 0.25 * (0.5 * Ar + 0.5 * CO2)

/-- The vibrational data of a substance (Julia `wavenumber` & co.; empty for a
mixture or a family without vibrations, which are Julia errors). -/
def vibData (M : Mole) (U : Units) (f : MoleGas → Units → FloatArray) : List Float :=
  match M with
  | .gas g => (f g U).toList
  | .mix _ => []

/-- Compare a scalar-or-tuple golden with a list. -/
def Tally.scalarOrList (t : Tally) (got : List Float) (want : Json) (what : Unit → String) :
    Tally :=
  match want with
  | .str _ => t.fs got (Json.arr #[want]) what
  | _ => t.fs got want what

/-- `gases.json`. -/
def gasesSuite : IO Tally := do
  let j ← load "gases"
  let mut t := Tally.new "gases"
  let ein := fld j "_einstein"
  t := t.fs ((floats (fld ein "x")).toList.map einstein) (fld ein "y") fun _ => "einstein"
  for (nm, M) in moles ++ [("Nested", (nested : Mole))] do
    let d := fld j nm
    t := t.f M.relativemass (fld d "relativemass") fun _ => s!"{nm} relativemass"
    t := t.fs M.fractions.toList (fld d "fractions") fun _ => s!"{nm} fractions"
    for un in ["Metric", "English", "British", "Gauss", "IPS"] do
      let U := sysOf un
      let u := Units.of U
      let s := fld d un
      let w (k : String) := s!"{nm} {un} {k}"
      t := t.f (M.molarmass U) (fld s "molarmass") fun _ => w "molarmass"
      t := t.f (M.molecularmass U) (fld s "molecularmass") fun _ => w "molecularmass"
      t := t.f (M.gasconstant U) (fld s "gasconstant") fun _ => w "gasconstant"
      t := t.f (M.viscosityParam U) (fld s "viscosityParam") fun _ => w "viscosityParam"
      t := t.f (M.conductivityParam U) (fld s "conductivityParam") fun _ => w "conductivityParam"
      t := t.f (M.sutherlandviscosity U) (fld s "sutherlandviscosity") fun _ => w "sutherlandviscosity"
      t := t.f (M.sutherlandconductivity U) (fld s "sutherlandconductivity")
        fun _ => w "sutherlandconductivity"
      t := t.scalarOrList (vibData M u MoleGas.wavenumber) (fld s "wavenumber") fun _ => w "wavenumber"
      t := t.scalarOrList (vibData M u MoleGas.wavelength) (fld s "wavelength") fun _ => w "wavelength"
      t := t.scalarOrList (vibData M u MoleGas.frequency) (fld s "frequency") fun _ => w "frequency"
      t := t.scalarOrList (vibData M u MoleGas.vibration) (fld s "vibration") fun _ => w "vibration"
      t := t.f (M.heatratioRef U) (fld s "heatratioRef") fun _ => w "heatratioRef"
      t := t.f (M.heatvolumeRef U) (fld s "heatvolumeRef") fun _ => w "heatvolumeRef"
      t := t.f (M.heatpressureRef U) (fld s "heatpressureRef") fun _ => w "heatpressureRef"
      let Ts := (floats (fld s "T")).toList
      let g (k : String) (f : Float → Float) : Tally → Tally := fun t =>
        t.fs (Ts.map f) (fld s k) fun _ => w k
      t := t |> g "viscosity" (M.viscosity · U) |> g "thermalconductivity" (M.thermalconductivity · U)
        |> g "heatvolume" (M.heatvolume · U) |> g "heatpressure" (M.heatpressure · U)
        |> g "heatratio" (M.heatratio · U) |> g "specificenergy" (M.specificenergy · U)
        |> g "specificenthalpy" (M.specificenthalpy · U) |> g "freedom" (M.freedom · U)
        |> g "prandtl" (M.prandtl · U) |> g "sonicspeed" (M.sonicspeed · U)
  return t

/-- The fluid-state functions of `fluidstate.json`, by Julia name. -/
def fluidFunctions : List (String × (FluidState → Sys → Float)) :=
  [("temperature", fun F U => F.temperature U), ("pressure", fun F U => F.pressure U),
   ("density", fun F U => F.density U), ("specificvolume", fun F U => F.specificvolume U),
   ("kinematic", fun F U => F.kinematic U), ("heatcapacity", fun F U => F.heatcapacity U),
   ("thermaldiffusivity", fun F U => F.thermaldiffusivity U),
   ("elasticity", fun F U => F.elasticity U),
   ("specificimpedance", fun F U => F.specificimpedance U),
   ("viscosity", fun F U => F.viscosity U),
   ("thermalconductivity", fun F U => F.thermalconductivity U),
   ("heatvolume", fun F U => F.heatvolume U), ("heatpressure", fun F U => F.heatpressure U),
   ("heatratio", fun F U => F.heatratio U), ("prandtl", fun F U => F.prandtl U),
   ("sonicspeed", fun F U => F.sonicspeed U), ("freedom", fun F U => F.freedom U),
   ("specificenergy", fun F U => F.specificenergy U),
   ("specificenthalpy", fun F U => F.specificenthalpy U),
   ("molecularmass", fun F U => F.molecularmass U), ("gasconstant", fun F U => F.gasconstant U),
   ("intensity", fun F U => F.intensity U)]

/-- `fluidstate.json`. -/
def fluidSuite : IO Tally := do
  let j ← load "fluidstate"
  let mut t := Tally.new "fluid states"
  let fluids : List (String × Mole) := [("Air", Air), ("N2", N2), ("Ar", Ar), ("CO2", CO2)]
  for c in arr (fld j "cases") do
    let nm := str (fld c "fluid")
    let M := (fluids.lookup nm).getD Air
    let F := M.state (float1 (fld c "T")) (float1 (fld c "P"))
    for (key, U) in [("native", F.units), ("English", Sys.English), ("British", .British)] do
      let s := fld c key
      for (fn, f) in fluidFunctions do
        t := t.f (f F U) (fld s fn) fun _ => s!"{nm} {fmt F.T} {fmt F.P} {key} {fn}"
    let E := F.toUnits .English
    t := t.fs [E.temperature, E.pressure] (fld c "toEnglish") fun _ => s!"{nm} English(F)"
  return t

end Tests.GeophysicsTests

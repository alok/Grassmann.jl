import Tests.Geophysics.Common

/-!
# Julia elementary functions and unit factors

`math.json` samples Julia's own `sin/cos/tan/atan/asin/atanh/log1p/exp/^`
(`JuliaBase.F64.sin`, … must match bit for bit); `units.json` holds the UnitSystems
constants behind `Geophysics.Units` for five systems.
-/

namespace Tests.GeophysicsTests

open Lean Tests.Units Geophysics UnitSystems JuliaBase

/-- `math.json`: Julia's elementary functions. -/
def mathSuite : IO Tally := do
  let j ← load "math"
  let mut t := Tally.new "math (JuliaBase vs Julia)"
  for r in arr (fld j "trig") do
    let x := float1 (idx r 0)
    t := t.f (F64.sin x) (idx r 1) fun _ => s!"sin {fmt x}"
    t := t.f (F64.cos x) (idx r 2) fun _ => s!"cos {fmt x}"
    t := t.f (F64.tan x) (idx r 3) fun _ => s!"tan {fmt x}"
  for r in arr (fld j "atan") do
    let x := float1 (idx r 0)
    t := t.f (F64.atan x) (idx r 1) fun _ => s!"atan {fmt x}"
  for r in arr (fld j "arc") do
    let x := float1 (idx r 0)
    t := t.f (F64.asin x) (idx r 1) fun _ => s!"asin {fmt x}"
    t := t.f (F64.atanh x) (idx r 2) fun _ => s!"atanh {fmt x}"
    t := t.f (F64.log1p x) (idx r 3) fun _ => s!"log1p {fmt x}"
  for r in arr (fld j "exp") do
    let x := float1 (idx r 0)
    t := t.f (F64.exp x) (idx r 1) fun _ => s!"exp {fmt x}"
  for r in arr (fld j "pow") do
    let x := float1 (idx r 0)
    let y := float1 (idx r 1)
    t := t.f (F64.pow x y) (idx r 2) fun _ => s!"pow {fmt x} {fmt y}"
  return t

/-- `units.json`: the constants of `Geophysics.Units` against UnitSystems.jl. -/
def unitsSuite : IO Tally := do
  let j ← load "units"
  let mut t := Tally.new "units"
  for (nm, U) in [("Metric", Sys.Metric), ("English", .English), ("British", .British),
      ("Gauss", .Gauss), ("IPS", .IPS)] do
    let u := Units.of U
    let d := fld j nm
    let inv (k : String) : Float := 1.0 / float1 (fld d k)
    t := t.ok (u.sys == U) fun _ => s!"{nm}: table order"
    t := t.f u.lengthM (fld d "lengthM") fun _ => s!"{nm} lengthM"
    t := t.f u.timeM (fld d "timeM") fun _ => s!"{nm} timeM"
    t := t.ok (sameBits u.gravitationInv (inv "gravitationDen")) fun _ => s!"{nm} gravitationInv"
    t := t.ok (sameBits u.newtonInv (inv "G")) fun _ => s!"{nm} newtonInv"
    t := t.f u.gc (fld d "gc") fun _ => s!"{nm} gc"
    t := t.ok (sameBits u.gcInv (inv "gc")) fun _ => s!"{nm} gcInv"
    t := t.f u.molar (fld d "molar") fun _ => s!"{nm} molar"
    t := t.ok (sameBits u.avogadroInv (inv "avogadro")) fun _ => s!"{nm} avogadroInv"
    t := t.f u.universal (fld d "universal") fun _ => s!"{nm} universal"
    t := t.f u.viscosityM (fld d "viscosityM") fun _ => s!"{nm} viscosityM"
    t := t.f u.temperatureM (fld d "temperatureM") fun _ => s!"{nm} temperatureM"
    t := t.f u.conductivityM (fld d "conductivityM") fun _ => s!"{nm} conductivityM"
    t := t.f u.wavenumberM (fld d "wavenumberM") fun _ => s!"{nm} wavenumberM"
    t := t.f u.lightspeed (fld d "lightspeed") fun _ => s!"{nm} lightspeed"
    t := t.f u.vibration (fld d "vibration") fun _ => s!"{nm} vibration"
    t := t.f u.reference (fld d "reference") fun _ => s!"{nm} reference"
  -- every system of the table is indexed by its constructor
  for s in Sys.all do
    t := t.ok ((Units.of s).sys == s) fun _ => s!"Units.of {s.name}"
  return t

end Tests.GeophysicsTests

import Tests.Geophysics.Common
import Geophysics.Typed

/-!
# Typed quantities and Julia's own tests

Compile-time checks of the typed layer (`Geophysics.Typed`), runtime checks that
it returns exactly the `Float` API's values, and the equalities of Julia's
`test/runtests.jl`.
-/

namespace Tests.GeophysicsTests

open Lean Tests.Units Geophysics UnitSystems Similitude

/-! Typed inputs: an English altitude cannot feed a Metric column, nor a
temperature an altitude. -/
example : Qty .Metric Dim.temperature := (Earth1959.typed .Metric).temperature ⟨1000.0⟩
example : True := by
  fail_if_success
    have : Qty .Metric Dim.temperature :=
      (Earth1959.typed .Metric).temperature (⟨1000.0⟩ : Qty .English Dim.length)
  fail_if_success
    have : Qty .Metric Dim.pressure :=
      (Earth1959.typed .Metric).pressure (⟨288.0⟩ : Qty .Metric Dim.temperature)
  trivial

/-! Julia's `kinematic = viscosity/density` is a diffusivity in Metric only. -/
example : Qty .Metric Dim.diffusivity :=
  ((Earth1959.typed .Metric).kinematic ⟨1000.0⟩).recast Dim.diffusivity
/--
error: could not synthesize default value for parameter '_h' using tactics
---
error: Tactic `decide` proved that the proposition
  Sys.English.hom.halfDim (Dim.viscosity / Dim.density) = Sys.English.hom.halfDim Dim.diffusivity
is false
-/
#guard_msgs in
example : Qty .English Dim.diffusivity :=
  ((Earth1959English.typed .English).kinematic ⟨1000.0⟩).recast Dim.diffusivity

/-! Formula-derived dimensions agree with the named ones where Julia is consistent. -/
example : Qty .English Dim.specificweight := (Earth1959English.typed .English).specificweight ⟨1.0⟩
example : Qty .English Dim.specificenergy := (Earth1959English.typed .English).geopotential ⟨1.0⟩
example : Qty .English Dim.specificvolume := (Earth1959English.typed .English).specificvolume ⟨1.0⟩
example : Qty .Metric Dim.length := (Earth.gravitationQ .Metric / Earth.gravitySphericalQ .Metric).sqrt

/-- Typed results are the `Float` API's, bit for bit; Julia's `runtests.jl`. -/
def typedSuite : IO Tally := do
  let mut t := Tally.new "typed API and runtests.jl"
  for (U, W) in [(Sys.Metric, Earth1959), (.English, Earth1959), (.British, Earth1959)] do
    let C := W.typed U
    let N := W.column U
    for h in [-1000.0, 0.0, 1000.0, 11000.0, 44000.0, 45000.0, 90000.0, 200000.0] do
      let q : Qty U Dim.length := ⟨h⟩
      let same (a b : Float) (what : String) : Tally → Tally :=
        fun t => t.ok (sameBits a b) fun _ => s!"typed {U.name} {what} {h}"
      t := t |> same (C.temperature q).val (N.eval .temperature h) "temperature"
        |> same (C.pressure q).val (N.eval .pressure h) "pressure"
        |> same (C.density q).val (N.eval .density h) "density"
        |> same (C.kinematic q).val (N.eval .kinematic h) "kinematic"
        |> same (C.sonicspeed q).val (N.eval .sonicspeed h) "sonicspeed"
        |> same (C.gravity q).val (N.gravity h) "gravity"
        |> same (C.geopotential q).val (N.geopotential h) "geopotential"
        |> same (C.ratio q .pressure).val (N.ratio .pressure h) "pressureratio"
    t := t.ok (sameBits (Earth.semimajorQ U).val (Earth.semimajor U)) fun _ => s!"semimajorQ {U.name}"
    t := t.ok (sameBits (Earth.gravityQ U stdLatitude).val (Earth.gravity stdLatitude U))
      fun _ => s!"gravityQ {U.name}"
  -- test/runtests.jl: the no-argument defaults equal the Standard(0) fluid state
  let st := Standard.state 0.0
  let W := Standard
  t := t.ok (sameBits W.gravitySea (W.gravity 0.0)) fun _ => "gravity() == gravity(0)"
  t := t.ok (sameBits (W.sea .temperature) st.T) fun _ => "temperature() == temperature(Standard(0))"
  t := t.ok (sameBits (W.sea .pressure) st.pressure) fun _ => "pressure() == pressure(st)"
  t := t.ok (sameBits (W.sea .thermalconductivity) st.thermalconductivity)
    fun _ => "thermalconductivity() == thermalconductivity(st)"
  t := t.ok (sameBits (W.sea .elasticity) st.elasticity) fun _ => "elasticity() == elasticity(st)"
  t := t.ok (sameBits (W.sea .viscosity) st.viscosity) fun _ => "viscosity() == viscosity(st)"
  t := t.ok (sameBits (W.sea .specificenergy) st.specificenergy)
    fun _ => "specificenergy() == specificenergy(st)"
  t := t.ok (sameBits (W.sea .specificenthalpy) st.specificenthalpy)
    fun _ => "specificenthalpy() == specificenthalpy(st)"
  t := t.ok (sameBits (W.sea .sonicspeed) st.sonicspeed) fun _ => "sonicspeed() == sonicspeed(st)"
  -- the port-notes' exact values: Somigliana at the standard latitude, the Nitrox mass
  t := t.ok (W.gravitySea == 9.80665) fun _ => "gravity(Standard) == 9.80665"
  t := t.ok ((Air : Mole).relativemass == 28.965696264700004) fun _ => "Nitrox M"
  t := t.ok (match standard with | .ok ⟨11, _⟩ => true | _ => false) fun _ => "standard()"
  t := t.ok (match standard "1976" true with | .ok ⟨7, _⟩ => true | _ => false)
    fun _ => "standard 1976 english"
  t := t.ok (match standard "2000" with | .error _ => true | _ => false) fun _ => "standard 2000"
  -- explicit-temperature primitives agree with the layer-level operations
  for h in [0.0, 5000.0, 30000.0, 150000.0] do
    let hG := W.altgeopotent h
    let i := W.layer hG
    let T := W.opAt .temperature hG i
    t := t.ok (sameBits (W.pressureT hG T i) (W.opAt .pressure hG i)) fun _ => s!"pressureT {h}"
    t := t.ok (sameBits (W.densityT hG T i) (W.opAt .density hG i)) fun _ => s!"densityT {h}"
    t := t.ok (sameBits (W.kinematicT hG T i) (W.opAt .kinematic hG i)) fun _ => s!"kinematicT {h}"
  t := t.ok (gage 101325.0 == 0.0) fun _ => "gage(atm) == 0"
  t := t.ok (((N2 : Mole).wavenumber).toList == [274400.0]) fun _ => "wavenumber(N2)"
  -- converting a weather to another system and back reproduces the tables to rounding
  let back := (Earth1959.toUnits .English).toUnits .Metric
  for i in List.finRange 11 do
    let rel (a b : Float) := (a - b).abs ≤ 1e-12 * b.abs
    t := t.ok (rel (back.T.get i) (Earth1959.T.get i) && rel (back.p.get i) (Earth1959.p.get i))
      fun _ => s!"Weather.toUnits round trip layer {i}"
  return t

end Tests.GeophysicsTests

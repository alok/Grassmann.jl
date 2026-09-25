import MeasureSystems.Measures

/-!
# Derived units and constants with uncertainties

MeasureSystems re-evaluates Similitude's derived units over its measured
constants (`MeasureSystems.jl:407-414`). Every unit is Similitude's exact value
evaluated with uncertainties (`measured`), except those whose formula involves a
*measured number* rather than a measured generator:

* `μE☾ = measurement("81.300568(3)")` (`MeasureSystems.jl:392`), the Earth–Moon
  mass ratio, which Similitude keeps as a plain `Float64`: `lunarmass = earthmass/μE☾`
  is a group with the measured coefficient `/81.3005680(30)`;
* sums of constants, which MeasureSystems evaluates to measurements
  (`MeasureSystems.jl:328-337`): `siderealyear`, `siderealmonth`, `synodicmonth`,
  `jovianyear` divide by the square root of a sum of masses.

These are recomputed here in `MValue` arithmetic, with the formulas of
`Similitude.Units` (`derived.jl`, `physics.jl:47-59`). `derivedTable` lists all
193 units; `δμ₀` and the measured module constants follow.
-/

namespace MeasureSystems

open FieldConstants FieldAlgebra UnitSystems Similitude

/-- `μE☾ = measurement("81.300568(3)")`, an independent measurement (tag 45, after
the 44 generators). -/
def μE : MValue := .meas ((Measurement.parse? "81.300568(3)" 45).getD default)

namespace Units

open Similitude.Units (earthmass solarmass jupitermass gaussianyear gaussianmonth jupiterdistance day)

/-- `lunarmass = earthmass/μE☾` with the measured ratio. -/
def lunarmass : Quantity .IAU Dim.mass MValue := measured earthmass / μE

/-- `siderealyear = gaussianyear/√(solarmass+earthmass+lunarmass).v`. -/
def siderealyear : Quantity .IAU Dim.time MValue :=
  measured gaussianyear / QScalar.sqrt (measured solarmass + measured earthmass + lunarmass).val

/-- `siderealmonth = gaussianmonth/normal(sqrt(earthmass(IAUE)+lunarmass(IAUE)))`. -/
def siderealmonth : Quantity .IAU Dim.time MValue :=
  measured gaussianmonth / ((measured earthmass).to .IAUE + lunarmass.to .IAUE).sqrt.val

/-- `synodicmonth = inv(inv(siderealmonth(IAU))-inv(siderealyear(IAU)))`. -/
def synodicmonth : Quantity .IAU Dim.time MValue :=
  ((siderealmonth.to .IAU).inv - (siderealyear.to .IAU).inv).inv

/-- `jovianyear = τ*sqrt(normal(jupiterdistance(IAU)^3/solarmass/gravitation(IAU)))*day/normal(sqrt(solarmass+jupitermass))`. -/
def jovianyear : Quantity .IAU Dim.time MValue :=
  let τ : MValue := .exact UnitAlg.tau
  (τ * QScalar.sqrt (measured ((jupiterdistance.to .IAU).npow 3 / solarmass / gravitation .IAU)).val) *
      measured day / (measured solarmass + measured jupitermass).sqrt.val

/-- A measured quantity together with its system and dimension. -/
structure AnyQM where
  /-- unit system -/
  U : Sys
  /-- USQ dimension -/
  d : Dim
  /-- the quantity -/
  q : Quantity U d MValue

/-- Package a measured quantity. -/
def AnyQM.of {U : Sys} {d : Dim} (q : Quantity U d MValue) : AnyQM := ⟨U, d, q⟩

/-- The units recomputed in `MValue` arithmetic. -/
def remeasured : List (String × AnyQM) :=
  [("lunarmass", .of lunarmass), ("siderealyear", .of siderealyear),
   ("siderealmonth", .of siderealmonth), ("synodicmonth", .of synodicmonth),
   ("jovianyear", .of jovianyear)]

/-- MeasureSystems' derived units by Julia name: Similitude's (`Similitude.Units.table`)
evaluated with uncertainties, the recomputed ones in their place. -/
def derivedTable : List (String × AnyQM) :=
  Similitude.Units.table.map fun (nm, ⟨U, d, q⟩) =>
    (nm, (remeasured.lookup nm).getD ⟨U, d, measured q⟩)

end Units

/-- `δμ₀ = μ₀ - 4π*1e-7` (`MeasureSystems.jl:404`): the measured deviation of the
2019 vacuum permeability from its pre-2019 value, `6.9e-16 ± 1.9e-16`. -/
def δμ₀ : MNum :=
  MNum.sub (productM (match μ₀ Scalar with | .grp g => g | _ => Group.one))
    (.float (f64! 12.566370614359172 * f64! 1e-7))

/-! ### Named measured constants (UnitSystems `systems.jl:28-72` re-evaluated)

The SI2019 quantities of the physics constants, with uncertainties. -/

namespace Constants

/-- A generator of the measured constants group as a value. -/
private def gen (i : Nat) (h : i < 44 := by decide) : MValue := .exact (.grp (Consts.gen i h))

/-- `eV = electronvolt(SI2019)` -/ def eV := measured Similitude.Units.electronvolt
/-- `κ = einstein(SI2019)` -/ def κ := measured (Similitude.einstein .SI2019)
/-- `σ = stefan(SI2019)` -/ def σ := measured (Similitude.stefan .SI2019)
/-- `μB = magneton(SI2019)` -/ def μB := measured (Similitude.magneton .SI2019)
/-- `ε₀ = vacuumpermittivity(SI2019)` -/ def ε₀ := measured (Similitude.vacuumpermittivity .SI2019)
/-- `kₑ = electrostatic(SI2019)` -/ def kₑ := measured (Similitude.electrostatic .SI2019)
/-- `mₚ = protonmass(SI2019)` -/ def mₚ := measured (Similitude.protonmass .SI2019)
/-- `Da = dalton(SI2019)` -/ def Da := measured (Similitude.dalton .SI2019)
/-- `𝔉 = faraday(SI2019)` -/ def 𝔉 := measured (Similitude.faraday .SI2019)
/-- `Φ₀ = magneticfluxquantum(SI2019)` -/ def Φ₀ := measured (Similitude.magneticfluxquantum .SI2019)
/-- `Z₀ = vacuumimpedance(SI2019)` -/ def Z₀ := measured (Similitude.vacuumimpedance .SI2019)
/-- `G₀ = conductancequantum(SI2019)` -/ def G₀ := measured (Similitude.conductancequantum .SI2019)
/-- `Eₕ = hartree(SI2019)` -/ def Eₕ := measured (Similitude.hartree .SI2019)
/-- `a₀ = bohr(SI2019)` -/ def a₀ := measured (Similitude.bohr .SI2019)
/-- `rₑ = electronradius(SI2019)` -/ def rₑ := measured (Similitude.electronradius .SI2019)
/-- `BTUJ = thermalunit(SI2019)` -/ def BTUJ := measured (Similitude.Units.thermalunit.to .SI2019)
/-- `BTUftlb = thermalunit(British)` -/ def BTUftlb := measured (Similitude.Units.thermalunit.to .British)
/-- `kcal = kilocalorie(SI2019)` -/ def kcal := measured (Similitude.Units.kilocalorie.to .SI2019)
/-- `cal = calorie(SI2019)` -/ def cal := measured (Similitude.Units.calorie.to .SI2019)
/-- `RK = RK2014`, the measured von Klitzing constant (a generator) -/ def RK : MValue := gen 24
/-- `KJ = KJ2014`, the measured Josephson constant (a generator) -/ def KJ : MValue := gen 25
/-- `Ry = 𝘩*𝘤*R∞`, the Rydberg energy -/ def Ry : MValue := gen 2 * gen 3 * gen 7
/-- `RH = R∞*mₚ/(mₑ + mₚ)`, the Rydberg constant of hydrogen (a sum: its value is a
group with a measured coefficient). -/
def RH : Quantity .SI2019 Dim.dimensionless MValue :=
  gen 7 * ((measured (Similitude.protonmass .SI2019) /
    (measured (Similitude.electronmass .SI2019) + measured (Similitude.protonmass .SI2019))).recast _)

/-- The named measured constants with their Julia names (displays of values; the
quantities print with their unit and system). -/
def table : List (String × String × MNum) :=
  let q {U : Sys} {d : Dim} (x : Quantity U d MValue) : String × MNum := (toString x, x.val.toMNum)
  let v (x : MValue) : String × MNum := (x.jprint, x.toMNum)
  [("RH", q RH), ("Ry", v Ry), ("eV", q eV), ("κ", q κ), ("σ", q σ), ("μB", q μB), ("ε₀", q ε₀),
   ("kₑ", q kₑ), ("mₚ", q mₚ), ("Da", q Da), ("𝔉", q 𝔉), ("Φ₀", q Φ₀), ("Z₀", q Z₀), ("G₀", q G₀),
   ("Eₕ", q Eₕ), ("a₀", q a₀), ("rₑ", q rₑ), ("RK", v RK), ("KJ", v KJ), ("BTUJ", q BTUJ),
   ("BTUftlb", q BTUftlb), ("kcal", q kcal), ("cal", q cal)]

end Constants

end MeasureSystems

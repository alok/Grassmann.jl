import UnitSystems

/-!
# Unit-system factors used by Geophysics

Geophysics.jl evaluates every formula in a UnitSystems.jl `UnitSystem` `U`
(`src/Geophysics.jl:32-51`). With `usingSimilitude = false` its `Quantity` and
`normal` wrappers are the identity, so the only unit machinery is UnitSystems'
conversion factors and constants, which are `FieldConstants.Constant`s. Mixed
arithmetic between a plain `Float64` and a `Constant` follows
`FieldConstants.jl:64-100`, and the last bits depend on it:

* `x * c` and `c * x` multiply by the payload;
* `x / c` is `x * inv(c)` and `c / x` is `c * inv(x)`, two roundings;
* `c₁ * c₂` and `c₁ / c₂` are closed (`Constant{A*B}`), one rounding.

`Units` evaluates, once per system, the Constants that Geophysics mixes with
Floats, already combined the way Julia combines them, so each Geophysics formula
is plain `Float` arithmetic afterwards. The factors come from the Lean
UnitSystems port (`UnitSystem FieldConstants.Num`), which reproduces Julia's
values bit for bit.
-/

namespace Geophysics

open UnitSystems FieldConstants

/-- UnitSystems' defining constants of the named system `U` as Julia `Constant`s. -/
@[inline] def usys (U : Sys) : UnitSystem Num := Sys.sys Num U

/-- Julia `q(U, S)`: how many `S`-units make one `U`-unit of quantity `q`. -/
def factor (q : Conv) (U S : Sys) : Num := Conv.factor q (usys U) (usys S)

/-- Julia `q(v, U, S)` (`UnitSystems.jl:300-305`) for a plain `Float64` `v`
given in `S`: the value in `U`. It is `v` when the systems are identical or the
factor is exactly one, otherwise `v / q(U, S) = v * inv(q(U, S))`. -/
def convert (q : Conv) (v : Float) (U S : Sys) : Float :=
  if U == S then v
  else
    let u := factor q U S
    if u.v.isOne then v else v * u.inv.toFloat

/-- The UnitSystems constants of one system that Geophysics mixes with `Float64`s
(Julia folds them at compile time from `Constant` type parameters). Each field
is already in the form Julia's mixed arithmetic uses it. -/
structure Units where
  /-- the system -/
  sys : Sys
  /-- `length(Metric, U)`: `semimajor(P, U) = a * length(Metric, U)` -/
  lengthM : Float
  /-- `time(Metric, U)`: `period(P, U) = t * time(Metric, U)` -/
  timeM : Float
  /-- `inv(length(U, Metric) * specificenergy(U, Metric))`: `gravitation(P, U)` -/
  gravitationInv : Float
  /-- `inv(gravitation(U))` (Newton's `G`): `mass(P, U)` -/
  newtonInv : Float
  /-- `gravity(U)`, the force constant `g_c` -/
  gc : Float
  /-- `inv(gravity(U))` -/
  gcInv : Float
  /-- `molarmass(U)`, the molar-mass constant `Mᵤ` -/
  molar : Float
  /-- `inv(avogadro(U))` -/
  avogadroInv : Float
  /-- `universal(U) = molargas(U)`, the molar gas constant -/
  universal : Float
  /-- `viscosity(Metric, U)` -/
  viscosityM : Float
  /-- `temperature(Metric, U)` -/
  temperatureM : Float
  /-- `thermalconductivity(Metric, U)` -/
  conductivityM : Float
  /-- `wavenumber(Metric, U)` -/
  wavenumberM : Float
  /-- `lightspeed(U)` -/
  lightspeed : Float
  /-- `planck(U)/boltzmann(U)/1.2`: the `Constant` ratio times `inv(1.2)` -/
  vibration : Float
  /-- `temperature(288.16, U, Metric)`, the reference temperature of the
  one-argument heat capacities (`chemistry.jl:111-113`) -/
  reference : Float

namespace Units

/-- Evaluate the constants of `U` (`Geophysics.jl`, `chemistry.jl`). -/
def ofSys (U : Sys) : Units :=
  let u := usys U
  let lenUM := factor .length U .Metric
  let seUM := factor .specificenergy U .Metric
  { sys := U
    lengthM := (factor .length .Metric U).toFloat
    timeM := (factor .time .Metric U).toFloat
    gravitationInv := (lenUM * seUM).inv.toFloat
    newtonInv := (UnitSystems.gravitation u).inv.toFloat
    gc := (UnitSystems.gravity u).toFloat
    gcInv := (UnitSystems.gravity u).inv.toFloat
    molar := (UnitSystems.molarmass u).toFloat
    avogadroInv := (UnitSystems.avogadro u).inv.toFloat
    universal := (UnitSystems.molargas u).toFloat
    viscosityM := (factor .viscosity .Metric U).toFloat
    temperatureM := (factor .temperature .Metric U).toFloat
    conductivityM := (factor .thermalconductivity .Metric U).toFloat
    wavenumberM := (factor .wavenumber .Metric U).toFloat
    lightspeed := (UnitSystems.lightspeed u).toFloat
    vibration := (UnitSystems.planck u / UnitSystems.boltzmann u).toFloat * (1.0 / 1.2)
    reference := convert .temperature 288.16 U .Metric }

/-- The Metric constants. -/
def metric : Units := ofSys .Metric

instance : Inhabited Units := ⟨metric⟩

/-- All 48 systems, evaluated once (a closed term, computed at initialization). -/
def table : Array Units := Sys.all.toArray.map ofSys

/-- `Sys.all` lists the systems in constructor order, so `table` is indexed by
`Sys.ctorIdx`. -/
theorem all_ctorIdx : (Sys.all.zipIdx.all fun (s, i) => s.ctorIdx == i) = true := by decide

/-- The constants of `U`, from the precomputed table. -/
@[inline] def of (U : Sys) : Units := table[U.ctorIdx]!

end Units

/-- `x / c` for a plain `Float64` `x` and a `Constant` `c` of UnitSystems:
`x * inv(c)` (`FieldConstants.jl:74`). -/
@[inline] def divConst (x : Float) (c : Num) : Float := x * c.inv.toFloat

end Geophysics

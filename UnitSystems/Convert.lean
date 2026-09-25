import UnitSystems.Physics
import Std.Data.HashMap

/-!
# The 131 conversion factors

`q U S` is how many `S`-units make one `U`-unit of the quantity `q`
(`length English Metric = 0.3048`). Each chain is the Julia definition verbatim
(`kinematic.jl`, `electromagnetic.jl`, `thermodynamic.jl`,
`UnitSystems.jl:279-299`), including every intermediate `unit(…)` snap, so the
`Num` instance agrees with Julia bit for bit; generic in the scalar, the same
chains also compute exact ratios (Similitude) and dimensions
(`UnitSystems.Dims`, where each chain's dimension is proved).

The IAU special cases of `kinematic.jl:45-67` are live: `length` between a
system with `𝘤` (or `𝘤/ft`) and IAU☉ snaps to `1/au`, `au`, `ft/au` or `au/ft`.
The `time` variants pass a snap target that `time` ignores (a Julia bug), and
the CGS variants can never match, so neither changes a result.
-/

namespace UnitSystems

open FieldConstants UnitAlg

namespace Convert

variable {α : Type} [UnitAlg α]

/-- The ratio `unit(f(S)/f(U))` of a defining constant (the `Constants` loop,
`UnitSystems.jl:297-299`). -/
@[inline] def constRatio (f : UnitSystem α → α) (U S : UnitSystem α) : α := unit (f S / f U)

/-- `dimensionless(U,S) = one(U)*one(S)` -/
def dimensionless (U S : UnitSystem α) : α := oneU U * oneU S
/-- `angle(U,S) = unit(radian(S)/radian(U))` -/
def angle (U S : UnitSystem α) : α := unit (S.θ / U.θ)
/-- `solidangle(U,S) = unit(angle(U,S)^2)` -/
def solidangle (U S : UnitSystem α) : α := unit (angle U S ^ (2 : Int))
/-- `mass(U,S) = electronmass(U,S)` -/
def mass (U S : UnitSystem α) : α := constRatio electronmass U S
/-- `speed(U,S) = lightspeed(U,S)` -/
def speed (U S : UnitSystem α) : α := constRatio lightspeed U S
/-- `stagnance(U,S) = lightspeed(S,U)` -/
def stagnance (U S : UnitSystem α) : α := constRatio lightspeed S U
/-- `gravityforce(U,S) = unit(gravity(U,S))` -/
def gravityforce (U S : UnitSystem α) : α := unit (constRatio gravity U S)
/-- `molarmass(U,S)` (constants loop) -/
def molarmass (U S : UnitSystem α) : α := constRatio UnitSystems.molarmass U S
/-- `luminousefficacy(U,S)` (constants loop) -/
def luminousefficacy (U S : UnitSystem α) : α := constRatio UnitSystems.luminousefficacy U S
/-- `permeability(U,S)` (constants loop) -/
def permeability (U S : UnitSystem α) : α := constRatio UnitSystems.permeability U S

/-- `DAY*𝘤/au`: the lightspeed of IAU☉, the pattern of the IAU special cases. -/
def iauLightspeed : α := DAY α * ms α .cc / ms α .au

/-- The snap target of the IAU special cases of `length` (`kinematic.jl:45-67`),
if one applies. -/
def iauSnap (U S : UnitSystem α) : Option α :=
  if !special (α := α) then none
  else
    let c := ms α .cc
    let ciau := iauLightspeed (α := α)
    let cft := c / ms α .ft
    if ident U.c c && ident S.c ciau then some (plit 1 / ms α .au)
    else if ident U.c ciau && ident S.c c then some (ms α .au)
    else if ident U.c cft && ident S.c ciau then some (ms α .ft / ms α .au)
    else if ident U.c ciau && ident S.c cft then some (ms α .au / ms α .ft)
    else none

/-- `length(U,S,l=1) = unit((turn(S)/turn(U))*(ħS·mₑU·cU·gS)/(ħU·mₑS·cS·gU), l)`
(`kinematic.jl:71`), with the IAU snaps. -/
def length (U S : UnitSystem α) : α :=
  let x := (turn S / turn U) * (S.ħ * U.mₑ * U.c * S.g₀) / (U.ħ * S.mₑ * S.c * U.g₀)
  snap x ((iauSnap U S).getD one)

/-- `time(U,S,t=1) = unit(length(U,S)/lightspeed(U,S), 1)` (`kinematic.jl:95`;
the snap argument `t` is ignored in Julia). -/
def time (U S : UnitSystem α) : α := unit (length U S / constRatio lightspeed U S)

/-- `angulartime = unit(time(U,S)*angle(S,U))` -/
def angulartime (U S : UnitSystem α) : α := unit (time U S * angle S U)
/-- `angularlength = unit(length(U,S)*angle(S,U))` -/
def angularlength (U S : UnitSystem α) : α := unit (length U S * angle S U)
/-- `area = unit(length(U,S)^2)` -/
def area (U S : UnitSystem α) : α := unit (length U S ^ (2 : Int))
/-- `angulararea = unit(area(U,S)*solidangle(S,U))` -/
def angulararea (U S : UnitSystem α) : α := unit (area U S * solidangle S U)
/-- `volume = unit(length(U,S)^3)` -/
def volume (U S : UnitSystem α) : α := unit (length U S ^ (3 : Int))
/-- `wavenumber = unit(length(S,U))` -/
def wavenumber (U S : UnitSystem α) : α := unit (length S U)
/-- `angularwavenumber = unit(angle(U,S)*length(S,U))` -/
def angularwavenumber (U S : UnitSystem α) : α := unit (angle U S * length S U)
/-- `fuelefficiency = area(S,U)` -/
def fuelefficiency (U S : UnitSystem α) : α := area S U
/-- `numberdensity = volume(S,U)` -/
def numberdensity (U S : UnitSystem α) : α := volume S U
/-- `frequency = time(S,U)` -/
def frequency (U S : UnitSystem α) : α := time S U
/-- `angularfrequency = unit(angle(U,S)*time(S,U))` -/
def angularfrequency (U S : UnitSystem α) : α := unit (angle U S * time S U)
/-- `frequencydrift = unit(time(S,U)^2)` -/
def frequencydrift (U S : UnitSystem α) : α := unit (time S U ^ (2 : Int))
/-- `acceleration = unit(speed(U,S)/time(U,S))` -/
def acceleration (U S : UnitSystem α) : α := unit (speed U S / time U S)
/-- `jerk = unit(speed(U,S)/time(U,S)^2)` -/
def jerk (U S : UnitSystem α) : α := unit (speed U S / time U S ^ (2 : Int))
/-- `snap = unit(speed(U,S)/time(U,S)^3)` -/
def snap (U S : UnitSystem α) : α := unit (speed U S / time U S ^ (3 : Int))
/-- `crackle = unit(speed(U,S)/time(U,S)^4)` -/
def crackle (U S : UnitSystem α) : α := unit (speed U S / time U S ^ (4 : Int))
/-- `pop = unit(speed(U,S)/time(U,S)^5)` -/
def pop (U S : UnitSystem α) : α := unit (speed U S / time U S ^ (5 : Int))
/-- `volumeflow = unit(area(U,S)*speed(U,S))` -/
def volumeflow (U S : UnitSystem α) : α := unit (area U S * speed U S)
/-- `etendue = unit(area(U,S)*solidangle(U,S))` -/
def etendue (U S : UnitSystem α) : α := unit (area U S * solidangle U S)
/-- `photonintensity = unit(frequency(U,S)/solidangle(U,S))` -/
def photonintensity (U S : UnitSystem α) : α := unit (frequency U S / solidangle U S)
/-- `photonirradiance = unit(length(S,U)*speed(S,U))` (dimension `L⁻²T`, as in Julia) -/
def photonirradiance (U S : UnitSystem α) : α := unit (length S U * speed S U)
/-- `photonradiance = unit(photonirradiance(U,S)/solidangle(U,S))` -/
def photonradiance (U S : UnitSystem α) : α := unit (photonirradiance U S / solidangle U S)

/-- `inertia = unit(mass(U,S)/gravity(U,S))` -/
def inertia (U S : UnitSystem α) : α := unit (mass U S / constRatio gravity U S)
/-- `specificenergy = unit(speed(U,S)^2/gravity(U,S))` -/
def specificenergy (U S : UnitSystem α) : α := unit (speed U S ^ (2 : Int) / constRatio gravity U S)
/-- `energy = unit(mass(U,S)*specificenergy(U,S))` -/
def energy (U S : UnitSystem α) : α := unit (mass U S * specificenergy U S)
/-- `power = unit(energy(U,S)/time(U,S))` -/
def power (U S : UnitSystem α) : α := unit (energy U S / time U S)
/-- `force = unit(inertia(U,S)*acceleration(U,S))` -/
def force (U S : UnitSystem α) : α := unit (inertia U S * acceleration U S)
/-- `specificforce = unit(acceleration(U,S)/gravity(U,S))` -/
def specificforce (U S : UnitSystem α) : α := unit (acceleration U S / constRatio gravity U S)
/-- `pressure = unit(force(U,S)/area(U,S))` -/
def pressure (U S : UnitSystem α) : α := unit (force U S / area U S)
/-- `impulse = unit(force(U,S)*time(U,S))` -/
def impulse (U S : UnitSystem α) : α := unit (force U S * time U S)
/-- `momentum = unit(mass(U,S)*speed(U,S))` -/
def momentum (U S : UnitSystem α) : α := unit (mass U S * speed U S)
/-- `angularmomentum = unit(impulse(U,S)*length(U,S)/angle(U,S))` -/
def angularmomentum (U S : UnitSystem α) : α := unit (impulse U S * length U S / angle U S)
/-- `yank = unit(mass(U,S)*jerk(U,S))` -/
def yank (U S : UnitSystem α) : α := unit (mass U S * jerk U S)
/-- `areadensity = unit(mass(U,S)/area(U,S))` -/
def areadensity (U S : UnitSystem α) : α := unit (mass U S / area U S)
/-- `density = unit(mass(U,S)/volume(U,S))` -/
def density (U S : UnitSystem α) : α := unit (mass U S / volume U S)
/-- `specificweight = unit(force(U,S)/volume(U,S))` -/
def specificweight (U S : UnitSystem α) : α := unit (force U S / volume U S)
/-- `specificvolume = unit(volume(U,S)/mass(U,S))` -/
def specificvolume (U S : UnitSystem α) : α := unit (volume U S / mass U S)
/-- `action = unit(energy(U,S)*time(U,S))` -/
def action (U S : UnitSystem α) : α := unit (energy U S * time U S)
/-- `irradiance = unit(power(U,S)/area(U,S))` -/
def irradiance (U S : UnitSystem α) : α := unit (power U S / area U S)
/-- `radiance = unit(irradiance(U,S)/solidangle(U,S))` -/
def radiance (U S : UnitSystem α) : α := unit (irradiance U S / solidangle U S)
/-- `radiantintensity = unit(power(U,S)/solidangle(U,S))` -/
def radiantintensity (U S : UnitSystem α) : α := unit (power U S / solidangle U S)
/-- `spectralexposure = unit(force(U,S)/speed(U,S))` -/
def spectralexposure (U S : UnitSystem α) : α := unit (force U S / speed U S)
/-- `diffusivity = unit(speed(U,S)*length(U,S))` -/
def diffusivity (U S : UnitSystem α) : α := unit (speed U S * length U S)
/-- `viscosity = unit(force(U,S)/speed(U,S)/length(U,S))` -/
def viscosity (U S : UnitSystem α) : α := unit (force U S / speed U S / length U S)
/-- `lineardensity = unit(mass(U,S)/length(U,S))` -/
def lineardensity (U S : UnitSystem α) : α := unit (mass U S / length U S)
/-- `massflow = unit(mass(U,S)/time(U,S))` -/
def massflow (U S : UnitSystem α) : α := unit (mass U S / time U S)
/-- `spectralflux = unit(power(U,S)/length(U,S))` -/
def spectralflux (U S : UnitSystem α) : α := unit (power U S / length U S)
/-- `powerdensity = unit(power(U,S)/volume(U,S))` -/
def powerdensity (U S : UnitSystem α) : α := unit (power U S / volume U S)
/-- `compressibility = pressure(S,U)` -/
def compressibility (U S : UnitSystem α) : α := pressure S U
/-- `fluence = unit(energy(U,S)/area(U,S))` -/
def fluence (U S : UnitSystem α) : α := unit (energy U S / area U S)
/-- `rotationalinertia = unit(mass(U,S)*area(U,S))` -/
def rotationalinertia (U S : UnitSystem α) : α := unit (mass U S * area U S)
/-- `soundexposure = unit(time(U,S)*pressure(U,S)^2)` -/
def soundexposure (U S : UnitSystem α) : α := unit (time U S * pressure U S ^ (2 : Int))
/-- `specificimpedance = unit(pressure(U,S)/speed(U,S))` -/
def specificimpedance (U S : UnitSystem α) : α := unit (pressure U S / speed U S)
/-- `impedance = unit(specificimpedance(U,S)/area(U,S))` -/
def impedance (U S : UnitSystem α) : α := unit (specificimpedance U S / area U S)
/-- `admittance = unit(area(U,S)/specificimpedance(U,S))` -/
def admittance (U S : UnitSystem α) : α := unit (area U S / specificimpedance U S)
/-- `compliance = unit(time(U,S)^2/mass(U,S))` -/
def compliance (U S : UnitSystem α) : α := unit (time U S ^ (2 : Int) / mass U S)
/-- `inertance = unit(mass(U,S)/length(U,S)^4)` -/
def inertance (U S : UnitSystem α) : α := unit (mass U S / length U S ^ (4 : Int))

/-- `charge(U,S)` (`electromagnetic.jl:15`) -/
def charge (U S : UnitSystem α) : α :=
  unit (UnitAlg.sqrt ((turn S / turn U) *
    (S.ħ * U.μ₀ * U.c * U.lam * U.αL ^ (2 : Int)) / (U.ħ * S.μ₀ * S.c * S.lam * S.αL ^ (2 : Int))))
/-- `current = unit(charge(U,S)/time(U,S))` -/
def current (U S : UnitSystem α) : α := unit (charge U S / time U S)
/-- `electricpotential = unit(energy(U,S)/charge(U,S))` -/
def electricpotential (U S : UnitSystem α) : α := unit (energy U S / charge U S)
/-- `capacitance = unit(charge(U,S)/electricpotential(U,S))` -/
def capacitance (U S : UnitSystem α) : α := unit (charge U S / electricpotential U S)
/-- `resistance = unit(electricpotential(U,S)/current(U,S))` -/
def resistance (U S : UnitSystem α) : α := unit (electricpotential U S / current U S)
/-- `conductance = unit(current(U,S)/electricpotential(U,S))` -/
def conductance (U S : UnitSystem α) : α := unit (current U S / electricpotential U S)
/-- `magneticflux = unit(energy(U,S)/lorentz(U,S)/current(U,S))` -/
def magneticflux (U S : UnitSystem α) : α := unit (energy U S / constRatio lorentz U S / current U S)
/-- `magneticfluxdensity = unit(magneticflux(U,S)/area(U,S))` -/
def magneticfluxdensity (U S : UnitSystem α) : α := unit (magneticflux U S / area U S)
/-- `inductance = unit(magneticflux(U,S)/current(U,S)*lorentz(U,S))` -/
def inductance (U S : UnitSystem α) : α := unit (magneticflux U S / current U S * constRatio lorentz U S)
/-- `linearchargedensity = unit(charge(U,S)/length(U,S))` -/
def linearchargedensity (U S : UnitSystem α) : α := unit (charge U S / length U S)
/-- `electricdisplacement = unit(charge(U,S)*rationalization(U,S)/area(U,S))` -/
def electricdisplacement (U S : UnitSystem α) : α :=
  unit (charge U S * constRatio rationalization U S / area U S)
/-- `chargedensity = unit(charge(U,S)/volume(U,S))` -/
def chargedensity (U S : UnitSystem α) : α := unit (charge U S / volume U S)
/-- `currentdensity = unit(current(U,S)/area(U,S))` -/
def currentdensity (U S : UnitSystem α) : α := unit (current U S / area U S)
/-- `conductivity = unit(conductance(U,S)/length(U,S))` -/
def conductivity (U S : UnitSystem α) : α := unit (conductance U S / length U S)
/-- `permittivity = unit(capacitance(U,S)*rationalization(U,S)/length(U,S))` -/
def permittivity (U S : UnitSystem α) : α :=
  unit (capacitance U S * constRatio rationalization U S / length U S)
/-- `electricfield = unit(electricpotential(U,S)/length(U,S))` -/
def electricfield (U S : UnitSystem α) : α := unit (electricpotential U S / length U S)
/-- `magneticfield = unit(current(U,S)*rationalization(U,S)*lorentz(U,S)/length(U,S))` -/
def magneticfield (U S : UnitSystem α) : α :=
  unit (current U S * constRatio rationalization U S * constRatio lorentz U S / length U S)
/-- `exposure = unit(charge(U,S)/mass(U,S))` -/
def exposure (U S : UnitSystem α) : α := unit (charge U S / mass U S)
/-- `resistivity = unit(resistance(U,S)*length(U,S))` -/
def resistivity (U S : UnitSystem α) : α := unit (resistance U S * length U S)
/-- `magneticdipolemoment = unit(current(U,S)*lorentz(U,S)*area(U,S)/angle(U,S))` -/
def magneticdipolemoment (U S : UnitSystem α) : α :=
  unit (current U S * constRatio lorentz U S * area U S / angle U S)
/-- `mobility = unit(length(U,S)*speed(U,S)*electricpotential(U,S))` -/
def mobility (U S : UnitSystem α) : α := unit (length U S * speed U S * electricpotential U S)
/-- `reluctance = unit(rationalization(U,S)*lorentz(U,S)^2/inductance(U,S))` -/
def reluctance (U S : UnitSystem α) : α :=
  unit (constRatio rationalization U S * constRatio lorentz U S ^ (2 : Int) / inductance U S)
/-- `vectorpotential = unit(magneticflux(U,S)/length(U,S))` -/
def vectorpotential (U S : UnitSystem α) : α := unit (magneticflux U S / length U S)
/-- `magneticmoment = unit(magneticflux(U,S)*length(U,S))` -/
def magneticmoment (U S : UnitSystem α) : α := unit (magneticflux U S * length U S)
/-- `susceptibility = unit(rationalization(S,U))` -/
def susceptibility (U S : UnitSystem α) : α := unit (constRatio rationalization S U)
/-- `electricflux = unit(electricpotential(U,S)*length(U,S))` -/
def electricflux (U S : UnitSystem α) : α := unit (electricpotential U S * length U S)
/-- `electricdipolemoment = unit(charge(U,S)*length(U,S))` -/
def electricdipolemoment (U S : UnitSystem α) : α := unit (charge U S * length U S)
/-- `magneticpotential = unit(magneticflux(U,S)*reluctance(U,S))` -/
def magneticpotential (U S : UnitSystem α) : α := unit (magneticflux U S * reluctance U S)
/-- `polestrength = unit(magneticdipolemoment(U,S)/length(U,S))` -/
def polestrength (U S : UnitSystem α) : α := unit (magneticdipolemoment U S / length U S)
/-- `permeance = reluctance(S,U)` -/
def permeance (U S : UnitSystem α) : α := reluctance S U
/-- `specificsusceptibility = unit(magneticdipolemoment(U,S)/magneticfield(U,S)/mass(U,S))` -/
def specificsusceptibility (U S : UnitSystem α) : α :=
  unit (magneticdipolemoment U S / magneticfield U S / mass U S)
/-- `electricpolarizability = unit(electricdipolemoment(U,S)/electricfield(U,S))` -/
def electricpolarizability (U S : UnitSystem α) : α :=
  unit (electricdipolemoment U S / electricfield U S)
/-- `magneticpolarizability = unit(magneticdipolemoment(U,S)/magneticfield(U,S))` -/
def magneticpolarizability (U S : UnitSystem α) : α :=
  unit (magneticdipolemoment U S / magneticfield U S)
/-- `specificmagnetization = unit(magneticmoment(S,U)/mass(S,U))` (inverted in Julia) -/
def specificmagnetization (U S : UnitSystem α) : α := unit (magneticmoment S U / mass S U)
/-- `demagnetizingfactor = unit(rationalization(U,S))` -/
def demagnetizingfactor (U S : UnitSystem α) : α := unit (constRatio rationalization U S)

/-- `temperature(U,S)` (`thermodynamic.jl:43`) -/
def temperature (U S : UnitSystem α) : α :=
  unit ((U.kB * S.mₑ * S.c ^ (2 : Int) * U.g₀) / (S.kB * U.mₑ * U.c ^ (2 : Int) * S.g₀))
/-- `entropy = unit(energy(U,S)/temperature(U,S))` -/
def entropy (U S : UnitSystem α) : α := unit (energy U S / temperature U S)
/-- `specificentropy = unit(specificenergy(U,S)/temperature(U,S))` -/
def specificentropy (U S : UnitSystem α) : α := unit (specificenergy U S / temperature U S)
/-- `volumeheatcapacity = unit(entropy(U,S)/volume(U,S))` -/
def volumeheatcapacity (U S : UnitSystem α) : α := unit (entropy U S / volume U S)
/-- `thermalconductivity = unit(force(U,S)/time(U,S)/temperature(U,S))` -/
def thermalconductivity (U S : UnitSystem α) : α := unit (force U S / time U S / temperature U S)
/-- `thermalconductance = unit(thermalconductivity(U,S)*length(U,S))` -/
def thermalconductance (U S : UnitSystem α) : α := unit (thermalconductivity U S * length U S)
/-- `thermalresistivity = thermalconductivity(S,U)` -/
def thermalresistivity (U S : UnitSystem α) : α := thermalconductivity S U
/-- `thermalresistance = thermalconductance(S,U)` -/
def thermalresistance (U S : UnitSystem α) : α := thermalconductance S U
/-- `thermalexpansion = temperature(S,U)` -/
def thermalexpansion (U S : UnitSystem α) : α := temperature S U
/-- `lapserate = unit(temperature(U,S)/length(U,S))` -/
def lapserate (U S : UnitSystem α) : α := unit (temperature U S / length U S)
/-- `molality = molarmass(S,U)` -/
def molality (U S : UnitSystem α) : α := molarmass S U
/-- `molaramount = unit(mass(U,S)*molality(U,S))` -/
def molaramount (U S : UnitSystem α) : α := unit (mass U S * molality U S)
/-- `molarity = unit(molaramount(U,S)/volume(U,S))` -/
def molarity (U S : UnitSystem α) : α := unit (molaramount U S / volume U S)
/-- `molarvolume = unit(volume(U,S)/molaramount(U,S))` -/
def molarvolume (U S : UnitSystem α) : α := unit (volume U S / molaramount U S)
/-- `molarentropy = unit(entropy(U,S)/molaramount(U,S))` -/
def molarentropy (U S : UnitSystem α) : α := unit (entropy U S / molaramount U S)
/-- `molarenergy = unit(energy(U,S)/molaramount(U,S))` -/
def molarenergy (U S : UnitSystem α) : α := unit (energy U S / molaramount U S)
/-- `molarconductivity = unit(conductivity(U,S)*area(U,S)/molaramount(U,S))` -/
def molarconductivity (U S : UnitSystem α) : α :=
  unit (conductivity U S * area U S / molaramount U S)
/-- `molarsusceptibility = unit(specificsusceptibility(U,S)*molarmass(U,S))` -/
def molarsusceptibility (U S : UnitSystem α) : α :=
  unit (specificsusceptibility U S * molarmass U S)
/-- `catalysis = unit(molaramount(U,S)/time(U,S))` -/
def catalysis (U S : UnitSystem α) : α := unit (molaramount U S / time U S)
/-- `specificity = unit(volume(U,S)/molaramount(U,S)/time(U,S))` -/
def specificity (U S : UnitSystem α) : α := unit (volume U S / molaramount U S / time U S)
/-- `diffusionflux = unit(molaramount(U,S)*photonirradiance(U,S))` -/
def diffusionflux (U S : UnitSystem α) : α := unit (molaramount U S * photonirradiance U S)
/-- `luminousenergy = unit(frequency(U,S)*(luminousefficacy(S)*planck(S))/(luminousefficacy(U)*planck(U)))` -/
def luminousenergy (U S : UnitSystem α) : α :=
  unit (frequency U S * (S.Kcd * planck S) / (U.Kcd * planck U))
/-- `luminousflux = unit(frequency(U,S)*luminousenergy(U,S))` -/
def luminousflux (U S : UnitSystem α) : α := unit (frequency U S * luminousenergy U S)
/-- `luminousintensity = unit(luminousflux(U,S)/solidangle(U,S))` -/
def luminousintensity (U S : UnitSystem α) : α := unit (luminousflux U S / solidangle U S)
/-- `illuminance = unit(luminousflux(U,S)/area(U,S))` -/
def illuminance (U S : UnitSystem α) : α := unit (luminousflux U S / area U S)
/-- `luminance = unit(luminousintensity(U,S)/area(U,S))` -/
def luminance (U S : UnitSystem α) : α := unit (luminousintensity U S / area U S)
/-- `luminousexposure = unit(illuminance(U,S)*time(U,S))` -/
def luminousexposure (U S : UnitSystem α) : α := unit (illuminance U S * time U S)

end Convert

/-- The 131 convertible quantities (Julia `UnitSystems.Convert`, `UnitSystems.jl:53`),
in Julia order. -/
inductive Conv where
  | dimensionless | angle | solidangle | time | angulartime | length | angularlength | area
  | angulararea | volume | wavenumber | angularwavenumber | fuelefficiency | numberdensity
  | frequency | angularfrequency | frequencydrift | stagnance | speed | acceleration | jerk | snap
  | crackle | pop | volumeflow | etendue | photonintensity | photonirradiance | photonradiance
  | inertia | mass | massflow | lineardensity | areadensity | density | specificweight
  | specificvolume | force | specificforce | gravityforce | pressure | compressibility | viscosity
  | diffusivity | rotationalinertia | impulse | momentum | angularmomentum | yank | energy
  | specificenergy | action | fluence | power | powerdensity | irradiance | radiance
  | radiantintensity | spectralflux | spectralexposure | soundexposure | impedance
  | specificimpedance | admittance | compliance | inertance | charge | chargedensity
  | linearchargedensity | exposure | mobility | current | currentdensity | resistance
  | conductance | resistivity | conductivity | capacitance | inductance | reluctance | permeance
  | permittivity | permeability | susceptibility | specificsusceptibility | demagnetizingfactor
  | vectorpotential | electricpotential | magneticpotential | electricfield | magneticfield
  | electricflux | magneticflux | electricdisplacement | magneticfluxdensity
  | electricdipolemoment | magneticdipolemoment | electricpolarizability | magneticpolarizability
  | magneticmoment | specificmagnetization | polestrength | temperature | entropy
  | specificentropy | volumeheatcapacity | thermalconductivity | thermalconductance
  | thermalresistivity | thermalresistance | thermalexpansion | lapserate | molarmass | molality
  | molaramount | molarity | molarvolume | molarentropy | molarenergy | molarconductivity
  | molarsusceptibility | catalysis | specificity | diffusionflux | luminousflux
  | luminousintensity | luminance | illuminance | luminousenergy | luminousexposure
  | luminousefficacy
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Conv

variable {α : Type} [UnitAlg α]

/-- The conversion factor `q(U,S)`: `S`-units per `U`-unit. -/
def factor : Conv → UnitSystem α → UnitSystem α → α
  | .dimensionless => Convert.dimensionless | .angle => Convert.angle
  | .solidangle => Convert.solidangle | .time => Convert.time | .angulartime => Convert.angulartime
  | .length => Convert.length | .angularlength => Convert.angularlength | .area => Convert.area
  | .angulararea => Convert.angulararea | .volume => Convert.volume
  | .wavenumber => Convert.wavenumber | .angularwavenumber => Convert.angularwavenumber
  | .fuelefficiency => Convert.fuelefficiency | .numberdensity => Convert.numberdensity
  | .frequency => Convert.frequency | .angularfrequency => Convert.angularfrequency
  | .frequencydrift => Convert.frequencydrift | .stagnance => Convert.stagnance
  | .speed => Convert.speed | .acceleration => Convert.acceleration | .jerk => Convert.jerk
  | .snap => Convert.snap | .crackle => Convert.crackle | .pop => Convert.pop
  | .volumeflow => Convert.volumeflow | .etendue => Convert.etendue
  | .photonintensity => Convert.photonintensity | .photonirradiance => Convert.photonirradiance
  | .photonradiance => Convert.photonradiance | .inertia => Convert.inertia
  | .mass => Convert.mass | .massflow => Convert.massflow | .lineardensity => Convert.lineardensity
  | .areadensity => Convert.areadensity | .density => Convert.density
  | .specificweight => Convert.specificweight | .specificvolume => Convert.specificvolume
  | .force => Convert.force | .specificforce => Convert.specificforce
  | .gravityforce => Convert.gravityforce | .pressure => Convert.pressure
  | .compressibility => Convert.compressibility | .viscosity => Convert.viscosity
  | .diffusivity => Convert.diffusivity | .rotationalinertia => Convert.rotationalinertia
  | .impulse => Convert.impulse | .momentum => Convert.momentum
  | .angularmomentum => Convert.angularmomentum | .yank => Convert.yank
  | .energy => Convert.energy | .specificenergy => Convert.specificenergy
  | .action => Convert.action | .fluence => Convert.fluence | .power => Convert.power
  | .powerdensity => Convert.powerdensity | .irradiance => Convert.irradiance
  | .radiance => Convert.radiance | .radiantintensity => Convert.radiantintensity
  | .spectralflux => Convert.spectralflux | .spectralexposure => Convert.spectralexposure
  | .soundexposure => Convert.soundexposure | .impedance => Convert.impedance
  | .specificimpedance => Convert.specificimpedance | .admittance => Convert.admittance
  | .compliance => Convert.compliance | .inertance => Convert.inertance
  | .charge => Convert.charge | .chargedensity => Convert.chargedensity
  | .linearchargedensity => Convert.linearchargedensity | .exposure => Convert.exposure
  | .mobility => Convert.mobility | .current => Convert.current
  | .currentdensity => Convert.currentdensity | .resistance => Convert.resistance
  | .conductance => Convert.conductance | .resistivity => Convert.resistivity
  | .conductivity => Convert.conductivity | .capacitance => Convert.capacitance
  | .inductance => Convert.inductance | .reluctance => Convert.reluctance
  | .permeance => Convert.permeance | .permittivity => Convert.permittivity
  | .permeability => Convert.permeability | .susceptibility => Convert.susceptibility
  | .specificsusceptibility => Convert.specificsusceptibility
  | .demagnetizingfactor => Convert.demagnetizingfactor
  | .vectorpotential => Convert.vectorpotential | .electricpotential => Convert.electricpotential
  | .magneticpotential => Convert.magneticpotential | .electricfield => Convert.electricfield
  | .magneticfield => Convert.magneticfield | .electricflux => Convert.electricflux
  | .magneticflux => Convert.magneticflux | .electricdisplacement => Convert.electricdisplacement
  | .magneticfluxdensity => Convert.magneticfluxdensity
  | .electricdipolemoment => Convert.electricdipolemoment
  | .magneticdipolemoment => Convert.magneticdipolemoment
  | .electricpolarizability => Convert.electricpolarizability
  | .magneticpolarizability => Convert.magneticpolarizability
  | .magneticmoment => Convert.magneticmoment
  | .specificmagnetization => Convert.specificmagnetization
  | .polestrength => Convert.polestrength | .temperature => Convert.temperature
  | .entropy => Convert.entropy | .specificentropy => Convert.specificentropy
  | .volumeheatcapacity => Convert.volumeheatcapacity
  | .thermalconductivity => Convert.thermalconductivity
  | .thermalconductance => Convert.thermalconductance
  | .thermalresistivity => Convert.thermalresistivity
  | .thermalresistance => Convert.thermalresistance
  | .thermalexpansion => Convert.thermalexpansion | .lapserate => Convert.lapserate
  | .molarmass => Convert.molarmass | .molality => Convert.molality
  | .molaramount => Convert.molaramount | .molarity => Convert.molarity
  | .molarvolume => Convert.molarvolume | .molarentropy => Convert.molarentropy
  | .molarenergy => Convert.molarenergy | .molarconductivity => Convert.molarconductivity
  | .molarsusceptibility => Convert.molarsusceptibility | .catalysis => Convert.catalysis
  | .specificity => Convert.specificity | .diffusionflux => Convert.diffusionflux
  | .luminousflux => Convert.luminousflux | .luminousintensity => Convert.luminousintensity
  | .luminance => Convert.luminance | .illuminance => Convert.illuminance
  | .luminousenergy => Convert.luminousenergy | .luminousexposure => Convert.luminousexposure
  | .luminousefficacy => Convert.luminousefficacy

/-- All 131 quantities in Julia order. -/
def all : List Conv :=
  [dimensionless, angle, solidangle, time, angulartime, length, angularlength, area, angulararea,
   volume, wavenumber, angularwavenumber, fuelefficiency, numberdensity, frequency,
   angularfrequency, frequencydrift, stagnance, speed, acceleration, jerk, snap, crackle, pop,
   volumeflow, etendue, photonintensity, photonirradiance, photonradiance, inertia, mass,
   massflow, lineardensity, areadensity, density, specificweight, specificvolume, force,
   specificforce, gravityforce, pressure, compressibility, viscosity, diffusivity,
   rotationalinertia, impulse, momentum, angularmomentum, yank, energy, specificenergy, action,
   fluence, power, powerdensity, irradiance, radiance, radiantintensity, spectralflux,
   spectralexposure, soundexposure, impedance, specificimpedance, admittance, compliance,
   inertance, charge, chargedensity, linearchargedensity, exposure, mobility, current,
   currentdensity, resistance, conductance, resistivity, conductivity, capacitance, inductance,
   reluctance, permeance, permittivity, permeability, susceptibility, specificsusceptibility,
   demagnetizingfactor, vectorpotential, electricpotential, magneticpotential, electricfield,
   magneticfield, electricflux, magneticflux, electricdisplacement, magneticfluxdensity,
   electricdipolemoment, magneticdipolemoment, electricpolarizability, magneticpolarizability,
   magneticmoment, specificmagnetization, polestrength, temperature, entropy, specificentropy,
   volumeheatcapacity, thermalconductivity, thermalconductance, thermalresistivity,
   thermalresistance, thermalexpansion, lapserate, molarmass, molality, molaramount, molarity,
   molarvolume, molarentropy, molarenergy, molarconductivity, molarsusceptibility, catalysis,
   specificity, diffusionflux, luminousflux, luminousintensity, luminance, illuminance,
   luminousenergy, luminousexposure, luminousefficacy]

theorem all_length : all.length = 131 := by decide

/-- Julia name of the quantity. -/
def name (q : Conv) : String := ((reprStr q).splitOn ".").getLast!

/-- Look a quantity up by its Julia name. -/
def ofName? (s : String) : Option Conv := all.find? (·.name == s)

/-- `q(U,S)`, deliberately not inlined: at a call site with a literal quantity and
literal systems (`Conv.factorOf .energy (English Num) (Metric Num)`) the whole
application is a closed term, which the compiler evaluates once and hoists, as
Julia folds `energy(English, Metric)` into a constant. -/
@[noinline] def factorOf (q : Conv) (U S : UnitSystem α) : α := q.factor U S

/-- Julia `q(v::Real, U, S)` for a value `v` given in `S` (`UnitSystems.jl:300-305`):
`v` unchanged when `U` and `S` are the same system or the factor is exactly one,
otherwise `v / q(U,S)` (for a plain `v` that is `v*inv(q(U,S))`). Inlined, with the
factor and the `===` test out of line, so that with literal `q`, `U`, `S` both are
closed terms computed once and the conversion is one division. -/
@[inline] def convert (q : Conv) (v : α) (U S : UnitSystem α) : α :=
  if U.ident S then v
  else
    let u := factorOf q U S
    if isOne u then v else v / u

/-- Julia `q(U) = q(Natural, U)`: one natural unit of `q` expressed in `U`.
For the names that are also defining constants (`angle`, `molarmass`,
`luminousefficacy`, `permeability`) the one-argument form is the accessor
(`UnitSystems.jl:306`). -/
def natural (q : Conv) (U : UnitSystem α) : α :=
  match q with
  | .angle => U.θ
  | .molarmass => U.Mᵤ
  | .luminousefficacy => U.Kcd
  | .permeability => U.μ₀
  | q => q.factor (Natural α) U

theorem ctorIdx_all : all.map Conv.ctorIdx = List.range 131 := by decide

/-! ### Fast paths

Julia compiles `energy(v, English, Metric)` to one multiplication: the factor is a
function of type parameters and folds to a constant. The Lean equivalents:

* literal systems: `convert`/`convertF` with `factorOf`/`floatFactor` out of line,
  so the factor is a closed term, computed once (`unitsystems/convert_literal`);
* named systems chosen at run time (`Sys`): all 131 factors of an ordered pair of
  systems are computed on first use and cached (`factorSys`, `convertSys`,
  `naturalSys`), so a conversion is an array read (`unitsystems/convert_sys`);
* arbitrary systems: the chains over bare `Float64` (`UnitAlg Float`), or
  `factorAny`, which recognises the named systems by their parameters first. -/

/-- Julia's `q(v, U, S)` for a plain `v::Float64` as one operation on `v`: multiply
by `k` (`mul`) or divide by it. -/
structure FloatFactor where
  /-- the constant -/
  k : Float
  /-- multiply (`true`) or divide (`false`) -/
  mul : Bool
  deriving Inhabited

/-- The `FloatFactor` of a `Num` factor `u`: `v` unchanged when `u` is one;
`v / u` for a plain `v` and a `Constant` `u` is `v * inv(u)` (`FieldConstants.jl:93`,
two roundings), for a plain `u` one division. -/
def FloatFactor.ofNum (u : Num) : FloatFactor :=
  if u.v.isOne then ⟨f64! 1.0, true⟩
  else if u.const then ⟨u.v.inv.toFloat, true⟩
  else ⟨u.toFloat, false⟩

/-- Apply a `FloatFactor`. -/
@[inline] def FloatFactor.apply (f : FloatFactor) (v : Float) : Float :=
  if f.mul then v * f.k else v / f.k

/-- `q(v, U, S)` for `v::Float64` as a `FloatFactor` (the identity when the systems
are `===`). Not inlined, so that literal arguments make it a closed term. -/
@[noinline] def floatFactor (q : Conv) (U S : UnitSystem Num) : FloatFactor :=
  if U.ident S then ⟨f64! 1.0, true⟩ else FloatFactor.ofNum (q.factor U S)

/-- Julia `q(v::Float64, U, S)`, bit for bit (`Num` semantics with a plain value):
with literal `q`, `U`, `S` one multiplication by a precomputed constant. -/
@[inline] def convertF (q : Conv) (v : Float) (U S : UnitSystem Num) : Float :=
  (floatFactor q U S).apply v

/-- All 131 factors `q(U,S)` of one ordered pair of named systems, indexed by
`Conv.ctorIdx`, with their `FloatFactor`s unpacked. -/
structure PairFactors where
  /-- `q(U,S)` as `Num` -/
  num : Array Num
  /-- `FloatFactor.k` -/
  k : FloatArray
  /-- `FloatFactor.mul` (`1` = multiply) -/
  mul : ByteArray
  /-- are the two systems `===`? -/
  same : Bool
  deriving Inhabited

/-- Compute the factors of a pair of systems. -/
def PairFactors.build (U S : UnitSystem Num) : PairFactors :=
  let same := U.ident S
  let num := all.toArray.map fun q => q.factor U S
  let ff := num.map fun u => if same then ⟨f64! 1.0, true⟩ else FloatFactor.ofNum u
  { num, k := ⟨ff.map (·.k)⟩, mul := ⟨ff.map fun f => if f.mul then 1 else 0⟩, same }

/-- One lazily computed `PairFactors` per ordered pair of the 48 named systems
(index `48·U + S`). -/
def pairTable : Array (Thunk PairFactors) :=
  (List.range (48 * 48)).toArray.map fun k => Thunk.mk fun _ =>
    let sys := Sys.all.toArray
    PairFactors.build ((sys[k / 48]!).sys Num) ((sys[k % 48]!).sys Num)

/-- The factors of a pair of named systems (computed on first use). -/
@[inline] def pairFactors (U S : Sys) : PairFactors := (pairTable[U.ctorIdx * 48 + S.ctorIdx]!).get

/-- Julia `q(U, S)` for named systems chosen at run time: an array read after the
first use of the pair. Bit-identical to `q.factor (U.sys Num) (S.sys Num)`. -/
def factorSys (q : Conv) (U S : Sys) : Num := (pairFactors U S).num[q.ctorIdx]!

/-- Julia `q(v, U, S)` for a `Num` value and named systems chosen at run time. -/
def convertSysNum (q : Conv) (v : Num) (U S : Sys) : Num :=
  let p := pairFactors U S
  if p.same then v
  else
    let u := p.num[q.ctorIdx]!
    if u.v.isOne then v else v / u

/-- Julia `q(v::Float64, U, S)` for named systems chosen at run time. -/
def convertSys (q : Conv) (v : Float) (U S : Sys) : Float :=
  let p := pairFactors U S
  let i := q.ctorIdx
  let k := p.k.get! i
  if p.mul.get! i == 1 then v * k else v / k

/-- Julia `q(U) = q(Natural, U)` for a named system chosen at run time (the
accessor for `angle`, `molarmass`, `luminousefficacy`, `permeability`). -/
def naturalSys (q : Conv) (U : Sys) : Num :=
  match q with
  | .angle => (U.sys Num).θ
  | .molarmass => (U.sys Num).Mᵤ
  | .luminousefficacy => (U.sys Num).Kcd
  | .permeability => (U.sys Num).μ₀
  | q => factorSys q .Natural U

end Conv

namespace Sys

/-- The sixteen parameters of a system's Julia type: the eleven defining constants
and the five couplings. -/
def params (U : UnitSystem Num) : List Num :=
  [U.kB, U.ħ, U.c, U.μ₀, U.mₑ, U.Mᵤ, U.Kcd, U.θ, U.lam, U.αL, U.g₀,
   U.C.αG, U.C.α, U.C.μₑᵤ, U.C.μₚᵤ, U.C.ΩΛ]

/-- The hash of one parameter: payload bits, kind and `Constant` flag. -/
@[inline] def numHash (x : Num) : UInt64 :=
  match x.v with
  | .int n => n.toUInt64 ^^^ 0x9E3779B97F4A7C15 ^^^ (if x.const then 0 else 0xC2B2AE3D27D4EB4F)
  | .float f => f.toBits ^^^ (if x.const then 0 else 0xC2B2AE3D27D4EB4F)

/-- A hash of a system for bucketing (four of its parameters; `identFull` decides). -/
def paramHash (U : UnitSystem Num) : UInt64 :=
  mixHash (mixHash (numHash U.kB) (numHash U.ħ)) (mixHash (numHash U.mₑ) (numHash U.g₀))

/-- Julia `===` of two systems' types: the eleven constants and the coupling. -/
def identFull (U S : UnitSystem Num) : Bool :=
  U.ident S && U.C.αG.ident S.C.αG && U.C.α.ident S.C.α && U.C.μₑᵤ.ident S.C.μₑᵤ &&
    U.C.μₚᵤ.ident S.C.μₚᵤ && U.C.ΩΛ.ident S.C.ΩΛ

theorem identFull_refl (U : UnitSystem Num) : identFull U U = true := by
  simp [identFull, UnitSystem.ident, UnitAlg.ident, Num.ident_refl]

/-- The named systems by parameter hash, in Julia order. -/
def byHash : Std.HashMap UInt64 (List Sys) :=
  all.foldl (fun m s => m.alter (paramHash (s.sys Num)) fun
    | some l => some (l ++ [s]) | none => some [s]) {}

/-- The named system whose Julia type this system has (`===` on the eleven
defining constants and the coupling), if any; ties go to the first in Julia order.
Julia `unitname` of an arbitrary system is this name, or `Unknown`. Not inlined, so
that it is computed once for a literal system. -/
@[noinline] def ofSystem? (U : UnitSystem Num) : Option Sys :=
  (byHash.getD (paramHash U) []).find? fun s =>
    -- a named system is usually passed as the very object `s.sys Num`
    withPtrEq (s.sys Num) U (fun _ => identFull (s.sys Num) U) fun h => h ▸ identFull_refl _

end Sys

namespace Conv

/-- Julia `q(U, S)` for any two systems: named systems (recognised by their
parameters, `Sys.ofSystem?`) read the per-pair table, other systems evaluate the
chain. Bit-identical to `q.factor U S`. -/
@[inline] def factorAny (q : Conv) (U S : UnitSystem Num) : Num :=
  match Sys.ofSystem? U, Sys.ofSystem? S with
  | some u, some s => factorSys q u s
  | _, _ => q.factor U S

end Conv

end UnitSystems

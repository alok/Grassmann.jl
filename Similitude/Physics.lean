import Similitude.Quantity

/-!
# Typed physical constants

Similitude binds each of UnitSystems' `Constants` and `Physics` to its SI2019
*quantity* and converts it on application (`derived.jl:157-159`):
`boltzmann(Metric)` is `boltzmann(SI2019)` converted to `Metric`. Here each is a
function `Sys → Q U d` whose dimension is part of its type.

The `similitude_constant` command defines the function and proves, by `decide`,
that UnitSystems' formula for the constant, evaluated in the exponent model
(`UnitSystems.dimOf`), has exactly the dimension written in the type. A wrong
dimension in any signature below is a build error.
-/

namespace Similitude

open FieldConstants FieldAlgebra UnitSystems

/-- The SI2019 value of a UnitSystems constant, converted to `U`. -/
def siConstant (d : Dim) (f : UnitSystem Scalar → Scalar) (U : Sys) : Q U d :=
  (Sys.SI2019.qty d (f Sys.SI2019.consts)).to U

/-- `similitude_constant name : d := f` defines `Similitude.name (U : Sys) : Q U d`
as the SI2019 quantity of UnitSystems' formula `f` converted to `U`, and the
theorem `Similitude.name_dim : dimOf f = HalfDim.ofDim d` (by `decide`). -/
syntax (docComment)? "similitude_constant " ident " : " term " := " ident : command

macro_rules
  | `($[$doc]? similitude_constant $n : $d := $f) => do
    let thm := Lean.mkIdentFrom n (n.getId.appendAfter "_dim")
    `($[$doc]? def $n (U : Sys) : Q U $d := siConstant $d (fun S => $f S) U
      /-- The dimension in the type is the one UnitSystems' formula computes. -/
      theorem $thm : dimOf (fun S => $f S) = HalfDim.ofDim $d := by decide)

section
/-- Speed of light `𝘤` (`lightspeed`). -/
similitude_constant lightspeed : Dim.speed := UnitSystems.lightspeed
/-- Planck constant `𝘩` (`planck`). -/
similitude_constant planck : Dim.action := UnitSystems.planck
/-- Reduced Planck constant `ħ` (`planckreduced`). -/
similitude_constant planckreduced : Dim.angularmomentum := UnitSystems.planckreduced
/-- Electron mass `mₑ` (`electronmass`). -/
similitude_constant electronmass : Dim.mass := UnitSystems.electronmass
/-- Molar mass constant `Mᵤ` (`molarmass`). -/
similitude_constant molarmass : Dim.molarmass := UnitSystems.molarmass
/-- Boltzmann constant `kB` (`boltzmann`). -/
similitude_constant boltzmann : Dim.entropy := UnitSystems.boltzmann
/-- Vacuum permeability `μ₀` (`vacuumpermeability`). -/
similitude_constant vacuumpermeability : Dim.permeability := UnitSystems.vacuumpermeability
/-- Gauss rationalization `λ` (`rationalization`). -/
similitude_constant rationalization : Dim.demagnetizingfactor := UnitSystems.rationalization
/-- Lorentz constant `αL` (`lorentz`). -/
similitude_constant lorentz : USQ.C⁻¹ := UnitSystems.lorentz
/-- Luminous efficacy `Kcd` (`luminousefficacy`). -/
similitude_constant luminousefficacy : Dim.luminousefficacy := UnitSystems.luminousefficacy
/-- Gravitational force reference `g₀` (`gravity`). -/
similitude_constant gravity : Dim.gravityforce := UnitSystems.gravity
/-- The radian `θ` (`radian`). -/
similitude_constant radian : Dim.angle := UnitSystems.radian
/-- A full turn `τ·θ` (`turn`). -/
similitude_constant turn : Dim.angle := UnitSystems.turn
/-- The spat `2τθ²` (`spat`). -/
similitude_constant spat : Dim.solidangle := UnitSystems.spat
/-- Atomic mass unit (`dalton`). -/
similitude_constant dalton : Dim.mass := UnitSystems.dalton
/-- Proton mass (`protonmass`). -/
similitude_constant protonmass : Dim.mass := UnitSystems.protonmass
/-- Planck mass (`planckmass`). -/
similitude_constant planckmass : Dim.mass := UnitSystems.planckmass
/-- Newton's gravitational constant `G` (`gravitation`). -/
similitude_constant gravitation : USQ.F * USQ.L ^ 2 / USQ.M ^ 2 := UnitSystems.gravitation
/-- Einstein's constant `8πG/c⁴` (`einstein`). -/
similitude_constant einstein : USQ.F * USQ.T ^ 4 / (USQ.M ^ 2 * USQ.L ^ 2) := UnitSystems.einstein
/-- Hartree energy (`hartree`). -/
similitude_constant hartree : Dim.energy := UnitSystems.hartree
/-- Rydberg constant `R∞` (`rydberg`). -/
similitude_constant rydberg : Dim.wavenumber := UnitSystems.rydberg
/-- Bohr radius (`bohr`). -/
similitude_constant bohr : Dim.angularlength := UnitSystems.bohr
/-- Classical electron radius (`electronradius`). -/
similitude_constant electronradius : Dim.angularlength := UnitSystems.electronradius
/-- Avogadro constant `NA` (`avogadro`). -/
similitude_constant avogadro : USQ.N⁻¹ := UnitSystems.avogadro
/-- Molar gas constant `Rᵤ` (`molargas`). -/
similitude_constant molargas : Dim.molarentropy := UnitSystems.molargas
/-- Stefan–Boltzmann constant `σ` (`stefan`). -/
similitude_constant stefan : USQ.F / (USQ.L * USQ.T * USQ.Θ ^ 4) := UnitSystems.stefan
/-- Radiation density constant (`radiationdensity`). -/
similitude_constant radiationdensity : USQ.F / (USQ.L ^ 2 * USQ.Θ ^ 4) := UnitSystems.radiationdensity
/-- Vacuum permittivity `ε₀` (`vacuumpermittivity`). -/
similitude_constant vacuumpermittivity : Dim.permittivity := UnitSystems.vacuumpermittivity
/-- Coulomb's constant `kₑ` (`electrostatic`). -/
similitude_constant electrostatic : USQ.F * USQ.L ^ 2 / USQ.Q ^ 2 := UnitSystems.electrostatic
/-- Magnetostatic constant (`magnetostatic`). -/
similitude_constant magnetostatic : USQ.F * USQ.T ^ 2 / USQ.Q ^ 2 := UnitSystems.magnetostatic
/-- Biot–Savart constant (`biotsavart`). -/
similitude_constant biotsavart : USQ.F * USQ.T ^ 2 * USQ.C / USQ.Q ^ 2 := UnitSystems.biotsavart
/-- Elementary charge `𝘦` (`elementarycharge`). -/
similitude_constant elementarycharge : Dim.charge := UnitSystems.elementarycharge
/-- Faraday constant (`faraday`). -/
similitude_constant faraday : USQ.Q / USQ.N := UnitSystems.faraday
/-- Vacuum impedance `Z₀` (`vacuumimpedance`). -/
similitude_constant vacuumimpedance : Dim.resistance := UnitSystems.vacuumimpedance
/-- Conductance quantum (`conductancequantum`). -/
similitude_constant conductancequantum : Dim.conductance := UnitSystems.conductancequantum
/-- von Klitzing constant `RK` (`klitzing`). -/
similitude_constant klitzing : Dim.resistance := UnitSystems.klitzing
/-- Josephson constant `KJ` (`josephson`). -/
similitude_constant josephson : USQ.Q / (USQ.F * USQ.L * USQ.T * USQ.C) := UnitSystems.josephson
/-- Magnetic flux quantum `Φ₀` (`magneticfluxquantum`). -/
similitude_constant magneticfluxquantum : Dim.magneticflux := UnitSystems.magneticfluxquantum
/-- Bohr magneton `μB` (`magneton`). -/
similitude_constant magneton : USQ.F * USQ.L * USQ.T * USQ.Q / (USQ.M * USQ.A * USQ.C) := UnitSystems.magneton
end

end Similitude

import UnitSystems.Systems

/-!
# Physical constants of a unit system

The `Coupling`-aware constants of `UnitSystems.jl:285-289, 377-397` and
`physics.jl:15-39`. Each takes the system `U` and a `Coupling` `C`
(default: the system's own universe).

**Value-dispatch overrides.** Julia specialises a few constants on the exact
*values* of a system's type parameters (`UnitSystems.jl:377-397`); only the
patterns that are `Constant`s can ever match (the others are dead code, see
`docs/port-notes/unitsystems.md` §4.7). The live ones are reproduced here, for
scalars with `UnitAlg.special`:

| override | fires for |
|---|---|
| `electronmass(::typeof(Planck), C) = sqrt(spat(U)*coupling(C))` | Planck |
| `electronmass(::typeof(PlanckGauss), C) = sqrt(coupling(C))` | PlanckGauss |
| `electronmass(mₑ = √(αG·αinv), C) = sqrt(coupling(C)/finestructure(C))` | Stoney, Schrodinger |
| `electronmass(𝘤, mₑ = electronmass(CODATA / Conventional)) = electronmass(planck(U), C)` | CODATA, Conventional |
| `lightspeed(𝘤 = αinv, C) = inv(finestructure(C))` | Hartree, Schrodinger |
| `planckreduced(ħ = αinv, C) = inv(finestructure(C))` | Stoney, Electronic |
| `vacuumpermeability(𝘤, μ₀ = μ₀, C) = finestructure(C)*2𝘩/𝘤/𝘦^2` | SI2019 |
| `vacuumpermeability(::typeof(CODATA / Conventional), C) = 2RK*finestructure(C)/𝘤` | CODATA, Conventional |

Overrides that contain a bare Julia literal (`2𝘩`, `2RK2014`) produce *plain*
numbers, whose subsequent divisions round twice (`a*inv(b)`); `Num` tracks this.
-/

namespace UnitSystems

open FieldConstants UnitAlg

variable {α : Type} [UnitAlg α]

/-- A plain (non-`Constant`) Julia integer literal such as the `2` in `2𝘩`.
For non-special scalars this is the ordinary literal. -/
def plainLit (n : Int) : α := plit n

/-- Julia `electronmass(𝘩::Number, C) = inv(finestructure(C))^2*R∞*2𝘩/𝘤`
(`UnitSystems.jl:285`). -/
def electronmassH (h : α) (C : Coupling α) : α :=
  UnitAlg.inv C.finestructure ^ (2 : Int) * ms α .Rinf * (plainLit 2 * h) / ms α .cc

/-- `lightspeed(U, C)` with the Hartree/Schrodinger override. -/
def lightspeedC (U : UnitSystem α) (C : Coupling α) : α :=
  if special (α := α) && ident U.c (ms α .αinv) then UnitAlg.inv C.finestructure else U.c

/-- `planckreduced(U, C)` with the Stoney/Electronic override. -/
def planckreducedC (U : UnitSystem α) (C : Coupling α) : α :=
  if special (α := α) && ident U.ħ (ms α .αinv) then UnitAlg.inv C.finestructure else U.ħ

/-- `planck(U, C) = turn(U)*planckreduced(U, C)` (`UnitSystems.jl:287`). -/
def planckC (U : UnitSystem α) (C : Coupling α) : α := turn U * planckreducedC U C

/-- `planck(U) = planck(U, universe(U))`. -/
def planck (U : UnitSystem α) : α := planckC U U.C

/-- `electronmass(U, C)` with the Planck/PlanckGauss/Stoney/CODATA overrides. -/
def electronmassC (U : UnitSystem α) (C : Coupling α) : α :=
  if special (α := α) then
    if U.ident (Planck α) then UnitAlg.sqrt (spat U * C.coupling)
    else if U.ident (PlanckGauss α) then UnitAlg.sqrt C.coupling
    else if ident U.mₑ (UnitAlg.sqrt (αG α * ms α .αinv)) then UnitAlg.sqrt (C.coupling / C.finestructure)
    else if ident U.c (ms α .cc) && (ident U.mₑ (CODATA α).mₑ || ident U.mₑ (Conventional α).mₑ) then
      electronmassH (planck U) C
    else U.mₑ
  else U.mₑ

/-- `vacuumpermeability(U, C)` with the SI2019/CODATA/Conventional overrides. -/
def vacuumpermeabilityC (U : UnitSystem α) (C : Coupling α) : α :=
  if special (α := α) then
    if U.ident (CODATA α) then plainLit 2 * ms α .RK2014 * C.finestructure / ms α .cc
    else if U.ident (Conventional α) then plainLit 2 * ms α .RK1990 * C.finestructure / ms α .cc
    else if ident U.μ₀ (μ₀ α) then
      -- `where {kB,ħ,𝘤}`: here `𝘤` is the system's own lightspeed, `𝘩`, `𝘦` are globals
      C.finestructure * (plainLit 2 * ms α .hh) / U.c / ms α .ee ^ (2 : Int)
    else U.μ₀
  else U.μ₀

/-- `planckmass(U, C) = electronmass(U, C)/√coupling(C)` (`UnitSystems.jl:286`). -/
def planckmass (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  electronmassC U C / UnitAlg.sqrt C.coupling

/-- `gravitation(U, C) = lightspeed(U,C)*planck(U,C)/tau(U)/planckmass(U,C)^2`
(`UnitSystems.jl:288`). -/
def gravitation (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  lightspeedC U C * planckC U C / tau U / planckmass U C ^ (2 : Int)

/-- `elementarycharge(U, C)` (`UnitSystems.jl:289`); uses `planck(U)` with the
system's own coupling and the stored `μ₀`, `𝘤`. -/
def elementarycharge (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  UnitAlg.sqrt (two U * planck U / (vacuumpermeability U / C.finestructure) /
    (lightspeed U * rationalization U * lorentz U ^ (2 : Int)))

/-- `avogadro(U, C) = molarmass(U,C)*electronunit(C)/electronmass(U,C)` (`physics.jl:15`). -/
def avogadro (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  molarmass U * C.electronunit / electronmassC U C
/-- `dalton(U, C) = electronmass(U,C)/electronunit(C)` (`physics.jl:16`). -/
def dalton (U : UnitSystem α) (C : Coupling α := U.C) : α := electronmassC U C / C.electronunit
/-- `protonmass(U, C) = protonelectron(C)*electronmass(U,C)` (`physics.jl:17`). -/
def protonmass (U : UnitSystem α) (C : Coupling α := U.C) : α := C.protonelectron * electronmassC U C
/-- `einstein(U, C) = two(U)^2*tau(U)*gravitation(U,C)/lightspeed(U,C)^4` (`physics.jl:19`). -/
def einstein (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  two U ^ (2 : Int) * tau U * gravitation U C / lightspeedC U C ^ (4 : Int)
/-- `molargas(U, C) = boltzmann(U,C)*avogadro(U,C)` (`physics.jl:21`). -/
def molargas (U : UnitSystem α) (C : Coupling α := U.C) : α := boltzmann U * avogadro U C
/-- `stefan(U, C)` (`physics.jl:22`). -/
def stefan (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  tau U ^ (5 : Int) / two U ^ (4 : Int) * boltzmann U ^ (4 : Int) /
    (three U * five U * planckC U C ^ (3 : Int) * lightspeedC U C ^ (2 : Int))
/-- `radiationdensity(U, C) = two(U)^2*stefan(U,C)/lightspeed(U,C)` (`physics.jl:23`). -/
def radiationdensity (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  two U ^ (2 : Int) * stefan U C / lightspeedC U C
/-- `vacuumpermittivity(U, C) = inv(vacuumpermeability(U,C)*(lightspeed(U,C)*lorentz(U))^2)`
(`physics.jl:24`). -/
def vacuumpermittivity (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  UnitAlg.inv (vacuumpermeabilityC U C * (lightspeedC U C * lorentz U) ^ (2 : Int))
/-- `electrostatic(U, C) = rationalization(U)/(two(U)*tau(U))/vacuumpermittivity(U,C)`
(`physics.jl:25`). -/
def electrostatic (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  rationalization U / (two U * tau U) / vacuumpermittivity U C
/-- `biotsavart(U, C) = vacuumpermeability(U,C)*lorentz(U)*(rationalization(U)/(two(U)*tau(U)))`
(`physics.jl:26`). -/
def biotsavart (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  vacuumpermeabilityC U C * lorentz U * (rationalization U / (two U * tau U))
/-- `magnetostatic(U) = lorentz(U)*biotsavart(U)` (`physics.jl:27`). -/
def magnetostatic (U : UnitSystem α) : α := lorentz U * biotsavart U
/-- `vacuumimpedance(U, C) = vacuumpermeability(U,C)*lightspeed(U,C)*rationalization(U)*lorentz(U)^2`
(`physics.jl:28`). -/
def vacuumimpedance (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  vacuumpermeabilityC U C * lightspeedC U C * rationalization U * lorentz U ^ (2 : Int)
/-- `faraday(U, C) = elementarycharge(U,C)*avogadro(U,C)` (`physics.jl:29`). -/
def faraday (U : UnitSystem α) (C : Coupling α := U.C) : α := elementarycharge U C * avogadro U C
/-- `josephson(U, C) = two(U)*elementarycharge(U,C)*lorentz(U)/planck(U,C)` (`physics.jl:30`). -/
def josephson (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  two U * elementarycharge U C * lorentz U / planckC U C
/-- `magneticfluxquantum(U, C) = inv(josephson(U,C))` (`physics.jl:31`). -/
def magneticfluxquantum (U : UnitSystem α) (C : Coupling α := U.C) : α := UnitAlg.inv (josephson U C)
/-- `klitzing(U, C) = planck(U,C)/elementarycharge(U,C)^2` (`physics.jl:32`). -/
def klitzing (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  planckC U C / elementarycharge U C ^ (2 : Int)
/-- `conductancequantum(U, C) = two(U)*elementarycharge(U,C)^2/planck(U,C)` (`physics.jl:33`). -/
def conductancequantum (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  two U * elementarycharge U C ^ (2 : Int) / planckC U C
/-- `hartree(U, C) = electronmass(U,C)/gravity(U)*(lightspeed(U,C)*finestructure(C))^2`
(`physics.jl:34`). -/
def hartree (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  electronmassC U C / gravity U * (lightspeedC U C * C.finestructure) ^ (2 : Int)
/-- `rydberg(U, C) = hartree(U,C)/(two(U)*planck(U,C))/lightspeed(U,C)` (`physics.jl:35`). -/
def rydberg (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  hartree U C / (two U * planckC U C) / lightspeedC U C
/-- `bohr(U, C) = planckreduced(U,C)*gravity(U)/electronmass(U,C)/lightspeed(U,C)/finestructure(C)`
(`physics.jl:36`). -/
def bohr (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  planckreducedC U C * gravity U / electronmassC U C / lightspeedC U C / C.finestructure
/-- `electronradius(U, C)` (`physics.jl:38`). -/
def electronradius (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  C.finestructure * planckreducedC U C * gravity U / electronmassC U C / lightspeedC U C
/-- `magneton(U, C) = elementarycharge(U,C)*planckreduced(U,C)*lorentz(U)/(two(U)*electronmass(U,C))`
(`physics.jl:39`). -/
def magneton (U : UnitSystem α) (C : Coupling α := U.C) : α :=
  elementarycharge U C * planckreducedC U C * lorentz U / (two U * electronmassC U C)

end UnitSystems

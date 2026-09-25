import UnitSystems.Registry

/-!
# Display of unit systems and couplings

`show(io, U)` prints the system's name (`UnitSystems.jl:187`) and
`display(U)` the 12-line parameter table (`UnitSystems.jl:188-201`), with the
rationalization printed as `4π` when it equals `Float64(4π)`.
-/

namespace UnitSystems

open FieldConstants

/-- Julia `display(U::UnitSystem)` for a system named `name` (12 lines, each
ending in a newline). -/
def UnitSystem.display (name : String) (U : UnitSystem Num) : String :=
  let pad (s : String) : String := s ++ String.ofList (List.replicate (17 - s.length) ' ')
  let line (label : String) (v : String) : String := "  " ++ pad label ++ ": " ++ v ++ "\n"
  let rat := rationalization U
  "UnitSystem: " ++ name ++ "\n" ++
  line "entropy" (toString (boltzmann U)) ++
  line "angularmomentum" (toString (planckreduced U)) ++
  line "speed" (toString (lightspeed U)) ++
  line "permeability" (toString (vacuumpermeability U)) ++
  line "mass" (toString (electronmass U)) ++
  line "molarmass" (toString (molarmass U)) ++
  line "luminousefficacy" (toString (luminousefficacy U)) ++
  line "angle" (toString (radian U)) ++
  line "rationalization" (if rat.toFloat == 4.0 * 3.141592653589793 then "4π" else toString rat) ++
  line "lorentz" (toString (lorentz U)) ++
  line "gravityforce" (toString (gravity U))

/-- Julia `display(C::Coupling)` (`UnitSystems.jl:116`), with its newline. -/
def Coupling.display (C : Coupling Num) : String :=
  s!"Coupling\{αG = {C.αG}, α = {C.α}, μₑᵤ = {C.μₑᵤ}, μₚᵤ = {C.μₚᵤ}, ΩΛ = {C.ΩΛ}}\n"

/-- Julia `display` of a named system. -/
def Sys.display (u : Sys) : String := (u.sys Num).display u.name

/-- Julia `display(U)` of any system: its name (`unitname`: a named system's, or
`Unknown`) and its parameters. -/
def UnitSystem.displayAny (U : UnitSystem Num) : String := U.display U.unitname

instance : ToString Sys := ⟨Sys.name⟩

end UnitSystems

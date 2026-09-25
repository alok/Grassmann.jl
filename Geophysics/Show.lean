import Geophysics.Data

/-!
# Julia display strings

Julia's printing of Geophysics values, reproduced exactly (the oracle compares
the strings):

* `show(io, G::MoleGas)` (`chemistry.jl:92-94, 247-250`):
  `DiatomicGas{M=0.028013000000000003,ν=3290.0031276899135,μ=…,Tμ=107,k=…,Tk=150}`,
  where `M` is the molar mass in kg/mol and `ν` is the vibrational *temperature*;
* a `Mixture` prints as its type, `Geophysics.Mixture{M, N, (gas, …)}([f, …])`;
* `Planet{f, a, t, Gm}()`, `FluidState{fluid, U}(T, P)`;
* `display(A::Atmosphere)` and `display(W::Weather)` (`Geophysics.jl:456-461, 556-563`).

Floats print as Julia's shortest round-trip form (`JuliaBase.F64.showString`),
integer parameters as integers. Two gas families cannot print in Julia (the
`SutherlandGas` overflows the stack, the `PentatomicGas` fallback reads an
undefined variable); they print here as the evident intent.
-/

namespace Geophysics

open StaticVectors UnitSystems FieldConstants

/-- Julia `show` of a `Float64`. -/
@[inline] def showF (x : Float) : String := JuliaBase.F64.showString x

/-- Julia `show` of a `Vector`/`Values` of `Float64`: `[x, y, z]`. -/
def showVals {n : Nat} (v : Values Float n) : String :=
  "[" ++ ", ".intercalate (v.toList.map showF) ++ "]"

/-- Julia `show(io, P::Planet)`: `Planet{f, a, t, Gm}()`. -/
def Planet.jshow (P : Planet) : String := s!"Planet\{{P.f}, {P.a}, {P.t}, {P.Gm}}()"

namespace MoleGas

/-- Julia `gastext(G)` (`chemistry.jl:92, 247-250`). -/
def gastext (G : MoleGas) : String :=
  let U := Units.metric
  let m := showF (G.molarmass U)
  let θ := G.vibration U
  match G.kind with
  | .atomic => s!"AtomicGas\{M={m},"
  | .diatomic _ => s!"DiatomicGas\{M={m},ν={showF (θ.get! 0)},"
  | .triatomic _ _ => s!"TriatomicGas\{M={m},ν₁={showF (θ.get! 0)},ν₂={showF (θ.get! 1)},"
  | .pentatomic => s!"MoleGas\{{m},"
  | .sutherland cv => s!"Gas\{M={m},cᵥ={cv},cₚ={showF (cv.toFloat + G.gasconstant U)},"

/-- Julia `show(io, G::MoleGas)` (`chemistry.jl:94`). -/
def jshow (G : MoleGas) : String :=
  s!"{G.gastext}μ={showF G.μ},Tμ={G.Tμ},k={showF G.k},Tk={G.Tk}}"

end MoleGas

mutual
/-- Julia `show` of a substance. -/
def Mole.jshow : Mole → String
  | .gas g => g.jshow
  | .mix m => Mixture.jshow m

/-- Julia's default `show` of a `Mixture{M,N,C}`: its type and its fractions. -/
def Mixture.jshow : Mixture → String
  | .mk M ps =>
    let n := Parts.count ps
    let tup := if n == 1 then Parts.showList ps ++ "," else Parts.showList ps
    s!"Geophysics.Mixture\{{showF M}, {n}, ({tup})}([{Parts.showFractions ps}])"

/-- The constituents joined by `", "`. -/
def Parts.showList : Parts → String
  | .one _ c => c.jshow
  | .cons _ c rest => c.jshow ++ ", " ++ Parts.showList rest

/-- The fractions joined by `", "`. -/
def Parts.showFractions : Parts → String
  | .one f _ => showF f
  | .cons f _ rest => showF f ++ ", " ++ Parts.showFractions rest

/-- The number of constituents. -/
def Parts.count : Parts → Nat
  | .one _ _ => 1
  | .cons _ _ rest => Parts.count rest + 1
end

instance : ToString Planet := ⟨Planet.jshow⟩
instance : ToString MoleGas := ⟨MoleGas.jshow⟩
instance : ToString Mole := ⟨Mole.jshow⟩
instance : ToString Mixture := ⟨Mixture.jshow⟩

/-- Julia `show(io, F::FluidState)`: `FluidState{fluid, U}(T, P)`. -/
def FluidState.jshow (F : FluidState) : String :=
  s!"FluidState\{{F.fluid.jshow}, {F.units.name}}({showF F.T}, {showF F.P})"

instance : ToString FluidState := ⟨FluidState.jshow⟩

/-- Julia `typeof(A)` of an atmosphere: `Atmosphere{n, Planet{…}(), U}`. -/
def Atmosphere.typeString {n : Nat} (A : Atmosphere n) : String :=
  s!"Atmosphere\{{n}, {A.planet.jshow}, {A.units.name}}"

/-- Julia `display(A::Atmosphere)` (`Geophysics.jl:456-461`). -/
def Atmosphere.display {n : Nat} (A : Atmosphere n) : String :=
  s!"{A.typeString}\n a = {showVals A.a}\n h = {showVals A.h}\n m = {showVals A.m}\n"

/-- Julia `typeof(W)` of a weather: `Weather{ϕ, fluid, n, Planet{…}(), U}`. -/
def Weather.typeString {n : Nat} (W : Weather n) : String :=
  s!"Weather\{{showF W.latitude}, {W.fluid.jshow}, {n}, {W.planet.jshow}, {W.units.name}}"

/-- Julia `display(W::Weather)` (`Geophysics.jl:556-563`). -/
def Weather.display {n : Nat} (W : Weather n) : String :=
  s!"{W.typeString}\n a = {showVals W.atm.a}\n h = {showVals W.atm.h}\n T = {showVals W.T}\n" ++
  s!" P = {showVals W.p}\n ρ = {showVals W.rho}\n"

end Geophysics

import Geophysics.Units
import Geophysics.JuliaMath

/-!
# Ideal gases, mixtures and fluid states

Geophysics.jl `src/chemistry.jl`. A `MoleGas` is an ideal gas with Sutherland-law
viscosity and conductivity and an Einstein-function vibrational heat capacity;
a `Mixture` averages constituents by mole fraction; a `FluidState` is a fluid
at a temperature and pressure in a unit system.

Julia makes every gas a singleton type whose parameters live in the type
(`AtomicGas{M,μ,Tμ,k,Tk}`, …). Here they are runtime values: the families
become `GasKind`, and `Mole` (Julia `AbstractMole`) is either a gas or a
mixture. A mixture's constituents may themselves be mixtures (`0.5*Nitrox`),
so `Mole`, `Mixture` and the non-empty constituent list `Parts` are mutually
inductive and every mixture property is a structural recursion that sums
`fᵢ·xᵢ` left to right, like StaticVectors' `⋅` (`linalg.jl:62-67`).

The Sutherland temperatures keep their Julia kind (`Tμ = 107` is an integer,
`110.4` a float) because Julia prints them that way; arithmetic uses `Float`.

Julia defects and how they are handled here (none has a Julia golden):

* `heatvolume(T, ::SutherlandGas, U)` recurses forever (`chemistry.jl:235-236`);
  here it is the evident intent, the constant `cᵥ` converted to `U`.
* `PentatomicGas` has no `heatvolume` method (a `MethodError`); here its
  heat capacities are `NaN`.
* `intensity(::FluidState)` calls the undefined `impedance`
  (`chemistry.jl:444`); here it is the documented intent `P²/(ρ·a)`.
-/

namespace Geophysics

open FieldConstants UnitSystems JMath

/-- The gas families of `chemistry.jl:167-171` with their family parameters. -/
inductive GasKind where
  /-- monatomic, `cᵥ = 3R/2` (Julia `AtomicGas`) -/
  | atomic
  /-- diatomic with vibrational wavenumber `ν` [m⁻¹] (Julia `DiatomicGas`) -/
  | diatomic (ν : Float)
  /-- triatomic with two vibrational wavenumbers [m⁻¹] (Julia `TriatomicGas`) -/
  | triatomic (ν₁ ν₂ : Float)
  /-- pentatomic (Julia `PentatomicGas`; not exported and without heat capacity) -/
  | pentatomic
  /-- constant specific heat `cᵥ` [J kg⁻¹ K⁻¹] (Julia `SutherlandGas`) -/
  | sutherland (cv : JNum)
  deriving Inhabited

/-- An ideal gas (Julia `MoleGas{M,μ,Tμ,k,Tk}` and its subtypes,
`chemistry.jl:68, 167-171`). `μ` and `k` are the internal Sutherland prefactors
computed by `viscond`, not reference values. -/
structure MoleGas where
  /-- the family and its vibrational parameters -/
  kind : GasKind
  /-- relative molar mass `M` (g mol⁻¹, dimensionless) -/
  M : Float
  /-- Sutherland viscosity prefactor -/
  μ : Float
  /-- Sutherland viscosity temperature [K] -/
  Tμ : Float
  /-- Sutherland conductivity prefactor -/
  k : Float
  /-- Sutherland conductivity temperature [K] -/
  Tk : Float
  /-- `Tμ` as Julia holds it (an `Int` such as `107`, or a `Float64`), for printing -/
  TμJ : JNum
  /-- `Tk` as Julia holds it, for printing -/
  TkJ : JNum
  deriving Inhabited

/-- Julia `viscond(μ0, Tμ, k0, Tk, T0 = 288.16)` (`chemistry.jl:104-109`): the
Sutherland prefactors `μ0*sqrt(Tμ)*(T0 + Tμ)/(2T0^1.5)` from reference values at `T0`. -/
def viscond (μ0 : Float) (Tμ : JNum) (k0 : Float) (Tk : JNum) (T0 : Float := 288.16) :
    Float × Float :=
  let t1 := (f64% 2.0) * pow T0 (f64% 1.5)
  let tμ := Tμ.toFloat
  let tk := Tk.toFloat
  (μ0 * Float.sqrt tμ * (T0 + tμ) / t1, k0 * Float.sqrt tk * (T0 + tk) / t1)

/-- Julia `AtomicGas(M, μ0, Tμ, k0, Tk, T0 = 288.16)` (`chemistry.jl:173-176`). -/
def AtomicGas (M μ0 : Float) (Tμ : JNum) (k0 : Float) (Tk : JNum) (T0 : Float := 288.16) :
    MoleGas :=
  let (μ, k) := viscond μ0 Tμ k0 Tk T0
  ⟨.atomic, M, μ, Tμ.toFloat, k, Tk.toFloat, Tμ, Tk⟩

/-- Julia `DiatomicGas(M, ν, μ0, Tμ, k0, Tk, T0 = 288.16)` (`chemistry.jl:177-180`). -/
def DiatomicGas (M ν μ0 : Float) (Tμ : JNum) (k0 : Float) (Tk : JNum) (T0 : Float := 288.16) :
    MoleGas :=
  let (μ, k) := viscond μ0 Tμ k0 Tk T0
  ⟨.diatomic ν, M, μ, Tμ.toFloat, k, Tk.toFloat, Tμ, Tk⟩

/-- Julia `TriatomicGas(M, ν1, ν2, μ0, Tμ, k0, Tk, T0 = 288.16)` (`chemistry.jl:181-184`). -/
def TriatomicGas (M ν₁ ν₂ μ0 : Float) (Tμ : JNum) (k0 : Float) (Tk : JNum)
    (T0 : Float := 288.16) : MoleGas :=
  let (μ, k) := viscond μ0 Tμ k0 Tk T0
  ⟨.triatomic ν₁ ν₂, M, μ, Tμ.toFloat, k, Tk.toFloat, Tμ, Tk⟩

/-- Julia `PentatomicGas(M, μ0, Tμ, k0, Tk, T0 = 288.16)` (`chemistry.jl:185-188`). -/
def PentatomicGas (M μ0 : Float) (Tμ : JNum) (k0 : Float) (Tk : JNum) (T0 : Float := 288.16) :
    MoleGas :=
  let (μ, k) := viscond μ0 Tμ k0 Tk T0
  ⟨.pentatomic, M, μ, Tμ.toFloat, k, Tk.toFloat, Tμ, Tk⟩

/-- Julia `SutherlandGas(M, cᵥ, μ0, Tμ, k0, Tk, T0 = 288.16)` (`chemistry.jl:189-192`). -/
def SutherlandGas (M : Float) (cv : JNum) (μ0 : Float) (Tμ : JNum) (k0 : Float) (Tk : JNum)
    (T0 : Float := 288.16) : MoleGas :=
  let (μ, k) := viscond μ0 Tμ k0 Tk T0
  ⟨.sutherland cv, M, μ, Tμ.toFloat, k, Tk.toFloat, Tμ, Tk⟩

/-- Julia `vibration(x::AbstractFloat) = x^2*eˣ/(eˣ - 1)^2`, the Einstein function
(`chemistry.jl:224`); it overflows to `NaN` for `x ≳ 710` exactly as in Julia. -/
def einstein (x : Float) : Float :=
  let e := exp x
  x * x * e / ((e - (f64% 1.0)) * (e - (f64% 1.0)))

/-- The per-constituent quantities a mixture averages (`chemistry.jl:266-271`). -/
inductive Property where
  /-- `viscosity(T, G, U)` -/
  | viscosity
  /-- `thermalconductivity(T, G, U)` -/
  | conductivity
  /-- `heatvolume(T, G, U)` -/
  | heatvolume
  /-- `heatpressure(T, G, U)` -/
  | heatpressure
  /-- `viscosity(G, U)`, the converted prefactor -/
  | viscosityParam
  /-- `thermalconductivity(G, U)` -/
  | conductivityParam
  /-- `sutherlandviscosity(G, U)` -/
  | sutherlandViscosity
  /-- `sutherlandconductivity(G, U)` -/
  | sutherlandConductivity
  deriving DecidableEq, Repr, Inhabited

namespace MoleGas

variable (G : MoleGas) (U : Units)

/-- `molarmass(G, U) = molarmass(U)*M` (`chemistry.jl:40`). -/
@[inline] def molarmass : Float := U.molar * G.M

/-- `gasconstant(G, U) = universal(U)/molarmass(G, U)` (`chemistry.jl:54`; a
`Constant` over a `Float64`, i.e. `universal(U)*inv(molarmass)`). -/
@[inline] def gasconstant : Float := U.universal * ((f64% 1.0) / G.molarmass U)

/-- `sutherlandviscosity(G, U) = Tμ*temperature(Metric, U)` (`chemistry.jl:79`). -/
@[inline] def sutherlandviscosity : Float := G.Tμ * U.temperatureM

/-- `sutherlandconductivity(G, U) = Tk*temperature(Metric, U)` (`chemistry.jl:90`). -/
@[inline] def sutherlandconductivity : Float := G.Tk * U.temperatureM

/-- `viscosity(G, U) = μ*viscosity(Metric, U)` (`chemistry.jl:78`). -/
@[inline] def viscosityParam : Float := G.μ * U.viscosityM

/-- `thermalconductivity(G, U) = k*thermalconductivity(Metric, U)` (`chemistry.jl:89`). -/
@[inline] def conductivityParam : Float := G.k * U.conductivityM

/-- The Sutherland law `((2μ)/sqrt(Tμ))*(sqrt(T)/(1 + Tμ/T))` (`chemistry.jl:96-102`). -/
@[inline] def sutherland (c ts T : Float) : Float :=
  (((f64% 2.0) * c) / Float.sqrt ts) * (Float.sqrt T / ((f64% 1.0) + ts / T))

/-- `viscosity(T, G, U)`: dynamic viscosity by Sutherland's law (`chemistry.jl:96-102`). -/
def viscosity (T : Float) : Float := sutherland (G.viscosityParam U) (G.sutherlandviscosity U) T

/-- `thermalconductivity(T, G, U)` by Sutherland's law (`chemistry.jl:96-102`). -/
def thermalconductivity (T : Float) : Float :=
  sutherland (G.conductivityParam U) (G.sutherlandconductivity U) T

/-- `wavenumber(G, U)`: the vibrational wavenumbers converted to `U`
(`chemistry.jl:199-202`); empty for families without them (a Julia `MethodError`). -/
def wavenumber : FloatArray :=
  match G.kind with
  | .diatomic ν => FloatArray.empty.push (ν * U.wavenumberM)
  | .triatomic ν₁ ν₂ => (FloatArray.empty.push (ν₁ * U.wavenumberM)).push (ν₂ * U.wavenumberM)
  | _ => .empty

/-- `wavelength(G, U) = inv.(wavenumber(G, U))` (`chemistry.jl:209`). -/
def wavelength : FloatArray := (G.wavenumber U).foldl (fun acc x => acc.push ((f64% 1.0) / x)) .empty

/-- `frequency(G, U) = wavenumber(G, U).*lightspeed(U)` (`chemistry.jl:216`). -/
def frequency : FloatArray := (G.wavenumber U).foldl (fun acc x => acc.push (x * U.lightspeed)) .empty

/-- `vibration(G, U) = frequency(G, U).*(planck(U)/boltzmann(U)/1.2)`: the vibrational
temperatures `θ` (`chemistry.jl:223`, including Reed's `/1.2`). -/
def vibration : FloatArray := (G.frequency U).foldl (fun acc x => acc.push (x * U.vibration)) .empty

/-- `heatvolume(T, G, U)`: specific heat at constant volume (`chemistry.jl:234-245`). -/
def heatvolume (T : Float) : Float :=
  let R := G.gasconstant U
  match G.kind with
  | .atomic => (f64% 1.5) * R
  | .diatomic ν => R * ((f64% 2.5) + einstein (ν * U.wavenumberM * U.lightspeed * U.vibration / T))
  | .triatomic ν₁ ν₂ =>
    R * ((f64% 2.5) + einstein (ν₁ * U.wavenumberM * U.lightspeed * U.vibration / T) +
      einstein (ν₂ * U.wavenumberM * U.lightspeed * U.vibration / T))
  | .pentatomic => JMath.nan
  | .sutherland cv => convert .specificentropy cv.toFloat U.sys .Metric

/-- `heatpressure(T, G, U) = heatvolume(T, G, U) + gasconstant(G, U)` (`chemistry.jl:120`). -/
def heatpressure (T : Float) : Float := G.heatvolume U T + G.gasconstant U

/-- One constituent quantity. -/
def eval (p : Property) (T : Float) : Float :=
  match p with
  | .viscosity => G.viscosity U T
  | .conductivity => G.thermalconductivity U T
  | .heatvolume => G.heatvolume U T
  | .heatpressure => G.heatpressure U T
  | .viscosityParam => G.viscosityParam U
  | .conductivityParam => G.conductivityParam U
  | .sutherlandViscosity => G.sutherlandviscosity U
  | .sutherlandConductivity => G.sutherlandconductivity U

end MoleGas

mutual
/-- A chemical substance (Julia `AbstractMole{M}`, `chemistry.jl:26`): a gas or a
mixture. -/
inductive Mole where
  /-- a pure gas -/
  | gas (g : MoleGas)
  /-- a mixture -/
  | mix (m : Mixture)

/-- A mole-fraction mixture (Julia `Mixture{M,N,C}`, `chemistry.jl:252-257`): the
relative molar mass `M` and the constituents with their fractions. Fractions are
not normalised. -/
inductive Mixture where
  /-- `Mixture{M,N,C}(f)` -/
  | mk (M : Float) (parts : Parts)

/-- The constituents of a mixture, in Julia order: a non-empty list of
(fraction, substance). -/
inductive Parts where
  /-- the last constituent -/
  | one (f : Float) (c : Mole)
  /-- a constituent followed by more -/
  | cons (f : Float) (c : Mole) (rest : Parts)
end

instance : Inhabited Mole := ⟨.gas default⟩
instance : Inhabited Parts := ⟨.one (f64% 1.0) default⟩
instance : Inhabited Mixture := ⟨.mk (f64% 0.0) default⟩
instance : Coe MoleGas Mole := ⟨.gas⟩
instance : Coe Mixture Mole := ⟨.mix⟩

mutual
/-- A constituent quantity of a substance: the gas value, or the mole-fraction
average `f ⋅ values` for a mixture (`chemistry.jl:266-271`). -/
def Mole.eval (p : Property) (U : Units) (T : Float) : Mole → Float
  | .gas g => g.eval U p T
  | .mix (.mk _ ps) => Parts.dot p U T ps

/-- `f ⋅ values`, summed left to right with no leading zero (StaticVectors `∑`). -/
def Parts.dot (p : Property) (U : Units) (T : Float) : Parts → Float
  | .one f c => f * c.eval p U T
  | .cons f c rest => Parts.dotAcc p U T (f * c.eval p U T) rest

/-- Continue a left-to-right dot product from `acc`. -/
def Parts.dotAcc (p : Property) (U : Units) (T : Float) (acc : Float) : Parts → Float
  | .one f c => acc + f * c.eval p U T
  | .cons f c rest => Parts.dotAcc p U T (acc + f * c.eval p U T) rest
end

namespace Parts

/-- The constituents in order. -/
def toList : Parts → List (Float × Mole)
  | .one f c => [(f, c)]
  | .cons f c rest => (f, c) :: rest.toList

/-- Append two constituent lists. -/
def append : Parts → Parts → Parts
  | .one f c, ys => .cons f c ys
  | .cons f c rest, ys => .cons f c (rest.append ys)

/-- `f ⋅ M` of the constituents' relative molar masses, left to right. -/
def dotWith (g : Mole → Float) : Parts → Float
  | .one f c => f * g c
  | .cons f c rest => go (f * g c) rest
where
  /-- the accumulating loop -/
  go (acc : Float) : Parts → Float
    | .one f c => acc + f * g c
    | .cons f c rest => go (acc + f * g c) rest

end Parts

namespace Mole

/-- `relativemass(x) = M` (`chemistry.jl:33`). -/
def relativemass : Mole → Float
  | .gas g => g.M
  | .mix (.mk M _) => M

end Mole

namespace Mixture

/-- The relative molar mass `M` of the mixture. -/
def relativemass : Mixture → Float
  | .mk M _ => M

/-- The constituents. -/
def parts : Mixture → Parts
  | .mk _ ps => ps

/-- Julia `Mixture{N,C}(f)` (`chemistry.jl:256`): build from constituents, with
`M = f ⋅ relativemass.(C)`. -/
def ofParts (ps : Parts) : Mixture := .mk (ps.dotWith Mole.relativemass) ps

/-- Julia `chemical(M)`/`molecules(M)` (`chemistry.jl:259-260`): the constituents. -/
def molecules (m : Mixture) : Array Mole := (m.parts.toList.map (·.2)).toArray

/-- Julia `fractions(M) = M.f` (`chemistry.jl:261`). -/
def fractions (m : Mixture) : FloatArray := m.parts.toList.foldl (fun acc x => acc.push x.1) .empty

/-- Julia `length(M) = N` (`chemistry.jl:262`). -/
def length (m : Mixture) : Nat := m.parts.toList.length

/-- Julia `M[i]` (`chemistry.jl:263`, 0-based here): the `i`-th constituent. -/
def get? (m : Mixture) (i : Nat) : Option Mole := (m.parts.toList.map (·.2))[i]?

/-- Julia `+(m::Mixture...)` for two arguments (`chemistry.jl:275-278`): concatenate
the constituents and recompute `M`. -/
def add (a b : Mixture) : Mixture := ofParts (a.parts.append b.parts)

/-- Julia `+(m::Mixture)`: a single mixture with `M` recomputed from its fractions. -/
def recompute (a : Mixture) : Mixture := ofParts a.parts

instance : Add Mixture := ⟨add⟩

end Mixture

/-- Julia `f * G` (`chemistry.jl:273`): the one-constituent mixture of `G` with
fraction `f`. Its `M` is `G`'s, not `f·M`. -/
def Mole.scale (f : Float) (G : Mole) : Mixture := .mk G.relativemass (.one f G)

instance : HMul Float Mole Mixture := ⟨Mole.scale⟩
instance : HMul Float MoleGas Mixture := ⟨fun f g => Mole.scale f (.gas g)⟩
instance : HMul Float Mixture Mixture := ⟨fun f m => Mole.scale f (.mix m)⟩

namespace Mole

variable (G : Mole)

/-- `molarmass(G, U) = molarmass(U)*relativemass(G)` (`chemistry.jl:40`). -/
def molarmass (U : Sys := .Metric) : Float := (Units.of U).molar * G.relativemass

/-- `molecularmass(G, U) = molarmass(G, U)/avogadro(U)` (`chemistry.jl:47`). -/
def molecularmass (U : Sys := .Metric) : Float := G.molarmass U * (Units.of U).avogadroInv

/-- `gasconstant(G, U) = universal(U)/molarmass(G, U)` (`chemistry.jl:54`). -/
def gasconstantU (U : Units) : Float := U.universal * ((f64% 1.0) / (U.molar * G.relativemass))

/-- `gasconstant(G, U)`: the specific gas constant (`chemistry.jl:54`). -/
def gasconstant (U : Sys := .Metric) : Float := G.gasconstantU (Units.of U)

/-- `viscosity(T, G, U)` (`chemistry.jl:96-102, 266-268`). -/
def viscosityU (U : Units) (T : Float) : Float := G.eval .viscosity U T
/-- `thermalconductivity(T, G, U)`. -/
def thermalconductivityU (U : Units) (T : Float) : Float := G.eval .conductivity U T
/-- `heatvolume(T, G, U)`. -/
def heatvolumeU (U : Units) (T : Float) : Float := G.eval .heatvolume U T
/-- `heatpressure(T, G, U)`. -/
def heatpressureU (U : Units) (T : Float) : Float := G.eval .heatpressure U T

/-- `heatratio(T, G, U)`: `gasconstant/heatvolume + 1` for a gas (`chemistry.jl:127`),
`heatpressure/heatvolume` for a mixture (`chemistry.jl:264`). -/
def heatratioU (U : Units) (T : Float) : Float :=
  match G with
  | .gas g => g.gasconstant U / g.heatvolume U T + (f64% 1.0)
  | .mix _ => G.heatpressureU U T / G.heatvolumeU U T

/-- `specificenergy(T, G, U) = heatvolume(T, G, U)*T` (`chemistry.jl:134`). -/
def specificenergyU (U : Units) (T : Float) : Float := G.heatvolumeU U T * T

/-- `specificenthalpy(T, G, U) = heatpressure(T, G, U)*T` (`chemistry.jl:141`). -/
def specificenthalpyU (U : Units) (T : Float) : Float := G.heatpressureU U T * T

/-- `freedom(T, G, U) = heatvolume(T, G, U)*(2/gasconstant(G, U))` (`chemistry.jl:148`). -/
def freedomU (U : Units) (T : Float) : Float := G.heatvolumeU U T * ((f64% 2.0) / G.gasconstantU U)

/-- `prandtl(T, G, U) = gravity(U)*viscosity*heatpressure/thermalconductivity`
(`chemistry.jl:155`). -/
def prandtlU (U : Units) (T : Float) : Float :=
  U.gc * G.viscosityU U T * G.heatpressureU U T / G.thermalconductivityU U T

/-- `sonicspeed(T, G, U) = sqrt((gasconstant*gravity(U)*heatratio)*T)` (`chemistry.jl:162`). -/
def sonicspeedU (U : Units) (T : Float) : Float :=
  Float.sqrt (G.gasconstantU U * U.gc * G.heatratioU U T * T)

/-- `viscosity(T, G, U)`: dynamic viscosity. -/
def viscosity (T : Float) (U : Sys := .Metric) : Float := G.viscosityU (Units.of U) T
/-- `thermalconductivity(T, G, U)`. -/
def thermalconductivity (T : Float) (U : Sys := .Metric) : Float :=
  G.thermalconductivityU (Units.of U) T
/-- `heatvolume(T, G, U)`: specific heat at constant volume. -/
def heatvolume (T : Float) (U : Sys := .Metric) : Float := G.heatvolumeU (Units.of U) T
/-- `heatpressure(T, G, U)`: specific heat at constant pressure. -/
def heatpressure (T : Float) (U : Sys := .Metric) : Float := G.heatpressureU (Units.of U) T
/-- `heatratio(T, G, U)`: `γ`. -/
def heatratio (T : Float) (U : Sys := .Metric) : Float := G.heatratioU (Units.of U) T
/-- `specificenergy(T, G, U)`. -/
def specificenergy (T : Float) (U : Sys := .Metric) : Float := G.specificenergyU (Units.of U) T
/-- `specificenthalpy(T, G, U)`. -/
def specificenthalpy (T : Float) (U : Sys := .Metric) : Float :=
  G.specificenthalpyU (Units.of U) T
/-- `freedom(T, G, U)`: degrees of freedom. -/
def freedom (T : Float) (U : Sys := .Metric) : Float := G.freedomU (Units.of U) T
/-- `prandtl(T, G, U)`: Prandtl number. -/
def prandtl (T : Float) (U : Sys := .Metric) : Float := G.prandtlU (Units.of U) T
/-- `sonicspeed(T, G, U)`: speed of sound. -/
def sonicspeed (T : Float) (U : Sys := .Metric) : Float := G.sonicspeedU (Units.of U) T

/-- `viscosity(G, U)`: the converted Sutherland prefactor, fraction-averaged for a
mixture (`chemistry.jl:78, 269-271`). -/
def viscosityParam (U : Sys := .Metric) : Float := G.eval .viscosityParam (Units.of U) (f64% 0.0)
/-- `thermalconductivity(G, U)`: the converted prefactor. -/
def conductivityParam (U : Sys := .Metric) : Float :=
  G.eval .conductivityParam (Units.of U) (f64% 0.0)
/-- `sutherlandviscosity(G, U)`: the Sutherland temperature of viscosity. -/
def sutherlandviscosity (U : Sys := .Metric) : Float :=
  G.eval .sutherlandViscosity (Units.of U) (f64% 0.0)
/-- `sutherlandconductivity(G, U)`: the Sutherland temperature of conductivity. -/
def sutherlandconductivity (U : Sys := .Metric) : Float :=
  G.eval .sutherlandConductivity (Units.of U) (f64% 0.0)

/-- `heatratio(G, U)` at the reference temperature `temperature(288.16, U, Metric)`
(`chemistry.jl:111-113`). -/
def heatratioRef (U : Sys := .Metric) : Float := G.heatratio (Units.of U).reference U
/-- `heatvolume(G, U)` at the reference temperature. -/
def heatvolumeRef (U : Sys := .Metric) : Float := G.heatvolume (Units.of U).reference U
/-- `heatpressure(G, U)` at the reference temperature. -/
def heatpressureRef (U : Sys := .Metric) : Float := G.heatpressure (Units.of U).reference U

/-- The mixture fractions (Julia `fractions`), empty for a pure gas (a Julia error). -/
def fractions : Mole → FloatArray
  | .gas _ => .empty
  | .mix m => m.fractions

/-! The `UnitSystems.Constants` forwarded by `chemistry.jl:56-60`: `op(G, U) = op(U)`. -/

/-- `lightspeed(G, U)` -/
def lightspeed (_ : Mole) (U : Sys := .Metric) : Num := UnitSystems.lightspeed (usys U)
/-- `planck(G, U)` -/
def planck (_ : Mole) (U : Sys := .Metric) : Num := UnitSystems.planck (usys U)
/-- `planckreduced(G, U)` -/
def planckreduced (_ : Mole) (U : Sys := .Metric) : Num := UnitSystems.planckreduced (usys U)
/-- `electronmass(G, U)` -/
def electronmass (_ : Mole) (U : Sys := .Metric) : Num :=
  UnitSystems.electronmassC (usys U) (usys U).C
/-- `boltzmann(G, U)` -/
def boltzmann (_ : Mole) (U : Sys := .Metric) : Num := UnitSystems.boltzmann (usys U)
/-- `vacuumpermeability(G, U)` -/
def vacuumpermeability (_ : Mole) (U : Sys := .Metric) : Num :=
  UnitSystems.vacuumpermeabilityC (usys U) (usys U).C
/-- `rationalization(G, U)` -/
def rationalization (_ : Mole) (U : Sys := .Metric) : Num := UnitSystems.rationalization (usys U)
/-- `lorentz(G, U)` -/
def lorentz (_ : Mole) (U : Sys := .Metric) : Num := UnitSystems.lorentz (usys U)
/-- `luminousefficacy(G, U)` -/
def luminousefficacy (_ : Mole) (U : Sys := .Metric) : Num :=
  UnitSystems.luminousefficacy (usys U)
/-- `gravity(G, U)` (the force constant `g_c`) -/
def gravity (_ : Mole) (U : Sys := .Metric) : Num := UnitSystems.gravity (usys U)
/-- `radian(G, U)` -/
def radian (_ : Mole) (U : Sys := .Metric) : Num := UnitSystems.radian (usys U)

end Mole

/-- A thermodynamic state of a fluid (Julia `FluidState{f,u}`, `chemistry.jl:288-291`):
temperature `T` and pressure `P` in the unit system `units`. -/
structure FluidState where
  /-- the fluid -/
  fluid : Mole
  /-- the unit system of `T` and `P` -/
  units : Sys
  /-- absolute temperature -/
  T : Float
  /-- absolute pressure -/
  P : Float
  deriving Inhabited

/-- Julia `(G::Gas)(T = 288.15, P = atm, U = Metric)` (`chemistry.jl:293-295`). -/
def Mole.state (G : Mole) (T : Float := 288.15) (P : Float := 101325.0) (U : Sys := .Metric) :
    FluidState := ⟨G, U, T, P⟩

namespace FluidState

variable (F : FluidState)

/-- `temperature(F, U) = temperature(F.T, U, units(F))` (`chemistry.jl:312-313`). -/
def temperature (U : Sys := F.units) : Float := convert .temperature F.T U F.units

/-- `pressure(F, U) = pressure(F.P, U, units(F))` (`chemistry.jl:320-321`). -/
def pressure (U : Sys := F.units) : Float := convert .pressure F.P U F.units

/-- Julia `(U::UnitSystem)(F::FluidState)` (`chemistry.jl:298`): the state in `U`. -/
def toUnits (U : Sys) : FluidState := ⟨F.fluid, U, F.temperature U, F.pressure U⟩

/-- `molecularmass(F, U)` (`chemistry.jl:323-325`). -/
def molecularmass (U : Sys := F.units) : Float := F.fluid.molecularmass U
/-- `gasconstant(F, U)`. -/
def gasconstant (U : Sys := F.units) : Float := F.fluid.gasconstant U

/-- `viscosity(F, U) = viscosity(temperature(F, U), fluid(F), U)` (`chemistry.jl:326-328`). -/
def viscosity (U : Sys := F.units) : Float := F.fluid.viscosity (F.temperature U) U
/-- `thermalconductivity(F, U)`. -/
def thermalconductivity (U : Sys := F.units) : Float :=
  F.fluid.thermalconductivity (F.temperature U) U
/-- `heatvolume(F, U)`. -/
def heatvolume (U : Sys := F.units) : Float := F.fluid.heatvolume (F.temperature U) U
/-- `heatpressure(F, U)`. -/
def heatpressure (U : Sys := F.units) : Float := F.fluid.heatpressure (F.temperature U) U
/-- `heatratio(F, U)`. -/
def heatratio (U : Sys := F.units) : Float := F.fluid.heatratio (F.temperature U) U
/-- `prandtl(F, U)`. -/
def prandtl (U : Sys := F.units) : Float := F.fluid.prandtl (F.temperature U) U
/-- `sonicspeed(F, U)`. -/
def sonicspeed (U : Sys := F.units) : Float := F.fluid.sonicspeed (F.temperature U) U
/-- `freedom(F, U)`. -/
def freedom (U : Sys := F.units) : Float := F.fluid.freedom (F.temperature U) U
/-- `specificenergy(F, U)`. -/
def specificenergy (U : Sys := F.units) : Float := F.fluid.specificenergy (F.temperature U) U
/-- `specificenthalpy(F, U)`. -/
def specificenthalpy (U : Sys := F.units) : Float :=
  F.fluid.specificenthalpy (F.temperature U) U

/-- `density(F, U) = (pressure/temperature)/gasconstant` (`chemistry.jl:395`). -/
def density (U : Sys := F.units) : Float := F.pressure U / F.temperature U / F.gasconstant U
/-- `specificvolume(F, U) = inv(density(F, U))` (`chemistry.jl:402`). -/
def specificvolume (U : Sys := F.units) : Float := (f64% 1.0) / F.density U
/-- `kinematic(F, U) = viscosity/density` (`chemistry.jl:409`). -/
def kinematic (U : Sys := F.units) : Float := F.viscosity U / F.density U
/-- `heatcapacity(F, U) = heatpressure*density` (`chemistry.jl:416`). -/
def heatcapacity (U : Sys := F.units) : Float := F.heatpressure U * F.density U
/-- `thermaldiffusivity(F, U) = thermalconductivity/heatcapacity` (`chemistry.jl:423`). -/
def thermaldiffusivity (U : Sys := F.units) : Float :=
  F.thermalconductivity U / F.heatcapacity U
/-- `elasticity(F, U) = heatratio*pressure` (`chemistry.jl:430`). -/
def elasticity (U : Sys := F.units) : Float := F.heatratio U * F.pressure U
/-- `specificimpedance(F, U) = density*sonicspeed` (`chemistry.jl:437`). -/
def specificimpedance (U : Sys := F.units) : Float := F.density U * F.sonicspeed U
/-- `intensity(F, U) = pressure^2/impedance`: Julia calls the undefined `impedance`
(`chemistry.jl:444`); this is the documented intent `P²/(ρ·a)` (no Julia golden). -/
def intensity (U : Sys := F.units) : Float :=
  let p := F.pressure U
  p * p / F.specificimpedance U

end FluidState

end Geophysics

import UnitSystems.System

/-!
# The 48 named unit systems

Every definition is `initdata.jl:88-156` verbatim, generic in the scalar. `Sys`
enumerates them in Julia's `UnitSystems.Systems` order
(`UnitSystems.jl:22`); it is the type index of dimensioned quantities in
Similitude, so a quantity's unit system is known statically.
-/

namespace UnitSystems

open FieldConstants UnitAlg

section named
variable (α : Type) [UnitAlg α]

/-- `τ/𝟐^6/𝟓^7 = 4π·10⁻⁷`, the pre-2019 permeability. -/
def μ₀Metric : α := UnitAlg.tau / c2 α ^ (6 : Int) / c5 α ^ (7 : Int)

/-- `SI2019 = MetricSystem()` -/
def SI2019 : UnitSystem α := MetricSystem α
/-- `Metric = MetricSystem(milli, τ/𝟐^6/𝟓^7)` -/
def Metric : UnitSystem α := MetricSystem α (milli α) (μ₀Metric α)
/-- `SI1976 = MetricSystem(milli, τ/𝟐^6/𝟓^7, Constant(8.31432))` -/
def SI1976 : UnitSystem α := MetricSystem α (milli α) (μ₀Metric α) (flit 8.31432)
/-- `CODATA = ConventionalSystem(RK2014, KJ2014, Rᵤ2014)` -/
def CODATA : UnitSystem α := ConventionalSystem α (ms α .RK2014) (ms α .KJ2014) (ms α .Rᵤ2014)
/-- `Conventional = ConventionalSystem(RK1990, KJ1990)` -/
def Conventional : UnitSystem α := ConventionalSystem α (ms α .RK1990) (ms α .KJ1990)
/-- `International = ElectricSystem(Metric, Ωᵢₜ, Vᵢₜ)` -/
def International : UnitSystem α := ElectricSystem (Metric α) (ms α .Ωᵢₜ) (ms α .Vᵢₜ)
/-- `InternationalMean = ElectricSystem(Metric, Constant(1.00049), Constant(1.00034))` -/
def InternationalMean : UnitSystem α := ElectricSystem (Metric α) (flit 1.00049) (flit 1.00034)
/-- `MetricTurn = MetricSystem(milli, τ/𝟐^6/𝟓^7, Rᵤ, 𝟏, 𝟏/τ)` -/
def MetricTurn : UnitSystem α :=
  MetricSystem α (milli α) (μ₀Metric α) (Rᵤ α) one (one / UnitAlg.tau)
/-- `MetricSpatian = MetricSystem(milli, τ/𝟐^6/𝟓^7, Rᵤ, 𝟏, 𝟏/ς)` -/
def MetricSpatian : UnitSystem α := MetricSystem α (milli α) (μ₀Metric α) (Rᵤ α) one (one / ς α)
/-- `MetricGradian`: `θ = 𝟐^4*𝟓^2/τ` -/
def MetricGradian : UnitSystem α :=
  MetricSystem α (milli α) (μ₀Metric α) (Rᵤ α) one (c2 α ^ (4 : Int) * c5 α ^ (2 : Int) / UnitAlg.tau)
/-- `MetricDegree`: `θ = 𝟐^3*𝟑^2*𝟓/τ` -/
def MetricDegree : UnitSystem α :=
  MetricSystem α (milli α) (μ₀Metric α) (Rᵤ α) one
    (c2 α ^ (3 : Int) * c3 α ^ (2 : Int) * c5 α / UnitAlg.tau)
/-- `MetricArcminute`: `θ = 𝟐^5*𝟑^3*𝟓^2/τ` -/
def MetricArcminute : UnitSystem α :=
  MetricSystem α (milli α) (μ₀Metric α) (Rᵤ α) one
    (c2 α ^ (5 : Int) * c3 α ^ (3 : Int) * c5 α ^ (2 : Int) / UnitAlg.tau)
/-- `MetricArcsecond`: `θ = 𝟐^7*𝟑^4*𝟓^3/τ` -/
def MetricArcsecond : UnitSystem α :=
  MetricSystem α (milli α) (μ₀Metric α) (Rᵤ α) one
    (c2 α ^ (7 : Int) * c3 α ^ (4 : Int) * c5 α ^ (3 : Int) / UnitAlg.tau)
/-- `Engineering = MetricSystem(milli, τ/𝟐^6/𝟓^7/g₀, Rᵤ, g₀)` -/
def Engineering : UnitSystem α :=
  MetricSystem α (milli α) (μ₀Metric α / ms α .g₀) (Rᵤ α) (ms α .g₀)
/-- `Gravitational = EntropySystem(Metric, 𝟏, 𝟏, g₀)` -/
def Gravitational : UnitSystem α := EntropySystem (Metric α) one one (ms α .g₀)
/-- `MTS = EntropySystem(Metric, 𝟏, 𝟏, kilo)` -/
def MTS : UnitSystem α := EntropySystem (Metric α) one one (kilo α)
/-- `EMU = GaussSystem(Metric, 𝟏, 𝟐*τ)` -/
def EMU : UnitSystem α := GaussSystem (Metric α) one (c2 α * UnitAlg.tau)
/-- `ESU = GaussSystem(Metric, (hecto*𝘤)^-2, 𝟐*τ)` -/
def ESU : UnitSystem α := GaussSystem (Metric α) ((hecto α * ms α .cc) ^ (-2 : Int)) (c2 α * UnitAlg.tau)
/-- `Gauss = GaussSystem(Metric, 𝟏, 𝟐*τ, centi/𝘤)` -/
def Gauss : UnitSystem α := GaussSystem (Metric α) one (c2 α * UnitAlg.tau) (some (centi α / ms α .cc))
/-- `LorentzHeaviside = GaussSystem(Metric, 𝟏, 𝟏, centi/𝘤)` -/
def LorentzHeaviside : UnitSystem α := GaussSystem (Metric α) one one (some (centi α / ms α .cc))
/-- `FPS = RankineSystem(Metric, ft, lb)` -/
def FPS : UnitSystem α := RankineSystem α (Metric α) (ms α .ft) (ms α .lb)
/-- `IPS = RankineSystem(Metric, ft/𝟐^2/𝟑, lb*g₀*𝟐^2*𝟑/ft)` -/
def IPS : UnitSystem α :=
  RankineSystem α (Metric α) (ms α .ft / c2 α ^ (2 : Int) / c3 α)
    (ms α .lb * ms α .g₀ * c2 α ^ (2 : Int) * c3 α / ms α .ft)
/-- `British = RankineSystem(Metric, ft, lb*g₀/ft)` -/
def British : UnitSystem α := RankineSystem α (Metric α) (ms α .ft) (ms α .lb * ms α .g₀ / ms α .ft)
/-- `English = RankineSystem(Metric, ft, lb, g₀/ft)` -/
def English : UnitSystem α := RankineSystem α (Metric α) (ms α .ft) (ms α .lb) (ms α .g₀ / ms α .ft)
/-- `Survey = RankineSystem(Metric, ftUS, lb, g₀/ftUS)` -/
def Survey : UnitSystem α :=
  RankineSystem α (Metric α) (ms α .ftUS) (ms α .lb) (ms α .g₀ / ms α .ftUS)
/-- `FFF = EntropySystem(Metric, 𝟕*𝟐*DAY, fur, (𝟐*𝟑^2*𝟓)*lb, °R, Constant(0.), 𝟏)`:
fortnight, furlong, firkin (with `μ₀ = 0`). -/
def FFF : UnitSystem α :=
  EntropySystem' (Metric α) (c7 α * c2 α * DAY α) (fur α) ((c2 α * c3 α ^ (2 : Int) * c5 α) * ms α .lb)
    (degR α) (flit 0.0) (some one)
/-- `MPH = EntropySystem(FPS, HOUR, mi, 𝟏)` (built on FPS). -/
def MPH : UnitSystem α := EntropySystem (FPS α) (HOUR α) (mi α) one
/-- `KKH = EntropySystem(Metric, HOUR, kilo, 𝟏)` -/
def KKH : UnitSystem α := EntropySystem (Metric α) (HOUR α) (kilo α) one
/-- `Nautical = EntropySystem(Metric, HOUR, nm, em^3, 𝟏, τ*𝟑^3/𝟐^10/𝟓^12, milli)` -/
def Nautical : UnitSystem α :=
  EntropySystem' (Metric α) (HOUR α) (nm α) (em α ^ (3 : Int)) one
    (UnitAlg.tau * c3 α ^ (3 : Int) / c2 α ^ (10 : Int) / c5 α ^ (12 : Int)) (some (milli α))
/-- `Meridian = EntropySystem(Metric, 𝟏, em, em^3, 𝟏, τ/𝟐^6/𝟓^7, milli)` -/
def Meridian : UnitSystem α :=
  EntropySystem' (Metric α) one (em α) (em α ^ (3 : Int)) one (μ₀Metric α) (some (milli α))
/-- `IAU☉ = EntropySystem(Metric, DAY, au, GM☉/G)` -/
def IAU : UnitSystem α := EntropySystem (Metric α) (DAY α) (ms α .au) (GMsun α / G α)
/-- `IAUE = EntropySystem(Metric, DAY, LD, GME/G)` -/
def IAUE : UnitSystem α := EntropySystem (Metric α) (DAY α) (ms α .LD) (ms α .GME / G α)
/-- `IAUJ = EntropySystem(Metric, DAY, JD, GMJ/G)` -/
def IAUJ : UnitSystem α := EntropySystem (Metric α) (DAY α) (ms α .JD) (ms α .GMJ / G α)
/-- `Hubble = AstronomicalSystem(Metric, th, 𝘤*th, mₑ)` -/
def Hubble : UnitSystem α := AstronomicalSystem (Metric α) (th α) (ms α .cc * th α) (mₑ α)
/-- `Cosmological = AstronomicalSystem(Metric, lc/𝘤, lc, mc)` -/
def Cosmological : UnitSystem α := AstronomicalSystem (Metric α) (lc α / ms α .cc) (lc α) (mc α)
/-- `CosmologicalQuantum = AstronomicalSystem(Metric, tcq, lcq, mcq)` -/
def CosmologicalQuantum : UnitSystem α := AstronomicalSystem (Metric α) (tcq α) (lcq α) (mcq α)
/-- `Planck = unitsystem(𝟏,𝟏,𝟏,𝟏,√(𝟐*τ*αG))` (rationalized) -/
def Planck : UnitSystem α :=
  unitsystem (Universe α) one one one one (UnitAlg.sqrt (c2 α * UnitAlg.tau * αG α))
/-- `PlanckGauss = unitsystem(𝟏,𝟏,𝟏,𝟐*τ,√αG)` -/
def PlanckGauss : UnitSystem α :=
  unitsystem (Universe α) one one one (c2 α * UnitAlg.tau) (UnitAlg.sqrt (αG α))
/-- `Stoney = unitsystem(𝟏,αinv,𝟏,𝟐*τ,√(αG*αinv))` -/
def Stoney : UnitSystem α :=
  unitsystem (Universe α) one (ms α .αinv) one (c2 α * UnitAlg.tau) (UnitAlg.sqrt (αG α * ms α .αinv))
/-- `Hartree = unitsystem(𝟏,𝟏,αinv,𝟐*τ*α^2,𝟏)` -/
def Hartree : UnitSystem α :=
  unitsystem (Universe α) one one (ms α .αinv) (c2 α * UnitAlg.tau * ms α .α ^ (2 : Int)) one
/-- `Rydberg = unitsystem(𝟏,𝟏,𝟐*αinv,τ/𝟐*α^2,inv(𝟐))` -/
def Rydberg : UnitSystem α :=
  unitsystem (Universe α) one one (c2 α * ms α .αinv) (UnitAlg.tau / c2 α * ms α .α ^ (2 : Int))
    (UnitAlg.inv (c2 α))
/-- `Schrodinger = unitsystem(𝟏,𝟏,αinv,𝟐*τ*α^2,√(αG*αinv))` -/
def Schrodinger : UnitSystem α :=
  unitsystem (Universe α) one one (ms α .αinv) (c2 α * UnitAlg.tau * ms α .α ^ (2 : Int))
    (UnitAlg.sqrt (αG α * ms α .αinv))
/-- `Electronic = unitsystem(𝟏,αinv,𝟏,𝟐*τ,𝟏)` -/
def Electronic : UnitSystem α :=
  unitsystem (Universe α) one (ms α .αinv) one (c2 α * UnitAlg.tau) one
/-- `Natural = unitsystem(𝟏,𝟏,𝟏,𝟏,𝟏)` -/
def Natural : UnitSystem α := unitsystem (Universe α) one one one one one
/-- `NaturalGauss = unitsystem(𝟏,𝟏,𝟏,𝟐*τ,𝟏)` -/
def NaturalGauss : UnitSystem α := unitsystem (Universe α) one one one (c2 α * UnitAlg.tau) one
/-- `QCD = unitsystem(𝟏,𝟏,𝟏,𝟏,inv(μₚₑ))` -/
def QCD : UnitSystem α := unitsystem (Universe α) one one one one (UnitAlg.inv (μₚₑ α))
/-- `QCDGauss = unitsystem(𝟏,𝟏,𝟏,𝟐*τ,inv(μₚₑ))` -/
def QCDGauss : UnitSystem α :=
  unitsystem (Universe α) one one one (c2 α * UnitAlg.tau) (UnitAlg.inv (μₚₑ α))
/-- `QCDoriginal = unitsystem(𝟏,𝟏,𝟏,𝟐*τ*α,inv(μₚₑ))` -/
def QCDoriginal : UnitSystem α :=
  unitsystem (Universe α) one one one (c2 α * UnitAlg.tau * ms α .α) (UnitAlg.inv (μₚₑ α))

end named

/-- The 48 named unit systems, in Julia's `UnitSystems.Systems` order
(`UnitSystems.jl:22`). -/
inductive Sys where
  | Metric | SI2019 | SI1976 | CODATA | Conventional | International | InternationalMean
  | MetricTurn | MetricSpatian | MetricGradian | MetricDegree | MetricArcminute | MetricArcsecond
  | Engineering | Gravitational | MTS | EMU | ESU | Gauss | LorentzHeaviside | FPS | IPS | British
  | English | Survey | FFF | MPH | KKH | Nautical | Meridian | IAU | IAUE | IAUJ | Hubble
  | Cosmological | CosmologicalQuantum | Planck | PlanckGauss | Stoney | Hartree | Rydberg
  | Schrodinger | Electronic | Natural | NaturalGauss | QCD | QCDGauss | QCDoriginal
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Sys

/-- All systems in Julia order. -/
def all : List Sys :=
  [Metric, SI2019, SI1976, CODATA, Conventional, International, InternationalMean, MetricTurn,
   MetricSpatian, MetricGradian, MetricDegree, MetricArcminute, MetricArcsecond, Engineering,
   Gravitational, MTS, EMU, ESU, Gauss, LorentzHeaviside, FPS, IPS, British, English, Survey, FFF,
   MPH, KKH, Nautical, Meridian, IAU, IAUE, IAUJ, Hubble, Cosmological, CosmologicalQuantum,
   Planck, PlanckGauss, Stoney, Hartree, Rydberg, Schrodinger, Electronic, Natural, NaturalGauss,
   QCD, QCDGauss, QCDoriginal]

theorem all_length : all.length = 48 := by decide

/-- Julia `unitname` (`initdata.jl:169-171`); `IAU` prints as `IAU☉`. -/
def name : Sys → String
  | Metric => "Metric" | SI2019 => "SI2019" | SI1976 => "SI1976" | CODATA => "CODATA"
  | Conventional => "Conventional" | International => "International"
  | InternationalMean => "InternationalMean" | MetricTurn => "MetricTurn"
  | MetricSpatian => "MetricSpatian" | MetricGradian => "MetricGradian"
  | MetricDegree => "MetricDegree" | MetricArcminute => "MetricArcminute"
  | MetricArcsecond => "MetricArcsecond" | Engineering => "Engineering"
  | Gravitational => "Gravitational" | MTS => "MTS" | EMU => "EMU" | ESU => "ESU" | Gauss => "Gauss"
  | LorentzHeaviside => "LorentzHeaviside" | FPS => "FPS" | IPS => "IPS" | British => "British"
  | English => "English" | Survey => "Survey" | FFF => "FFF" | MPH => "MPH" | KKH => "KKH"
  | Nautical => "Nautical" | Meridian => "Meridian" | IAU => "IAU☉" | IAUE => "IAUE"
  | IAUJ => "IAUJ" | Hubble => "Hubble" | Cosmological => "Cosmological"
  | CosmologicalQuantum => "CosmologicalQuantum" | Planck => "Planck"
  | PlanckGauss => "PlanckGauss" | Stoney => "Stoney" | Hartree => "Hartree"
  | Rydberg => "Rydberg" | Schrodinger => "Schrodinger" | Electronic => "Electronic"
  | Natural => "Natural" | NaturalGauss => "NaturalGauss" | QCD => "QCD"
  | QCDGauss => "QCDGauss" | QCDoriginal => "QCDoriginal"

/-- Look a system up by its Julia name (including the aliases of
`initdata.jl:158-167`: `SI`, `MKS`, `CGS`, `IAU`, `EE`, …). -/
def ofName? (s : String) : Option Sys :=
  match s with
  | "SI" => some SI2019 | "MKS" => some Metric | "ME" | "MetricEngineering" => some Engineering
  | "GM" | "GravitationalMetric" => some Gravitational | "IAU" | "IAU☉" => some IAU
  | "CGS" => some Gauss | "CGSm" | "EMU2019" => some EMU | "CGSe" | "ESU2019" => some ESU
  | "HLU" => some LorentzHeaviside | "EnglishEngineering" | "EE" => some English
  | "BritishGravitational" | "BG" => some British | "EnglishUS" => some Survey
  | "AbsoluteEnglish" | "AE" => some FPS
  | s => all.find? (·.name == s)

/-- The system's constants in scalar `α`. -/
def sys (α : Type) [UnitAlg α] : Sys → UnitSystem α
  | Metric => UnitSystems.Metric α | SI2019 => UnitSystems.SI2019 α | SI1976 => UnitSystems.SI1976 α
  | CODATA => UnitSystems.CODATA α | Conventional => UnitSystems.Conventional α
  | International => UnitSystems.International α
  | InternationalMean => UnitSystems.InternationalMean α | MetricTurn => UnitSystems.MetricTurn α
  | MetricSpatian => UnitSystems.MetricSpatian α | MetricGradian => UnitSystems.MetricGradian α
  | MetricDegree => UnitSystems.MetricDegree α | MetricArcminute => UnitSystems.MetricArcminute α
  | MetricArcsecond => UnitSystems.MetricArcsecond α | Engineering => UnitSystems.Engineering α
  | Gravitational => UnitSystems.Gravitational α | MTS => UnitSystems.MTS α | EMU => UnitSystems.EMU α
  | ESU => UnitSystems.ESU α | Gauss => UnitSystems.Gauss α
  | LorentzHeaviside => UnitSystems.LorentzHeaviside α | FPS => UnitSystems.FPS α
  | IPS => UnitSystems.IPS α | British => UnitSystems.British α | English => UnitSystems.English α
  | Survey => UnitSystems.Survey α | FFF => UnitSystems.FFF α | MPH => UnitSystems.MPH α
  | KKH => UnitSystems.KKH α | Nautical => UnitSystems.Nautical α | Meridian => UnitSystems.Meridian α
  | IAU => UnitSystems.IAU α | IAUE => UnitSystems.IAUE α | IAUJ => UnitSystems.IAUJ α
  | Hubble => UnitSystems.Hubble α | Cosmological => UnitSystems.Cosmological α
  | CosmologicalQuantum => UnitSystems.CosmologicalQuantum α | Planck => UnitSystems.Planck α
  | PlanckGauss => UnitSystems.PlanckGauss α | Stoney => UnitSystems.Stoney α
  | Hartree => UnitSystems.Hartree α | Rydberg => UnitSystems.Rydberg α
  | Schrodinger => UnitSystems.Schrodinger α | Electronic => UnitSystems.Electronic α
  | Natural => UnitSystems.Natural α | NaturalGauss => UnitSystems.NaturalGauss α
  | QCD => UnitSystems.QCD α | QCDGauss => UnitSystems.QCDGauss α
  | QCDoriginal => UnitSystems.QCDoriginal α

end Sys

end UnitSystems

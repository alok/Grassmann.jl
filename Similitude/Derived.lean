import Similitude.Physics

/-!
# Derived units as quantities

Similitude defines ~190 named units as quantities in the system where they are
exactly one (or a simple multiple), `derived.jl:161-420`: `foot = English(𝟏, L)`,
`calorie = kilocalorie*milli`, `lightyear = year(Metric)*lightspeed(Metric)`.
Each definition below is Julia's, written with the typed API, so every unit's
system and dimension is checked by the elaborator (`lightyear : Q .Metric
Dim.length` only typechecks because `T · LT⁻¹` reduces to `L`), and its value is
Julia's exact group (`mile = 2⁵3⋅5⋅11 [ft] English`, `mile.to .Metric =
ft⋅2⁵3⋅5⋅11 = 1609.344 [m] Metric`).

Not ported: `neper`, `bel`, `decibel` (their dimension is a `LogGroup`, outside
the typed `Dim`), and `rem`, which is `Base.rem` in Julia (an error).
-/

namespace Similitude.Units

open FieldConstants FieldAlgebra UnitSystems Similitude

/-- A Similitude number. -/
local notation "𝐒" => Scalar
local notation "𝟏" => (UnitAlg.one : Scalar)
local notation "𝟐" => (c2 Scalar)
local notation "𝟑" => (c3 Scalar)
local notation "𝟓" => (c5 Scalar)
local notation "𝟕" => (c7 Scalar)
local notation "𝟏𝟏" => (c11 Scalar)
local notation "𝟏𝟗" => (c19 Scalar)
local notation "𝟒𝟑" => (c43 Scalar)
local notation "τ" => (UnitAlg.tau : Scalar)

/-- A measured constant as a Similitude number. -/
private def k (m : Measured) : 𝐒 := Scalar.measured m

/-! ### Constants of nature as quantities (`derived.jl:161-177`) -/

/-- `hyperfine = SI2019(ΔνCs, inv(T))`, the caesium frequency. -/
def hyperfine : Q .SI2019 Dim.frequency := Sys.SI2019.qty _ (k .ΔνCs)
/-- `hubble = Hubble(𝟏, inv(T))`. -/
def hubble : Q .Hubble Dim.frequency := Sys.Hubble.qty _ 𝟏
/-- `cosmological = 𝟑*ΩΛ*(hubble/lightspeed(Hubble))^2`. -/
def cosmological : Q .Hubble Dim.fuelefficiency := (𝟑 * k .ΩΛ) * (hubble / lightspeed .Hubble).npow 2
/-- `eddington = Cosmological(𝟏, M)(QCD)`. -/
def eddington : Q .QCD Dim.mass := (Sys.Cosmological.qty Dim.mass 𝟏).to .QCD
/-- `solarmass = IAU(𝟏, M)`. -/
def solarmass : Q .IAU Dim.mass := Sys.IAU.qty _ 𝟏
/-- `earthmass = Metric(GME/G, M)(IAU)`. -/
def earthmass : Q .IAU Dim.mass := (Sys.Metric.qty Dim.mass (k .GME / G 𝐒)).to .IAU
/-- `jupitermass = Metric(GMJ/G, M)(IAU)`. -/
def jupitermass : Q .IAU Dim.mass := (Sys.Metric.qty Dim.mass (k .GMJ / G 𝐒)).to .IAU
/-- `lunarmass = earthmass/μE☾` (`μE☾` is a `FieldConstants.Constant`). -/
def lunarmass : Q .IAU Dim.mass := earthmass / k .μE
/-- `gforce = English(𝟏, specificforce)`. -/
def gforce : Q .English Dim.specificforce := Sys.English.qty _ 𝟏
/-- `atmosphere = Metric(atm, pressure)`. -/
def atmosphere : Q .Metric Dim.pressure := Sys.Metric.qty _ (k .atm)
/-- `loschmidt(U) = U(atmosphere(U), pressure)/U(SI2019(T₀,Θ)(U), Θ)/boltzmann(U)`. -/
def loschmidt (U : Sys) : Q U Dim.numberdensity :=
  (U.qty Dim.pressure (atmosphere.to U).val / U.qty Dim.temperature
    ((Sys.SI2019.qty Dim.temperature (k .T₀)).to U).val) / boltzmann U
/-- `amagat = loschmidt(SI2019)/avogadro(SI2019)`. -/
def amagat : Q .SI2019 Dim.molarity := loschmidt .SI2019 / avogadro .SI2019
/-- `wienwavelength = planck(SI)*lightspeed(SI)/boltzmann(SI)/Constant(4.965114231744276303)`. -/
def wienwavelength : Q .SI2019 (Dim.length * Dim.temperature) :=
  planck .SI2019 * lightspeed .SI2019 / boltzmann .SI2019 / Scalar.ofFloat 4.965114231744276303
/-- `wienfrequency = Constant(2.821439372122078893)*boltzmann(SI)/planck(SI)`. -/
def wienfrequency : Q .SI2019 (Dim.frequency / Dim.temperature) :=
  Scalar.ofFloat 2.821439372122078893 * boltzmann .SI2019 / planck .SI2019

/-! ### Energy units needed early -/

/-- `kilocalorie = International(𝟐^5*𝟓^4*𝟑^2/𝟒𝟑, energy)(Metric)`. -/
def kilocalorie : Q .Metric Dim.energy :=
  (Sys.International.qty Dim.energy (𝟐 ^ (5 : Int) * 𝟓 ^ (4 : Int) * 𝟑 ^ (2 : Int) / 𝟒𝟑)).to .Metric
/-- `calorie = kilocalorie*milli`. -/
def calorie : Q .Metric Dim.energy := kilocalorie * milli 𝐒
/-- `mechanicalheat(U) = molargas(U)*U(normal(calorie(Metric)/molargas(Metric)), Θ*N)`. -/
def mechanicalheat (U : Sys) : Q U Dim.energy :=
  molargas U * U.qty (Dim.temperature * Dim.molaramount) (calorie.to .Metric / molargas .Metric).val

/-! ### Angle -/

/-- `spatian = MetricSpatian(𝟏, A)` -/
def spatian : Q .MetricSpatian Dim.angle := Sys.MetricSpatian.qty _ 𝟏
/-- `steradian = Engineering(𝟏, solidangle)` -/
def steradian : Q .Engineering Dim.solidangle := Sys.Engineering.qty _ 𝟏
/-- `degree = MetricDegree(𝟏, A)` -/
def degree : Q .MetricDegree Dim.angle := Sys.MetricDegree.qty _ 𝟏
/-- `squaredegree = MetricDegree(𝟏, solidangle)` -/
def squaredegree : Q .MetricDegree Dim.solidangle := Sys.MetricDegree.qty _ 𝟏
/-- `gradian = MetricGradian(𝟏, A)` -/
def gradian : Q .MetricGradian Dim.angle := Sys.MetricGradian.qty _ 𝟏
/-- `bradian = Engineering(τ/𝟐^8, A)` -/
def bradian : Q .Engineering Dim.angle := Sys.Engineering.qty _ (τ / 𝟐 ^ (8 : Int))
/-- `arcminute = MetricArcminute(𝟏, A)` -/
def arcminute : Q .MetricArcminute Dim.angle := Sys.MetricArcminute.qty _ 𝟏
/-- `arcsecond = MetricArcsecond(𝟏, A)` -/
def arcsecond : Q .MetricArcsecond Dim.angle := Sys.MetricArcsecond.qty _ 𝟏

/-! ### Length -/

/-- `meter = Metric(𝟏, L)` -/
def meter : Q .Metric Dim.length := Sys.Metric.qty _ 𝟏
/-- `angstrom = hecto*pico*meter` -/
def angstrom : Q .Metric Dim.length := (hecto 𝐒 * pico 𝐒) * meter
/-- `inch = IPS(𝟏, L)` -/
def inch : Q .IPS Dim.length := Sys.IPS.qty _ 𝟏
/-- `foot = English(𝟏, L)` -/
def foot : Q .English Dim.length := Sys.English.qty _ 𝟏
/-- `surveyfoot = Survey(𝟏, L)` -/
def surveyfoot : Q .Survey Dim.length := Sys.Survey.qty _ 𝟏
/-- `yard = 𝟑*foot` -/
def yard : Q .English Dim.length := 𝟑 * foot
/-- `mile = English(𝟐^5*𝟑*𝟓*𝟏𝟏, L)` -/
def mile : Q .English Dim.length := Sys.English.qty _ (𝟐 ^ (5 : Int) * 𝟑 * 𝟓 * 𝟏𝟏)
/-- `statutemile = Survey(𝟐^5*𝟑*𝟓*𝟏𝟏, L)` -/
def statutemile : Q .Survey Dim.length := Sys.Survey.qty _ (𝟐 ^ (5 : Int) * 𝟑 * 𝟓 * 𝟏𝟏)
/-- `earthradius = sqrt(earthmass(Metric)*gravitation(Metric)/gforce(Metric))` -/
def earthradius : Q .Metric Dim.length :=
  (earthmass.to .Metric * gravitation .Metric / gforce.to .Metric).sqrt
/-- `greatcircle = τ*earthradius` -/
def greatcircle : Q .Metric Dim.length := τ * earthradius
/-- `earthmeter = Meridian(𝟏, L)` -/
def earthmeter : Q .Meridian Dim.length := Sys.Meridian.qty _ 𝟏
/-- `nauticalmile = Nautical(𝟏, L)` -/
def nauticalmile : Q .Nautical Dim.length := Sys.Nautical.qty _ 𝟏
/-- `admiraltymile = English(𝟐^6*𝟓*𝟏𝟗, L)` -/
def admiraltymile : Q .English Dim.length := Sys.English.qty _ (𝟐 ^ (6 : Int) * 𝟓 * 𝟏𝟗)
/-- `meridianmile = Metric(𝟐^4*𝟓^5/𝟑^3, L)` -/
def meridianmile : Q .Metric Dim.length :=
  Sys.Metric.qty _ (𝟐 ^ (4 : Int) * 𝟓 ^ (5 : Int) / 𝟑 ^ (3 : Int))
/-- `astronomicalunit = IAU(𝟏, L)` -/
def astronomicalunit : Q .IAU Dim.length := Sys.IAU.qty _ 𝟏
/-- `lunardistance = IAUE(𝟏, L)(Metric)` -/
def lunardistance : Q .Metric Dim.length := (Sys.IAUE.qty Dim.length 𝟏).to .Metric
/-- `jupiterdistance = IAUJ(𝟏, L)(Metric)` -/
def jupiterdistance : Q .Metric Dim.length := (Sys.IAUJ.qty Dim.length 𝟏).to .Metric
/-- `parsec = astronomicalunit*(𝟐^7*𝟑^4*𝟓^3/τ)` -/
def parsec : Q .IAU Dim.length :=
  astronomicalunit * (𝟐 ^ (7 : Int) * 𝟑 ^ (4 : Int) * 𝟓 ^ (3 : Int) / τ)

/-! ### Time -/

/-- `second = Metric(𝟏, T)` -/
def second : Q .Metric Dim.time := Sys.Metric.qty _ 𝟏
/-- `minute = (𝟐^2*𝟑*𝟓)*second` -/
def minute : Q .Metric Dim.time := (𝟐 ^ (2 : Int) * 𝟑 * 𝟓) * second
/-- `hour = (𝟐^2*𝟑*𝟓)*minute` -/
def hour : Q .Metric Dim.time := (𝟐 ^ (2 : Int) * 𝟑 * 𝟓) * minute
/-- `day = IAU(𝟏, T)` -/
def day : Q .IAU Dim.time := Sys.IAU.qty _ 𝟏
/-- `year = IAU(aⱼ, T)` -/
def year : Q .IAU Dim.time := Sys.IAU.qty _ (k .aⱼ)
/-- `lightyear = year(Metric)*lightspeed(Metric)` -/
def lightyear : Q .Metric Dim.length := year.to .Metric * lightspeed .Metric
/-- `radarmile = 𝟐*nauticalmile(Metric)/lightspeed(Metric)` -/
def radarmile : Q .Metric Dim.time := 𝟐 * nauticalmile.to .Metric / lightspeed .Metric
/-- `gaussgravitation = sqrt(normal(gravitation(IAU)))*radian(IAU)/day(IAU)` -/
def gaussgravitation : Q .IAU Dim.angularfrequency :=
  (gravitation .IAU).val.sqrt * radian .IAU / day.to .IAU
/-- `gaussianyear = turn(IAU)/gaussgravitation` -/
def gaussianyear : Q .IAU Dim.time := turn .IAU / gaussgravitation
/-- `siderealyear = gaussianyear/√(solarmass+earthmass+lunarmass).v` -/
def siderealyear : Q .IAU Dim.time := gaussianyear / (solarmass + earthmass + lunarmass).val.sqrt
/-- `gaussianmonth = τ/sqrt(normal(gravitation(IAUE)))*day` -/
def gaussianmonth : Q .IAU Dim.time := (τ / (gravitation .IAUE).val.sqrt) * day
/-- `siderealmonth = gaussianmonth/normal(sqrt(earthmass(IAUE)+lunarmass(IAUE)))` -/
def siderealmonth : Q .IAU Dim.time :=
  gaussianmonth / (earthmass.to .IAUE + lunarmass.to .IAUE).sqrt.val
/-- `synodicmonth = inv(inv(siderealmonth(IAU))-inv(siderealyear(IAU)))` -/
def synodicmonth : Q .IAU Dim.time :=
  ((siderealmonth.to .IAU).inv - (siderealyear.to .IAU).inv).inv
/-- `jovianyear = τ*sqrt(normal(jupiterdistance(IAU)^3/solarmass/gravitation(IAU)))*day/normal(sqrt(solarmass+jupitermass))` -/
def jovianyear : Q .IAU Dim.time :=
  (τ * ((jupiterdistance.to .IAU).npow 3 / solarmass / gravitation .IAU).val.sqrt) * day /
    (solarmass + jupitermass).sqrt.val

/-! ### Area and volume -/

/-- `barn = Metric((𝟐*𝟓)^-28, area)` -/
def barn : Q .Metric Dim.area := Sys.Metric.qty _ ((𝟐 * 𝟓) ^ (-28 : Int))
/-- `hectare = Metric(hecto*hecto, area)` -/
def hectare : Q .Metric Dim.area := Sys.Metric.qty _ (hecto 𝐒 * hecto 𝐒)
/-- `acre = MPH(𝟐^-7/𝟓, area)(English)` -/
def acre : Q .English Dim.area := (Sys.MPH.qty Dim.area (𝟐 ^ (-7 : Int) / 𝟓)).to .English
/-- `surveyacre = Survey(𝟐^3*𝟑^2*𝟓*𝟏𝟏^2, area)` -/
def surveyacre : Q .Survey Dim.area :=
  Sys.Survey.qty _ (𝟐 ^ (3 : Int) * 𝟑 ^ (2 : Int) * 𝟓 * 𝟏𝟏 ^ (2 : Int))
/-- `gallon = IPS(𝟑*𝟕*𝟏𝟏, volume)` -/
def gallon : Q .IPS Dim.volume := Sys.IPS.qty _ (𝟑 * 𝟕 * 𝟏𝟏)
/-- `liter = Metric(milli, volume)` -/
def liter : Q .Metric Dim.volume := Sys.Metric.qty _ (milli 𝐒)
/-- `quart = gallon/𝟐^2` -/
def quart : Q .IPS Dim.volume := gallon / 𝟐 ^ (2 : Int)
/-- `pint = quart/𝟐` -/
def pint : Q .IPS Dim.volume := quart / 𝟐
/-- `cup = pint/𝟐` -/
def cup : Q .IPS Dim.volume := pint / 𝟐
/-- `fluidounce = cup/𝟐^3` -/
def fluidounce : Q .IPS Dim.volume := cup / 𝟐 ^ (3 : Int)
/-- `teaspoon = 𝟓*milli*liter` -/
def teaspoon : Q .Metric Dim.volume := (𝟓 * milli 𝐒) * liter
/-- `tablespoon = 𝟑*teaspoon` -/
def tablespoon : Q .Metric Dim.volume := 𝟑 * teaspoon

/-! ### Speed -/

/-- `bubnoff = meter(Metric)/year(Metric)` -/
def bubnoff : Q .Metric Dim.speed := meter.to .Metric / year.to .Metric
/-- `ips = IPS(𝟏, speed)` -/
def ips : Q .IPS Dim.speed := Sys.IPS.qty _ 𝟏
/-- `fps = British(𝟏, speed)` -/
def fps : Q .British Dim.speed := Sys.British.qty _ 𝟏
/-- `fpm = foot(British)/minute(British)` -/
def fpm : Q .British Dim.speed := foot.to .British / minute.to .British
/-- `ms = Metric(𝟏, speed)` -/
def ms : Q .Metric Dim.speed := Sys.Metric.qty _ 𝟏
/-- `kmh = kilo*meter/hour` -/
def kmh : Q .Metric Dim.speed := kilo 𝐒 * meter / hour
/-- `mph = MPH(𝟏, speed)` -/
def mph : Q .MPH Dim.speed := Sys.MPH.qty _ 𝟏
/-- `knot = Nautical(𝟏, speed)` -/
def knot : Q .Nautical Dim.speed := Sys.Nautical.qty _ 𝟏
/-- `mps = mile(MPH)/second(MPH)` -/
def mps : Q .MPH Dim.speed := mile.to .MPH / second.to .MPH

/-! ### Mass -/

/-- `gram = Metric(milli, M)` -/
def gram : Q .Metric Dim.mass := Sys.Metric.qty _ (milli 𝐒)
/-- `earthgram = Meridian(milli, M)` -/
def earthgram : Q .Meridian Dim.mass := Sys.Meridian.qty _ (milli 𝐒)
/-- `kilogram = Metric(𝟏, M)` -/
def kilogram : Q .Metric Dim.mass := Sys.Metric.qty _ 𝟏
/-- `tonne = Metric(kilo, M)` -/
def tonne : Q .Metric Dim.mass := Sys.Metric.qty _ (kilo 𝐒)
/-- `ton = English(𝟐*kilo, M)` -/
def ton : Q .English Dim.mass := Sys.English.qty _ (𝟐 * kilo 𝐒)
/-- `pound = English(𝟏, M)` -/
def pound : Q .English Dim.mass := Sys.English.qty _ 𝟏
/-- `ounce = English(𝟐^-4, M)` -/
def ounce : Q .English Dim.mass := Sys.English.qty _ (𝟐 ^ (-4 : Int))
/-- `grain = milli*pound/𝟕` -/
def grain : Q .English Dim.mass := milli 𝐒 * pound / 𝟕
/-- `slug = British(𝟏, M)` -/
def slug : Q .British Dim.mass := Sys.British.qty _ 𝟏
/-- `slinch = IPS(𝟏, M)` -/
def slinch : Q .IPS Dim.mass := Sys.IPS.qty _ 𝟏
/-- `hyl = Gravitational(𝟏, M)` -/
def hyl : Q .Gravitational Dim.mass := Sys.Gravitational.qty _ 𝟏

/-! ### Force and pressure -/

/-- `dyne = Gauss(𝟏, force)` -/
def dyne : Q .Gauss Dim.force := Sys.Gauss.qty _ 𝟏
/-- `newton = Metric(𝟏, force)` -/
def newton : Q .Metric Dim.force := Sys.Metric.qty _ 𝟏
/-- `poundal = FPS(𝟏, force)` -/
def poundal : Q .FPS Dim.force := Sys.FPS.qty _ 𝟏
/-- `kilopond = Engineering(𝟏, force)` -/
def kilopond : Q .Engineering Dim.force := Sys.Engineering.qty _ 𝟏
/-- `poundforce = English(𝟏, F)` -/
def poundforce : Q .English Dim.force := Sys.English.qty _ 𝟏
/-- `psi = IPS(𝟏, pressure)` -/
def psi : Q .IPS Dim.pressure := Sys.IPS.qty _ 𝟏
/-- `bar = Metric(hecto*kilo, pressure)` -/
def bar : Q .Metric Dim.pressure := Sys.Metric.qty _ (hecto 𝐒 * kilo 𝐒)
/-- `barye = Gauss(𝟏, pressure)` -/
def barye : Q .Gauss Dim.pressure := Sys.Gauss.qty _ 𝟏
/-- `pascal = Metric(𝟏, pressure)` -/
def pascal : Q .Metric Dim.pressure := Sys.Metric.qty _ 𝟏
/-- `technicalatmosphere = kilopond/(centi*meter(ME))^2` -/
def technicalatmosphere : Q .Engineering Dim.pressure :=
  kilopond / (centi 𝐒 * meter.to .Engineering).npow 2
/-- `inchmercury = Metric(inv(inHg), pressure)` -/
def inchmercury : Q .Metric Dim.pressure := Sys.Metric.qty _ (k .inHg)⁻¹
/-- `torr = Metric(atm/𝟐^3/𝟓/𝟏𝟗, pressure)` -/
def torr : Q .Metric Dim.pressure := Sys.Metric.qty _ (k .atm / 𝟐 ^ (3 : Int) / 𝟓 / 𝟏𝟗)

/-! ### Energy and power -/

/-- `electronvolt = elementarycharge(SI2019)*SI2019(𝟏, electricpotential)` -/
def electronvolt : Q .SI2019 Dim.energy :=
  elementarycharge .SI2019 * Sys.SI2019.qty Dim.electricpotential 𝟏
/-- `erg = Gauss(𝟏, energy)` -/
def erg : Q .Gauss Dim.energy := Sys.Gauss.qty _ 𝟏
/-- `joule = Metric(𝟏, energy)` -/
def joule : Q .Metric Dim.energy := Sys.Metric.qty _ 𝟏
/-- `footpound = poundforce*foot` -/
def footpound : Q .English Dim.energy := poundforce * foot
/-- `meancalorie = InternationalMean(𝟐^2*𝟓*𝟑^2/𝟒𝟑, energy)(Metric)` -/
def meancalorie : Q .Metric Dim.energy :=
  (Sys.InternationalMean.qty Dim.energy (𝟐 ^ (2 : Int) * 𝟓 * 𝟑 ^ (2 : Int) / 𝟒𝟑)).to .Metric
/-- `earthcalorie = mechanicalheat(Meridian)` -/
def earthcalorie : Q .Meridian Dim.energy := mechanicalheat .Meridian
/-- `thermalunit = mechanicalheat(English)` -/
def thermalunit : Q .English Dim.energy := mechanicalheat .English
/-- `tontnt = giga*calorie(Metric)` -/
def tontnt : Q .Metric Dim.energy := giga 𝐒 * calorie.to .Metric
/-- `gasgallon = 𝟐*𝟑*𝟏𝟗*kilo*thermalunit(Metric)` -/
def gasgallon : Q .Metric Dim.energy := (𝟐 * 𝟑 * 𝟏𝟗 * kilo 𝐒) * thermalunit.to .Metric
/-- `watt = Metric(𝟏, power)` -/
def watt : Q .Metric Dim.power := Sys.Metric.qty _ 𝟏
/-- `horsepower = British(𝟐*𝟓^2*𝟏𝟏, power)` -/
def horsepower : Q .British Dim.power := Sys.British.qty _ (𝟐 * 𝟓 ^ (2 : Int) * 𝟏𝟏)
/-- `horsepowerwatt = British(𝟐^4*𝟑^3/𝟓*τ, power)` -/
def horsepowerwatt : Q .British Dim.power :=
  Sys.British.qty _ (𝟐 ^ (4 : Int) * 𝟑 ^ (3 : Int) / 𝟓 * τ)
/-- `horsepowermetric = GM(𝟑*𝟓^2, power)` -/
def horsepowermetric : Q .Gravitational Dim.power := Sys.Gravitational.qty _ (𝟑 * 𝟓 ^ (2 : Int))
/-- `tonsrefrigeration = thermalunit(Metric)/Metric(𝟑/𝟐/𝟓, T)` -/
def tonsrefrigeration : Q .Metric Dim.power :=
  thermalunit.to .Metric / Sys.Metric.qty Dim.time (𝟑 / 𝟐 / 𝟓)
/-- `boilerhorsepower = Constant(1339)/Metric(𝟐^4*𝟑^2, T)*thermalunit(Metric)` -/
def boilerhorsepower : Q .Metric Dim.power :=
  ((1339 : 𝐒) * (Sys.Metric.qty Dim.time (𝟐 ^ (4 : Int) * 𝟑 ^ (2 : Int))).inv) * thermalunit.to .Metric
/-- `electricalhorsepower = Metric(𝟐*373, power)` -/
def electricalhorsepower : Q .Metric Dim.power := Sys.Metric.qty _ (𝟐 * 373)

/-! ### Electromagnetic -/

/-- `coulomb = Metric(𝟏, Q)` -/
def coulomb : Q .Metric Dim.charge := Sys.Metric.qty _ 𝟏
/-- `ampere = Metric(𝟏, current)` -/
def ampere : Q .Metric Dim.current := Sys.Metric.qty _ 𝟏
/-- `volt = Metric(𝟏, electricpotential)` -/
def volt : Q .Metric Dim.electricpotential := Sys.Metric.qty _ 𝟏
/-- `henry = Metric(𝟏, inductance)` -/
def henry : Q .Metric Dim.inductance := Sys.Metric.qty _ 𝟏
/-- `ohm = Metric(𝟏, resistance)` -/
def ohm : Q .Metric Dim.resistance := Sys.Metric.qty _ 𝟏
/-- `siemens = Metric(𝟏, conductance)` -/
def siemens : Q .Metric Dim.conductance := Sys.Metric.qty _ 𝟏
/-- `farad = Metric(𝟏, capacitance)` -/
def farad : Q .Metric Dim.capacitance := Sys.Metric.qty _ 𝟏
/-- `weber = Metric(𝟏, magneticflux)` -/
def weber : Q .Metric Dim.magneticflux := Sys.Metric.qty _ 𝟏
/-- `tesla = Metric(𝟏, magneticfluxdensity)` -/
def tesla : Q .Metric Dim.magneticfluxdensity := Sys.Metric.qty _ 𝟏
/-- `statcoulomb = ESU(𝟏, Q)` -/
def statcoulomb : Q .ESU Dim.charge := Sys.ESU.qty _ 𝟏
/-- `statampere = ESU(𝟏, current)` -/
def statampere : Q .ESU Dim.current := Sys.ESU.qty _ 𝟏
/-- `statvolt = ESU(𝟏, electricpotential)` -/
def statvolt : Q .ESU Dim.electricpotential := Sys.ESU.qty _ 𝟏
/-- `stathenry = ESU(𝟏, inductance)` -/
def stathenry : Q .ESU Dim.inductance := Sys.ESU.qty _ 𝟏
/-- `statohm = ESU(𝟏, resistance)` -/
def statohm : Q .ESU Dim.resistance := Sys.ESU.qty _ 𝟏
/-- `statmho = ESU(𝟏, conductance)` -/
def statmho : Q .ESU Dim.conductance := Sys.ESU.qty _ 𝟏
/-- `statfarad = ESU(𝟏, capacitance)` -/
def statfarad : Q .ESU Dim.capacitance := Sys.ESU.qty _ 𝟏
/-- `statweber = ESU(𝟏, magneticflux)` -/
def statweber : Q .ESU Dim.magneticflux := Sys.ESU.qty _ 𝟏
/-- `stattesla = ESU(𝟏, magneticfluxdensity)` -/
def stattesla : Q .ESU Dim.magneticfluxdensity := Sys.ESU.qty _ 𝟏
/-- `abcoulomb = EMU(𝟏, Q)` -/
def abcoulomb : Q .EMU Dim.charge := Sys.EMU.qty _ 𝟏
/-- `abampere = EMU(𝟏, current)` -/
def abampere : Q .EMU Dim.current := Sys.EMU.qty _ 𝟏
/-- `abvolt = EMU(𝟏, electricpotential)` -/
def abvolt : Q .EMU Dim.electricpotential := Sys.EMU.qty _ 𝟏
/-- `abhenry = EMU(𝟏, inductance)` -/
def abhenry : Q .EMU Dim.inductance := Sys.EMU.qty _ 𝟏
/-- `abohm = EMU(𝟏, resistance)` -/
def abohm : Q .EMU Dim.resistance := Sys.EMU.qty _ 𝟏
/-- `abmho = EMU(𝟏, conductance)` -/
def abmho : Q .EMU Dim.conductance := Sys.EMU.qty _ 𝟏
/-- `abfarad = EMU(𝟏, capacitance)` -/
def abfarad : Q .EMU Dim.capacitance := Sys.EMU.qty _ 𝟏
/-- `maxwell = EMU(𝟏, magneticflux)` -/
def maxwell : Q .EMU Dim.magneticflux := Sys.EMU.qty _ 𝟏
/-- `gauss = EMU(𝟏, magneticfluxdensity)` -/
def gauss : Q .EMU Dim.magneticfluxdensity := Sys.EMU.qty _ 𝟏
/-- `oersted = EMU(𝟏, magneticfield)` -/
def oersted : Q .EMU Dim.magneticfield := Sys.EMU.qty _ 𝟏
/-- `gilbert = EMU(𝟏/𝟐/τ, current/A)` -/
def gilbert : Q .EMU (Dim.current / USQ.A) := Sys.EMU.qty _ (𝟏 / 𝟐 / τ)
/-- `earthcoulomb = Meridian(𝟏, Q)` -/
def earthcoulomb : Q .Meridian Dim.charge := Sys.Meridian.qty _ 𝟏

/-! ### Temperature, amount, photometry -/

/-- `boiling = Metric(T₀+Constant(99.9839), Θ)` (a `Float64`: sums of unlike constants are not exact) -/
def boiling : Q .Metric Dim.temperature := Sys.Metric.qty _ (k .T₀ + Scalar.ofFloat 99.9839)
/-- `sealevel = Metric(T₀+𝟑*𝟓, Θ)` -/
def sealevel : Q .Metric Dim.temperature := Sys.Metric.qty _ (k .T₀ + 𝟑 * 𝟓)
/-- `kelvin = Metric(𝟏, Θ)` -/
def kelvin : Q .Metric Dim.temperature := Sys.Metric.qty _ 𝟏
/-- `celsius = Metric(T₀, Θ)` -/
def celsius : Q .Metric Dim.temperature := Sys.Metric.qty _ (k .T₀)
/-- `rankine = English(𝟏, Θ)` -/
def rankine : Q .English Dim.temperature := Sys.English.qty _ 𝟏
/-- `fahrenheit = English(459.67, Θ)` -/
def fahrenheit : Q .English Dim.temperature := Sys.English.qty _ (Scalar.ofFloat 459.67)
/-- `mole = Metric(𝟏, N)` -/
def mole : Q .Metric Dim.molaramount := Sys.Metric.qty _ 𝟏
/-- `earthmole = Meridian(𝟏, N)` -/
def earthmole : Q .Meridian Dim.molaramount := Sys.Meridian.qty _ 𝟏
/-- `poundmole = English(𝟏, N)` -/
def poundmole : Q .English Dim.molaramount := Sys.English.qty _ 𝟏
/-- `slugmole = British(𝟏, N)` -/
def slugmole : Q .British Dim.molaramount := Sys.British.qty _ 𝟏
/-- `slinchmole = IPS(𝟏, N)` -/
def slinchmole : Q .IPS Dim.molaramount := Sys.IPS.qty _ 𝟏
/-- `katal = Metric(𝟏, catalysis)` -/
def katal : Q .Metric Dim.catalysis := Sys.Metric.qty _ 𝟏
/-- `lumen = Metric(𝟏, luminousflux)` -/
def lumen : Q .Metric Dim.luminousflux := Sys.Metric.qty _ 𝟏
/-- `candela = Metric(𝟏, luminousintensity)` -/
def candela : Q .Metric Dim.luminousintensity := Sys.Metric.qty _ 𝟏
/-- `lux = Metric(𝟏, illuminance)` -/
def lux : Q .Metric Dim.illuminance := Sys.Metric.qty _ 𝟏
/-- `phot = Gauss(𝟏, illuminance)` -/
def phot : Q .Gauss Dim.illuminance := Sys.Gauss.qty _ 𝟏
/-- `footcandle = English(𝟏, illuminance)` -/
def footcandle : Q .English Dim.illuminance := Sys.English.qty _ 𝟏
/-- `nit = Metric(𝟏, luminance)` -/
def nit : Q .Metric Dim.luminance := Sys.Metric.qty _ 𝟏
/-- `apostilb = Metric(𝟐/τ, luminance)` -/
def apostilb : Q .Metric Dim.luminance := Sys.Metric.qty _ (𝟐 / τ)
/-- `stilb = Gauss(𝟏, luminance)` -/
def stilb : Q .Gauss Dim.luminance := Sys.Gauss.qty _ 𝟏
/-- `lambert = Gauss(𝟐/τ, luminance)` -/
def lambert : Q .Gauss Dim.luminance := Sys.Gauss.qty _ (𝟐 / τ)
/-- `footlambert = English(𝟐/τ, luminance)` -/
def footlambert : Q .English Dim.luminance := Sys.English.qty _ (𝟐 / τ)
/-- `bril = centi*nano*lambert` -/
def bril : Q .Gauss Dim.luminance := (centi 𝐒 * nano 𝐒) * lambert
/-- `talbot = Metric(𝟏, luminousenergy)` -/
def talbot : Q .Metric Dim.luminousenergy := Sys.Metric.qty _ 𝟏
/-- `lumerg = Gauss(centi^2*milli, luminousenergy)` -/
def lumerg : Q .Gauss Dim.luminousenergy := Sys.Gauss.qty _ (centi 𝐒 ^ (2 : Int) * milli 𝐒)
/-- `rayleigh = Metric(deka*giga, photonirradiance)` -/
def rayleigh : Q .Metric Dim.photonirradiance := Sys.Metric.qty _ (deka 𝐒 * giga 𝐒)
/-- `flick = Metric(deka*giga, radiance/L)` -/
def flick : Q .Metric (Dim.radiance / USQ.L) := Sys.Metric.qty _ (deka 𝐒 * giga 𝐒)

/-! ### Miscellaneous (`derived.jl:393-414`) -/

/-- `hertz = inv(second(Metric))` -/
def hertz : Q .Metric Dim.frequency := (second.to .Metric).inv
/-- `apm = inv(minute(Metric))` -/
def apm : Q .Metric Dim.frequency := (minute.to .Metric).inv
/-- `rpm = turn(Metric)/minute(Metric)` -/
def rpm : Q .Metric Dim.angularfrequency := turn .Metric / minute.to .Metric
/-- `galileo = Gauss(𝟏, specificforce)` -/
def galileo : Q .Gauss Dim.specificforce := Sys.Gauss.qty _ 𝟏
/-- `eotvos = Gauss(nano, specificforce/L)` -/
def eotvos : Q .Gauss (Dim.specificforce / USQ.L) := Sys.Gauss.qty _ (nano 𝐒)
/-- `poise = Gauss(𝟏, viscosity)` -/
def poise : Q .Gauss Dim.viscosity := Sys.Gauss.qty _ 𝟏
/-- `reyn = IPS(𝟏, viscosity)` -/
def reyn : Q .IPS Dim.viscosity := Sys.IPS.qty _ 𝟏
/-- `diopter = Metric(𝟏, angularwavenumber)` -/
def diopter : Q .Metric Dim.angularwavenumber := Sys.Metric.qty _ 𝟏
/-- `kayser = Gauss(𝟏, wavenumber)` -/
def kayser : Q .Gauss Dim.wavenumber := Sys.Gauss.qty _ 𝟏
/-- `darcy = Gauss(milli/atm, area)` -/
def darcy : Q .Gauss Dim.area := Sys.Gauss.qty _ (milli 𝐒 / k .atm)
/-- `stokes = Gauss(𝟏, diffusivity)` -/
def stokes : Q .Gauss Dim.diffusivity := Sys.Gauss.qty _ 𝟏
/-- `mpge = mile(Metric)/gasgallon(Metric)` -/
def mpge : Q .Metric (Dim.length / Dim.energy) := mile.to .Metric / gasgallon.to .Metric
/-- `curie = Constant(37)*giga*hertz` -/
def curie : Q .Metric Dim.frequency := ((37 : 𝐒) * giga 𝐒) * hertz
/-- `gray = Metric(𝟏, energy/M)` -/
def gray : Q .Metric Dim.specificenergy := Sys.Metric.qty _ 𝟏
/-- `roentgen = ESU(𝟏, chargedensity)(Metric)/Metric(Constant(1.293), density)` -/
def roentgen : Q .Metric Dim.exposure :=
  (Sys.ESU.qty Dim.chargedensity 𝟏).to .Metric / Sys.Metric.qty Dim.density (Scalar.ofFloat 1.293)
/-- `rayl = Metric(𝟏, specificimpedance)` -/
def rayl : Q .Metric Dim.specificimpedance := Sys.Metric.qty _ 𝟏
/-- `langley = calorie(Metric)/(centi*meter(Metric))^2` -/
def langley : Q .Metric Dim.fluence := calorie.to .Metric / (centi 𝐒 * meter.to .Metric).npow 2
/-- `jansky = Metric((𝟐*𝟓)^-26, fluence)` -/
def jansky : Q .Metric Dim.fluence := Sys.Metric.qty _ ((𝟐 * 𝟓) ^ (-26 : Int))
/-- `solarflux = hecto*hecto*jansky` -/
def solarflux : Q .Metric Dim.fluence := (hecto 𝐒 * hecto 𝐒) * jansky

/-- A quantity together with its system and dimension. -/
structure AnyQ where
  /-- unit system -/
  U : Sys
  /-- USQ dimension -/
  d : Dim
  /-- the quantity -/
  q : Q U d

/-- Package a typed quantity. -/
def AnyQ.of {U : Sys} {d : Dim} (q : Q U d) : AnyQ := ⟨U, d, q⟩

/-- Similitude's derived units and constants by Julia name (`UnitSystems.Derived`
order), for lookup and golden tests. Functions of the system (`loschmidt`,
`mechanicalheat`) are listed at `Metric`. -/
def table : List (String × AnyQ) :=
  [("hyperfine", .of hyperfine), ("loschmidt", .of (loschmidt .Metric)),
   ("wienwavelength", .of wienwavelength), ("wienfrequency", .of wienfrequency),
   ("mechanicalheat", .of (mechanicalheat .Metric)), ("eddington", .of eddington),
   ("solarmass", .of solarmass), ("jupitermass", .of jupitermass), ("earthmass", .of earthmass),
   ("lunarmass", .of lunarmass), ("earthradius", .of earthradius), ("greatcircle", .of greatcircle),
   ("radarmile", .of radarmile), ("hubble", .of hubble), ("cosmological", .of cosmological),
   ("steradian", .of steradian), ("spatian", .of spatian), ("degree", .of degree),
   ("squaredegree", .of squaredegree), ("gradian", .of gradian), ("bradian", .of bradian),
   ("arcminute", .of arcminute), ("arcsecond", .of arcsecond), ("second", .of second),
   ("minute", .of minute), ("hour", .of hour), ("day", .of day), ("gaussianmonth", .of gaussianmonth),
   ("siderealmonth", .of siderealmonth), ("synodicmonth", .of synodicmonth), ("year", .of year),
   ("gaussianyear", .of gaussianyear), ("siderealyear", .of siderealyear),
   ("jovianyear", .of jovianyear), ("angstrom", .of angstrom), ("inch", .of inch),
   ("foot", .of foot), ("surveyfoot", .of surveyfoot), ("yard", .of yard), ("meter", .of meter),
   ("earthmeter", .of earthmeter), ("mile", .of mile), ("statutemile", .of statutemile),
   ("meridianmile", .of meridianmile), ("admiraltymile", .of admiraltymile),
   ("nauticalmile", .of nauticalmile), ("lunardistance", .of lunardistance),
   ("astronomicalunit", .of astronomicalunit), ("jupiterdistance", .of jupiterdistance),
   ("lightyear", .of lightyear), ("parsec", .of parsec), ("barn", .of barn),
   ("hectare", .of hectare), ("acre", .of acre), ("surveyacre", .of surveyacre),
   ("liter", .of liter), ("gallon", .of gallon), ("quart", .of quart), ("pint", .of pint),
   ("cup", .of cup), ("fluidounce", .of fluidounce), ("teaspoon", .of teaspoon),
   ("tablespoon", .of tablespoon), ("bubnoff", .of bubnoff), ("ips", .of ips), ("fps", .of fps),
   ("fpm", .of fpm), ("ms", .of ms), ("kmh", .of kmh), ("mph", .of mph), ("knot", .of knot),
   ("mps", .of mps), ("grain", .of grain), ("gram", .of gram), ("earthgram", .of earthgram),
   ("kilogram", .of kilogram), ("tonne", .of tonne), ("ton", .of ton), ("pound", .of pound),
   ("ounce", .of ounce), ("slug", .of slug), ("slinch", .of slinch), ("hyl", .of hyl),
   ("dyne", .of dyne), ("newton", .of newton), ("poundal", .of poundal),
   ("poundforce", .of poundforce), ("kilopond", .of kilopond), ("psi", .of psi),
   ("pascal", .of pascal), ("bar", .of bar), ("barye", .of barye),
   ("technicalatmosphere", .of technicalatmosphere), ("atmosphere", .of atmosphere),
   ("inchmercury", .of inchmercury), ("torr", .of torr), ("electronvolt", .of electronvolt),
   ("erg", .of erg), ("joule", .of joule), ("footpound", .of footpound), ("calorie", .of calorie),
   ("kilocalorie", .of kilocalorie), ("meancalorie", .of meancalorie),
   ("earthcalorie", .of earthcalorie), ("thermalunit", .of thermalunit),
   ("gasgallon", .of gasgallon), ("tontnt", .of tontnt), ("watt", .of watt),
   ("horsepower", .of horsepower), ("horsepowerwatt", .of horsepowerwatt),
   ("horsepowermetric", .of horsepowermetric), ("electricalhorsepower", .of electricalhorsepower),
   ("tonsrefrigeration", .of tonsrefrigeration), ("boilerhorsepower", .of boilerhorsepower),
   ("coulomb", .of coulomb), ("earthcoulomb", .of earthcoulomb), ("ampere", .of ampere),
   ("volt", .of volt), ("henry", .of henry), ("ohm", .of ohm), ("siemens", .of siemens),
   ("farad", .of farad), ("weber", .of weber), ("tesla", .of tesla), ("abcoulomb", .of abcoulomb),
   ("abampere", .of abampere), ("abvolt", .of abvolt), ("abhenry", .of abhenry),
   ("abohm", .of abohm), ("abmho", .of abmho), ("abfarad", .of abfarad), ("maxwell", .of maxwell),
   ("gauss", .of gauss), ("oersted", .of oersted), ("gilbert", .of gilbert),
   ("statcoulomb", .of statcoulomb), ("statampere", .of statampere), ("statvolt", .of statvolt),
   ("stathenry", .of stathenry), ("statohm", .of statohm), ("statmho", .of statmho),
   ("statfarad", .of statfarad), ("statweber", .of statweber), ("stattesla", .of stattesla),
   ("kelvin", .of kelvin), ("rankine", .of rankine), ("celsius", .of celsius),
   ("fahrenheit", .of fahrenheit), ("sealevel", .of sealevel), ("boiling", .of boiling),
   ("mole", .of mole), ("earthmole", .of earthmole), ("poundmole", .of poundmole),
   ("slugmole", .of slugmole), ("slinchmole", .of slinchmole), ("katal", .of katal),
   ("amagat", .of amagat), ("lumen", .of lumen), ("candela", .of candela), ("lux", .of lux),
   ("phot", .of phot), ("footcandle", .of footcandle), ("nit", .of nit), ("apostilb", .of apostilb),
   ("stilb", .of stilb), ("lambert", .of lambert), ("footlambert", .of footlambert),
   ("bril", .of bril), ("talbot", .of talbot), ("lumerg", .of lumerg), ("hertz", .of hertz),
   ("apm", .of apm), ("rpm", .of rpm), ("kayser", .of kayser), ("diopter", .of diopter),
   ("rayleigh", .of rayleigh), ("flick", .of flick), ("gforce", .of gforce),
   ("galileo", .of galileo), ("eotvos", .of eotvos), ("darcy", .of darcy), ("poise", .of poise),
   ("reyn", .of reyn), ("stokes", .of stokes), ("rayl", .of rayl), ("mpge", .of mpge),
   ("langley", .of langley), ("jansky", .of jansky), ("solarflux", .of solarflux),
   ("curie", .of curie), ("gray", .of gray), ("roentgen", .of roentgen),
   ("gaussgravitation", .of gaussgravitation)]

end Similitude.Units

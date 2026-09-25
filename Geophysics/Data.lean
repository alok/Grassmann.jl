import Geophysics.Atmosphere

/-!
# Planets, gases, atmosphere tables and standard weathers

The data of Geophysics.jl `src/planets.jl`: 13 reference bodies, 11 gases and
5 mixtures, 14 standard-atmosphere tables (US 1922–1976, Metric and English) and
the 14 standard weather columns integrated from them. The literals are Julia's,
including the arithmetic that forms them (`25.38*24*60^2` folds left) and the
negative-zero first layer bases.

Julia picks `Standard` at load time from the `STDATM`/`GEOUNITS` environment
variables (`planets.jl:143-164`); here `Standard` is the default (`Earth1959`)
and `standard` makes the choice explicit.
-/

namespace Geophysics

open StaticVectors UnitSystems FieldConstants

/-! ### Planets (`planets.jl:26-38`) -/

/-- The Sun. -/
def Sun : Planet := .of (.float 0.00005) (.float 696342e3) (.float (25.38 * 24.0 * 3600.0))
  (.float 1.32712440018e20)
/-- Mercury (a sphere: `f` is the integer `0`). -/
def Mercury : Planet := .of 0 (.float 2439.7e3) (.float (1407.5 * 3600.0)) (.float 2.2032e13)
/-- Venus (a sphere; retrograde rotation). -/
def Venus : Planet := .of 0 (.float 6051.8e3) (.float (-243.025 * 24.0 * 3600.0))
  (.float 3.24859e14)
/-- The Moon. -/
def Moon : Planet := .of (.float 0.0012) (.float 1738.1e3) (.float (27.321661 * 24.0 * 3600.0))
  (.float 4.9048695e12)
/-- Mars. -/
def Mars : Planet := .of (.float 0.00589) (.float 3396.2e3) (.float (1.025957 * 24.0 * 3600.0))
  (.float 4.282837e13)
/-- Jupiter. -/
def Jupiter : Planet := .of (.float 0.06487) (.float 71492e3) (.float (9.925 * 3600.0))
  (.float 1.26686534e17)
/-- Saturn (its period is the integer `38018`). -/
def Saturn : Planet := .of (.float 0.09796) (.float 60268e3) 38018 (.float 3.7931187e16)
/-- Uranus (retrograde rotation). -/
def Uranus : Planet := .of (.float 0.02293) (.float 25559e3) (.float (-0.71833 * 24.0 * 3600.0))
  (.float 5.793939e15)
/-- Neptune. -/
def Neptune : Planet := .of (.float 0.01708) (.float 24764e3) (.float (16.11 * 3600.0))
  (.float 6.836529e15)
/-- Pluto (a sphere). -/
def Pluto : Planet := .of 0 (.float 1188.3e3) (.float (6.38723 * 24.0 * 3600.0)) (.float 8.71e11)
/-- Ceres (a sphere). -/
def Ceres : Planet := .of 0 (.float 469.73e3) (.float (9.074170 * 3600.0)) (.float 6.26325e10)
/-- Eris (a sphere). -/
def Eris : Planet := .of 0 (.float 1163e3) (.float (349.44 * 3600.0)) (.float 1.108e12)

/-- All bodies with their Julia names, in `planets.jl` order. -/
def planets : List (String × Planet) :=
  [("Sun", Sun), ("Mercury", Mercury), ("Venus", Venus), ("Earth", Earth), ("Moon", Moon),
   ("Mars", Mars), ("Jupiter", Jupiter), ("Saturn", Saturn), ("Uranus", Uranus),
   ("Neptune", Neptune), ("Pluto", Pluto), ("Ceres", Ceres), ("Eris", Eris)]

/-! ### Gases (`planets.jl:45-83`); reference viscosity and conductivity at 288.16 K -/

/-- Julia's `NaN` Sutherland temperature (unknown). -/
def nanT : JNum := .float JMath.nan

/-- Nitrogen `N₂`. -/
def Nitrogen : MoleGas := DiatomicGas 28.013 2744e2 1.735e-5 107 25.11e-3 150
/-- Oxygen `O₂`. -/
def Oxygen : MoleGas := DiatomicGas 31.999 2061e2 1.999e-5 139 25.33e-3 240
/-- Argon `Ar`. -/
def Argon : MoleGas := AtomicGas 39.948 2.187e-5 144 17.23e-3 170
/-- Carbon dioxide `CO₂`. -/
def CarbonDioxide : MoleGas := TriatomicGas 44.01 2565e2 1480e2 14.45e-5 222 15.8e-3 1800
/-- Neon `Ne` (unknown Sutherland temperatures: its viscosity is `NaN`). -/
def Neon : MoleGas := AtomicGas 20.18 3.078e-5 nanT 48.29e-3 nanT
/-- Helium `He`. -/
def Helium : MoleGas := AtomicGas 4.003 2.928e-5 nanT 152.07e-3 nanT
/-- Methane `CH₄` (pentatomic: no heat capacity in Julia). -/
def Methane : MoleGas := PentatomicGas 16.042 10.74e-5 nanT 32.7e-3 nanT
/-- Krypton `Kr`. -/
def Krypton : MoleGas := AtomicGas 82.798 2.432e-5 nanT 9.12e-3 nanT
/-- Hydrogen `H₂`. -/
def Hydrogen : MoleGas := DiatomicGas 2.016 4342e2 0.866e-5 97 180.1e-3 120
/-- Xenon `Xe`. -/
def Xenon : MoleGas := AtomicGas 131.293 2.229e-5 nanT 5.27e-3 nanT

/-- `N2 ≡ N₂ ≡ Nitrogen` -/ abbrev N2 := Nitrogen
/-- `O2 ≡ O₂ ≡ Oxygen` -/ abbrev O2 := Oxygen
/-- `CO2 ≡ CO₂ ≡ CarbonDioxide` -/ abbrev CO2 := CarbonDioxide
/-- `CH4 ≡ CH₄ ≡ Methane` -/ abbrev CH4 := Methane
/-- `H2 ≡ H₂ ≡ Hydrogen` -/ abbrev H2 := Hydrogen
/-- `Ar ≡ Argon` -/ abbrev Ar := Argon
/-- `Ne ≡ Neon` -/ abbrev Ne := Neon
/-- `He ≡ Helium` -/ abbrev He := Helium
/-- `Kr ≡ Krypton` -/ abbrev Kr := Krypton
/-- `Xe ≡ Xenon` -/ abbrev Xe := Xenon

/-- The constant-`cᵥ` Sutherland air model (`planets.jl:62`; its heat capacities
recurse forever in Julia, see `Gas`). -/
def air : MoleGas := SutherlandGas 28.965923 720 1.7894e-5 110.4 0.02531 194 288.16

/-- `Nitrox = 0.7808093N₂ + 0.2094552O₂ + 0.009338Ar + 0.0003975CO₂`, Reed's dry air
(`planets.jl:68`). -/
def Nitrox : Mixture :=
  0.7808093 * N2 + 0.2094552 * O2 + 0.009338 * Ar + 0.0003975 * CO2

/-- `Air ≡ Nitrox`, the default fluid of every atmosphere (`planets.jl:66-74`). -/
def Air : Mixture := Nitrox

/-- `Traces = 0.726803Ne + 0.20966He + 0.04006Kr + 0.019824H₂ + 0.003653Xe`. -/
def Traces : Mixture :=
  0.726803 * Ne + 0.20966 * He + 0.04006 * Kr + 0.019824 * H2 + 0.003653 * Xe

/-- `MainGases` (not exported by Julia). -/
def MainGases : Mixture :=
  0.7808089 * N2 + 0.2094551 * O2 + 0.009338 * Ar + 0.0003976 * CO2 + 4.96e-7 * H2

/-- `TraceGases` (not exported by Julia). -/
def TraceGases : Mixture := 0.7415 * Ne + 0.2139 * He + 0.040871 * Kr + 0.003729 * Xe

/-- `AirMix`: nine constituents (its viscosity is `NaN` through the noble gases). -/
def AirMix : Mixture :=
  0.7807898 * N2 + 0.20945 * O2 + 0.0093378 * Ar + 0.00039738 * CO2 + 0.000018186 * Ne +
    0.0000052461 * He + 0.0000010024 * Kr + 0.00000049603 * H2 + 0.000000091399 * Xe

/-- All gases and mixtures with their Julia names. -/
def moles : List (String × Mole) :=
  [("N2", N2), ("O2", O2), ("Ar", Ar), ("CO2", CO2), ("H2", H2), ("He", He), ("Ne", Ne),
   ("Kr", Kr), ("Xe", Xe), ("CH4", CH4), ("air", air), ("Nitrox", Nitrox), ("AirMix", AirMix),
   ("Traces", Traces), ("MainGases", MainGases), ("TraceGases", TraceGases)]

/-! ### Atmosphere tables (`planets.jl:87-123`) -/

/-- US Standard Atmosphere 1922 (Metric). -/
def US22 : Atmosphere 2 := .make (vals [-6.5e-3, 0e-3]) (vals [-0e3, 11e3])
/-- US Standard Atmosphere 1925 (Metric). -/
def US25 : Atmosphere 2 := .make (vals [-6.5e-3, 0e-3]) (vals [-0e3, 10.76923e3])
/-- US Standard Atmosphere 1956 (Metric). -/
def US56 : Atmosphere 9 := .make
  (vals [-6.5e-3, 0e-3, 3e-3, 0e-3, -3.9e-3, 0e-3, 3.5e-3, 10e-3, 5.8e-3])
  (vals [-0e3, 11e3, 25e3, 47e3, 53e3, 75e3, 90e3, 126e3, 175e3])
/-- US Standard Atmosphere 1959, ARDC (Metric). -/
def US59 : Atmosphere 11 := .make
  (vals [-6.5e-3, 0e-3, 3e-3, 0e-3, -4.5e-3, 0e-3, 4e-3, 20e-3, 10e-3, 5e-3, 3.5e-3])
  (vals [-0e3, 11e3, 25e3, 47e3, 53e3, 79e3, 90e3, 105e3, 160e3, 170e3, 200e3])
/-- US Standard Atmosphere 1962 (Metric). -/
def US62 : Atmosphere 21 := .make
  (vals [-6.5e-3, 0.0, 1e-3, 2.8e-3, 0e3, -2e-3, -4e-3, 0.0, 3e-3, 5e-3, 10e-3, 20e-3, 15e-3,
    10e-3, 7e-3, 5e-3, 4e-3, 3.3e-3, 2.6e-3, 1.7e-3, 1.1e-3])
  (vals [-0e3, 11e3, 20e3, 32e3, 47e3, 52e3, 61e3, 79e3, 90e3, 100e3, 110e3, 120e3, 150e3,
    160e3, 170e3, 190e3, 230e3, 300e3, 400e3, 600e3, 700e3])
/-- US Standard Atmosphere 1966 (Metric). -/
def US66 : Atmosphere 9 := .make
  (vals [-6.5e-3, 0.0, 1e-3, 2.8e-3, 0e3, -2e-3, -3.9e-3, 0.0, 3e-3])
  (vals [-0e3, 11e3, 20.1e3, 32.2e3, 47.3e3, 52.4e3, 61.6e3, 80e3, 90e3])
/-- US Standard Atmosphere 1976 (Metric; `±Inf` mark the elliptic and exponential layers). -/
def US76 : Atmosphere 11 := .make
  (vals [-6.5e-3, 0.0, 1e-3, 2.8e-3, 0e3, -2.8e-3, -2e-3, 0.0, -JMath.inf, 12e-3, JMath.inf])
  (vals [-0e3, 11e3, 20e3, 32e3, 47e3, 51e3, 71e3, 86e3, 91e3, 110e3, 120e3])
/-- US Standard Atmosphere 1922 (English: °R/ft and ft). -/
def US22E : Atmosphere 2 := .make (vals [-3.5658e-3, 0e-3]) (vals [-0e3, 36.089e3]) Earth .English
/-- US Standard Atmosphere 1925 (English). -/
def US25E : Atmosphere 2 := .make (vals [-3.5658e-3, 0e-3]) (vals [-0e3, 35.332e3]) Earth .English
/-- US Standard Atmosphere 1956 (English). -/
def US56E : Atmosphere 9 := .make
  (vals [-3.5658e-3, 0.0, 1.64584e-3, 0.0, -2.1397e-3, 0.0, 1.92024e-3, 5.4864e-3, 3.1821e-3])
  (vals [-0.0, 36089.0, 82021.0, 154199.0, 173885.0, 246063.0, 295276.0, 413386.0, 574147.0])
  Earth .English
/-- US Standard Atmosphere 1959, ARDC (English). -/
def US59E : Atmosphere 11 := .make
  (vals [-3.5658e-3, 0.0, 1.64584e-3, 0.0, -2.46876e-3, 0.0, 2.19456e-3, 10.9728e-3, 5.4864e-3,
    2.7432e-3, 1.92024e-3])
  (vals [-0.0, 36089.0, 82021.0, 154199.0, 173885.0, 259176.0, 295276.0, 344488.0, 524934.0,
    557743.0, 656168.0])
  Earth .English
/-- US Standard Atmosphere 1962 (English). -/
def US62E : Atmosphere 9 := .make
  (vals [-3.5658e-3, 0.0, 0.54864e-3, 1.53612e-3, 0e3, -1.09728e-3, -2.1946e-3, 0.0, 1.6459e-3])
  (vals [-0.0, 36089.0, 65617.0, 104987.0, 154199.0, 170604.0, 200131.0, 259186.0, 295276.0])
  Earth .English
/-- US Standard Atmosphere 1966 (English). -/
def US66E : Atmosphere 9 := .make
  (vals [-3.5658e-3, 0.0, 0.54864e-3, 1.53612e-3, 0e3, -1.09728e-3, -2.1397e-3, 0.0, 1.6459e-3])
  (vals [-0.0, 36089.0, 65945.0, 105643.0, 155184.0, 171916.0, 202.1e3, 262467.0, 295276.0])
  Earth .English
/-- US Standard Atmosphere 1976 (English). -/
def US76E : Atmosphere 7 := .make
  (vals [-3.5658e-3, 0e3, 0.54864e-3, 1.53612e-3, 0e3, -1.53612e-3, -1.09728e-3])
  (vals [-0e3, 36.089e3, 65.617e3, 104.987e3, 154.199e3, 167.323e3, 232.940e3])
  Earth .English

/-- `ARDC ≡ US59` -/ abbrev ARDC := US59
/-- `ARDCE ≡ US59E` -/ abbrev ARDCE := US59E

/-- Julia's unused table of layer names (`planets.jl:130`). -/
def layers : List String :=
  ["Troposphere", "Tropopause", "Stratosphere", "Stratosphere", "Stratopause", "Mesosphere",
   "Mesosphere", "Mesopause"]

/-- Julia `(A::Atmosphere)(T, p = atm, ϕ = 1.0111032235724π/4)` (`Geophysics.jl:549`):
the weather of `A` from `Air` at sea-level temperature `T` and pressure `p` (in
`A`'s units). -/
def Atmosphere.weather {n : Nat} (A : Atmosphere n) (T : Float) (p : Float := 101325.0)
    (ϕ : Float := stdLatitude) : Weather n :=
  A.weatherOf Air T p ϕ

/-! ### Standard weathers (`planets.jl:135-141`) -/

/-- 1922 standard atmosphere. -/ def Earth1922 : Weather 2 := US22.weather 288.16
/-- 1925 standard atmosphere. -/ def Earth1925 : Weather 2 := US25.weather 288.16
/-- 1956 standard atmosphere. -/ def Earth1956 : Weather 9 := US56.weather 288.16
/-- 1959 standard atmosphere. -/ def Earth1959 : Weather 11 := US59.weather 288.16
/-- 1962 standard atmosphere. -/ def Earth1962 : Weather 21 := US62.weather 288.15
/-- 1966 standard atmosphere. -/ def Earth1966 : Weather 9 := US66.weather 288.15
/-- 1976 standard atmosphere (garbage above 91 km, as in Julia). -/
def Earth1976 : Weather 11 := US76.weather 288.15
/-- 1922 standard atmosphere, English units. -/
def Earth1922English : Weather 2 := US22E.weather 518.69 2116.2
/-- 1925 standard atmosphere, English units. -/
def Earth1925English : Weather 2 := US25E.weather 518.69 2116.2
/-- 1956 standard atmosphere, English units. -/
def Earth1956English : Weather 9 := US56E.weather 518.69 2116.2
/-- 1959 standard atmosphere, English units. -/
def Earth1959English : Weather 11 := US59E.weather 518.69 2116.2
/-- 1962 standard atmosphere, English units. -/
def Earth1962English : Weather 9 := US62E.weather 518.67 2116.2
/-- 1966 standard atmosphere, English units. -/
def Earth1966English : Weather 9 := US66E.weather 518.67 2116.2
/-- 1976 standard atmosphere, English units. -/
def Earth1976English : Weather 7 := US76E.weather 518.67 2116.2

/-- The default standard atmosphere, `Earth1959` (Julia `Standard` without
`STDATM`/`GEOUNITS`, `planets.jl:143-164`). -/
def Standard : Weather 11 := Earth1959

/-- A weather of any layer count. -/
abbrev AnyWeather := Σ n, Weather n

/-- All 14 standard weathers with their Julia names. -/
def weathers : List (String × AnyWeather) :=
  [("Earth1922", ⟨_, Earth1922⟩), ("Earth1925", ⟨_, Earth1925⟩), ("Earth1956", ⟨_, Earth1956⟩),
   ("Earth1959", ⟨_, Earth1959⟩), ("Earth1962", ⟨_, Earth1962⟩), ("Earth1966", ⟨_, Earth1966⟩),
   ("Earth1976", ⟨_, Earth1976⟩), ("Earth1922English", ⟨_, Earth1922English⟩),
   ("Earth1925English", ⟨_, Earth1925English⟩), ("Earth1956English", ⟨_, Earth1956English⟩),
   ("Earth1959English", ⟨_, Earth1959English⟩), ("Earth1962English", ⟨_, Earth1962English⟩),
   ("Earth1966English", ⟨_, Earth1966English⟩), ("Earth1976English", ⟨_, Earth1976English⟩)]

/-- Julia's load-time choice of `Standard` (`planets.jl:143-164`) as a function of
the `STDATM` year and `GEOUNITS == "english"`; an unknown year is an error, as in
Julia. -/
def standard (year : String := "1959") (english : Bool := false) : Except String AnyWeather :=
  let name := "Earth" ++ year ++ (if english then "English" else "")
  if ["1922", "1925", "1956", "1959", "1962", "1966", "1976"].contains year then
    match weathers.lookup name with
    | some w => .ok w
    | none => .error "unsupported STDATM environment"
  else .error "unsupported STDATM environment"

end Geophysics

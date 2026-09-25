import UnitSystems.Alg

/-!
# Couplings, unit systems and their constructors

A unit system is fixed by **eleven dimensional constants** plus a
dimensionless `Coupling` (`UnitSystems.jl:107-176`):

| slot | Julia | meaning | accessor |
|---|---|---|---|
| `kB` | `kB` | Boltzmann constant | `boltzmann` |
| `ħ` | `ħ` | reduced Planck constant | `planckreduced` |
| `c` | `𝘤` | speed of light | `lightspeed` |
| `μ₀` | `μ₀` | vacuum permeability | `vacuumpermeability` |
| `mₑ` | `mₑ` | electron mass | `electronmass` |
| `Mᵤ` | `Mᵤ` | molar-mass constant | `molarmass` |
| `Kcd` | `Kcd` | luminous efficacy | `luminousefficacy` |
| `θ` | `θ` | radian | `radian` |
| `lam` | `λ` | Gauss rationalization | `rationalization` |
| `αL` | `αL` | Lorentz constant | `lorentz` |
| `g₀` | `g₀` | gravity/force reference | `gravity` |

Julia keeps all of these in type parameters of `UnitSystem{kB,ħ,𝘤,μ₀,mₑ,Mᵤ,extra}`
and the extra slots `τ, 𝟐, 𝟑, 𝟓, 𝟕, 𝟏𝟏, 𝟏𝟗, 𝟒𝟑` never vary, so they are not stored
here (`two U` etc. are the literals). The constructors follow
`initdata.jl:37-84` and `UnitSystems.jl:205-274` operation by operation, so the
`JNum` instance reproduces Julia's floating-point values exactly.
-/

namespace UnitSystems

open FieldConstants UnitAlg

/-- Dimensionless constants of a universe (Julia `Coupling{αG,α,μₑᵤ,μₚᵤ,ΩΛ}`,
`UnitSystems.jl:107-116`). -/
structure Coupling (R : Type) where
  /-- gravitational coupling `αG = (mₑ/mP)²` -/
  αG : R
  /-- fine structure constant -/
  α : R
  /-- electron to atomic mass ratio -/
  μₑᵤ : R
  /-- proton to atomic mass ratio -/
  μₚᵤ : R
  /-- dark energy density -/
  ΩΛ : R
  deriving Inhabited

namespace Coupling
variable {α : Type} [UnitAlg α]
/-- `coupling(C)` -/
def coupling (C : Coupling α) : α := C.αG
/-- `finestructure(C)` -/
def finestructure (C : Coupling α) : α := C.α
/-- `electronunit(C)` -/
def electronunit (C : Coupling α) : α := C.μₑᵤ
/-- `protonunit(C)` -/
def protonunit (C : Coupling α) : α := C.μₚᵤ
/-- `protonelectron(C) = protonunit(C)/electronunit(C)` -/
def protonelectron (C : Coupling α) : α := C.μₚᵤ / C.μₑᵤ
/-- `darkenergydensity(C)` -/
def darkenergydensity (C : Coupling α) : α := C.ΩΛ
end Coupling

/-- A unit system: the eleven defining constants and the coupling
(Julia `UnitSystem{kB,ħ,𝘤,μ₀,mₑ,Mᵤ,(Kcd,θ,λ,αL,g₀,C,…)}`). -/
structure UnitSystem (α : Type) where
  /-- Boltzmann constant (entropy) -/
  kB : α
  /-- reduced Planck constant (angular momentum) -/
  ħ : α
  /-- speed of light -/
  c : α
  /-- vacuum permeability -/
  μ₀ : α
  /-- electron mass -/
  mₑ : α
  /-- molar mass constant -/
  Mᵤ : α
  /-- luminous efficacy -/
  Kcd : α
  /-- radian (angle unit) -/
  θ : α
  /-- Gauss rationalization `λ` -/
  lam : α
  /-- Lorentz constant -/
  αL : α
  /-- gravity/force reference -/
  g₀ : α
  /-- dimensionless coupling constants -/
  C : Coupling α
  deriving Inhabited

namespace UnitSystem

variable {α : Type} [UnitAlg α]

/-- Julia `===` of two systems: all eleven parameters identical. -/
def ident (U S : UnitSystem α) : Bool :=
  UnitAlg.ident U.kB S.kB && UnitAlg.ident U.ħ S.ħ && UnitAlg.ident U.c S.c &&
  UnitAlg.ident U.μ₀ S.μ₀ && UnitAlg.ident U.mₑ S.mₑ && UnitAlg.ident U.Mᵤ S.Mᵤ &&
  UnitAlg.ident U.Kcd S.Kcd && UnitAlg.ident U.θ S.θ && UnitAlg.ident U.lam S.lam &&
  UnitAlg.ident U.αL S.αL && UnitAlg.ident U.g₀ S.g₀

/-- Map a function over every slot (Julia `normal`, `constant`, measurement caches). -/
def map {β : Type} (f : α → β) (U : UnitSystem α) : UnitSystem β :=
  ⟨f U.kB, f U.ħ, f U.c, f U.μ₀, f U.mₑ, f U.Mᵤ, f U.Kcd, f U.θ, f U.lam, f U.αL, f U.g₀,
   ⟨f U.C.αG, f U.C.α, f U.C.μₑᵤ, f U.C.μₚᵤ, f U.C.ΩΛ⟩⟩

end UnitSystem

section accessors
variable {α : Type} [UnitAlg α]

/-- `boltzmann(U)` -/
@[inline] def boltzmann (U : UnitSystem α) : α := U.kB
/-- `planckreduced(U)` -/
@[inline] def planckreduced (U : UnitSystem α) : α := U.ħ
/-- `lightspeed(U)` -/
@[inline] def lightspeed (U : UnitSystem α) : α := U.c
/-- `vacuumpermeability(U)` -/
@[inline] def vacuumpermeability (U : UnitSystem α) : α := U.μ₀
/-- `permeability(U) = vacuumpermeability(U)` -/
@[inline] def permeability (U : UnitSystem α) : α := U.μ₀
/-- `electronmass(U)` -/
@[inline] def electronmass (U : UnitSystem α) : α := U.mₑ
/-- `molarmass(U)` -/
@[inline] def molarmass (U : UnitSystem α) : α := U.Mᵤ
/-- `luminousefficacy(U)` -/
@[inline] def luminousefficacy (U : UnitSystem α) : α := U.Kcd
/-- `radian(U)` (`angle(U)`) -/
@[inline] def radian (U : UnitSystem α) : α := U.θ
/-- `rationalization(U)` -/
@[inline] def rationalization (U : UnitSystem α) : α := U.lam
/-- `lorentz(U)` -/
@[inline] def lorentz (U : UnitSystem α) : α := U.αL
/-- `gravity(U)` -/
@[inline] def gravity (U : UnitSystem α) : α := U.g₀
/-- Julia `universe(U)` -/
@[inline] def universeOf (U : UnitSystem α) : Coupling α := U.C
/-- `tau(U) = τ` -/
@[inline] def tau (_ : UnitSystem α) : α := UnitAlg.tau
/-- `two(U) = 𝟐` -/
@[inline] def two (_ : UnitSystem α) : α := ilit 2
/-- `three(U) = 𝟑` -/
@[inline] def three (_ : UnitSystem α) : α := ilit 3
/-- `five(U) = 𝟓` -/
@[inline] def five (_ : UnitSystem α) : α := ilit 5
/-- `seven(U) = 𝟕` -/
@[inline] def seven (_ : UnitSystem α) : α := ilit 7
/-- `eleven(U) = 𝟏𝟏` -/
@[inline] def eleven (_ : UnitSystem α) : α := ilit 11
/-- `nineteen(U) = 𝟏𝟗` -/
@[inline] def nineteen (_ : UnitSystem α) : α := ilit 19
/-- `fourtythree(U) = 𝟒𝟑` -/
@[inline] def fourtythree (_ : UnitSystem α) : α := ilit 43

/-- `one(U) = unit(two(U)/two(U))`: the integer `1` (`UnitSystems.jl:277`). -/
def oneU (U : UnitSystem α) : α := unit (two U / two U)
/-- `zero(U) = one(U) - one(U)` (`UnitSystems.jl:278`). -/
def zeroU (U : UnitSystem α) : α := oneU U - oneU U
/-- `turn(U) = tau(U)*radian(U)` (`UnitSystems.jl:280`). -/
def turn (U : UnitSystem α) : α := tau U * radian U
/-- `spat(U) = two(U)*turn(U)*radian(U)` (`UnitSystems.jl:283`). -/
def spat (U : UnitSystem α) : α := two U * turn U * radian U
/-- `isrationalized(U) = rationalization(U) ≠ spat(U)` (`UnitSystems.jl:179`). -/
def isrationalized (U : UnitSystem α) : Bool := !(rationalization U == spat U)

/-- The dimensionless couplings of a system (`UnitSystems.jl:291-293`). -/
def coupling (U : UnitSystem α) : α := U.C.coupling
/-- `finestructure(U)` -/
def finestructure (U : UnitSystem α) : α := U.C.finestructure
/-- `electronunit(U)` -/
def electronunit (U : UnitSystem α) : α := U.C.electronunit
/-- `protonunit(U)` -/
def protonunit (U : UnitSystem α) : α := U.C.protonunit
/-- `protonelectron(U)` -/
def protonelectron (U : UnitSystem α) : α := U.C.protonelectron
/-- `darkenergydensity(U)` -/
def darkenergydensity (U : UnitSystem α) : α := U.C.darkenergydensity

end accessors

/-! ### Constructors (`initdata.jl:37-84`, `UnitSystems.jl:205-274`) -/

section constructors
variable {α : Type} [UnitAlg α]

/-- Julia `unitsystem(kB,ħ,𝘤,μ₀,mₑ,Mᵤ=𝟏,Kcd=𝟏,θ=𝟏,λ=𝟏,αL=𝟏,g=𝟏,C=Universe)`. -/
def unitsystem (C : Coupling α) (kB ħ c μ₀ mₑ : α) (Mᵤ Kcd θ lam αL g₀ : α := one) : UnitSystem α :=
  ⟨kB, ħ, c, μ₀, mₑ, Mᵤ, Kcd, θ, lam, αL, g₀, C⟩

/-- Julia `EntropySystem(u,t,l,m,θ,μ0,Mu=molarmass(u)/m,g0=gravity(u),
e=m*l*l/(t*t),λ=one(u),αL=one(u),Kcd=luminousefficacy(u)*e/t*g0)`
(`UnitSystems.jl:254-264`): rescale time, length, mass and temperature units. -/
def EntropySystem' (u : UnitSystem α) (t l m θT μ0 : α) (Mu : Option α := none)
    (g0 : Option α := none) (e : Option α := none) (lam αL : Option α := none)
    (Kcd : Option α := none) : UnitSystem α :=
  let Mu := Mu.getD (molarmass u / m)
  let g0 := g0.getD (gravity u)
  let e := e.getD (m * l * l / (t * t))
  let lam := lam.getD (oneU u)
  let αL := αL.getD (oneU u)
  let Kcd := Kcd.getD (luminousefficacy u * e / t * g0)
  ⟨boltzmann u * θT / e / g0, planckreduced u / t / e / g0, lightspeed u * t / l, μ0,
   electronmass u / m, Mu, Kcd, radian u, lam, αL, g0, universeOf u⟩

/-- Julia `EntropySystem(u,t,l,m,θ=one(u))` (`UnitSystems.jl:251-253`). -/
def EntropySystem (u : UnitSystem α) (t l m : α) (θT : Option α := none) : UnitSystem α :=
  let θT := θT.getD (oneU u)
  EntropySystem' u t l m θT (permeability u / (m * l)) (some (molarmass u / m))
    (some (gravity u)) (some (m * l * l / (t * t)))

/-- Julia `AstronomicalSystem(u,t,l,m,e=m*lightspeed(u)^2)` (`UnitSystems.jl:272-274`). -/
def AstronomicalSystem (u : UnitSystem α) (t l m : α) : UnitSystem α :=
  let e := m * lightspeed u ^ (2 : Int)
  EntropySystem' u t l m (e / boltzmann u) (spat u) (some (oneU u)) (some (oneU u)) (some e)
    (some (oneU u)) (some (oneU u)) (some (oneU u))

/-- Julia `ElectricSystem(u,Ω,V)` (`UnitSystems.jl:228`): mass rescaled by `V²/Ω`. -/
def ElectricSystem (u : UnitSystem α) (Ω V : α) : UnitSystem α :=
  EntropySystem' u (oneU u) (oneU u) (V * V / Ω) (oneU u) (vacuumpermeability u / Ω)

/-- Julia `GaussSystem(u,μ0,λ,αL=one(u),l=inv((two(u)*five(u))^2),m=inv((two(u)*five(u))^3),
g0=gravity(u))` (`UnitSystems.jl:237-239`). -/
def GaussSystem (u : UnitSystem α) (μ0 lam : α) (αL : Option α := none) : UnitSystem α :=
  let αL := αL.getD (oneU u)
  let l := UnitAlg.inv ((two u * five u) ^ (2 : Int))
  let m := UnitAlg.inv ((two u * five u) ^ (3 : Int))
  let g0 := gravity u
  let Mu := if UnitAlg.eqFloat m (1.0 / 1000.0) then oneU u else molarmass u / m
  EntropySystem' u (oneU u) l m (oneU u) μ0 (some Mu) (some g0) (some (m * (l * l)))
    (some lam) (some αL)

end constructors

/-! ### Defined constants (`initdata.jl:15-35`) -/

section initdata
variable (α : Type) [UnitAlg α]

/-- `𝟐` etc.: integer generators. -/
@[inline] def c2 : α := ilit 2
/-- `𝟑` -/ @[inline] def c3 : α := ilit 3
/-- `𝟓` -/ @[inline] def c5 : α := ilit 5
/-- `𝟕` -/ @[inline] def c7 : α := ilit 7
/-- `𝟏𝟏` -/ @[inline] def c11 : α := ilit 11
/-- `𝟏𝟗` -/ @[inline] def c19 : α := ilit 19
/-- `𝟒𝟑` -/ @[inline] def c43 : α := ilit 43
/-- a measured constant -/ @[inline] def ms (m : Measured) : α := UnitAlg.measured m

/-- `deka = 𝟐*𝟓` -/ def deka : α := c2 α * c5 α
/-- `byte = 𝟐^3` -/ def byte : α := c2 α ^ (3 : Int)
/-- `sixty = 𝟐^2*𝟑*𝟓` -/ def sixty : α := c2 α ^ (2 : Int) * c3 α * c5 α
/-- `hecto = deka^2` -/ def hecto : α := deka α ^ (2 : Int)
/-- `kilo = deka^3` -/ def kilo : α := deka α ^ (3 : Int)
/-- `mega = kilo^2` -/ def mega : α := kilo α ^ (2 : Int)
/-- `giga = kilo^3` -/ def giga : α := kilo α ^ (3 : Int)
/-- `tera = kilo^4` -/ def tera : α := kilo α ^ (4 : Int)
/-- `peta = kilo^5` -/ def peta : α := kilo α ^ (5 : Int)
/-- `exa = kilo^6` -/ def exa : α := kilo α ^ (6 : Int)
/-- `deci = inv(deka)` -/ def deci : α := UnitAlg.inv (deka α)
/-- `centi = inv(hecto)` -/ def centi : α := UnitAlg.inv (hecto α)
/-- `milli = inv(kilo)` -/ def milli : α := UnitAlg.inv (kilo α)
/-- `micro = inv(mega)` -/ def micro : α := UnitAlg.inv (mega α)
/-- `nano = inv(giga)` -/ def nano : α := UnitAlg.inv (giga α)
/-- `pico = inv(tera)` -/ def pico : α := UnitAlg.inv (tera α)
/-- `femto = inv(peta)` -/ def femto : α := UnitAlg.inv (peta α)
/-- `atto = inv(exa)` -/ def atto : α := UnitAlg.inv (exa α)
/-- `kibi = 𝟐^10` -/ def kibi : α := c2 α ^ (10 : Int)
/-- `mebi = 𝟐^20` -/ def mebi : α := c2 α ^ (20 : Int)
/-- `gibi = 𝟐^30` -/ def gibi : α := c2 α ^ (30 : Int)
/-- `tebi = 𝟐^40` -/ def tebi : α := c2 α ^ (40 : Int)
/-- `pebi = 𝟐^50` -/ def pebi : α := c2 α ^ (50 : Int)
/-- `exbi = 𝟐^60` -/ def exbi : α := c2 α ^ (60 : Int)
/-- `zebi = (Constant(1.0)*𝟐)^70` -/ def zebi : α := (flit 1.0 * c2 α) ^ (70 : Int)
/-- `yobi = (Constant(1.0)*𝟐)^80` -/ def yobi : α := (flit 1.0 * c2 α) ^ (80 : Int)

/-- furlong `fur = 𝟔𝟎*𝟏𝟏*ft` -/ def fur : α := sixty α * c11 α * ms α .ft
/-- degree Rankine `°R = 𝟓/𝟑^2` (K per °R) -/ def degR : α := c5 α / c3 α ^ (2 : Int)
/-- `K = 𝟑^2/𝟓` (°R per K) -/ def degK : α := c3 α ^ (2 : Int) / c5 α
/-- `HOUR = 𝟔𝟎^2` -/ def HOUR : α := sixty α ^ (2 : Int)
/-- Gaussian constant `k = kG*τ/(𝟐^7*𝟑^4*𝟓^3)` (rad/day) -/
def kGauss : α := ms α .kG * UnitAlg.tau / (c2 α ^ (7 : Int) * c3 α ^ (4 : Int) * c5 α ^ (3 : Int))
/-- electron mass `mₑ = αinv^2*R∞*𝟐*𝘩/𝘤` -/
def mₑ : α := ms α .αinv ^ (2 : Int) * ms α .Rinf * c2 α * ms α .hh / ms α .cc
/-- SI2019 permeability `μ₀ = 𝟐*𝘩/𝘤*α/𝘦^2` -/
def μ₀ : α := c2 α * ms α .hh / ms α .cc * ms α .α / ms α .ee ^ (2 : Int)
/-- `ħ = 𝘩/τ` -/ def ħ : α := ms α .hh / UnitAlg.tau
/-- `μₚₑ = μₚᵤ/μₑᵤ` -/ def μₚₑ : α := ms α .μₚᵤ / ms α .μₑᵤ
/-- `μₑₚ = μₑᵤ/μₚᵤ` -/ def μₑₚ : α := ms α .μₑᵤ / ms α .μₚᵤ
/-- molar gas constant `Rᵤ = NA*kB` -/ def Rᵤ : α := ms α .NA * ms α .kB
/-- Gaussian Lorentz constant `αL = centi/𝘤` -/ def αL : α := centi α / ms α .cc
/-- gravitational coupling `αG = (mₑ/mP)^2` -/ def αG : α := (mₑ α / ms α .mP) ^ (2 : Int)
/-- molar mass constant `Mᵤ = NA*mₑ/μₑᵤ` -/ def Mᵤ : α := ms α .NA * mₑ α / ms α .μₑᵤ
/-- parsec `pc = au*𝟐^7*𝟑^4*𝟓^3/τ` -/
def pc : α := ms α .au * c2 α ^ (7 : Int) * c3 α ^ (4 : Int) * c5 α ^ (3 : Int) / UnitAlg.tau
/-- Newton constant `G = 𝘤*ħ/mP^2` -/ def G : α := ms α .cc * ħ α / ms α .mP ^ (2 : Int)
/-- `DAY = 𝟐^7*𝟑^3*𝟓^2` -/ def DAY : α := c2 α ^ (7 : Int) * c3 α ^ (3 : Int) * c5 α ^ (2 : Int)
/-- nautical mile `nm = sqrt(GME/g₀)*τ/𝟐^5/𝟑^3/𝟓^2` -/
def nm : α := UnitAlg.sqrt (ms α .GME / ms α .g₀) * UnitAlg.tau / c2 α ^ (5 : Int) / c3 α ^ (3 : Int) / c5 α ^ (2 : Int)
/-- solar mass parameter `GM☉ = au^3*k^2/DAY^2` -/
def GMsun : α := ms α .au ^ (3 : Int) * kGauss α ^ (2 : Int) / DAY α ^ (2 : Int)
/-- Hubble time `th = 𝟏𝟎^3*pc/H0` -/ def th : α := deka α ^ (3 : Int) * pc α / ms α .H0
/-- cosmological constant `ΛC = 𝟑*ΩΛ*(th*𝘤)^-2` -/
def ΛC : α := c3 α * ms α .ΩΛ * (th α * ms α .cc) ^ (-2 : Int)
/-- cosmological length `lc = 𝟐*sqrt(τ/ΛC)` -/ def lc : α := c2 α * UnitAlg.sqrt (UnitAlg.tau / ΛC α)
/-- cosmological mass `mc = 𝘤^2/(𝟐*G*sqrt(τ*ΛC))` -/
def mc : α := ms α .cc ^ (2 : Int) / (c2 α * G α * UnitAlg.sqrt (UnitAlg.tau * ΛC α))
/-- vacuum energy density `ρΛ = ΛC*𝘤^4/(𝟐^2*τ)/G` -/
def ρΛ : α := ΛC α * ms α .cc ^ (4 : Int) / (c2 α ^ (2 : Int) * UnitAlg.tau) / G α
/-- natural charge `𝘦ₙ = 𝘦/√α` -/ def eₙ : α := ms α .ee / UnitAlg.sqrt (ms α .α)
/-- spatian `ς = √(𝟐*τ)` -/ def ς : α := UnitAlg.sqrt (c2 α * UnitAlg.tau)
/-- `lcq = sqrt(sqrt(𝘤*ħ/ρΛ))` -/
def lcq : α := UnitAlg.sqrt (UnitAlg.sqrt (ms α .cc * ħ α / ρΛ α))
/-- `mcq = sqrt(sqrt(ρΛ*ħ^3/𝘤^5))` -/
def mcq : α := UnitAlg.sqrt (UnitAlg.sqrt (ρΛ α * ħ α ^ (3 : Int) / ms α .cc ^ (5 : Int)))
/-- rationalized natural charge `𝘦ᵣ = 𝘦ₙ/ς` -/ def eᵣ : α := eₙ α / ς α
/-- `tcq = lcq*sqrt(mcq/sqrt(sqrt(ρΛ*(𝘤*ħ)^3)))` -/
def tcq : α := lcq α * UnitAlg.sqrt (mcq α / UnitAlg.sqrt (UnitAlg.sqrt (ρΛ α * (ms α .cc * ħ α) ^ (3 : Int))))
/-- Earth meter `em = sqrt(GME/g₀)*τ/𝟐^9/𝟓^7` -/
def em : α := UnitAlg.sqrt (ms α .GME / ms α .g₀) * UnitAlg.tau / c2 α ^ (9 : Int) / c5 α ^ (7 : Int)
/-- statute mile in feet `mi = 𝟐^5*𝟑*𝟓*𝟏𝟏` -/ def mi : α := c2 α ^ (5 : Int) * c3 α * c5 α * c11 α

/-- `Universe = Coupling(αG, α, μₑᵤ, μₚᵤ, ΩΛ)` (`initdata.jl:35`). -/
def Universe : Coupling α := ⟨αG α, ms α .α, ms α .μₑᵤ, ms α .μₚᵤ, ms α .ΩΛ⟩

/-- Julia `MetricSystem(Mu=Mᵤ,μ0=μ₀,Ru=Rᵤ,g0=𝟏,θ=𝟏,h=𝘩,me=αinv^2*R∞*𝟐*h/𝘤)` (`initdata.jl:62`). -/
def MetricSystem (Mu : α := Mᵤ α) (μ0 : α := μ₀ α) (Ru : α := Rᵤ α) (g0 : α := one)
    (θ : α := one) (h : α := ms α .hh)
    (me : α := ms α .αinv ^ (2 : Int) * ms α .Rinf * c2 α * h / ms α .cc) : UnitSystem α :=
  unitsystem (Universe α) (Ru * me / Mu / ms α .μₑᵤ / g0) (h / UnitAlg.tau / g0 / θ) (ms α .cc) μ0 me
    Mu (ms α .Kcd * (mₑ α / me) ^ (2 : Int) * (h / ms α .hh) * g0) θ one one g0

/-- Julia `ConventionalSystem(klitz,joseph,Ru=Rᵤ,g0=𝟏,θ=𝟏) =
MetricSystem(milli,𝟐*klitz/𝘤*α,Ru,g0,θ,(𝟐*𝟐)/klitz/(joseph*joseph))` (`initdata.jl:71`). -/
def ConventionalSystem (klitz joseph : α) (Ru : α := Rᵤ α) (g0 : α := one) (θ : α := one) : UnitSystem α :=
  MetricSystem α (milli α) (c2 α * klitz / ms α .cc * ms α .α) Ru g0 θ ((c2 α * c2 α) / klitz / (joseph * joseph))

/-- Julia `RankineSystem(u,l,m,g0=𝟏)` (`initdata.jl:84`): the English-family
constructor (temperature in °R, molar mass snapped to the pound-mole). -/
def RankineSystem (u : UnitSystem α) (l m : α) (g0 : α := one) : UnitSystem α :=
  EntropySystem' u one l m (degR α) (vacuumpermeability u / (m * l) / g0)
    (some (unit (kilo α * molarmass u))) (some g0)

end initdata

end UnitSystems

import Similitude.Quantity
import Geophysics.Atmosphere

/-!
# Typed quantities

The `Float` API mirrors Julia: values in a unit system chosen by a runtime `Sys`.
This module adds, at no runtime cost, a typed layer on Similitude's
`Quantity U d Float` (the unit system `U` and the USQ dimension `d` live in the
type; a single-field structure is its field at runtime):

* inputs carry their system and dimension, so an English altitude cannot be
  passed where a Metric one is expected, nor a temperature where a length is;
* every result's dimension is **derived from Julia's formula**, not from the name
  of the quantity. Reed's Unified System of Quantities keeps force `F`
  independent of `M L T⁻²` (they are related by `g₀`), so where Geophysics.jl
  omits a `g₀` factor the typed result says so. For example `kinematic` is
  `viscosity/density`, whose dimension `F·T·L/M` is `diffusivity` in Metric
  (`g₀ = 1`) but not in English: `Quantity.recast` to `Dim.diffusivity` is
  accepted in Metric and rejected by the kernel in English (see
  `kinematic_metric`, `kinematic_english`);
* Julia's `gravitycomponents` adds a gravity (`F/M`) to a centripetal
  acceleration (`L/T²`), which is only consistent where `g₀ = 1`, so it has no
  typed form.

Conversions between systems of typed values use Similitude's exact ratios
(`Quantity.to`); the Julia-faithful cross-unit evaluation of Geophysics goes
through `Weather.column U` instead.
-/

namespace Geophysics

open UnitSystems Similitude StaticVectors

/-- A `Float` quantity of USQ dimension `d` in unit system `U` (erased to its value). -/
abbrev Qty (U : Sys) (d : Dim) := Similitude.Quantity U d Float

/-- The dimension of a standard gravitational parameter `GM` (Julia `F/M*L^2`,
`Geophysics.jl:75`). -/
abbrev Dim.gravitation : Dim := USQ.F / USQ.M * USQ.L ^ 2

/-! ### Dimensions of Julia's formulas -/

/-- `density*gravity(h)` is a specific weight. -/
theorem specificweight_dim : Dim.density * Dim.specificforce = Dim.specificweight := by decide
/-- `inv(density)` is a specific volume. -/
theorem specificvolume_dim : Dim.density⁻¹ = Dim.specificvolume := by decide
/-- `heatvolume*T` is a specific energy. -/
theorem specificenergy_dim : Dim.specificentropy * Dim.temperature = Dim.specificenergy := by decide
/-- `gravity(h)*h` is a specific energy. -/
theorem geopotential_dim : Dim.specificforce * Dim.length = Dim.specificenergy := by decide
/-- `k/cₚ/ρ` is a diffusivity in every system. -/
theorem thermaldiffusivity_dim :
    Dim.thermalconductivity / Dim.specificentropy / Dim.density = Dim.diffusivity := by decide
/-- `sqrt((R*g₀*γ)*T)` is a speed: `R*g₀*T` is a squared speed. -/
theorem sonicspeed_dim :
    Dim.specificentropy * Dim.gravityforce * Dim.temperature = Dim.speed ^ 2 := by decide
/-- `g₀*μ*cₚ/k` is dimensionless. -/
theorem prandtl_dim : Dim.gravityforce * Dim.viscosity * Dim.specificentropy /
    Dim.thermalconductivity = Dim.dimensionless := by decide
/-- `viscosity/density` is *not* a USQ diffusivity (it lacks `g₀`). -/
theorem kinematic_dim : Dim.viscosity / Dim.density ≠ Dim.diffusivity := by decide
/-- `density*sonicspeed` is not the USQ `specificimpedance` (`F·T/L³`). -/
theorem specificimpedance_dim : Dim.density * Dim.speed ≠ Dim.specificimpedance := by decide
/-- `pressure²/density/sonicspeed` is not an irradiance (it lacks `g₀`). -/
theorem intensity_dim : Dim.pressure ^ 2 / Dim.density / Dim.speed ≠ Dim.irradiance := by decide

/-- In Metric (`g₀ = 1`) `viscosity/density` and `diffusivity` have the same image. -/
theorem kinematic_metric :
    Sys.Metric.hom.halfDim (Dim.viscosity / Dim.density) = Sys.Metric.hom.halfDim Dim.diffusivity := by
  decide
/-- In English (`g₀ ≠ 1`) they differ: Julia's English `kinematic` is not in ft²/s. -/
theorem kinematic_english :
    Sys.English.hom.halfDim (Dim.viscosity / Dim.density) ≠
      Sys.English.hom.halfDim Dim.diffusivity := by
  decide

/-! ### Planets -/

namespace Planet

variable (P : Planet) (U : Sys)

/-- Typed `semimajor(P, U)`. -/
def semimajorQ : Qty U Dim.length := ⟨P.semimajor U⟩
/-- Typed `semiminor(P, U)`. -/
def semiminorQ : Qty U Dim.length := ⟨P.semiminor U⟩
/-- Typed `meanradius(P, U)`. -/
def meanradiusQ : Qty U Dim.length := ⟨P.meanradius U⟩
/-- Typed `authalicradius(P, U)`. -/
def authalicradiusQ : Qty U Dim.length := ⟨P.authalicradius U⟩
/-- Typed `lineareccentricity(P, U)`. -/
def lineareccentricityQ : Qty U Dim.length := ⟨P.lineareccentricity U⟩
/-- Typed `period(P, U)`. -/
def periodQ : Qty U Dim.time := ⟨P.period U⟩
/-- Typed `frequency(P, U) = 1/period`. -/
def frequencyQ : Qty U Dim.frequency := ⟨P.frequency U⟩
/-- Typed `angularfrequency(P, U) = 2π/period` (the `2π` is a plain number). -/
def angularfrequencyQ : Qty U Dim.frequency := ⟨P.angularfrequency U⟩
/-- Typed `gravitation(P, U)`, dimension `F/M·L²`. -/
def gravitationQ : Qty U Dim.gravitation := ⟨P.gravitation U⟩
/-- Typed `mass(P, U) = gravitation(P, U)/G`. -/
def massQ : Qty U Dim.mass := ⟨P.mass U⟩
/-- Typed `radius(θ, P, U)` at a geocentric latitude. -/
def radiusQ (θ : Float) : Qty U Dim.length := ⟨P.radius θ U⟩
/-- Typed `radiusgeodetic(ϕ, P, U)` at a geodetic latitude. -/
def radiusgeodeticQ (ϕ : Float) : Qty U Dim.length := ⟨P.radiusgeodetic ϕ U⟩
/-- Typed `speed(θ, P, U)`. -/
def speedQ (θ : Float) : Qty U Dim.speed := ⟨P.speed θ U⟩
/-- Typed `centripetal(θ, P, U)`: a kinematic acceleration `L/T²`. -/
def centripetalQ (θ : Float) : Qty U Dim.acceleration := ⟨P.centripetal θ U⟩
/-- Typed `gravity(P, U) = GM/a²`: force per mass `F/M`. -/
def gravitySphericalQ : Qty U Dim.specificforce := ⟨P.gravitySpherical U⟩
/-- Typed Somigliana `gravity(ϕ, P, U)`. -/
def gravityQ (ϕ : Float) : Qty U Dim.specificforce := ⟨P.gravity ϕ U⟩
/-- Typed Hirvonen `_gravity(ϕ, P, U)`. -/
def gravityNormalQ (ϕ : Float) : Qty U Dim.specificforce := ⟨P.gravityNormal ϕ U⟩
/-- Typed `gravitygeodetic(h, ϕ, P, U)`. -/
def gravitygeodeticQ (h : Qty U Dim.length) (ϕ : Float) : Qty U Dim.specificforce :=
  ⟨P.gravitygeodetic h.val ϕ U⟩
/-- Typed `deflection(h, ϕ, P, U)` (an angle, as a plain number). -/
def deflectionQ (h : Qty U Dim.length) (ϕ : Float) : Float := P.deflection h.val ϕ U

end Planet

/-! ### Gases and fluid states -/

namespace Mole

variable (G : Mole) (U : Sys)

/-- Typed `molarmass(G, U)`. -/
def molarmassQ : Qty U Dim.molarmass := ⟨G.molarmass U⟩
/-- Typed `gasconstant(G, U)`. -/
def gasconstantQ : Qty U Dim.specificentropy := ⟨G.gasconstant U⟩
/-- Typed `viscosity(T, G, U)`. -/
def viscosityQ (T : Qty U Dim.temperature) : Qty U Dim.viscosity := ⟨G.viscosity T.val U⟩
/-- Typed `thermalconductivity(T, G, U)`. -/
def thermalconductivityQ (T : Qty U Dim.temperature) : Qty U Dim.thermalconductivity :=
  ⟨G.thermalconductivity T.val U⟩
/-- Typed `heatvolume(T, G, U)`. -/
def heatvolumeQ (T : Qty U Dim.temperature) : Qty U Dim.specificentropy := ⟨G.heatvolume T.val U⟩
/-- Typed `heatpressure(T, G, U)`. -/
def heatpressureQ (T : Qty U Dim.temperature) : Qty U Dim.specificentropy :=
  ⟨G.heatpressure T.val U⟩
/-- Typed `heatratio(T, G, U)`. -/
def heatratioQ (T : Qty U Dim.temperature) : Qty U Dim.dimensionless := ⟨G.heatratio T.val U⟩
/-- Typed `specificenergy(T, G, U) = heatvolume*T`. -/
def specificenergyQ (T : Qty U Dim.temperature) : Qty U Dim.specificenergy :=
  ⟨G.specificenergy T.val U⟩
/-- Typed `specificenthalpy(T, G, U) = heatpressure*T`. -/
def specificenthalpyQ (T : Qty U Dim.temperature) : Qty U Dim.specificenergy :=
  ⟨G.specificenthalpy T.val U⟩
/-- Typed `freedom(T, G, U)`. -/
def freedomQ (T : Qty U Dim.temperature) : Qty U Dim.dimensionless := ⟨G.freedom T.val U⟩
/-- Typed `prandtl(T, G, U)`. -/
def prandtlQ (T : Qty U Dim.temperature) : Qty U Dim.dimensionless := ⟨G.prandtl T.val U⟩
/-- Typed `sonicspeed(T, G, U)`. -/
def sonicspeedQ (T : Qty U Dim.temperature) : Qty U Dim.speed := ⟨G.sonicspeed T.val U⟩
/-- Typed `G(T, P, U)`: a fluid state from typed temperature and pressure. -/
def stateQ (T : Qty U Dim.temperature) (P : Qty U Dim.pressure) : FluidState :=
  G.state T.val P.val U

end Mole

namespace FluidState

variable (F : FluidState) (U : Sys)

/-- Typed `temperature(F, U)`. -/
def temperatureQ : Qty U Dim.temperature := ⟨F.temperature U⟩
/-- Typed `pressure(F, U)`. -/
def pressureQ : Qty U Dim.pressure := ⟨F.pressure U⟩
/-- Typed `density(F, U)`. -/
def densityQ : Qty U Dim.density := ⟨F.density U⟩
/-- Typed `kinematic(F, U) = viscosity/density`. -/
def kinematicQ : Qty U (Dim.viscosity / Dim.density) := ⟨F.kinematic U⟩
/-- Typed `sonicspeed(F, U)`. -/
def sonicspeedQ : Qty U Dim.speed := ⟨F.sonicspeed U⟩

end FluidState

/-! ### Weather columns -/

/-- A weather column evaluated in the unit system `U`, with typed inputs and
results: the `Column` built for `U`, whose system is now in the type. -/
structure TypedColumn (U : Sys) (n : Nat) where
  /-- the evaluation column (built for `U`) -/
  col : Column n

/-- The typed column of `W` in `U` (Julia's evaluation `op(h, W, U)`). -/
def Weather.typed {n : Nat} (W : Weather n) (U : Sys) : TypedColumn U n := ⟨W.column U⟩

namespace TypedColumn

variable {U : Sys} {n : Nat} (C : TypedColumn U n) (h : Qty U Dim.length)

/-- Typed `altgeopotent(h, W, U)`: geopotential altitude. -/
def altgeopotent : Qty U Dim.length := ⟨C.col.altgeopotent h.val⟩
/-- Typed `gravity(h, W, U)`. -/
def gravity : Qty U Dim.specificforce := ⟨C.col.gravity h.val⟩
/-- Typed `geopotential(h, W, U) = gravity*h`. -/
def geopotential : Qty U (Dim.specificforce * Dim.length) := ⟨C.col.geopotential h.val⟩
/-- Typed `temperature(h, W, U)`. -/
def temperature : Qty U Dim.temperature := ⟨C.col.eval .temperature h.val⟩
/-- Typed `pressure(h, W, U)`. -/
def pressure : Qty U Dim.pressure := ⟨C.col.eval .pressure h.val⟩
/-- Typed `density(h, W, U)`. -/
def density : Qty U Dim.density := ⟨C.col.eval .density h.val⟩
/-- Typed `specificweight(h, W, U) = density*gravity`. -/
def specificweight : Qty U (Dim.density * Dim.specificforce) := ⟨C.col.eval .specificweight h.val⟩
/-- Typed `specificvolume(h, W, U) = inv(density)`. -/
def specificvolume : Qty U Dim.density⁻¹ := ⟨C.col.eval .specificvolume h.val⟩
/-- Typed `specificimpedance(h, W, U) = density*sonicspeed`. -/
def specificimpedance : Qty U (Dim.density * Dim.speed) := ⟨C.col.eval .specificimpedance h.val⟩
/-- Typed `thermaldiffusivity(h, W, U) = k/cₚ/ρ`. -/
def thermaldiffusivity :
    Qty U (Dim.thermalconductivity / Dim.specificentropy / Dim.density) :=
  ⟨C.col.eval .thermaldiffusivity h.val⟩
/-- Typed `intensity(h, W, U) = p²/ρ/a`. -/
def intensity : Qty U (Dim.pressure ^ 2 / Dim.density / Dim.speed) :=
  ⟨C.col.eval .intensity h.val⟩
/-- Typed `heatcapacity(h, W, U) = cₚ*ρ`. -/
def heatcapacity : Qty U (Dim.specificentropy * Dim.density) := ⟨C.col.eval .heatcapacity h.val⟩
/-- Typed `kinematic(h, W, U) = viscosity/density`. -/
def kinematic : Qty U (Dim.viscosity / Dim.density) := ⟨C.col.eval .kinematic h.val⟩
/-- Typed `elasticity(h, W, U) = γ*p`. -/
def elasticity : Qty U Dim.pressure := ⟨C.col.eval .elasticity h.val⟩
/-- Typed `viscosity(h, W, U)`. -/
def viscosity : Qty U Dim.viscosity := ⟨C.col.eval .viscosity h.val⟩
/-- Typed `thermalconductivity(h, W, U)`. -/
def thermalconductivity : Qty U Dim.thermalconductivity :=
  ⟨C.col.eval .thermalconductivity h.val⟩
/-- Typed `heatvolume(h, W, U)`. -/
def heatvolume : Qty U Dim.specificentropy := ⟨C.col.eval .heatvolume h.val⟩
/-- Typed `heatpressure(h, W, U)`. -/
def heatpressure : Qty U Dim.specificentropy := ⟨C.col.eval .heatpressure h.val⟩
/-- Typed `heatratio(h, W, U)`. -/
def heatratio : Qty U Dim.dimensionless := ⟨C.col.eval .heatratio h.val⟩
/-- Typed `prandtl(h, W, U)`. -/
def prandtl : Qty U Dim.dimensionless := ⟨C.col.eval .prandtl h.val⟩
/-- Typed `sonicspeed(h, W, U)`. -/
def sonicspeed : Qty U Dim.speed := ⟨C.col.eval .sonicspeed h.val⟩
/-- Typed `freedom(h, W, U)`. -/
def freedom : Qty U Dim.dimensionless := ⟨C.col.eval .freedom h.val⟩
/-- Typed `specificenergy(h, W, U) = heatvolume*T`. -/
def specificenergy : Qty U (Dim.specificentropy * Dim.temperature) :=
  ⟨C.col.eval .specificenergy h.val⟩
/-- Typed `specificenthalpy(h, W, U) = heatpressure*T`. -/
def specificenthalpy : Qty U (Dim.specificentropy * Dim.temperature) :=
  ⟨C.col.eval .specificenthalpy h.val⟩
/-- Typed `<op>ratio(h, W, U)`: dimensionless. -/
def ratio (o : Op) : Qty U Dim.dimensionless := ⟨C.col.ratio o h.val⟩

end TypedColumn

end Geophysics

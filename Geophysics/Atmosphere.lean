import StaticVectors.Values
import Geophysics.Planet
import Geophysics.Gas
import Geophysics.Layer

/-!
# Layered standard atmospheres

Geophysics.jl `src/Geophysics.jl:427-884`. An `Atmosphere n` is a table of `n`
lapse rates and layer-base geopotential altitudes on a planet, in a unit system.
A `Weather n` is that table integrated hydrostatically from a sea-level fluid
state at a geodetic latitude `ϕ`; it answers temperature, pressure, density,
transport properties, gravity and their sea-level ratios at any altitude.

**Types.** Julia's `Atmosphere{n,P,U}`/`Weather{ϕ,f,n,P,U}` keep the layer count
in the type; so does Lean (`n` indexes `StaticVectors.Values Float n`), which
makes `layer` a total `Fin n` and all tables the same length by construction.
Planet, fluid, latitude and unit system are runtime values.

**Evaluation columns.** Julia constant-folds everything that does not depend on
the altitude (sea-level gravity, gas constant, layer tables converted to the
output system, …) through `@pure` and type parameters. Here a `Column n`
holds those values for one output unit system, and every altitude function is
straight-line `Float` code over it. A `Weather` caches the column of its own
system; `Weather.column U` builds the column of another system (build it once
for repeated evaluation in `U`). The column also caches the sea-level values
`op(W, U) = op(0, W, U)` that divide the `…ratio` functions.

**Faithfulness.** Operation order, the altitude conventions and every quirk are
Julia's (`docs/port-notes/applied-misc.md` §4.1, §8.4):
* `layer` puts an exact layer base in the layer below;
* `gravity(h, W, U)` switches from the inverse-square law to `gravitygeodetic`
  at `h = 0.007·radius(W)` (a jump at ≈44.6 km), comparing `h` in `U` with a
  threshold in `W`'s units;
* `specificweight` evaluates altitude gravity at the geopotential altitude;
* the 1976 elliptic layer reads the still-zero next temperature during the
  integration, so `Earth1976` is garbage above 91 km, as in Julia;
* the elliptic layer's `Tc` and `ha` are used unconverted in any unit system.
Julia throws `DomainError` for `sqrt`/`^` of negative arguments; those give
`NaN` here (only `Earth1976English` above ~178 km reaches them).
-/

namespace Geophysics

open StaticVectors UnitSystems FieldConstants JMath

/-- The standard latitude `1.0111032235724π/4` of every preset (`planets.jl:133`),
at which Earth's Somigliana gravity is exactly `9.80665`. -/
def stdLatitude : Float := (f64% 1.0111032235724) * π₀ / (f64% 4.0)

/-- A `Values Float` literal from a list, with its length as the index. -/
def vals (l : List Float) : Values Float l.length := Values.ofFn fun i => l[i.1]

/-- A temperature column of a planet (Julia `Atmosphere{n,P,U}`,
`Geophysics.jl:427-461`): per layer the lapse rate `a` (temperature per
geopotential altitude, possibly `±Inf` for the 1976 elliptic/exponential layers)
and the base geopotential altitude `h`, in the unit system `units`. -/
structure Atmosphere (n : Nat) where
  /-- lapse rate of each layer -/
  a : Values Float n
  /-- geopotential altitude of each layer base (strictly increasing, `h[0] = -0.0`) -/
  h : Values Float n
  /-- "molar rate" (always zero, unused; Julia field `m`) -/
  m : Values Float n
  /-- the planet -/
  planet : Planet
  /-- the unit system of `a` and `h` -/
  units : Sys
  /-- there is at least one layer -/
  pos : 0 < n

namespace Atmosphere

variable {n : Nat}

/-- Julia `Atmosphere{P,U}(a, h)` (`Geophysics.jl:451-453`): `m` is zero. -/
def make (a h : Values Float n) (P : Planet := Earth) (U : Sys := .Metric)
    (pos : 0 < n := by decide) : Atmosphere n :=
  ⟨a, h, Values.replicate (f64% 0.0), P, U, pos⟩

/-- Julia `(U::UnitSystem)(A::Atmosphere)` (`Geophysics.jl:454`): the table converted
to `U` (`lapserate.(a, U, S)`, `length.(h, U, S)`; `m` reset to zero). -/
def toUnits (A : Atmosphere n) (U : Sys) : Atmosphere n :=
  ⟨A.a.map (convert .lapserate · U A.units), A.h.map (convert .length · U A.units),
   Values.replicate (f64% 0.0), A.planet, U, A.pos⟩

end Atmosphere

/-- Julia `layer(h, W)` on a table of layer bases (`Geophysics.jl:571`):
`h ≤ h[0]` gives layer 0; otherwise the layer below the first base `≥ h`, or the
last layer. An exact base `h = h[k]` (`k > 0`) belongs to layer `k - 1`; `NaN`
falls through to the last layer. This is `layerIdx` at `Float`, so its
specification (`Geophysics.Layer`) holds for IEEE comparisons: see
`layerOf_of_le`, `not_le_layerOf`, `le_layerOf_succ`. -/
@[inline] def layerOf {n : Nat} (hs : Values Float n) (pos : 0 < n) (x : Float) : Fin n :=
  layerIdx hs.get pos x

/-- At or below the first base the layer is `0`. -/
theorem layerOf_of_le {n : Nat} (hs : Values Float n) (pos : 0 < n) (x : Float)
    (h : x ≤ hs.get ⟨0, pos⟩) : layerOf hs pos x = ⟨0, pos⟩ :=
  layerIdx_of_le hs.get pos x h

/-- Above the first base, `x` is not `≤` the base of its layer. -/
theorem not_le_layerOf {n : Nat} (hs : Values Float n) (pos : 0 < n) (x : Float)
    (h : ¬ x ≤ hs.get ⟨0, pos⟩) : ¬ x ≤ hs.get (layerOf hs pos x) :=
  not_le_layerIdx hs.get pos x h

/-- Above the first base, `x` is `≤` the next base when there is one (an exact
base belongs to the layer below). -/
theorem le_layerOf_succ {n : Nat} (hs : Values Float n) (pos : 0 < n) (x : Float)
    (h : ¬ x ≤ hs.get ⟨0, pos⟩) (hn : (layerOf hs pos x).1 + 1 < n) :
    x ≤ hs.get ⟨(layerOf hs pos x).1 + 1, hn⟩ :=
  le_layerIdx_succ hs.get pos x h hn

/-- The layer-independent data of a weather column (the fields of Julia's
`Weather{ϕ,f,n,P,U}`, `Geophysics.jl:477-485`). -/
structure WeatherData (n : Nat) where
  /-- the temperature table -/
  atm : Atmosphere n
  /-- geodetic latitude `ϕ` of the column -/
  phi : Float
  /-- the fluid -/
  fluid : Mole
  /-- temperature at each layer base -/
  T : Values Float n
  /-- pressure at each layer base -/
  p : Values Float n
  /-- density at each layer base (Julia `ρ`) -/
  rho : Values Float n
  /-- centre temperature of the 1976 elliptic layer (else `0`) -/
  Tc : Float
  /-- semi-axis of the 1976 elliptic layer (else `0`) -/
  ha : Float

/-- The running state of the hydrostatic integration. -/
structure IntegrationState where
  /-- temperature at the current layer base -/
  T : Float
  /-- pressure at the current layer base -/
  p : Float
  /-- density at the current layer base -/
  rho : Float
  /-- elliptic-layer centre temperature so far -/
  Tc : Float
  /-- elliptic-layer semi-axis so far -/
  ha : Float
  deriving Inhabited

namespace WeatherData

variable {n : Nat}

/-- One step of Julia's hydrostatic integration, from layer `i-1` to layer `i`
(`Geophysics.jl:516-545`; the dead `μ, k, c, Δμ, Δk, Δc` arrays are skipped). In
the elliptic branch Julia reads `T[i]` before assigning it: it is still `0.0`. -/
def step (A : Atmosphere n) (gR : Float) (s : IntegrationState) (i : Nat) (hi : i < n)
    (hp : i - 1 < n) : IntegrationState :=
  let aPrev := A.a.get ⟨i - 1, hp⟩
  let hi' := A.h.get ⟨i, hi⟩
  let Δh := hi' - A.h.get ⟨i - 1, hp⟩
  let (Ti, Tc, ha) :=
    if aPrev.isInf then
      let Tz := (f64% 0.0)
      let Tc := (A.a.get ⟨i, hi⟩ * Δh * Tz + s.T * s.T - Tz * Tz) /
        (hi' * Δh + (f64% 2.0) * s.T - (f64% 2.0) * Tz)
      let d1 := s.T - Tc
      let d2 := Tz - Tc
      let ha := Δh * (s.T - Tc) / Float.sqrt (d1 * d1 - d2 * d2)
      let x := Δh / ha
      (Tc + (s.T - Tc) * Float.sqrt ((f64% 1.0) - x * x), Tc, ha)
    else (s.T + aPrev * Δh, s.Tc, s.ha)
  if aPrev == (f64% 0.0) then
    let v := exp (gR * Δh / Ti)
    ⟨Ti, s.p * v, s.rho * v, Tc, ha⟩
  else
    let t := Ti / s.T
    let gRa := gR / aPrev
    ⟨Ti, s.p * pow t gRa, s.rho * pow t (gRa - (f64% 1.0)), Tc, ha⟩

/-- The states at every layer base, in order. -/
def states (A : Atmosphere n) (gR : Float) (s₀ : IntegrationState) : Array IntegrationState :=
  go 1 s₀ #[s₀]
where
  /-- integrate upwards from layer `i - 1` with state `s` -/
  go (i : Nat) (s : IntegrationState) (acc : Array IntegrationState) : Array IntegrationState :=
    if hi : i < n then
      let s' := step A gR s i hi (by omega)
      go (i + 1) s' (acc.push s')
    else acc
  termination_by n - i

/-- Julia `Weather{ϕ}(A, F)` (`Geophysics.jl:496-546`): integrate the table from the
sea-level state `F` at latitude `ϕ`, with the gas constant of `F`'s fluid and the
Somigliana gravity at `ϕ`, both in `A`'s units. -/
def integrate (A : Atmosphere n) (F : FluidState) (ϕ : Float) : WeatherData n :=
  let U := A.units
  let T0 := F.temperature U
  let p0 := F.pressure U
  let R := F.gasconstant U
  let g := A.planet.gravity ϕ U
  let s₀ : IntegrationState := ⟨T0, p0, p0 / (R * T0), (f64% 0.0), (f64% 0.0)⟩
  let st := states A (-g / R) s₀
  let last := st.back?.getD s₀
  { atm := A, phi := ϕ, fluid := F.fluid
    T := Values.ofFn fun i => (st[i.1]?.getD default).T
    p := Values.ofFn fun i => (st[i.1]?.getD default).p
    rho := Values.ofFn fun i => (st[i.1]?.getD default).rho
    Tc := last.Tc, ha := last.ha }

end WeatherData

/-- The 21 altitude functions of Julia's common interface, in Julia order
(`Geophysics.jl:861-884`): the first eleven are column functions, the last ten
(`Intrinsic`, `Geophysics.jl:55`) are fluid properties at the local temperature. -/
inductive Op where
  | temperature | pressure | density | specificweight | specificvolume | specificimpedance
  | thermaldiffusivity | intensity | heatcapacity | kinematic | elasticity
  | viscosity | thermalconductivity | heatvolume | heatpressure | heatratio | prandtl
  | sonicspeed | freedom | specificenergy | specificenthalpy
  deriving DecidableEq, Repr, Inhabited

namespace Op

/-- All operations in Julia order. -/
def all : List Op :=
  [temperature, pressure, density, specificweight, specificvolume, specificimpedance,
   thermaldiffusivity, intensity, heatcapacity, kinematic, elasticity, viscosity,
   thermalconductivity, heatvolume, heatpressure, heatratio, prandtl, sonicspeed, freedom,
   specificenergy, specificenthalpy]

/-- The Julia name. -/
def name : Op → String
  | temperature => "temperature" | pressure => "pressure" | density => "density"
  | specificweight => "specificweight" | specificvolume => "specificvolume"
  | specificimpedance => "specificimpedance" | thermaldiffusivity => "thermaldiffusivity"
  | intensity => "intensity" | heatcapacity => "heatcapacity" | kinematic => "kinematic"
  | elasticity => "elasticity" | viscosity => "viscosity"
  | thermalconductivity => "thermalconductivity" | heatvolume => "heatvolume"
  | heatpressure => "heatpressure" | heatratio => "heatratio" | prandtl => "prandtl"
  | sonicspeed => "sonicspeed" | freedom => "freedom" | specificenergy => "specificenergy"
  | specificenthalpy => "specificenthalpy"

/-- Position in `all` (the index of the cached sea-level value). -/
def idx : Op → Nat
  | temperature => 0 | pressure => 1 | density => 2 | specificweight => 3
  | specificvolume => 4 | specificimpedance => 5 | thermaldiffusivity => 6 | intensity => 7
  | heatcapacity => 8 | kinematic => 9 | elasticity => 10 | viscosity => 11
  | thermalconductivity => 12 | heatvolume => 13 | heatpressure => 14 | heatratio => 15
  | prandtl => 16 | sonicspeed => 17 | freedom => 18 | specificenergy => 19
  | specificenthalpy => 20

theorem idx_all : (all.zipIdx.all fun (o, i) => o.idx == i) = true := by decide

/-- Julia defines `<op>ratio` for every operation except `heatcapacity`
(`Geophysics.jl:873`). -/
def hasRatio (o : Op) : Bool := o != heatcapacity

/-- Look an operation up by its Julia name. -/
def ofName? (s : String) : Option Op := all.find? (·.name == s)

end Op

/-- A weather column prepared for evaluation in one output unit system `U`:
everything Julia constant-folds per `(W, U)`. Build with `Column.build`. -/
structure Column (n : Nat) where
  /-- the output unit system's constants -/
  u : Units
  /-- the weather's own unit system -/
  wsys : Sys
  /-- `W[i, U]`: layer-base temperature in `U` -/
  T : Values Float n
  /-- `W[i, U]`: lapse rate in `U` -/
  a : Values Float n
  /-- `W[i, U]`: layer-base altitude in `U` -/
  h : Values Float n
  /-- `W[i, U]`: layer-base pressure in `U` -/
  p : Values Float n
  /-- `W[i, U]`: layer-base density in `U` -/
  rho : Values Float n
  /-- layer bases in the weather's own units (for `layer`) -/
  hW : Values Float n
  /-- there is at least one layer -/
  pos : 0 < n
  /-- multiplier of `length(x, units(W), U)` (`1` when no conversion) -/
  toW : Float
  /-- `gravity(W, U)`: Somigliana gravity at the column latitude -/
  g : Float
  /-- `gasconstant(W, U)` -/
  R : Float
  /-- `-g/R` -/
  gR : Float
  /-- `radius(W, U)`: sea-level radius at the column latitude -/
  r : Float
  /-- `0.007*radius(W)` in the weather's units: the gravity-model switch -/
  rSwitch : Float
  /-- `semimajor(P, U)` -/
  semimajor : Float
  /-- `2*(1 + f + m - 2f*sin(ϕ)^2)` of `gravitygeodetic` -/
  slope : Float
  /-- elliptic-layer centre temperature (unconverted, as in Julia) -/
  Tc : Float
  /-- elliptic-layer semi-axis (unconverted, as in Julia) -/
  ha : Float
  /-- the fluid -/
  fluid : Mole
  /-- sea-level values `op(0, W, U)` in `Op.all` order (filled by `build`) -/
  sea : FloatArray

/-- `radius(Earth1976)`: the Metric sea-level radius at the standard latitude, used
by the 1976 exponential layer in every unit system (`Geophysics.jl:653`). -/
def radius1976 : Float := Earth.radiusgeodetic stdLatitude

namespace Column

variable {n : Nat} (C : Column n)

/-- Julia `temperature(hG, i, W, U)` (`Geophysics.jl:647-661`). -/
def temperatureAt (hG : Float) (i : Fin n) : Float :=
  let T0 := C.T.get i
  let a0 := C.a.get i
  let h0 := C.h.get i
  if a0.isInf then
    let Δh := hG - h0
    if a0 < (f64% 0.0) then
      let x := Δh / C.ha
      C.Tc + (T0 - C.Tc) * Float.sqrt ((f64% 1.0) - x * x)
    else
      let r := radius1976
      let ξ := Δh * ((r + h0) / (r + hG))
      (f64% 1000.0) - ((f64% 1000.0) - T0) * exp ((-(f64% 0.012) / ((f64% 1000.0) - T0)) * ξ)
  else if a0 == (f64% 0.0) then T0 else T0 + a0 * (hG - h0)

/-- Whether Julia's `temperature(hG, i, W, U)` throws: in the 1976 elliptic layer
the argument of `sqrt(1 - (Δh/ha)^2)` is negative (a `DomainError`). Every
operation computes the temperature first, so all of them throw; Lean returns
`NaN` for all of them (otherwise `NaN^0 = 1` would let a pressure through). -/
def domainError (hG : Float) (i : Fin n) : Bool :=
  let a0 := C.a.get i
  a0.isInf && a0 < (f64% 0.0) &&
    (let x := (hG - C.h.get i) / C.ha
     (f64% 1.0) - x * x < (f64% 0.0))

/-- Julia `pressure(hG, T, i, W, U)` (`Geophysics.jl:736-744`). -/
def pressureT (hG T : Float) (i : Fin n) : Float :=
  let a := C.a.get i
  C.p.get i * (if a == (f64% 0.0) then exp (C.gR * (hG - C.h.get i) / T)
    else pow (T / C.T.get i) (C.gR / a))

/-- Julia `density(hG, T, i, W, U)` (`Geophysics.jl:752-761`). -/
def densityT (hG T : Float) (i : Fin n) : Float :=
  let a := C.a.get i
  C.rho.get i *
    (if a == (f64% 0.0) then exp (C.gR * (hG - C.h.get i) / T)
      else pow (T / C.T.get i) (C.gR / a - (f64% 1.0)))

/-- Julia `gravity(h, W, U)` (`Geophysics.jl:633-639`): inverse-square below
`0.007·radius(W)`, `gravitygeodetic` above. -/
def gravity (h : Float) : Float :=
  if h ≤ C.rSwitch then
    let rh := C.r + h
    C.g * (C.r * C.r) / (rh * rh)
  else
    let ha := h / C.semimajor
    C.g * (((f64% 1.0) - C.slope * ha) + (f64% 3.0) * (ha * ha))

/-- Julia `altgeopotent(h, W, U) = (h/altabs(h, W, U))*radius(W, U)`
(`Geophysics.jl:617`): geopotential altitude of a geometric altitude. -/
@[inline] def altgeopotent (h : Float) : Float := h / (C.r + h) * C.r

/-- Julia `layer(hG, W, U) = layer(length(hG, units(W), U), W)` (`Geophysics.jl:572`). -/
@[inline] def layer (hG : Float) : Fin n := layerOf C.hW C.pos (hG * C.toW)

/-- Julia `op(hG, i, W, U)`: the layer-level primitive of every operation (`NaN`
where Julia's temperature throws, see `domainError`). -/
def opAt (o : Op) (hG : Float) (i : Fin n) : Float :=
  if C.domainError hG i then JMath.nan else
  let U := C.u
  let F := C.fluid
  let T := C.temperatureAt hG i
  match o with
  | .temperature => T
  | .pressure => C.pressureT hG T i
  | .density => C.densityT hG T i
  | .specificweight => C.densityT hG T i * C.gravity hG
  | .specificvolume => (f64% 1.0) / C.densityT hG T i
  | .specificimpedance => C.densityT hG T i * F.sonicspeedU U T
  | .thermaldiffusivity => F.thermalconductivityU U T / F.heatpressureU U T / C.densityT hG T i
  | .intensity =>
    let a := C.a.get i
    let p := C.p.get i
    let v := if a == (f64% 0.0) then exp (C.gR * (hG - C.h.get i) / T)
      else
        let t := T / C.T.get i
        let gRa := C.gR / a
        pow t ((f64% 2.0) * gRa) / pow t (gRa - (f64% 1.0))
    p * p / C.rho.get i * v / F.sonicspeedU U T
  | .heatcapacity => F.heatpressureU U T * C.densityT hG T i
  | .kinematic => F.viscosityU U T / C.densityT hG T i
  | .elasticity => F.heatratioU U T * C.pressureT hG T i
  | .viscosity => F.viscosityU U T
  | .thermalconductivity => F.thermalconductivityU U T
  | .heatvolume => F.heatvolumeU U T
  | .heatpressure => F.heatpressureU U T
  | .heatratio => F.heatratioU U T
  | .prandtl => F.prandtlU U T
  | .sonicspeed => F.sonicspeedU U T
  | .freedom => F.freedomU U T
  | .specificenergy => F.specificenergyU U T
  | .specificenthalpy => F.specificenthalpyU U T

/-- Julia `op(h, W, U)` (`Geophysics.jl:864-868`): at geometric altitude `h` in `U`. -/
def eval (o : Op) (h : Float) : Float :=
  let hG := C.altgeopotent h
  C.opAt o hG (C.layer hG)

/-- Julia `op(W, U) = op(0, W, U)`: the sea-level value. -/
@[inline] def seaLevel (o : Op) : Float := C.sea.get! o.idx

/-- Julia `<op>ratio(hG, i, W, U) = op(hG, i, W, U)/op(W, U)` (`Geophysics.jl:876-881`). -/
def ratioAt (o : Op) (hG : Float) (i : Fin n) : Float := C.opAt o hG i / C.seaLevel o

/-- Julia `<op>ratio(h, W, U)`: the ratio at geometric altitude `h`. -/
def ratio (o : Op) (h : Float) : Float :=
  let hG := C.altgeopotent h
  C.ratioAt o hG (C.layer hG)

/-- Julia `geopotential(h, W, U) = gravity(h, W, U)*h` (`Geophysics.jl:856`). -/
def geopotential (h : Float) : Float := C.gravity h * h

/-- Prepare the column of `D` for output in `U`. -/
def build (D : WeatherData n) (U : Sys) : Column n :=
  let S := D.atm.units
  let P := D.atm.planet
  let cT := (factor .temperature S U).toFloat
  let cA := (factor .lapserate S U).toFloat
  let cH := (factor .length S U).toFloat
  let cP := (factor .pressure S U).toFloat
  let cR := (factor .density S U).toFloat
  let toW :=
    if S == U then (f64% 1.0)
    else
      let q := factor .length S U
      if q.v.isOne then (f64% 1.0) else q.inv.toFloat
  let g := P.gravity D.phi U
  let R := D.fluid.gasconstant U
  let core : Column n :=
    { u := Units.of U, wsys := S
      T := D.T.map (· * cT), a := D.atm.a.map (· * cA), h := D.atm.h.map (· * cH)
      p := D.p.map (· * cP), rho := D.rho.map (· * cR), hW := D.atm.h, pos := D.atm.pos
      toW := toW, g := g, R := R, gR := -g / R
      r := P.radiusgeodetic D.phi U, rSwitch := (f64% 0.007) * P.radiusgeodetic D.phi S
      semimajor := P.semimajor U, slope := P.geodeticSlope D.phi
      Tc := D.Tc, ha := D.ha, fluid := D.fluid, sea := .empty }
  { core with sea := Op.all.foldl (fun acc o => acc.push (core.eval o (f64% 0.0))) .empty }

end Column

/-- A weather column (Julia `Weather{ϕ,f,n,P,U}`, `Geophysics.jl:463-563`): the
integrated layer data plus its evaluation column in its own unit system. Build
with `Weather.ofData`, `Weather.integrate` or `Atmosphere.weather`. -/
structure Weather (n : Nat) where
  private mk ::
  /-- the Julia fields -/
  data : WeatherData n
  /-- the evaluation column in the weather's own units -/
  native : Column n

namespace Weather

variable {n : Nat}

/-- A weather from its data, with its native column. -/
def ofData (D : WeatherData n) : Weather n := ⟨D, Column.build D D.atm.units⟩

/-- Julia `Weather{ϕ}(A, F)`: hydrostatic integration of `A` from the state `F` at
latitude `ϕ` (`Geophysics.jl:496-546`). -/
def integrate (A : Atmosphere n) (F : FluidState) (ϕ : Float := stdLatitude) : Weather n :=
  ofData (WeatherData.integrate A F ϕ)

variable (W : Weather n)

/-- The temperature table. -/
@[inline] def atm : Atmosphere n := W.data.atm
/-- Julia `Planet(W)` (`Geophysics.jl:574`). -/
@[inline] def planet : Planet := W.data.atm.planet
/-- Julia `units(W)` (`Geophysics.jl:575`). -/
@[inline] def units : Sys := W.data.atm.units
/-- Julia `fluid(W)` (`Geophysics.jl:576`). -/
@[inline] def fluid : Mole := W.data.fluid
/-- Julia `latitude(W) = ϕ` (`Geophysics.jl:583`). -/
@[inline] def latitude : Float := W.data.phi
/-- Layer-base temperatures (Julia `W.T`). -/
@[inline] def T : Values Float n := W.data.T
/-- Layer-base pressures (Julia `W.p`). -/
@[inline] def p : Values Float n := W.data.p
/-- Layer-base densities (Julia `W.ρ`). -/
@[inline] def rho : Values Float n := W.data.rho
/-- Elliptic-layer centre temperature (Julia `W.Tc`). -/
@[inline] def Tc : Float := W.data.Tc
/-- Elliptic-layer semi-axis (Julia `W.ha`). -/
@[inline] def ha : Float := W.data.ha

/-- The evaluation column in `U`: the cached native one, or a new one. For many
evaluations in a foreign system, build it once and use `Column` directly. -/
def column (U : Sys := W.units) : Column n :=
  if U == W.units then W.native else Column.build W.data U

/-- Julia `W[i, U]` (`Geophysics.jl:565-568`): `(T, a, h, p, ρ)` of layer `i`
(0-based) converted to `U`. -/
def get (i : Fin n) (U : Sys := W.units) : Float × Float × Float × Float × Float :=
  let C := W.column U
  (C.T.get i, C.a.get i, C.h.get i, C.p.get i, C.rho.get i)

/-- Julia `layer(h, W) ` (`Geophysics.jl:571`): the layer (0-based) of a geopotential
altitude given in `W`'s units. -/
def layer (hG : Float) : Fin n := layerOf W.atm.h W.atm.pos hG

/-- Julia `layer(h, W, U) = layer(length(h, units(W), U), W)` (`Geophysics.jl:572`). -/
def layerIn (hG : Float) (U : Sys) : Fin n := (W.column U).layer hG

/-- Julia `lapserate(h, W) = W.A.a[layer(h, W)]` (`Geophysics.jl:570`). -/
def lapserate (hG : Float) : Float := W.atm.a.get (W.layer hG)

/-- Julia `radius(W, U) = radiusgeodetic(ϕ, Planet(W), U)` (`Geophysics.jl:590`). -/
def radius (U : Sys := W.units) : Float := W.planet.radiusgeodetic W.latitude U

/-- Julia `gravity(W, U) = gravity(ϕ, Planet(W), U)` (`Geophysics.jl:597`): sea-level
Somigliana gravity (exactly `9.80665` for the Metric presets). -/
def gravitySea (U : Sys := W.units) : Float := W.planet.gravity W.latitude U

/-- Julia `molecularmass(W, U)` (`Geophysics.jl:599`). -/
def molecularmass (U : Sys := W.units) : Float := W.fluid.molecularmass U
/-- Julia `gasconstant(W, U)` (`Geophysics.jl:600`). -/
def gasconstant (U : Sys := W.units) : Float := W.fluid.gasconstant U

/-- Julia `altabs(h, W, U) = radius(W, U) + h` (`Geophysics.jl:609`). -/
def altabs (h : Float) (U : Sys := W.units) : Float := W.radius U + h
/-- Julia `altabs(h, W, U, S) = altabs(h*length(S, U), W, U)` (`Geophysics.jl:610`). -/
def altabsFrom (h : Float) (U S : Sys) : Float := W.altabs (h * (factor .length S U).toFloat) U

/-- Julia `altgeopotent(h, W, U) = (h/altabs(h, W, U))*radius(W, U)` (`Geophysics.jl:617`). -/
def altgeopotent (h : Float) (U : Sys := W.units) : Float :=
  let r := W.radius U
  h / (r + h) * r
/-- Julia `altgeopotent(h, W, U, S) = altgeopotent(h*length(S, U), W, U)`. -/
def altgeopotentFrom (h : Float) (U S : Sys) : Float :=
  W.altgeopotent (h * (factor .length S U).toFloat) U

/-- Julia `altgeometric(hG, W, U) = r/(r/hG - 1)` (`Geophysics.jl:625`). -/
def altgeometric (hG : Float) (U : Sys := W.units) : Float :=
  let r := W.radius U
  r / (r / hG - (f64% 1.0))
/-- Julia `altgeometric(hG, W, U, S) = altgeometric(hG*length(S, U), W, U)`. -/
def altgeometricFrom (hG : Float) (U S : Sys) : Float :=
  W.altgeometric (hG * (factor .length S U).toFloat) U

/-- Julia `gravity(h, W, U)` (`Geophysics.jl:633-639`): gravity at geometric altitude `h`. -/
def gravity (h : Float) (U : Sys := W.units) : Float := (W.column U).gravity h
/-- Julia `gravity(h, W, U, S) = gravity(h*length(S, U), W, U)` (`Geophysics.jl:640`). -/
def gravityFrom (h : Float) (U S : Sys) : Float := W.gravity (h * (factor .length S U).toFloat) U

/-- Julia `geopotential(h, W, U) = gravity(h, W, U)*h` (`Geophysics.jl:856`). -/
def geopotential (h : Float) (U : Sys := W.units) : Float := (W.column U).geopotential h
/-- Julia `geopotential(h, W, U, S) = geopotential(h*length(S, U), W, U)`. -/
def geopotentialFrom (h : Float) (U S : Sys) : Float :=
  W.geopotential (h * (factor .length S U).toFloat) U
/-- Julia `geopotential(W, U = Metric) = geopotential(0, W, U)`. -/
def geopotentialSea (U : Sys := .Metric) : Float := W.geopotential (f64% 0.0) U

/-- Julia `op(hG, i, W, U)`: operation `o` at geopotential altitude `hG` in layer `i`. -/
def opAt (o : Op) (hG : Float) (i : Fin n) (U : Sys := W.units) : Float :=
  (W.column U).opAt o hG i

/-- Julia `op(h, W, U)`: operation `o` at geometric altitude `h`, result in `U`. -/
def eval (o : Op) (h : Float) (U : Sys := W.units) : Float := (W.column U).eval o h

/-- Julia `op(h, W, U, S) = op(length(h, U, S), W, U)`: `h` given in `S`. -/
def evalFrom (o : Op) (h : Float) (U S : Sys) : Float := W.eval o (convert .length h U S) U

/-- Julia `op(W, U = Metric) = op(0, W, U)`: the sea-level value (Metric by default,
even for an English weather). -/
def sea (o : Op) (U : Sys := .Metric) : Float := (W.column U).seaLevel o

/-- Julia `<op>ratio(h, W, U)`: `op(h, W, U)/op(W, U)`. -/
def ratio (o : Op) (h : Float) (U : Sys := W.units) : Float := (W.column U).ratio o h

/-- Julia `<op>ratio(h, W, U, S) = <op>ratio(length(h, U, S), W, U)`. -/
def ratioFrom (o : Op) (h : Float) (U S : Sys) : Float := W.ratio o (convert .length h U S) U

/-- Julia `pressure(hG, T, i, W, U)` with an explicit temperature (`Geophysics.jl:736`). -/
def pressureT (hG T : Float) (i : Fin n) (U : Sys := W.units) : Float :=
  (W.column U).pressureT hG T i
/-- Julia `density(hG, T, i, W, U)` with an explicit temperature (`Geophysics.jl:752`). -/
def densityT (hG T : Float) (i : Fin n) (U : Sys := W.units) : Float :=
  (W.column U).densityT hG T i
/-- Julia `kinematic(hG, T, i, W, U) = viscosity(T, fluid(W), U)/density(hG, T, i, W, U)`
(`Geophysics.jl:770`). -/
def kinematicT (hG T : Float) (i : Fin n) (U : Sys := W.units) : Float :=
  let C := W.column U
  W.fluid.viscosityU C.u T / C.densityT hG T i

/-- Julia `(W::Weather)(hG, i)` (`Geophysics.jl:551-554`): the fluid state at a
geopotential altitude in layer `i`, in `W`'s units. -/
def stateAt (hG : Float) (i : Fin n) : FluidState :=
  let C := W.native
  if C.domainError hG i then ⟨W.fluid, W.units, JMath.nan, JMath.nan⟩ else
  let T := C.temperatureAt hG i
  ⟨W.fluid, W.units, T, C.pressureT hG T i⟩

/-- Julia `(W::Weather)(h = 0)` (`Geophysics.jl:550`): the fluid state at geometric
altitude `h` in `W`'s units. -/
def state (h : Float := 0.0) : FluidState :=
  let hG := W.altgeopotent h
  W.stateAt hG (W.layer hG)

/-- The intent of Julia's broken `(U::UnitSystem)(W::Weather)` (`Geophysics.jl:486`):
the same weather with its tables converted to `U` (no Julia golden; `Tc` is
converted as a temperature and `ha` as a length). -/
def toUnits (U : Sys) : Weather n :=
  let D := W.data
  let S := W.units
  ofData { D with
    atm := D.atm.toUnits U
    T := D.T.map (convert .temperature · U S), p := D.p.map (convert .pressure · U S)
    rho := D.rho.map (convert .density · U S)
    Tc := convert .temperature D.Tc U S, ha := convert .length D.ha U S }

/-! Named forms of the common interface (Julia exports each as a function). -/

/-- `temperature(h, W, U)` -/ def temperature (h : Float) (U : Sys := W.units) := W.eval .temperature h U
/-- `pressure(h, W, U)` -/ def pressure (h : Float) (U : Sys := W.units) := W.eval .pressure h U
/-- `density(h, W, U)` -/ def density (h : Float) (U : Sys := W.units) := W.eval .density h U
/-- `specificweight(h, W, U)` -/
def specificweight (h : Float) (U : Sys := W.units) := W.eval .specificweight h U
/-- `specificvolume(h, W, U)` -/
def specificvolume (h : Float) (U : Sys := W.units) := W.eval .specificvolume h U
/-- `specificimpedance(h, W, U)` -/
def specificimpedance (h : Float) (U : Sys := W.units) := W.eval .specificimpedance h U
/-- `thermaldiffusivity(h, W, U)` -/
def thermaldiffusivity (h : Float) (U : Sys := W.units) := W.eval .thermaldiffusivity h U
/-- `intensity(h, W, U)` -/ def intensity (h : Float) (U : Sys := W.units) := W.eval .intensity h U
/-- `heatcapacity(h, W, U)` -/
def heatcapacity (h : Float) (U : Sys := W.units) := W.eval .heatcapacity h U
/-- `kinematic(h, W, U)` -/ def kinematic (h : Float) (U : Sys := W.units) := W.eval .kinematic h U
/-- `elasticity(h, W, U)` -/
def elasticity (h : Float) (U : Sys := W.units) := W.eval .elasticity h U
/-- `viscosity(h, W, U)` -/ def viscosity (h : Float) (U : Sys := W.units) := W.eval .viscosity h U
/-- `thermalconductivity(h, W, U)` -/
def thermalconductivity (h : Float) (U : Sys := W.units) := W.eval .thermalconductivity h U
/-- `heatvolume(h, W, U)` -/
def heatvolume (h : Float) (U : Sys := W.units) := W.eval .heatvolume h U
/-- `heatpressure(h, W, U)` -/
def heatpressure (h : Float) (U : Sys := W.units) := W.eval .heatpressure h U
/-- `heatratio(h, W, U)` -/ def heatratio (h : Float) (U : Sys := W.units) := W.eval .heatratio h U
/-- `prandtl(h, W, U)` -/ def prandtl (h : Float) (U : Sys := W.units) := W.eval .prandtl h U
/-- `sonicspeed(h, W, U)` -/
def sonicspeed (h : Float) (U : Sys := W.units) := W.eval .sonicspeed h U
/-- `freedom(h, W, U)` -/ def freedom (h : Float) (U : Sys := W.units) := W.eval .freedom h U
/-- `specificenergy(h, W, U)` -/
def specificenergy (h : Float) (U : Sys := W.units) := W.eval .specificenergy h U
/-- `specificenthalpy(h, W, U)` -/
def specificenthalpy (h : Float) (U : Sys := W.units) := W.eval .specificenthalpy h U

end Weather

/-- Julia `Weather{ϕ}(A, F)` as an atmosphere method: integrate `A` from the fluid
`G` at temperature `T` and pressure `p` (in `A`'s units) at latitude `ϕ`
(`Geophysics.jl:549` with an explicit fluid; `Atmosphere.weather` in `Data` uses `Air`). -/
def Atmosphere.weatherOf {n : Nat} (A : Atmosphere n) (G : Mole) (T : Float)
    (p : Float := 101325.0) (ϕ : Float := stdLatitude) : Weather n :=
  Weather.integrate A (G.state T p A.units) ϕ

end Geophysics

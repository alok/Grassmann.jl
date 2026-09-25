import Geophysics.Units

/-!
# Planet ellipsoids and normal gravity

Julia `Planet{f,a,t,Gm}` (`src/Geophysics.jl:66-425`): an oblate reference
ellipsoid with flattening `f`, semimajor axis `a` [m], sidereal period `t` [s]
(negative for retrograde rotation) and standard gravitational parameter `Gm`
[m³ s⁻²], and the geodesy derived from it: shape constants, latitude
conversions, radii, rotation, the Hirvonen zonal functions, `J₂`, Somigliana
normal gravity and gravity with altitude.

Julia keeps the four parameters in type parameters, so their *kind* is
observable: the spheres are `Planet{0,…}` with the integer `0`, and dispatch on
that literal (`q0`, `q01`, `q`, `q1`, `dynamicformfactor`); Saturn's period is
the integer `38018`. `Planet` stores Julia payloads (`FieldConstants.JNum`) for
exact printing and that dispatch; arithmetic uses `Float`, which agrees with
Julia's integer promotion for every value involved.

Every function follows Julia's operation order (`x^2` is `x*x`, n-ary `*` folds
left, `2f` binds tighter than `*`) and uses Julia's own elementary functions
(`JuliaBase.F64.sin`, …), so results agree with Julia bit for bit. Functions taking a
unit system `U` return values in `U` (default `Metric`), exactly as Julia does.
Julia's dispatch-overloaded names become distinct Lean names:

| Julia | Lean |
|---|---|
| `gravity(P, U)` (`GM/a²`) | `Planet.gravitySpherical` |
| `_gravity(ϕ, P, U)` (Hirvonen) | `Planet.gravityNormal` |
| `gravity(ϕ, P, U)` (Somigliana) | `Planet.gravity` |
| `_gravity(h, θ, P, U)` (`norm` of the components) | `Planet.gravityNorm` |
| `gravity(h, θ, P, U)` | `Planet.gravityAt` |
| `latitudegeocentric(h, ϕ, P, U)` | `Planet.latitudegeocentricAt` |
| `oblateness(θ, P, U)` / `oblateness(P, U)` | `Planet.oblatenessAt` / `Planet.oblateness` |
-/

namespace Geophysics

open FieldConstants UnitSystems

/-- A celestial reference ellipsoid (Julia `Planet{f,a,t,Gm}`,
`Geophysics.jl:74-75`). The fields are Julia's type parameters as given to the
constructor (`Quantity` is the identity in Geophysics). -/
structure Planet where
  /-- raw constructor; use `Planet.of`, which fills the cached constants -/
  private raw ::
  /-- flattening `f` -/
  f : Float
  /-- semimajor axis `a` [m] -/
  a : Float
  /-- sidereal rotation period `t` [s]; negative for retrograde rotation -/
  t : Float
  /-- standard gravitational parameter `GM` [m³ s⁻²] -/
  Gm : Float
  /-- `f` as Julia holds it (the integer `0` for spheres) -/
  fJ : JNum
  /-- `a` as Julia holds it -/
  aJ : JNum
  /-- `t` as Julia holds it (Saturn's is the integer `38018`) -/
  tJ : JNum
  /-- `Gm` as Julia holds it -/
  GmJ : JNum
  /-- cached `eccentricity(P)` (Julia folds the `@pure` planet constants at compile time) -/
  ecc : Float := 0.0
  /-- cached `eccentricity2(P)` -/
  ecc2 : Float := 0.0
  /-- cached `aspectratio(P)` -/
  aspect : Float := 0.0
  /-- cached Metric `oblateness(P)` -/
  obl : Float := 0.0
  /-- cached `q0(P)` -/
  q0v : Float := 0.0
  /-- cached `q01(P)` -/
  q01v : Float := 0.0
  /-- cached `dynamicformfactor(P)` -/
  j2 : Float := 0.0
  /-- cached Metric `_gravity(0, P)` (normal gravity at the equator) -/
  geM : Float := 0.0
  /-- cached Metric `_gravity(π/2, P)` (normal gravity at the pole) -/
  gpM : Float := 0.0
  /-- cached Metric `aspectratio(P)*(gp/ge) - 1` of Somigliana's formula -/
  somK : Float := 0.0
  /-- cached `f*(2 - f)` of Somigliana's formula -/
  somE : Float := 0.0
  deriving Inhabited

/-- `Float64(π)`. -/
def π₀ : Float := 3.141592653589793

/-- `2π` as Julia computes `2π` (`Float64(2)*Float64(π)`). -/
def twoπ : Float := 6.283185307179586

/-- `π/2`. -/
def halfπ : Float := 1.5707963267948966

namespace Planet

open JuliaBase.F64 (sin cos tan atan asin atanh)

variable (P : Planet)

/-- Julia's `Planet{0}` dispatch: the flattening is the integer literal `0`. -/
def isSphere : Bool :=
  match P.fJ with
  | .int n => n == 0
  | .float _ => false

/-- `flattening(P) = f` (`Geophysics.jl:88`). -/
@[inline] def flattening : Float := P.f

/-- `semimajor(P, U) = a*length(Metric, U)` (`Geophysics.jl:100`). -/
def semimajor (U : Sys := .Metric) : Float := P.a * (Units.of U).lengthM

/-- `period(P, U) = t*time(Metric, U)` (`Geophysics.jl:112`). -/
def period (U : Sys := .Metric) : Float := P.t * (Units.of U).timeM

/-- `gravitation(P, U) = Gm/(length(U,Metric)*specificenergy(U,Metric))`
(`Geophysics.jl:124-125`); `gravitation(P) = Gm` is the Metric case. -/
def gravitation (U : Sys := .Metric) : Float := P.Gm * (Units.of U).gravitationInv

/-- `mass(P, U) = gravitation(P, U)/gravitation(U)` (`Geophysics.jl:137`). -/
def mass (U : Sys := .Metric) : Float := P.gravitation U * (Units.of U).newtonInv

/-- `frequency(P, U) = 1/period(P, U)` (`Geophysics.jl:149`). -/
def frequency (U : Sys := .Metric) : Float := 1.0 / P.period U

/-- `angularfrequency(P, U) = 2π/period(P, U)` (`Geophysics.jl:161`). -/
def angularfrequency (U : Sys := .Metric) : Float := twoπ / P.period U

/-- `radius_fast(θ, P, U) = semimajor(P, U)*(1 - flattening(P)*sin(θ)^2)`
(`Geophysics.jl:164`). -/
def radiusFast (θ : Float) (U : Sys := .Metric) : Float :=
  let s := sin θ
  P.semimajor U * (1.0 - P.flattening * (s * s))

/-- `meanradius(P, U) = radius_fast(asin(sqrt(1/3)), P, U)` (`Geophysics.jl:163`). -/
def meanradius (U : Sys := .Metric) : Float := P.radiusFast (asin (Float.sqrt (1.0 / 3.0))) U

/-- `semiminor(P, U) = radius_fast(π/2, P, U)` (`Geophysics.jl:176`). -/
def semiminor (U : Sys := .Metric) : Float := P.radiusFast halfπ U

/-- The formula of `eccentricity(P) = sqrt(f*(2 - f))` (`Geophysics.jl:188`). -/
def eccentricityRaw : Float := let f := P.flattening; Float.sqrt (f * (2.0 - f))

/-- `eccentricity(P) = sqrt(f*(2 - f))` (`Geophysics.jl:188`; cached). -/
@[inline] def eccentricity : Float := P.ecc

/-- The formula of `eccentricity2(P) = eccentricity(P)/(1 - f)` (`Geophysics.jl:200`). -/
def eccentricity2Raw : Float := P.eccentricity / (1.0 - P.flattening)

/-- `eccentricity2(P) = eccentricity(P)/(1 - f)`, the second eccentricity `e′`
(`Geophysics.jl:200`; cached). -/
@[inline] def eccentricity2 : Float := P.ecc2

/-- `lineareccentricity(P, U) = semimajor(P, U)*eccentricity(P)` (`Geophysics.jl:207`). -/
def lineareccentricity (U : Sys := .Metric) : Float := P.semimajor U * P.eccentricity

/-- The formula of `aspectratio(P) = semiminor(P)/semimajor(P)` (`Geophysics.jl:219`). -/
def aspectratioRaw : Float := P.semiminor / P.semimajor

/-- `aspectratio(P) = semiminor(P)/semimajor(P)` (`Geophysics.jl:219`; cached). -/
@[inline] def aspectratio : Float := P.aspect

/-- `authalicradius(P, U) = sqrt((a^2 + b^2*atanh(e)/e)/2)` (`Geophysics.jl:221`). -/
def authalicradius (U : Sys := .Metric) : Float :=
  let a := P.semimajor U
  let b := P.semiminor U
  let e := P.eccentricity
  Float.sqrt ((a * a + b * b * atanh e / e) / 2.0)

/-- `latitudegeodetic(θ, P) = atan(tan(θ)/(1 - f)^2)`: geocentric to geodetic
latitude (`Geophysics.jl:228`). -/
def latitudegeodetic (θ : Float) : Float :=
  let c := 1.0 - P.flattening
  atan (tan θ / (c * c))

/-- `deflectiongeodetic(θ, P) = latitudegeodetic(θ, P) - θ` (`Geophysics.jl:229`). -/
def deflectiongeodetic (θ : Float) : Float := P.latitudegeodetic θ - θ

/-- `latitudegeocentric(ϕ, P) = atan(tan(ϕ)*(1 - f)^2)`: geodetic to geocentric
latitude (`Geophysics.jl:236`). -/
def latitudegeocentric (ϕ : Float) : Float :=
  let c := 1.0 - P.flattening
  atan (tan ϕ * (c * c))

/-- `deflectiongeocentric(ϕ, P) = latitudegeocentric(ϕ, P) - ϕ` (`Geophysics.jl:237`). -/
def deflectiongeocentric (ϕ : Float) : Float := P.latitudegeocentric ϕ - ϕ

/-- `latitudeparametric(ϕ, P) = atan(tan(ϕ)*(1 - f))`: geodetic to parametric
latitude (`Geophysics.jl:244`). -/
def latitudeparametric (ϕ : Float) : Float := atan (tan ϕ * (1.0 - P.flattening))

/-- `radiusgeodetic(ϕ, P, U) = a*(1 - f/2*(1 - cos(2ϕ)) + 5f^2/16*(1 - cos(4ϕ)))`:
the radius at geodetic latitude `ϕ` (`Geophysics.jl:275-278`). -/
def radiusgeodetic (ϕ : Float) (U : Sys := .Metric) : Float :=
  let f := P.flattening
  let a := P.semimajor U
  a * ((1.0 - f / 2.0 * (1.0 - cos (2.0 * ϕ))) +
    5.0 * (f * f) / 16.0 * (1.0 - cos (4.0 * ϕ)))

/-- `deflection(h, ϕ, P, U) = f*sin(2ϕ)*(1 - f/2 - h/radiusgeodetic(ϕ, P, U))`: the
angle between the geodetic and geocentric latitudes at altitude `h`
(`Geophysics.jl:251-254`). -/
def deflection (h ϕ : Float) (U : Sys := .Metric) : Float :=
  let f := P.flattening
  f * sin (2.0 * ϕ) * ((1.0 - f / 2.0) - h / P.radiusgeodetic ϕ U)

/-- `latitudegeocentric(h, ϕ, P, U) = ϕ - deflection(h, ϕ, P, U)` (`Geophysics.jl:261`). -/
def latitudegeocentricAt (h ϕ : Float) (U : Sys := .Metric) : Float := ϕ - P.deflection h ϕ U

/-- `radius(θ, P, U) = 1/sqrt((cos(θ)/a)^2 + (sin(θ)/b)^2)`: the radius at geocentric
latitude `θ` (`Geophysics.jl:268`). -/
def radius (θ : Float) (U : Sys := .Metric) : Float :=
  let x := cos θ / P.semimajor U
  let y := sin θ / P.semiminor U
  1.0 / Float.sqrt (x * x + y * y)

/-- `_speed(θ, P, U) = radius(θ, P, U)*angularfrequency(P, U)` (`Geophysics.jl:280`). -/
def speedRadial (θ : Float) (U : Sys := .Metric) : Float := P.radius θ U * P.angularfrequency U

/-- `speed(θ, P, U) = _speed(θ, P, U)*cos(θ)`: surface speed of rotation
(`Geophysics.jl:291`). -/
def speed (θ : Float) (U : Sys := .Metric) : Float := P.speedRadial θ U * cos θ

/-- `_centripetal(θ, P, U) = _speed(θ, P, U)*angularfrequency(P, U)` (`Geophysics.jl:293`). -/
def centripetalRadial (θ : Float) (U : Sys := .Metric) : Float :=
  P.speedRadial θ U * P.angularfrequency U

/-- `centripetal(θ, P, U) = _centripetal(θ, P, U)*cos(θ)` (`Geophysics.jl:299`). -/
def centripetal (θ : Float) (U : Sys := .Metric) : Float := P.centripetalRadial θ U * cos θ

/-- `gravity(P::Planet, U) = gravitation(P, U)/semimajor(P, U)^2`, the spherical
estimate at the equator (`Geophysics.jl:306`). -/
def gravitySpherical (U : Sys := .Metric) : Float :=
  let a := P.semimajor U
  P.gravitation U / (a * a)

/-- `oblateness(θ, P, U) = _centripetal(θ, P, U)/gravity(P, U)/gravity(U)`
(`Geophysics.jl:313`). -/
def oblatenessAt (θ : Float) (U : Sys := .Metric) : Float :=
  P.centripetalRadial θ U / P.gravitySpherical U * (Units.of U).gcInv

/-- `oblateness(P, U) = oblateness(π/2, P, U)`, Hirvonen's `m = ω²a²b/GM`
(`Geophysics.jl:325`; the Metric value is cached). -/
def oblateness (U : Sys := .Metric) : Float :=
  if U == .Metric then P.obl else P.oblatenessAt halfπ U

/-- `q0(P)` (cached). -/
@[inline] def q0 : Float := P.q0v

/-- `q01(P)` (cached). -/
@[inline] def q01 : Float := P.q01v

/-- The formula of `q0(P) = ((1 + 3/e′^2)*atan(e′) - 3/e′)/2`, or `1` for a sphere
(`Geophysics.jl:328, 334`). -/
def q0Raw : Float :=
  if P.isSphere then 1.0
  else
    let e2 := P.eccentricity2
    ((1.0 + 3.0 / (e2 * e2)) * atan e2 - 3.0 / e2) / 2.0

/-- The formula of `q01(P) = 3((1 + 1/e′^2)*(1 - atan(e′)/e′)) - 1`, or `1` for a
sphere (`Geophysics.jl:329, 335`). -/
def q01Raw : Float :=
  if P.isSphere then 1.0
  else
    let e2 := P.eccentricity2
    3.0 * ((1.0 + 1.0 / (e2 * e2)) * (1.0 - atan e2 / e2)) - 1.0

/-- `q(u, P, U)` with `E = lineareccentricity(P, U)/u`: `((1 + 3/E^2)*atan(E) - 3/E)/2`,
or `1` for a sphere (`Geophysics.jl:330, 336`). -/
def q (u : Float) (U : Sys := .Metric) : Float :=
  if P.isSphere then 1.0
  else
    let e := P.lineareccentricity U / u
    ((1.0 + 3.0 / (e * e)) * atan e - 3.0 / e) / 2.0

/-- `q1(u, P, U)` with `E = lineareccentricity(P, U)/u`:
`3((1 + E^-2)*(1 - atan(E)/E)) - 1`, or `1` for a sphere (`Geophysics.jl:331, 337`). -/
def q1 (u : Float) (U : Sys := .Metric) : Float :=
  if P.isSphere then 1.0
  else
    let e := P.lineareccentricity U / u
    let i := 1.0 / e
    3.0 * ((1.0 + i * i) * (1.0 - atan e / e)) - 1.0

/-- `dynamicformfactor(P)`, `J₂` (cached). -/
@[inline] def dynamicformfactor : Float := P.j2

/-- The formula of `dynamicformfactor(P) = (1 - 2m*e′/15q0)*f*(2 - f)/3`, the second
dynamic form factor `J₂` (`Geophysics.jl:349-350`); `0` for a sphere. -/
def dynamicformfactorRaw : Float :=
  if P.isSphere then 0.0
  else
    let f := P.flattening
    (1.0 - 2.0 * P.oblateness * P.eccentricity2 / (15.0 * P.q0)) * f * (2.0 - f) /
      3.0

/-- `secondzonalharmonic(P) = -J₂/sqrt(5)`, the normalized `C̄₂₀`
(`Geophysics.jl:362`). For a sphere Julia divides the integer `-0 = 0`, giving `+0.0`. -/
def secondzonalharmonic : Float :=
  if P.isSphere then 0.0 else -P.dynamicformfactor / Float.sqrt 5.0

/-- Julia `_gravity(ϕ, P, U)`: Hirvonen's closed form of normal gravity at geodetic
latitude `ϕ` (`Geophysics.jl:364-372`). -/
def gravityNormal (ϕ : Float) (U : Sys := .Metric) : Float :=
  let β := P.latitudeparametric ϕ
  let m := P.oblateness
  let a := P.semimajor U
  let b := P.semiminor U
  let q := m * P.eccentricity2 * P.q01 / (3.0 * P.q0)
  let sβ := sin β
  let cβ := cos β
  let x := a * sβ
  let y := b * cβ
  let g := P.gravitation U / (a * Float.sqrt (x * x + y * y))
  g * ((1.0 + q) * (sβ * sβ) + (1.0 - m - q / 2.0) * (cβ * cβ))

/-- `_gravity(0, P, U)`: normal gravity at the equator (cached for Metric). -/
def gravityEquator (U : Sys := .Metric) : Float :=
  if U == .Metric then P.geM else P.gravityNormal 0.0 U

/-- `_gravity(π/2, P, U)`: normal gravity at the pole (cached for Metric). -/
def gravityPole (U : Sys := .Metric) : Float :=
  if U == .Metric then P.gpM else P.gravityNormal halfπ U

/-- Julia `gravity(ϕ, P, U)`: Somigliana's normal gravity at geodetic latitude `ϕ`
(`Geophysics.jl:387-390`). At the standard latitude `1.0111032235724π/4` it is
`9.80665` exactly on Earth. -/
def gravity (ϕ : Float) (U : Sys := .Metric) : Float :=
  let s := sin ϕ
  let sϕ2 := s * s
  if U == .Metric then
    -- the planet constants of the formula are cached (Julia folds them)
    P.geM * ((f64! 1.0 + P.somK * sϕ2) / Float.sqrt (f64! 1.0 - P.somE * sϕ2))
  else
    let ge := P.gravityEquator U
    let gp := P.gravityPole U
    let f := P.flattening
    ge * ((f64! 1.0 + (P.aspectratio * (gp / ge) - f64! 1.0) * sϕ2) /
      Float.sqrt (f64! 1.0 - (f * (f64! 2.0 - f)) * sϕ2))

/-- The altitude factor of `gravitygeodetic`, `2*(1 + f + m - 2f*sin(ϕ)^2)`. -/
def geodeticSlope (ϕ : Float) : Float :=
  let f := P.flattening
  let s := sin ϕ
  2.0 * (1.0 + f + P.oblateness - 2.0 * f * (s * s))

/-- `gravitygeodetic(h, ϕ, P, U) = g(ϕ)*(1 - 2*(1 + f + m - 2f*sin(ϕ)^2)*h/a + 3*(h/a)^2)`
(`Geophysics.jl:397-400`). -/
def gravitygeodetic (h ϕ : Float) (U : Sys := .Metric) : Float :=
  let ha := h / P.semimajor U
  P.gravity ϕ U * ((1.0 - P.geodeticSlope ϕ * ha) + 3.0 * (ha * ha))

/-- `gravitycomponents(h, θ, P, U)`: the (tangential, radial) components of gravity
at geocentric latitude `θ` and altitude `h` (`Geophysics.jl:407-413`). -/
def gravitycomponents (h θ : Float) (U : Sys := .Metric) : Float × Float :=
  let r := P.radius θ U + h
  let ar := P.semimajor U / r
  let j2ar := 3.0 * P.dynamicformfactor * (ar * ar)
  let sθ := sin θ
  let cθ := cos θ
  let g := P.gravitation U / (r * r)
  let ω := P.angularfrequency U
  let ωc := ω * cθ
  (g * j2ar * sθ * cθ + r * (ω * ω) * sθ * cθ,
   g * (1.0 - j2ar / 2.0 * (3.0 * (sθ * sθ) - 1.0)) - r * (ωc * ωc))

/-- Julia `_gravity(h, θ, P, U) = norm(gravitycomponents(h, θ, P, U))`
(`Geophysics.jl:415`; StaticVectors' `norm` is `sqrt(x^2 + y^2)`). -/
def gravityNorm (h θ : Float) (U : Sys := .Metric) : Float :=
  let (x, y) := P.gravitycomponents h θ U
  Float.sqrt (x * x + y * y)

end Planet

/-- Julia `Planet(f, a, t, Gm)` (`Geophysics.jl:75`) from Julia payloads, with the
derived constants that Julia folds at compile time computed once. -/
def Planet.of (f a t Gm : JNum) : Planet :=
  let p : Planet := { f := f.toFloat, a := a.toFloat, t := t.toFloat, Gm := Gm.toFloat,
                      fJ := f, aJ := a, tJ := t, GmJ := Gm }
  let p := { p with ecc := p.eccentricityRaw }
  let p := { p with ecc2 := p.eccentricity2Raw, aspect := p.aspectratioRaw,
                    obl := p.oblatenessAt halfπ .Metric }
  let p := { p with q0v := p.q0Raw, q01v := p.q01Raw }
  let p := { p with j2 := p.dynamicformfactorRaw }
  let p := { p with geM := p.gravityNormal 0.0 .Metric, gpM := p.gravityNormal halfπ .Metric }
  let f := p.flattening
  { p with somK := p.aspectratio * (p.gpM / p.geM) - 1.0, somE := f * (2.0 - f) }

/-- Earth, the WGS 84 spheroid (`Geophysics.jl:76`, `planets.jl:29`). -/
def Earth : Planet :=
  .of (.float (1.0 / 298.257223563)) (.float 6378137.0) (.float 86164.098903691)
    (.float 3.986004418e14)

/-- `_gravity(0, π/2)`: the component norm at the pole on Earth in Metric (a constant
of `gravity(h, θ, P, U)`). -/
def earthPoleNorm : Float := Earth.gravityNorm 0.0 halfπ

namespace Planet

variable (P : Planet)

/-- Julia `gravity(h, θ, P, U) = _gravity(h, θ, P, U)*(1 + ((gp - gp0)/3gp)*sin(θ)^2)` with
`gp = _gravity(π/2, P, U)` (normal gravity at the pole) and `gp0 = _gravity(0, π/2)`
(the component norm at `h = 0`, `θ = π/2` on **Earth** in Metric, as written in
`Geophysics.jl:422-425`). -/
def gravityAt (h θ : Float) (U : Sys := .Metric) : Float :=
  let gp := P.gravityPole U
  let gp0 := earthPoleNorm
  let s := JuliaBase.F64.sin θ
  P.gravityNorm h θ U * (1.0 + ((gp - gp0) / (3.0 * gp)) * (s * s))

end Planet

end Geophysics

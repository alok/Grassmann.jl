# Porting spec: chakravala applied/misc packages → Lean 4

Scope: **Geophysics.jl** (planet ellipsoids, gas thermodynamics, standard atmospheres), **FlowGeometry.jl** (airfoil profiles, NACA families, structured meshes), **Clifford.jl** (sparse-multivector extension, never wired up), **Heisenberg.jl** (empty stub).

Sources (all at latest master, cloned under `/Users/alokbeniwal/chakravala/`):

| Package | Version | Last upstream commit | Source LOC |
|---|---|---|---|
| Geophysics.jl | 0.3.8 | 381a792 (2024-04-23) "changed AbstractTensors to StaticVectors" | 1498 (`src/Geophysics.jl` 890, `src/chemistry.jl` 444, `src/planets.jl` 164) |
| FlowGeometry.jl | 0.1.5 | 395ab65 (2025-08-04) "deprecated Requires" | 831 + 162 in `ext/` |
| Clifford.jl | 0.1.0 | 7044335 (2020-09-09) "initialized Clifford extension" | 364 (**none of it is loaded**) |
| Heisenberg.jl | 0.1.0 | 490632d (2019-01-29) "generated package files" | 5 (`greet()` only) |

Oracle environment. I made a separate env, `scratchpad/juliaenv-applied` (a copy of the shared `juliaenv` Project and Manifest, plus `Pkg.develop` of the local Geophysics and FlowGeometry clones and an offline `UnicodePlots` add). The shared env was not modified. Julia 1.13.0, UnitSystems 0.3.9, StaticVectors 1.0.9, Grassmann 0.8.46 (registered), Cartan 0.4.16. All numbers below were **re-run in that env**; I note where they differ from README text.

Oracle artifacts produced by this study, all under `scratchpad/`:

* `oracle/applied-misc/oracle_applied_misc.jl` writes the goldens. Usage: `julia --startup-file=no --project=scratchpad/juliaenv-applied oracle/applied-misc/oracle_applied_misc.jl <outdir>`.
* `oracle/applied-misc/geophysics.json` (1.2 MB) and `oracle/applied-misc/flowgeometry.json` (1.4 MB) are the goldens (schema in §9).
* `oracle/applied-misc/plots_applied_misc.jl` writes the reference PNGs in `notes/applied-misc-plots/` (`fg_airfoils.png`, `fg_profiles.png`, `fg_joukowski.png`, `fg_rakich_mesh.png`, `geo_atmosphere.png`, `geo_gravity.png`). It also writes UnicodePlots text goldens `oracle/applied-misc/unicodeplot_{NACA4_24_40,ClarkY_12_40,NACA_2412}.txt`, which are braille plots usable for LeanPlot text-backend cross-tests.

---

## 1. Purpose & scope

### 1.1 Geophysics.jl

The package summary is "Planetary science data for atmospheric geophysical models" (README.md:3). It has three layers:

1. **Planet ellipsoid geodesy** (`src/Geophysics.jl:66-425`): an oblate reference ellipsoid given by flattening `f`, semimajor `a`, sidereal period `t` and GM. It provides derived shape constants, latitude conversions, radius, rotation speed, the Hirvonen zonal functions, J2, Somigliana normal gravity and gravity components with altitude. Data for 13 bodies is in `src/planets.jl:26-38`.
2. **Gas chemistry and thermodynamics** (`src/chemistry.jl`): monatomic, diatomic, triatomic, pentatomic and "Sutherland" ideal gases with Sutherland-law viscosity and conductivity, and Einstein-function vibrational heat capacity. Mole-fraction `Mixture`s are built with `*` and `+`. `FluidState(T, P)` gives derived properties.
3. **Layered standard atmospheres** (`src/Geophysics.jl:427-884`, data `src/planets.jl:87-164`):
   * `Atmosphere{n,P,U}` is a table of lapse rates and base geopotential altitudes.
   * `Weather{ϕ,f,n,P,U}` is that table integrated hydrostatically from a sea-level state at geodetic latitude ϕ.
   * About 21 property functions and 20 "ratio" functions of geometric altitude are provided.
   * Models: US 1922/1925/1956/1959/1962/1966/1976, each in Metric and English. `Standard` defaults to Earth1959 Metric.

Unit handling goes through UnitSystems.jl. With `usingSimilitude = false` (`src/Geophysics.jl:37`), `Quantity(D,U,x) = x` and `normal(x) = x` (UnitSystems.jl `src/UnitSystems.jl:95,181`), so every computation is plain Float64 arithmetic multiplied by unit-conversion factors.

### 1.2 FlowGeometry.jl

The package summary is "Geometry for computational fluid dynamics flows with Grassmann.jl elements" (README.md:3). It provides:

* 1-D **profiles** (camber lines and thickness distributions) evaluated at a chord fraction x ∈ [0,1], with slopes (`src/profiles.jl`).
* **Airfoils** combining camber and thickness under the "American" and "British" conventions, symmetric and double arcs, and the Joukowski map (`src/airfoils.jl`).
* A `NACA"…"` string macro that parses NACA 4-, 5-, 16- and 6A-series designations.
* Structured meshing helpers: rectangle triangulation, the Rakich stretched mesh, rectangle–circle boundary points, icosahedron/sphere refinement, a brute-force 2-D convex hull, and a 3-D wing surface (`src/FlowGeometry.jl`).
* Plotting and meshing extensions for Makie, UnicodePlots, MiniQhull, TetGen and MATLAB (`ext/`).

Points are homogeneous `Chain{Submanifold(ℝ^3),1}(1.0, x, y)`, i.e. the v₁ weight is 1. Fields are Cartan `TensorField`s over `interval(p) = range(x0, c, length=p)`.

### 1.3 Clifford.jl

The README says "Geometric algebra extension for Grassmann in Julia" (README.md:2). `src/Clifford.jl:1-8` only defines `greet()`. The other three files (`algebra.jl`, `multivectors.jl`, `products.jl`) are **never `include`d**. They hold code carved out of an older Grassmann (v0.5–0.7 API): **`SparseChain{V,G,T}`**, a k-vector with `SparseVector` storage, and **`MultiGrade{V,G}`**, a multivector stored as a tuple of homogeneous-grade parts with grade bitmask `G`. The code depends on APIs that no longer exist (`TensorTerm`, `Simplex`, `mvec`, `FixedVector`, `SymField`, `insert_expr`, `generate_mutators`, …). Current Grassmann still *exports* the names `SparseChain` and `MultiGrade` (`Grassmann.jl/src/multivectors.jl:16`) but defines neither. **What Clifford adds conceptually: sparse graded storage.** Nothing is runnable. §2.3 and §4.3 give a semantic spec so a Lean `Grassmann.Sparse` module can be written later if wanted.

### 1.4 Heisenberg.jl

`src/Heisenberg.jl:1-5` contains `module Heisenberg; greet() = print("Hello World!"); end`. Project.toml has no deps. The last commit is from 2019. **Nothing to port.** At most, reserve the namespace.

---

## 2. Public API inventory

Notation: "file:line" is relative to the package root. The ASCII alias column lists the ASCII spelling where one exists. Names marked **(stale)** are exported but undefined. Names marked **(broken)** are defined but throw at runtime (verified in the oracle).

### 2.1 Geophysics.jl

#### 2.1.1 Types

| Name | Def | Description |
|---|---|---|
| `Planet{f,a,t,Gm}` | Geophysics.jl:74 | Empty struct. All data is in the type parameters: flattening `f` (Float64, or the Int `0` for spheres), semimajor `a` [m], sidereal period `t` [s] (negative = retrograde), `Gm` [m³ s⁻²]. |
| `Planet(f,a,t,Gm,U=Metric)` | :75 | Constructor. `Quantity` wrappers are identity. |
| `Atmosphere{n,P,U}` | :435-440 | Fields `a::Values{n,Float64}` (lapse rate per layer; may be ±Inf), `h::Values{n,Float64}` (layer base geopotential altitude), `m::Values{n,Float64}` ("molar rate", always zeros, unused). `P` is the Planet instance, `U` the UnitSystem. |
| `Atmosphere{P,U}(a,h,m)` | :439 | Inner constructor. |
| `Atmosphere(a,h)` = `Atmosphere{Earth}(a,h)` | :451 | |
| `Atmosphere{P}(a,h)` = `Atmosphere{P,Metric}(a,h)` | :452 | |
| `Atmosphere{P,U}(a,h)` | :453 | `m = zeros`. |
| `(U::UnitSystem)(A::Atmosphere)` | :454 | Converts `a` via `lapserate.(a,U,S)` and `h` via `length.(h,U,S)`. |
| `Weather{ϕ,f,n,P,U}` | :477-485 | Fields `A::Atmosphere{n,P,U}`, `T,p,ρ::Values{n,Float64}` (temperature, pressure, density at each layer base), `Tc::Float64`, `ha::Float64` (1976 elliptic-layer parameters, else 0). `ϕ` is the geodetic latitude (Float64) and `f` the fluid instance (a Mixture or gas). |
| `Weather{ϕ}(A,F::FluidState)` | :496-546 | Hydrostatic layer integration (§4.1.6). |
| `(A::Atmosphere)(T, p=atm, ϕ=1.0111032235724*π/4)` | :549 | `Weather{ϕ}(A, Air(T,p,units(A)))`. |
| `(A::Atmosphere)(F=Air(288.16,atm,US(A)),r,g)` | :548 | **(broken)**: `ϕ` is undefined in the body. |
| `(U::UnitSystem)(W::Weather)` | :486 | **(broken)**: calls a 4-arg `Weather{ϕ,f}` constructor, but the inner constructor needs 6 args. |
| `(W::Weather)(h::Real=0)` | :550 | Returns a `FluidState{fluid(W),units(W)}(T,p)` at geometric altitude `h`. |
| `(W::Weather)(hG,i)` | :551-554 | Same, at geopotential altitude `hG` in layer `i`. |
| `abstract type AbstractMole{M}` | chemistry.jl:26 | `M` = relative molar mass (dimensionless, g/mol numerically). |
| `abstract type MoleGas{M,μ,Tμ,k,Tk} <: AbstractMole{M}` | chemistry.jl:68 | μ, k are the internal Sutherland prefactors (§4.1.2); Tμ, Tk are the Sutherland temperatures. |
| `AtomicGas{M,μ,Tμ,k,Tk}` | :167 | Monatomic gas, cᵥ = 3R/2. |
| `DiatomicGas{M,ν,μ,Tμ,k,Tk}` | :168 | ν is the vibrational wavenumber [m⁻¹]. |
| `TriatomicGas{M,ν1,ν2,μ,Tμ,k,Tk}` | :169 | Two vibrational modes. |
| `PentatomicGas{M,μ,Tμ,k,Tk}` | :170 | **Not exported.** No `heatvolume` method, so every thermal function throws. |
| `SutherlandGas{M,cᵥ,μ,Tμ,k,Tk}` | :171 | Constant cᵥ. **(broken)**: `heatvolume` recurses infinitely (StackOverflow). `show` also overflows the stack. |
| `AtomicGas(M,μ0,Tμ,k0,Tk,T0=288.16,U=Metric)` etc. | :173-192 | Constructors taking the reference μ0, k0 at T0 (§4.1.2). |
| `Mixture{M,N,C} <: AbstractMole{M}` | :252-254 | **Not exported.** Field `f::Values{N,Float64}` holds mole fractions. `C` is a tuple of gas instances. `M = f ⋅ relativemass.(C)`. |
| `Mixture{N,C}(f)`, `Mixture{C}(f)` | :256-257 | |
| `FluidState{f,u}` | :288-291 | Fields `T::Float64`, `P::Float64`. `f` is the fluid instance and `u` the UnitSystem. |
| `(G::Gas)(T=288.15, P=atm, U=Metric)` | :293-295 | Defined for SutherlandGas, Mixture, AtomicGas, DiatomicGas, TriatomicGas. Returns `FluidState{G,U}(T,P)`. |
| `(U::UnitSystem)(F::FluidState)` | :298 | Unit conversion of T and P. |

#### 2.1.2 Operators

| Op | Def | Semantics |
|---|---|---|
| `*(f::Float64, G::AbstractMole{M})` | chemistry.jl:273 | Returns `Mixture{M,1,(G,)}(Values(f))`. **The M param of a 1-component mixture is the pure gas M, not f·M.** |
| `+(m::Mixture...)` | :275-278 | Concatenates constituents and fractions in argument order and recomputes `M = f ⋅ M_i`, summing left to right. No normalisation of fractions. |
| `getindex(M::Mixture, i)` | :263 | Returns the i-th constituent gas. |
| `length(M::Mixture)` | :262 | Returns N. |
| `getindex(W::Weather, i::Int, U=units(W))` | Geophysics.jl:565-568 | Returns the tuple `(T,a,h,p,ρ)` of layer i, converted to U. |
| `getindex(W, ::Val{i})` | :569 | |

There are no unicode operators. Unicode *identifiers* with ASCII aliases: `N₂≡N2≡Nitrogen`, `O₂≡O2≡Oxygen`, `CO₂≡CO2≡CarbonDioxide`, `CH₄≡CH4≡Methane`, `H₂≡H2≡Hydrogen`, `Ar≡Argon`, `Ne≡Neon`, `He≡Helium`, `Kr≡Krypton`, `Xe≡Xenon` (planets.jl:55-57). Weather field `ρ` has no ASCII alias; use `rho` in Lean. `ϕ` is a type parameter; use `phi`.

#### 2.1.3 Planet functions

The defaults `P=Earth`, `U=Metric` apply where shown. All are `@pure`.

| Function | Def | Formula |
|---|---|---|
| `flattening(P=Earth)` | :88 | `f` |
| `semimajor(P=Earth,U=Metric)` | :100 | `a·length(Metric,U)` |
| `period(P=Earth,U)` | :112 | `t·time(Metric,U)` |
| `gravitation(P=Earth)` | :124 | `Gm` |
| `gravitation(P,U)` | :125 | `Gm/(length(U,Metric)·specificenergy(U,Metric))` |
| `mass(P,U=Metric)` | :137 | `gravitation(P,U)/gravitation(U)`, where `gravitation(U)` is Newton's G from UnitSystems |
| `frequency(P,U)` | :149 | `1/period` |
| `angularfrequency(P,U)` | :161 | `2π/period` |
| `meanradius(P,U)` (not exported) | :163 | `radius_fast(asin(sqrt(1/3)))` |
| `radius_fast(θ,P,U)` (internal) | :164 | `a·(1 - f·sin(θ)^2)` |
| `semiminor(P,U)` | :176 | `radius_fast(π/2)` = `a(1-f)` |
| `eccentricity(P)` | :188 | `sqrt(f(2-f))` |
| `eccentricity2(P)` | :200 | `e/(1-f)` (second eccentricity e′) |
| `lineareccentricity(P,U)` | :207 | `a·e` |
| `aspectratio(P)` | :219 | `semiminor/semimajor` |
| `authalicradius(P,U)` (not exported) | :221 | `sqrt((a² + b²·atanh(e)/e)/2)` |
| `latitudegeodetic(θ,P=Earth)` | :228 | `atan(tan(θ)/(1-f)^2)` |
| `deflectiongeodetic(θ,P)` | :229 | `latitudegeodetic(θ)-θ` |
| `latitudegeocentric(ϕ,P=Earth)` | :236 | `atan(tan(ϕ)(1-f)^2)` |
| `deflectiongeocentric(ϕ,P)` | :237 | `latitudegeocentric(ϕ)-ϕ` |
| `latitudeparametric(ϕ,P=Earth)` | :244 | `atan(tan(ϕ)(1-f))` |
| `deflection(h,ϕ,P=Earth,U)` | :251-254 | `f·sin(2ϕ)·(1 - f/2 - h/radiusgeodetic(ϕ,P,U))` |
| `latitudegeocentric(h,ϕ,P=Earth,U)` | :261 | `ϕ - deflection(h,ϕ,P,U)` (4-arg form) |
| `radius(θ,P,U=Metric)` | :268 | `1/sqrt((cos θ/a)² + (sin θ/b)²)` (geocentric θ) |
| `radiusgeodetic(ϕ,P=Earth,U)` | :275-278 | `a·(1 - f/2·(1-cos 2ϕ) + 5f²/16·(1-cos 4ϕ))` |
| `speed(θ,P,U)` | :291 | `radius(θ)·ω·cos θ` |
| `centripetal(θ,P=Earth,U)` | :299 | `radius(θ)·ω²·cos θ` |
| `gravity(P::Planet,U=Metric)` | :306 | `GM/a²` (spherical estimate) |
| `oblateness(θ,P=Earth,U)` | :313 | `(radius(θ)·ω²)/gravity(P,U)/gravity(U)`; `gravity(U)` is g_c (1 in Metric) |
| `oblateness(P=Earth,U)` | :325 | `oblateness(π/2,P,U)` = `ω²a²b/GM` |
| `q0(P)` | :328 | `((1+3/e′²)·atan(e′) - 3/e′)/2` |
| `q01(P)` | :329 | `3((1+1/e′²)(1 - atan(e′)/e′)) - 1` |
| `q(u,P,U)` | :330 | `E=lineareccentricity/u`: `((1+3/E²)atan E - 3/E)/2` |
| `q1(u,P,U)` | :331 | `3((1+E⁻²)(1-atan(E)/E)) - 1` |
| `q0/q01/q/q1` for `Planet{0}` | :334-337 | Return `1`. **Dispatch is on the literal Int `0`, not `0.0`.** |
| `dynamicformfactor(P=Earth)` | :349 | `(1 - 2m·e′/(15 q0))·f(2-f)/3` (J2), with `m = oblateness(P)` |
| `dynamicformfactor(::Planet{0})` | :350 | `0` |
| `secondzonalharmonic(P)` | :362 | `-J2/sqrt(5)` (C̄₂₀) |
| `_gravity(ϕ,P=Earth,U)` (internal) | :364-372 | Hirvonen normal gravity, §4.1.1 |
| `gravity(ϕ::Real,P::Planet,U=Metric)` | :387-390 | Somigliana closed form, §4.1.1 |
| `gravitygeodetic(h,ϕ,P=Earth,U)` | :397-400 | `g(ϕ)·(1 - 2(1+f+m-2f sin²ϕ)·(h/a) + 3(h/a)²)` |
| `gravitycomponents(h,θ,P=Earth,U)` | :407-413 | `Values(gθ, gr)`, §4.1.1 |
| `_gravity(h,θ,P=Earth,U)` (internal, same name!) | :415 | `norm(gravitycomponents(h,θ,P,U))` |
| `gravity(h,θ,P=Earth,U)` | :422-425 | `_gravity(h,θ)·(1 + ((gp-gp0)/(3gp))·sin²θ)` with `gp=_gravity(π/2,P,U)` (**normal gravity at pole**) and `gp0=_gravity(0,π/2)` (**component-norm at h=0, θ=π/2 on Earth**, Metric) |

#### 2.1.4 Planet constants

planets.jl:26-38. Arguments are `Planet(f, a[m], t[s], Gm)`:

| Name | f | a | t | Gm |
|---|---|---|---|---|
| Sun | 0.00005 | 696342e3 | 25.38·24·60² | 1.32712440018e20 |
| Mercury | 0 (Int) | 2439.7e3 | 1407.5·60² | 2.2032e13 |
| Venus | 0 | 6051.8e3 | −243.025·24·60² | 3.24859e14 |
| Earth | 1/298.257223563 | 6378137.0 | 86164.098903691 | 3.986004418e14 |
| Moon | 0.0012 | 1738.1e3 | 27.321661·24·60² | 4.9048695e12 |
| Mars | 0.00589 | 3396.2e3 | 1.025957·24·60² | 4.282837e13 |
| Jupiter | 0.06487 | 71492e3 | 9.925·60² | 1.26686534e17 |
| Saturn | 0.09796 | 60268e3 | 38018 (Int) | 3.7931187e16 |
| Uranus | 0.02293 | 25559e3 | −0.71833·24·60² | 5.793939e15 |
| Neptune | 0.01708 | 24764e3 | 16.11·60² | 6.836529e15 |
| Pluto | 0 | 1188.3e3 | 6.38723·24·60² | 8.71e11 |
| Ceres | 0 | 469.73e3 | 9.074170·60² | 6.26325e10 |
| Eris | 0 | 1163e3 | 349.44·60² | 1.108e12 |

`Earth` is also defined at Geophysics.jl:76 (the same value, redefined at planets.jl:29).

#### 2.1.5 Gas and chemistry functions

chemistry.jl. `T` is absolute temperature in the unit system `U`. `G::MoleGas` unless noted.

| Function | Def | Formula |
|---|---|---|
| `relativemass(x::AbstractMole)` (not exported) | :33 | `M` |
| `molarmass(M::AbstractMole,U=Metric)` | :40 | `molarmass(U)·M` (`molarmass(Metric)=0.001`, `(English)=1`) |
| `molecularmass(M,U=Metric)` | :47 | `molarmass(M,U)/avogadro(U)` |
| `gasconstant(M,U=Metric)` | :54 | `universal(U)/molarmass(M,U)` (`universal`≡`molargas`) |
| `lightspeed, planck, planckreduced, electronmass, boltzmann, vacuumpermeability, rationalization, lorentz, luminousefficacy, gravity, radian` `(M::AbstractMole,U=Metric)` | :56-60 | Forward to `op(U)` (every `UnitSystems.Constants` except `molarmass`) |
| `viscosity(G)` / `sutherlandviscosity(G)` | :75-76 | Type params μ, Tμ |
| `viscosity(G,U)` / `sutherlandviscosity(G,U)` | :78-79 | `μ·viscosity(Metric,U)`, `Tμ·temperature(Metric,U)` |
| `thermalconductivity(G)` / `sutherlandconductivity(G)` (+`U` forms) | :86-90 | Type params k, Tk |
| `viscosity(T,G,U=Metric)` | :96-102 | `((2μ)/sqrt(Tμ))·(sqrt(T)/(1+Tμ/T))` |
| `thermalconductivity(T,G,U=Metric)` | :96-102 | Same formula with k, Tk |
| `viscond(μ0,Tμ,k0,Tk,T0=288.16,U)` (internal) | :104-109 | `μ = μ0·sqrt(Tμ)·(T0+Tμ)/(2T0^1.5)`, same for k |
| `heatratio(M::AbstractMole,U)`, `heatvolume(M,U)`, `heatpressure(M,U)` | :111-113 | Evaluated at `temperature(288.16,U,Metric)` |
| `heatpressure(T,G,U=Metric)` | :120 | `heatvolume(T,G,U)+gasconstant(G,U)` |
| `heatratio(T,G,U=Metric)` | :127 | `gasconstant(G,U)/heatvolume(T,G,U) + 1` |
| `specificenergy(T,G::AbstractMole,U)` | :134 | `heatvolume(T,G,U)·T` |
| `specificenthalpy(T,G,U)` | :141 | `heatpressure(T,G,U)·T` |
| `freedom(T,G,U)` | :148 | `heatvolume(T,G,U)·(2/gasconstant(G,U))` |
| `prandtl(T,G,U)` | :155 | `gravity(U)·μ(T)·cp(T)/k(T)` (g_c factor; 1 in Metric) |
| `sonicspeed(T,G,U)` | :162 | `sqrt((R·gravity(U)·γ(T))·T)` |
| `wavenumber(G::DiatomicGas)` | :199 | `ν` |
| `wavenumber(G::TriatomicGas)` | :200 | `(ν1,ν2)` |
| `wavenumber(G,U)` | :202 | `wavenumber(G).*wavenumber(Metric,U)` |
| `wavelength(G,U=Metric)` (not exported) | :209 | `inv.(wavenumber(G,U))` |
| `frequency(G,U=Metric)` | :216 | `wavenumber(G,U).*lightspeed(U)` |
| `vibration(G,U=Metric)` | :223 | `frequency(G,U).*(planck(U)/boltzmann(U)/1.2)`. **Note the /1.2.** |
| `vibration(x::AbstractFloat)` | :224 | Einstein function `x²eˣ/(eˣ-1)²` |
| `heatvolume(T,G::AtomicGas,U)` | :234 | `(3/2)·R` |
| `heatvolume(T,G::SutherlandGas)` | :235-236 | `cᵥ`. **(broken)**: the U form recurses. |
| `heatvolume(T,G::DiatomicGas,U)` | :237-240 | `R·(5/2 + vibration(θ/T))` |
| `heatvolume(T,G::TriatomicGas,U)` | :241-245 | `R·(5/2 + vib(θ1/T) + vib(θ2/T))` |
| `chemical(M::Mixture)` (internal) | :259 | Constituent tuple `C` |
| `molecules(M)` (internal) | :260 | `Values(C)` |
| `fractions(M)` (internal) | :261 | `M.f` |
| `heatratio(T,M::Mixture,U)` | :264 | `heatpressure/heatvolume` of the mixture |
| `viscosity, thermalconductivity, heatvolume, heatpressure (T,M::Mixture,U)` | :266-268 | `fractions ⋅ [op(T,Cᵢ,U)]` (mole-fraction average of per-mass quantities) |
| `viscosity, thermalconductivity, sutherlandviscosity, sutherlandconductivity (M::Mixture,U)` | :269-271 | `fractions ⋅ [op(Cᵢ,U)]` |
| `units(F::FluidState)` | :297 | `u` |
| `fluid(F)` | :305 | `f` |
| `temperature(F)`, `temperature(F,U)` | :312-313 | `F.T`, converted |
| `pressure(F)`, `pressure(F,U)` | :320-321 | `F.P`, converted |
| `molecularmass, gasconstant, <Constants…> (F::FluidState,U=units(F))` | :323-325 | Forwarded to `fluid(F)` |
| `viscosity, thermalconductivity, heatvolume, heatpressure, heatratio, prandtl, sonicspeed, freedom, specificenergy, specificenthalpy (F,U=units(F))` (the `Intrinsic` tuple, Geophysics.jl:55) | :326-328 | `op(temperature(F,U),fluid(F),U)` |
| `density(F,U)` | :395 | `(P/T)/R` |
| `specificvolume(F,U)` | :402 | `1/ρ` |
| `kinematic(F,U)` | :409 | `μ/ρ` |
| `heatcapacity(F,U)` | :416 | `cp·ρ` |
| `thermaldiffusivity(F,U)` | :423 | `k/(cp ρ)` |
| `elasticity(F,U)` | :430 | `γ·P` |
| `specificimpedance(F,U)` | :437 | `ρ·a` |
| `intensity(F,U)` | :444 | **(broken)**: calls the undefined `impedance(F,U)`. The intent is `P²/(ρ a)`. |

`show(io, G::MoleGas)` is at :94, with `gastext` at :92 and :247-250 (§5).

#### 2.1.6 Gas constants

planets.jl:45-83. The last constructor arguments are (μ0 [Pa·s], Tμ [K], k0 [W/m/K], Tk [K]) at T0=288.16; wavenumbers are in m⁻¹.

| Name | Constructor call |
|---|---|
| `Nitrogen` | `DiatomicGas(28.013, 2744e2, 1.735e-5, 107, 25.11e-3, 150)` |
| `Oxygen` | `DiatomicGas(31.999, 2061e2, 1.999e-5, 139, 25.33e-3, 240)` |
| `Argon` | `AtomicGas(39.948, 2.187e-5, 144, 17.23e-3, 170)` |
| `CarbonDioxide` | `TriatomicGas(44.01, 2565e2, 1480e2, 14.45e-5, 222, 15.8e-3, 1800)` |
| `Neon` | `AtomicGas(20.18, 3.078e-5, NaN, 48.29e-3, NaN)`. NaN Sutherland T, so viscosity is NaN. |
| `Helium` | `AtomicGas(4.003, 2.928e-5, NaN, 152.07e-3, NaN)` |
| `Methane` | `PentatomicGas(16.042, 10.74e-5, NaN, 32.7e-3, NaN)` |
| `Krypton` | `AtomicGas(82.798, 2.432e-5, NaN, 9.12e-3, NaN)` |
| `Hydrogen` | `DiatomicGas(2.016, 4342e2, 0.866e-5, 97, 180.1e-3, 120)` |
| `Xenon` | `AtomicGas(131.293, 2.229e-5, NaN, 5.27e-3, NaN)` |
| `air` | `SutherlandGas(28.965923, 720, 1.7894e-5, 110.4, 0.02531, 194, 288.16)` (**broken**) |
| `Nitrox` ≡ **`Air`** | `0.7808093N₂+0.2094552O₂+0.009338Ar+0.0003975CO₂`, so `M = 28.965696264700004`. `Air` is the default fluid of every atmosphere. |
| `Traces` | `0.726803Ne+0.20966He+0.04006Kr+0.019824H₂+0.003653Xe` |
| `MainGases` (not exported) | `0.7808089N₂+0.2094551O₂+0.009338Ar+0.0003976CO₂+4.96e-7·H₂` |
| `TraceGases` (not exported) | `0.7415Ne+0.2139He+0.040871Kr+0.003729Xe` |
| `AirMix` | 9 components. `M = 28.96545433597889`. Viscosity is NaN because Ne and others have NaN parameters. |

`AirEnglish` **(stale)**: exported, never defined. `layers` (planets.jl:130) is an unused tuple of layer names.

#### 2.1.7 Atmosphere tables

planets.jl:87-123. `a` is the lapse rate in K/m (Metric) or °R/ft (English). `h` is the layer base in m or ft.

| Name | n | a | h |
|---|---|---|---|
| US22 | 2 | −6.5e-3, 0 | 0, 11e3 |
| US25 | 2 | −6.5e-3, 0 | 0, 10.76923e3 |
| US56 | 9 | −6.5,0,3,0,−3.9,0,3.5,10,5.8 (e-3) | 0,11,25,47,53,75,90,126,175 (e3) |
| US59 (= ARDC) | 11 | −6.5,0,3,0,−4.5,0,4,20,10,5,3.5 (e-3) | 0,11,25,47,53,79,90,105,160,170,200 (e3) |
| US62 | 21 | −6.5,0,1,2.8,0,−2,−4,0,3,5,10,20,15,10,7,5,4,3.3,2.6,1.7,1.1 (e-3) | 0,11,20,32,47,52,61,79,90,100,110,120,150,160,170,190,230,300,400,600,700 (e3) |
| US66 | 9 | −6.5,0,1,2.8,0,−2,−3.9,0,3 (e-3) | 0,11,20.1,32.2,47.3,52.4,61.6,80,90 (e3) |
| US76 | 11 | −6.5,0,1,2.8,0,−2.8,−2,0,**−Inf**,12,**+Inf** (e-3) | 0,11,20,32,47,51,71,86,91,110,120 (e3) |
| US22E | 2 | −3.5658e-3, 0 | 0, 36089 |
| US25E | 2 | −3.5658e-3, 0 | 0, 35332 |
| US56E | 9 | −3.5658,0,1.64584,0,−2.1397,0,1.92024,5.4864,3.1821 (e-3) | 0,36089,82021,154199,173885,246063,295276,413386,574147 |
| US59E (= ARDCE) | 11 | −3.5658,0,1.64584,0,−2.46876,0,2.19456,10.9728,5.4864,2.7432,1.92024 (e-3) | 0,36089,82021,154199,173885,259176,295276,344488,524934,557743,656168 |
| US62E | 9 | −3.5658,0,0.54864,1.53612,0,−1.09728,−2.1946,0,1.6459 (e-3) | 0,36089,65617,104987,154199,170604,200131,259186,295276 |
| US66E | 9 | −3.5658,0,0.54864,1.53612,0,−1.09728,−2.1397,0,1.6459 (e-3) | 0,36089,65945,105643,155184,171916,202100,262467,295276 |
| US76E | 7 | −3.5658,0,0.54864,1.53612,0,−1.53612,−1.09728 (e-3) | 0,36089,65617,104987,154199,167323,232940 |

Every `h[1]` is literally `-00e3` or `-0.`, i.e. **negative zero**.

Weather presets (planets.jl:135-141):

| Presets | Metric state | English state |
|---|---|---|
| `Earth1922/1925/1956/1959` and `…English` | T0=288.16 K | T0=518.69 °R, p0=2116.2 lbf/ft² |
| `Earth1962/1966/1976` and `…English` | T0=288.15 K | T0=518.67 °R, p0=2116.2 |

All Metric presets use p0=atm=101325 Pa and ϕ=1.0111032235724·π/4 = 0.7941186147990025.

`Standard` (planets.jl:143-164) is chosen at load time:

* `ENV["STDATM"]` ∈ {"1922","1925","1956","1959","1962","1966","1976"} picks the year. Any other value throws `error("unsupported STDATM environment")`.
* `ENV["GEOUNITS"]=="english"` picks the English model.
* The default is `Earth1959`.

#### 2.1.8 Weather functions

Geophysics.jl. Every function below has the calling forms:

```text
op(h::Real, W::Weather=Standard, U=US(W))   # h geometric, in U units.
                                            # Computes hG = altgeopotent(h,W,U); i = layer(hG,W,U); op(hG,i,W,U)
op(W::Weather=Standard, U=Metric)           # = op(0,W,U).  NOTE default U=Metric even for an English W
op(h::Real, W, U, S)                        # h given in S units, result in U: op(length(h,U,S),W,U)
op(hG::Real, i, W=Standard, U=units(W))     # layer-level primitive
```

| Function | Def | Primitive formula |
|---|---|---|
| `temperature` | :647-661 | §4.1.7 |
| `pressure` | :735-744 | `p_i·(a==0 ? exp((-g/R)·(hG-h0)/T) : (T/T0)^((-g/R)/a))` |
| `density` | :751-761 | `ρ_i·(a==0 ? exp(same) : (T/T0)^((-g/R)/a-1))` |
| `kinematic` | :768-770 | `viscosity(T,f,U)/density` |
| `heatcapacity` | :777-780 | `heatpressure(T,f,U)·density` |
| `thermaldiffusivity` | :787-791 | `k/cp/ρ` |
| `elasticity` | :798-801 | `γ·p` |
| `specificimpedance` | :808-811 | `ρ·a_sound` |
| `intensity` | :818-828 | `(p_i²/ρ_i)·(a==0 ? exp(..) : t^(2gRa)/t^(gRa-1))/sonicspeed`, with `t=T/T0`, `gRa=(-g/R)/a` |
| `specificweight` | :842 | `density(hG,i,W,U)·gravity(hG,W,U)`. **Gravity is evaluated at hG as if it were geometric.** |
| `specificvolume` | :849 | `1/density` |
| `viscosity, thermalconductivity, heatvolume, heatpressure, heatratio, prandtl, sonicspeed, freedom, specificenergy, specificenthalpy` (Intrinsic) | :665-668 | `op(temperature(hG,i,W,U), fluid(W), U)` |
| `<op>ratio` for every op above **except `heatcapacity`** (20 functions: `temperatureratio`, `pressureratio`, `densityratio`, `specificweightratio`, `specificvolumeratio`, `specificimpedanceratio`, `thermaldiffusivityratio`, `intensityratio`, `kinematicratio`, `elasticityratio`, `viscosityratio`, `thermalconductivityratio`, `heatvolumeratio`, `heatpressureratio`, `heatratioratio`, `prandtlratio`, `sonicspeedratio`, `freedomratio`, `specificenergyratio`, `specificenthalpyratio`) | :874-883 | `op(hG,i,W,U)/op(W,U)`, i.e. divided by the value at h=0 |

Other Weather helpers:

| Function | Def | Formula |
|---|---|---|
| `lapserate(h,W=Standard)` (UnitSystems name, not exported by Geophysics) | :570 | `W.A.a[layer(h,W)]` |
| `layer(h,W=Standard)` | :571 | §4.1.5 |
| `layer(h,W,U)` | :572 | `layer(length(h,units(W),U),W)` |
| `Planet(W)`, `units(W)`, `fluid(W=Standard)` | :574-576 | |
| `latitude(W=Standard)` (not exported) | :583 | `ϕ` |
| `radius(W=Standard,U=US(W))` | :590 | `radiusgeodetic(ϕ,Planet(W),U)` |
| `gravity(W=Standard,U=units(W))` | :597 | `gravity(ϕ,Planet(W),U)` (Somigliana). **This is 9.80665 exactly for the Standard ϕ** (English: 1.0 lbf/lbm). |
| `molecularmass(W,U)`, `gasconstant(W,U)` | :599-600 | Of `fluid(W)` |
| `altabs(h=0,W,U)` (not exported) | :609-610 | `radius(W,U)+h` |
| `altgeopotent(h,W,U)` (not exported) | :617-618 | `(h/altabs(h,W,U))·radius(W,U)` |
| `altgeometric(hG,W,U)` (not exported) | :625-626 | `r/(r/hG-1)` |
| `gravity(h::Real,W=Standard,U=US(W))` | :633-639 | `h ≤ 0.007·radius(W)` ? `(g(W,U)·r²)/(r+h)²` : `gravitygeodetic(h,ϕ,P,U)`. Note `radius(W)` in the test is in **W's** units. |
| `gravity(h,W,U,S)` | :640 | |
| `geopotential(h,W,U)` (not exported) | :856-858 | `gravity(h,W,U)·h` |
| `display(A::Atmosphere)`, `display(W::Weather)` | :456-461, :556-563 | §5 |
| `gage(P,P0=pressure())` (internal) | :32 | `P-P0` |

Other exports: `units` (UnitSystems), and `Metric, English, British` (UnitSystem instances re-exported, :34). **Name clash:** FlowGeometry also exports an airfoil type `British`.

### 2.2 FlowGeometry.jl

#### 2.2.1 Profile types

`abstract type Profile{P}` (profiles.jl:26), where `P::Int` is the number of sample points. Every profile is callable: `p(x)` gives y at chord fraction x, and `p(x,c,x0=0)` gives `profile(p,x,c,x0)`.

| Type | Def | Params | Notes |
|---|---|---|---|
| `FlatPlate{p}` | :57-66 | | `y≡0`, slope ≡ 0 |
| `ParabolicArc{t,p}` | :70-77 | `t` = thickness in % (`ParabolicArc{p}()` gives t=6) | |
| `CircularArc{t,p}` | :81-102 | t in % (default 6) | Slope also accepts a `Chain` x (uses `x[2]`) |
| `ClarkY{t,te,p}` | :107-127 | t in %, te trailing-edge param in % (`ClarkY{t,p}()` gives te=0.21) | **This is the NACA 4-digit thickness polynomial.** |
| `Thickness{t,x,te,p}` | :132-148 | t %, x = max-thickness location in tenths (default 3), te % (default **te = t/100**, i.e. y_te = t%·t/100) | Coefficients from a 5×5 solve, precomputed via `@generated` |
| `Modified{t,m,te,p}` | :153-185 | t %, m = two digits "IM" (I = LE-radius index, M = max-thickness tenths), te % (default 0.2) | `Modified{t,p}()` gives m=63. NACA "modified 4-digit" thickness. |
| `NACA4{n,p}` | :190-219 | n = camber digits MP as Int (e.g. 24; `00` → 0) | |
| `NACA5{n,p}` | :224-268 | n = 3 digits CPR as Int (e.g. 230) | |
| `NACA6{c,n,p}` | :273-317 | Fields `a::Values{n}`, `Cl::Values{n}`; type param `c = 10·sum(Cl)` | `NACA6{c,p}()` gives `a=(1.0,)`, `Cl=(c/10,)`. `NACA6{p}(a,Cl)` builds a combined mean line. |
| `NACA6A{c,p}` | :322-338 | c = design-Cl digit | **(broken for x<0.87437)** |

#### 2.2.2 Profile functions

| Function | Def | Semantics |
|---|---|---|
| `profile(p::Profile)` | :28-31 | `TensorField(interval(p), p.(interval(p)))` (sampled field) |
| `profileslope(p::Profile)` | :32-35 | Same, sampling the slope |
| `profileangle(p::Profile)` | :36 | `atan.(profileslope(p))` |
| `profile(p,x)` | :37 | `p(x)` |
| `profile(p,x,c,x0=0)` | :38 | `c·profile(p,(x-x0)/c)` |
| `profileslope(p,x,c,x0=0)` | :39 | `profileslope(p,(x-x0)/c)` |
| `profileangle(p,x,c,x0=0)` | :40 | `atan(slope)` |
| `interval(p::Profile{P},c=1,x0=0)` | :41 | `interval(P,c,x0)` |
| `interval(p::Int,c=1,x0=0)` | :42 | `range(x0, c, length=p)`. **`c` is the END point, not the length.** |
| `doubleinterval(r)` (internal) | :43 | `r[1]:step(r):r[1]+2(r[end]-r[1])` (length 2p−1) |
| `points(N::Profile,c=1,x0=0)` (internal) | :44-46 | `Chain(1.0, interval(N,c,x0)[i], profile(N)[i])`. Note y is **not** scaled by c. |
| `p'` (Adjoint) | :51-53 | `(p')(x) = profileslope(p,x)` |
| `approx(x, coeffs)` (internal) | :15-18 | Power polynomial `Σ cᵢ xⁱ`, i from 0 |
| `AppendixI`, `AppendixII` (unused tables) | :48-49 | |

#### 2.2.3 Airfoil types

`abstract type Airfoil{p}` (airfoils.jl:15), where `p` is the number of outline points (2·profile_points − 2).

| Type | Def | Notes |
|---|---|---|
| `UpperArc{A,p}`, `LowerArc{A,p}` | :29-42 | Wrap an Airfoil as a Profile: `interval = real.(upper(a,c,x0))`, `profile = imag.(upper(a))`, `profileslope = Cartan.gradient(profile)`. `UpperArc(s::Airfoil)` sets p = `length(upper(s))`. |
| `SymmetricArc{S,P}` | :72-81 | `SymmetricArc(s::Profile{P})` gives P′ = 2P−2. upper = x + i·c·s(x), lower = x − i·c·s(x). **`complex`/`points` broken**: no `interval` method. |
| `DoubleArc{U,L,P}` | :90-99 | `DoubleArc(u::Profile{P}, l::Profile{Q})` gives P′ = P+Q−2. **`upperlower`, `complex`, `points` broken**: no `interval` method. `upper`/`lower` work. |
| `British{C,T,P}` | :108-122 | Thickness ⟂ chord. `British(c::Profile{P},t::Profile{P})` gives 2P−2. **`upper`/`lower`/`complex` broken**: `Vector*TensorField` has no method. `British{n,p}()` is also **broken** (refers to an undefined `Camber`). |
| `American{C,T,P}` | :131-146 | Thickness ⟂ camber line (standard NACA construction). The only fully working camber+thickness airfoil. `American{n,p}()` is **broken** (`Camber`). |
| `Joukowski{R,f,g,b,p}` | :171-183 | Conformal map of a circle |
| `Chord{p,c,x0}` | :20-25 | Unused, not exported |

#### 2.2.4 Airfoil functions

| Function | Def | Semantics |
|---|---|---|
| `chord(p)`, `chord(::Profile{p})`, `chord(::Airfoil{p})` | :44-46 | `range(0,0,length=p)` (zeros) |
| `upper(z,r)` / `lower(z,r)` | :47-48 | `U=z+r; U[end]=1` / `L=z-r; L[end]=1`. **The last point is forced to exactly `1+0im`.** |
| `upper(x,yc,dyc_dx,yt)` | :49 | `upper(x+im·yc, im·cis.(atan.(dyc_dx))·yt)` |
| `lower(x,yc,dyc_dx,yt)`, `upperlower(x,yc,dyc_dx,yt)` | :50-51 | Same construction |
| `upper(z::Profile,c=1,x0=0)` | :37 | `upper(interval(z,c,x0), profile(z)·(c·im))` |
| `upperlower(z::Profile,c,x)` | :52 | Profile form |
| `upperlower(z::Airfoil,c,x)` | :53 | `(upper(z,c,x), lower(z,c,x))` |
| `upperlower(z,r)` | :54 | |
| `complex(N::Airfoil)` | :56-59 | `TorusTopology(TensorField(doubleinterval(interval(N)), [U; reverse(L)[2:end]]))` (closed loop, 2p−1 samples). **In the current release it throws `UndefVarError: TorusTopology`**: the name lives in MeshTopology and is not imported. The oracle patches it with `Core.eval(FlowGeometry, :(const TorusTopology = Cartan.TorusTopology))`. |
| `points(N::Airfoil)` (internal) | :60-63 | Homogeneous points `Chain(1,Re z,Im z)` for `z = complex(N)[1:end-1]` (2p−2 points) |
| `camber(n)`, `thickness(n)` (British/American, internal) | :117-118, :140-141 | |
| `getprofiles(British)` | :122 | `(interval(n.c,c,x0), c·profile(n.c), chord(n.c), c·profile(n.t))` |
| `getprofiles(American)` | :145 | `(interval(n,c,x0), c·profile(n.c), profileslope(n.c), c·profile(n.t))` |
| `@NACA_str` | :150-167 | Macro; §4.2.4 |
| `joukowski(R,f,g,b,p)` (not exported) | :175 | |
| `interval(::Joukowski)` | :177 | `interval(2p-1, 2π)` = `range(0,2π,length=2p-1)` |
| `complex(::Joukowski)` | :179-183 | `z = R·cis.(θ) .- (f - g·im)`, `TensorField(θ, z .+ b^2 .* inv.(z))` |

#### 2.2.5 Mesh and point utilities

FlowGeometry.jl.

| Function | Def | Semantics |
|---|---|---|
| `initpoints(N::Profile)` | :38 | `Cartan.initpoints(interval(N))`, 1-D homogeneous points `Chain{⟨11_⟩}(1,x)` |
| `initedges(N::Profile)` | :39 | **(broken)**: Cartan `initpoint` method error |
| `edgeslist(p::PointCloud)` | :41-43 | `[(i, i%n+1) for i=1..n]` (closed polygon) |
| `edgeslist!(p,r)` | :44-48 | Appends points `r` to `p` in place. Returns the closed loop over the new indices `(l+1..l+n)`. |
| `addbound(e,r=rectangle(xn,xm,yn,ym))` | :52 | **(broken)**: default refers to undefined globals, and `[e; …]` has a convert error |
| `airfoilbox(n)` | :53 | **(broken)** |
| `airfoiledges(n)` | :54 | `edgeslist(PointCloud(points(n)))` |
| `rectcirc(n,xn,xm,yn,ym,c=(1,0,0))` | :56-80 | §4.2.6 |
| `rectangletriangle(i,m)`, `rectangletriangle(i,j,m)` | :86-90 | §4.2.5 |
| `rectangletriangles(m=51,JL=51)` | :93-95 | `SimplexTopology([rectangletriangle(i,JL) for i=1:2(m-1)(JL-1)], m·JL)` |
| `rectanglebounds(n=51,JL=51)` (not exported) | :96-99 | Boundary edge loop |
| `FittedPoint(k,JL=51)` | :101 | `Chain(1.0,(k-1)÷JL,(k-1)%JL)` (integer grid coordinates) |
| `RakichNewton(D=50,JL=51,Δy=6e-3)` | :107-114 | Stretching parameter κ, §4.2.7 |
| `Rakich(κ,j,y0=0,D=50,JL=51)` | :116 | |
| `RakichLine(y=0,D=50,JL=51,Δy=6e-3,κ=…)` | :117 | |
| `RakichPlate(::Profile{n},D=50,JL=51)` | :119-123 | |
| `RakichPoint(k,x,y,s,κ,JL)` (internal) | :125-128 | The default `JL=legnth(y)` has a typo but is never used |
| `rakichpoints(P=CircularArc{6,21}(),D=50,n=51,JL=51)` | :130-137 | |
| `initrakich(P=CircularArc{6,61}(),D=50,n=101,JL=51)` | :139-142 | Returns `(p(rectangletriangles(n,JL)), p(rectanglebounds(n,JL)))`, two Cartan `SimplexBundle`s |
| `square(x)`, `square(xn,xm)` (internal) | :148-149 | |
| `rectangle(xn,xm,yn,ym)` (internal) | :150-152 | 4 corners CCW from lower-left, homogeneous ℝ³ |
| `cube(x)`, `cube(xn,xm)` | :154-155 | |
| `box(xn,xm,yn,ym,zn,zm)` | :156-160 | 8 corners in ℝ⁴ homogeneous: bottom face CCW, then top face CCW |
| `icosahedron(a=1,b=a·φ)` | :162-167 | 12 vertices `(1,0,±a,±b)`, cyclic, in the listed order |
| `circlemid(x,r)` (internal, `@generated`) | :169-172 | `r·unit(x/2 - v₁) + v₁` (midpoint of a homogeneous sum, projected to radius r) |
| `sphere(r=1)` | :174 | `icosahedron(r/sqrt(1+φ²))` (vertices at radius r) |
| `sphere(fac::SimplexBundle,r=1,p=fullpoints(fac))` | :175-193 | 1→4 loop subdivision, midpoints pushed to the sphere, **no dedup of shared edge midpoints** |
| `wing(N::Airfoil,λ=0.7,σ=0.5)` (not exported) | :195-217 | 3-D wing surface, §4.2.8 |
| `convhull(p::PointCloud)`, `convhull(p,r)` (not exported) | :219-280 | O(n³) hull edges, §4.2.9 |
| `decsg(N::Airfoil)` | :282-289 | Builds a MATLAB decsg geometry, "R-A" (rectangle minus airfoil). Needs `MATLABExt`. |
| `cubesphere`, `spheresurf`, `spheremesh`, `cubemesh` | :291-294 | Stubs implemented in `ext/MiniQhullExt.jl:19-31` and `ext/TetGenExt.jl:19-20` |
| `arc`, `arcslope`, `chordedges` | :33, :105 | **(stale)** exports, undefined |

Extensions:

* `ext/MakieExt.jl:19-42`: `lines(N::Profile)` → `lines(profile(N))`; `lines(N::Airfoil)` → `lines(complex(N))`; `lines(N::DoubleArc)` → upper + mean line `(Im U + Im L)/2` + lower.
* `ext/UnicodePlotsExt.jl:19-40`: `lineplot` with the same semantics, but the Airfoil form also overlays the camber profile `N.c`. `Base.display(::Airfoil|::Profile)` prints `typeof` then the lineplot.
* `ext/MATLABExt.jl:19`: `decsg(args...) = mxcall(:decsg,1,args...)`.

### 2.3 Clifford.jl (dead code, API as written)

multivectors.jl:

| Name | Def | Semantics |
|---|---|---|
| `SparseChain{V,G,T} <: TensorGraded{V,G}` | :12-14 | Field `v::SparseVector{T,Int}` of length `binomial(N,G)` |
| `SparseChain{V,G}(v)` | :16 | |
| `chainvalues(V,m,::Val{G})` | :18-28 | For G∉{0,N}: if `(#zeros)/binomial(N,G) < fill_limit` (0.5, Leibniz `utilities.jl:107`) it returns a dense `Chain`, else a `SparseChain` of the nonzeros |
| `SparseChain(m::Chain)` and variants | :30-34 | `SparseChain{V}(v::Vector{<:TensorTerm})` builds a sparsevec from blade indices. `SparseChain(t::TensorTerm) = t`. |
| `show(io,::SparseChain)` | :36-59 | §5.3 |
| `==` | :61-64 | Same grade: termwise. Different grade: both zero. Vs `TensorTerm`: false. |
| `MultiGrade{V,G} <: TensorMixed{V}` | :68-70 | `@computed` field `v::Values{count_ones(G),TensorGraded{V}}`, where `G::UInt` is a grade bitmask (bit g ⇔ grade g present) |
| `terms`, `value` (concatenated values) | :78-79 | |
| Constructors from `Vector{TensorGraded}`, `Chain`, `MultiVector` | :81-96 | `MultiGrade(::MultiVector)` returns the dense MultiVector unchanged if `(#zeros)/2^N < fill_limit` |
| `show(io,::MultiGrade)` | :98-105 | Terms joined by `" + "`, zero(V) if empty |
| `==` (same G) | :122 | |
| `valuetype` | :124 | |
| `scalar`, `vector`, `volume`, `isscalar`, `isvector` | :127-131 | Pick the grade-0 / grade-1 / grade-N term, or `zero(V)` |
| `adjoint(::MultiGrade)` | :133 | Adjoint of each term over `dual(V)` |
| `valuetype`, `value(m,T)`, `scalar(::SparseChain{V,0})` | :145-149 | |
| `adjoint(::SparseChain)` | :155 | Over `dual(V)` |
| Exports | :142-143 | `basis, grade, hasinf, hasorigin, scalar, norm, gdims, betti, χ, valuetype, isscalar, vector, isvector, indices` (**mostly stale**) |

algebra.jl provides `+`/`-` (the pair `(op, eop)` ∈ {(+,+=), (−,−=)}):

| Signature | Def | Semantics |
|---|---|---|
| `SparseChain ± SparseChain` (same V,G) | :7-15 | Sparse vector add, keeping the denser operand as the base. Returns the other operand if one is empty. |
| `SparseChain ± TensorTerm` (same grade) | :16-20 | Scatter-add at `basisindex(N, bits(b))` |
| `TensorTerm/Chain ± SparseChain` | :22-24 | = `b + a`. **Wrong for `-`**: it gives b−… with the operands swapped, so the sign is lost. |
| `MultiGrade ± MultiGrade` | :26-52 | Merge by ascending grade; result mask `A|B` |
| `MultiGrade ± TensorGraded{V,B}` | :53-75 | Insert or add at grade B; mask `A|(1<<B)` |
| `SparseChain{V,A} ± TensorGraded{V,B}` (different grades) | :76 | `MultiGrade` of the two, ordered by grade. **The sign of the second operand is lost for `-`.** |

products.jl:

| Signature | Def | Semantics |
|---|---|---|
| `complementleft`, `complementright` (SparseChain, MultiGrade) | :5-10 | Termwise. The MultiGrade version builds a `SparseChain` with mask `G ⊻ ((1<<N)-1)`, which is a **bug**: it should flip grades g ↦ N−g. |
| `reverse`, `involute`, `conj`, unary `+`, unary `-` | :11-16 | Termwise. The MultiGrade version wrongly returns a `SparseChain`. |
| `generate_sums(Field,…)` | :18-105 | Metaprogramming that emits scalar `*` on MultiGrade (:28-29) and ± between SparseChain/MultiGrade and dense `MultiVector`/`Chain`, via `addmulti!(out, vals, binomsum(N,G)+nzind)` |
| `generate_products` | :111-119 | Only calls `generate_sums` |

### 2.4 Heisenberg.jl

`greet()` at src/Heisenberg.jl:3. There are no exports.

---

## 3. Data representations

### 3.1 Geophysics

**Compile-time vs runtime in Julia.** The following are type parameters, i.e. compile-time singletons: every `Planet` (f,a,t,Gm), every gas (M, ν, μ, Tμ, k, Tk, cᵥ), the Mixture's M, N and constituent tuple C, the Atmosphere's n, P and U, and the Weather's ϕ, f, n, P and U. `@pure` plus constant propagation folds most derived constants. The runtime payloads are the `Atmosphere` arrays (a,h,m), the `Weather` arrays (T,p,ρ, Tc, ha), the `Mixture` fractions f, and `FluidState` (T,P).

**Invariants, none enforced upstream:**

* `Atmosphere.h` is strictly increasing. The first entry is −0.0 in every table.
* The lengths of a and h agree; this is enforced by `Values{n}`.
* `n ≥ 1`.
* Mixture fractions are *not* normalised. Nitrox sums to 1.0000000; other mixtures sum to ≈1.
* `Weather.T/p/ρ[1]` is the sea-level state. `ρ[1] = p0/(R·T0)`.

**Layer semantics.** Layer i (1-based) has base altitude `h[i]`, lapse `a[i]` valid on (h[i], h[i+1]], and base state `T[i], p[i], ρ[i]`. The last layer extends to +∞. Layer 1 also covers h ≤ h[1] (negative altitudes extrapolate with a[1]).

**Units.** Every numeric field is in the unit system `U` of the Atmosphere. Conversions use UnitSystems factors. `f(S,U)` is the factor that multiplies an S-value to give a U-value, and `f(v,U,S) = v / f(U,S)` converts v from S into U. Values from `UnitSystems 0.3.9` (oracle `geophysics.json` → `units`):

| Quantity | Metric→English | English→Metric |
|---|---|---|
| length | 3.280839895013123 | 0.3048 |
| time | 1 | 1 |
| temperature | 1.7999999999999998 | 0.5555555555555556 |
| pressure | 0.02088543423315013 | 47.88025898033584 |
| density | 0.06242796057614463 | 16.018463373960138 |
| lapserate | 0.54864 | 1.8226888305628464 |
| specificenergy | 0.33455256331296856 | 2.98906692 |
| viscosity | 0.020885434233150132 | 47.88025898033583 |
| thermalconductivity | 0.12489385727761694 | 8.006798907468898 |
| specificentropy | 0.18586253517387144 | 5.380320456 |
| mass | 2.2046226218487757 | 0.45359237 |

Constants from UnitSystems (**not** the CODATA exact values; use these exact bits):

| Constant | Metric | English (lbm-ft-s-°R, "English Engineering") |
|---|---|---|
| universal R | 8.314462618153241 | 1545.3471008183458 |
| molarmass(U) | 0.001 | 1 |
| avogadro | 6.022140762070074e23 | 2.731597100740971e26 |
| gravity(U) (= g_c) | 1 | 32.17404855643044 |
| G | 6.674302101972535e-11 | 3.322928526687524e-11 |
| c | 2.99792458e8 | 9.835710564304461e8 |
| h | 6.62607015e-34 | 4.887138541095932e-34 |
| k_B | 1.3806489995254104e-23 | 5.657302463819266e-24 |
| atm | 101325.0 | 2116.2166236739367 |

g₀ = 9.80665. In English, "gravity" results come out in lbf/lbm (≈1.0), and density is in lbm/ft³.

**Ordering conventions:**

* `W[i]` returns `(T, a, h, p, ρ)`.
* `gravitycomponents` returns `(tangential/north, radial)`.
* Mixture constituent order is the order of the `+` arguments.
* `wavenumber(::TriatomicGas)` returns `(ν1, ν2)`.

### 3.2 FlowGeometry

**Compile-time in Julia:** the profile/airfoil sample count `p`; every profile parameter (t, te, x, m, n, c; possibly Float, e.g. `ClarkY{12.5}` from `NACA"2412.5"`); the Joukowski R,f,g,b; and `NACA6`'s c,n. **Runtime:** only `NACA6.a`, `NACA6.Cl` (Values), and the airfoil wrappers' contained profile instances (which are singletons anyway).

Coordinates:

* Chord fraction x ∈ [0,1]. Profiles return **0.0 outside [0,1]**. For NACA6 the cutoff is `x<1e-7 || x>1-1e-7`.
* `interval(p,c,x0) = range(x0,c,length=p)`: p samples from x0 to **c**.
* Airfoil outlines are complex numbers `x + i·y`. `upper`/`lower` run LE→TE with p samples, and the last sample is forced to `1+0i`.
* `complex(N)` has 2p−1 samples: the upper surface LE→TE, then the lower surface TE→LE excluding the duplicated TE. The first sample equals the last (both LE, 0+0i). Its base is `doubleinterval` = `0:1/(p-1):2`.
* `points(N)` gives 2p−2 homogeneous points `(1,x,y)`, with the duplicate LE removed.
* Joukowski: θ from 0 to 2π inclusive, 2p−1 samples. `points` gives 2p−2.

Mesh indexing (1-based):

* Structured grid point `k ↔ (column i = (k-1)÷JL + 1, row j = (k-1)%JL + 1)`, so `k = (i-1)·JL + j`. x varies by column, y (the stretched Rakich direction) by row.
* Triangles: two per cell, listed in the order produced by `rectangletriangle(i,JL)` for i = 1…2(m−1)(JL−1). Cells are ordered row-block by row-block (§4.2.5).
* `rectanglebounds` is a closed loop: column 1 bottom→top, then along the top row, then down the last column, then back along the bottom row.

### 3.3 Clifford

`SparseChain{V,G,T}` stores a `SparseVector{T,Int}` of length binomial(N,G). The index is the 1-based position of the blade in `indexbasis(N,G)`, which is Grassmann's canonical within-grade blade order (defined by the Leibniz/Grassmann port). `MultiGrade{V,G}` stores `count_ones(G)` graded terms sorted by ascending grade. Each term may be a TensorTerm (a single blade), a dense `Chain` or a `SparseChain`.

---

## 4. Algorithms

### 4.1 Geophysics

#### 4.1.1 Gravity models

**Hirvonen normal gravity** `_gravity(ϕ,P,U)` (Geophysics.jl:364-372). This is Julia-exact operation order:

```text
β  = atan(tan(ϕ)*(1-f))                       # parametric latitude
m  = oblateness(P)                            # ω²a²b/GM (Metric; see :313 for U≠Metric)
E  = a*e                                      # computed but unused
q  = m*e′*q01(P)/(3*q0(P))                    # Julia `m*eccentricity2(P)*q01(P)/3q0(P)`: 3q0 binds tighter
g  = GM/(a*sqrt((a*sin β)^2 + (b*cos β)^2))
return g*((1+q)*sin(β)^2 + (1-m-q/2)*cos(β)^2)
```

**Somigliana** `gravity(ϕ,P,U)` (:387-390):

```text
s2 = sin(ϕ)^2; ge = _gravity(0,P,U); gp = _gravity(π/2,P,U)
return ge*((1 + (aspectratio(P)*(gp/ge) - 1)*s2)/sqrt(1 - (f*(2-f))*s2))
```

Oracle values: Earth gives g(0) = 9.780325333855085 and g(π/2) = 9.832184939227085, matching WGS-84 to about 1e-9. The Standard latitude ϕ = 1.0111032235724·π/4 is chosen so that `gravity(ϕ,Earth) == 9.80665` exactly in Float64. **Test this bit-for-bit.**

For `Planet{0}` (f = Int 0), `q0=q01=1` and J2=0.

**Altitude gravity** `gravitygeodetic(h,ϕ)` (:397-400): `ha=h/a`, then `g(ϕ)*(1 - 2*(1+f+m-2f*sin(ϕ)^2)*ha + 3*ha^2)`.

**Components** `gravitycomponents(h,θ)` (:407-413), with geocentric θ:

```text
r = radius(θ,P,U) + h
J2ar = 3*J2*(a/r)^2
g = GM/r^2; ω = 2π/t
return (g*J2ar*sθ*cθ + r*ω^2*sθ*cθ,  g*(1 - J2ar/2*(3sθ^2-1)) - r*(ω*cθ)^2)
```

`gravity(h,θ,P,U)` (:422-425) is `norm(components)*(1 + ((gp-gp0)/(3gp))*sin(θ)^2)`, with gp and gp0 as in §2.1.3. Oracle: `gravity(1000,π/4,Earth)=9.803354299849625`, `gravitygeodetic(1000,π/4)=9.80311294321108`, `gravitycomponents(0,0)=[0.0, 9.780281645252511]`.

**Weather gravity** (:633-639): `h ≤ 0.007*radius(W)` gives `(g_W*r^2)/(r+h)^2`, otherwise `gravitygeodetic(h,ϕ,Earth,U)`. **There is a discontinuity at h ≈ 44,571 m**: 44,000 m gives 9.67250816941245 and 45,000 m gives 9.669266449918254.

#### 4.1.2 Gas constructors and Sutherland law

`viscond` (chemistry.jl:104-109) with `T1 = 2*(T0^1.5)` computes `μ = μ0*sqrt(Tμ)*(T0+Tμ)/T1` and stores it as the type parameter. The same applies to k. Then (:96-102):

```text
viscosity(T,G,U) = ((2*μ_U)/sqrt(Tμ_U)) * (sqrt(T)/(1 + Tμ_U/T))
```

This equals the standard Sutherland law `μ0·(T/T0)^{3/2}·(T0+S)/(T+S)`. Keep the operation order for exactness; the goldens allow 1e-14 relative. `Tμ_U = Tμ·temperature(Metric,U)` and `μ_U = μ·viscosity(Metric,U)`.

Examples at T=288.15 K, from the oracle: N₂ μ=1.7349535914662788e-5, k=0.02510926598657445; Air (Nitrox) μ=1.7995221548164308e-5, k=0.02507804197099703.

#### 4.1.3 Heat capacity

```text
R = universal(U)/(molarmass(U)*M)
θ = wavenumber*wavenumber(Metric,U)*lightspeed(U)*(planck(U)/boltzmann(U)/1.2)   # vibration(G,U)
Einstein(x) = (e=exp(x); x^2*e/(e-1)^2)          # ((x*x)*e)/((e-1)*(e-1)); x ≳ 355 → 0 or NaN (overflow), matches IEEE
Atomic:    cv = (3/2)*R
Diatomic:  cv = R*((5/2) + Einstein(θ/T))
Triatomic: cv = R*((5/2) + Einstein(θ1/T) + Einstein(θ2/T))
Mixture:   cv = Σ_i f_i*cv_i(T)   (left-to-right dot)
cp = cv + R   (MoleGas);   Mixture cp = Σ f_i*cp_i
γ  = R/cv + 1 (MoleGas);   Mixture γ = cp/cv
```

Oracle, N₂ at 288.15: cv=742.4438297200924, cp=1039.2511198408663, γ=1.399770700812037, a=345.99915908833685. Air at 288.15: cv=719.6311305945891, γ=1.4004723011173348, a=340.34680666426647, Pr=0.7231827174799603.

#### 4.1.4 Altitude conversions

`r = radiusgeodetic(ϕ)`, which is 6.3673029805857185e6 m for Standard.

* `hG = (h/(r+h))*r` (divide first, then multiply)
* `h = r/(r/hG - 1)`

Both are exact inverses over ℝ; the oracle stores the Float round-trip `altgeometric_of_hG`.

#### 4.1.5 Layer lookup

Geophysics.jl:571:

```text
layer(h) = h ≤ A.h[1] ? 1 : (j = findfirst(x -> x ≥ h, A.h); j === nothing ? n : j-1)
```

At an exact boundary h = A.h[k] (k>1) the result is k−1, the lower layer. Examples from the oracle: `layer.((-1,0,1,11000,11000.1,25000,200000,300000))` on Earth1959 gives `[1,1,1,1,2,2,10,11]`. Lean (0-based): `if h ≤ h₀ then 0 else match idx.findIdx? (· ≥ h) with | none => n-1 | some j => j-1`.

#### 4.1.6 Hydrostatic layer integration

`Weather{ϕ}(A,F)` (Geophysics.jl:496-546). Only T, p, ρ, Tc and ha are kept. The μ, k, c, Δμ, Δk and Δc arrays are dead computations; skip them.

```text
U = units; T0 = F.T; p0 = F.P
R = gasconstant(fluid,U); g = gravity(ϕ,P,U)        # Somigliana (= 9.80665 for Standard ϕ)
T[1]=T0; p[1]=p0; ρ[1]=p0/(R*T0); Tc=0.0; ha=0.0
for i in 2..n:
  Δh = h[i]-h[i-1]
  if isinf(a[i-1]):                                   # 1976 "elliptic" layer — FAITHFUL BUG:
     Tcur = T[i]                                      # still 0.0 (array initialised to zeros)
     Tc = (a[i]*Δh*Tcur + T[i-1]^2 - Tcur^2)/(h[i]*Δh + 2T[i-1] - 2Tcur)
     ha = Δh*(T[i-1]-Tc)/sqrt((T[i-1]-Tc)^2 - (Tcur-Tc)^2)
     T[i] = Tc + (T[i-1]-Tc)*sqrt(1-(Δh/ha)^2)
  else
     T[i] = T[i-1] + a[i-1]*Δh
  if a[i-1] == 0:  v = exp((-g/R)*Δh/T[i]); p[i]=p[i-1]*v; ρ[i]=ρ[i-1]*v
  else: t = T[i]/T[i-1]; gRa = -g/R/a[i-1]; p[i]=p[i-1]*t^gRa; ρ[i]=ρ[i-1]*t^(gRa-1)
```

`a = ±Inf` gives `gRa = ∓0.0`, so the pressure ratio is 1 and the density ratio is `1/t`. For US76 the result is garbage above 91 km: `Tc=1.6313692093470574e-5`, `ha=19000.000000000073`, `T[10]=3.2357551400325046e-5`, `ρ[10]=12.901319298080887`, `p[11]=2.376599340964436e-20`. Real US76 has Tc=263.19 K and A=−76.32 K. **The spec calls for a faithful port** (§8.4). Ship a flagged `Earth1976Fixed` later if wanted.

Oracle layer states for Earth1959: T = [288.16, 216.66000000000003, 216.66000000000003, 282.66, 282.66, 165.66000000000003, 165.66000000000003, 225.66000000000003, 1325.66, 1425.66, 1575.66] and p = [101325.0, 22632.490020212284, 2488.772621398659, 120.4563583100062, 58.32834953278311, 1.0096574685105715, 0.10446283649111857, 0.007454861913492818, 0.0003621319381400277, 0.00028246422925038334, 0.00014259382081873923]. The ρ values are in the JSON.

#### 4.1.7 Temperature at geopotential hG in layer i

Geophysics.jl:647-661:

```text
(T0,a0,h0) = (T[i],a[i],h[i]) converted to U
if isinf(a0):
   Δh = hG-h0
   if a0 < 0:  Tc + (T0-Tc)*sqrt(1-(Δh/ha)^2)        # Julia throws DomainError if negative; Lean sqrt gives NaN
   else:       r = radius(Earth1976)  # 6.3673029805857185e6 m, fixed Metric
               ξ = Δh*((r+h0)/(r+hG)); 1000 - (1000-T0)*exp((-0.012/(1000-T0))*ξ)
else: a0 == 0 ? T0 : T0 + a0*(hG-h0)
```

Pressure, density and intensity follow §2.1.8, with `g = gravity(W,U)` (sea-level Somigliana) and `R = gasconstant(W,U)`.

#### 4.1.8 Julia exceptions vs Lean NaN

Julia throws DomainError for `sqrt(<0)`, `log(<0)`, and `(neg)^(nonint)`. In Lean these produce NaN. The oracle records Julia errors as `{"error":…}`. **Lean tests must treat those entries as "expect NaN or skip".** The only atmosphere case is Earth1976English above ~178 km, where T < 0.

#### 4.1.9 Worked Standard (Earth1959) profile

From the oracle:

| h [m] | hG | layer | g | T | p | ρ | a_sound |
|---|---|---|---|---|---|---|---|
| −500 | −500.0392661749958 | 1 | 9.80819033902094 | 291.4102552301375 | 107477.95769172645 | 1.2848853024291107 | 342.26036318804125 |
| 0 | 0 | 1 | 9.80665 | 288.16 | 101325.0 | 1.2249904535333715 | 340.35269326515146 |
| 1000 | 999.8429722952806 | 1 | 9.803570410328458 | 281.6610206800807 | 89876.36320119529 | 1.1116511693111748 | 336.50428292372095 |
| 5000 | 4996.076771604212 | 1 | 9.791266546549824 | 255.68550098457266 | 54048.553885832414 | 0.7364237129154385 | 320.64401753820727 |
| 20000 | 19937.37575918728 | 2 | 9.745332748073912 | 216.66000000000003 | 5529.4703607054 | 0.08891081330650195 | 295.18081488564866 |
| 50000 | 49610.428242586764 | 4 | 9.65418240928256 | 282.66 | 87.86258612395723 | 0.0010829026454931404 | 337.09881971209944 |
| 100000 | 98453.7603959457 | 7 | 9.505330783810692 | 199.47504158378285 | 0.021377101503069967 | 3.7334474461633726e-7 | 283.235508681439 |
| 250000 | 240555.0644751545 | 11 | 9.080471698868491 | 1717.602725663041 | 6.143908886122951e-5 | 1.2461543366330106e-10 | 802.9324104008081 |

### 4.2 FlowGeometry

#### 4.2.1 Thickness families

All use `thickness(x,a,t) = (x<0||x>1) ? 0 : 5t·(Y(x)⋅a)` with basis `Y(x) = (√x, x, x², x³, x⁴)`. The slope uses `dY = (0.5/√x, 1, 2x, 3x², 4x³)`, which gives **+Inf slope at x=0**. Source: profiles.jl:112-120.

**ClarkY{t,te}** (:122-127) uses coefficients `clarky(te/100) = (0.2969, −0.1260, −0.3516+1e-16, 0.2843, te/100 − 0.1036)` and thickness t/100. The default te=0.21 gives the last coefficient −0.10149999999999999, which is the classic NACA open-TE `−0.1015`.

**Thickness{t,x,te}** (:142-148) solves the 5×5 system `M·a = rhs` with rows at X=x/10 and TS=`tailslope(X)`:

| Row | Constraint |
|---|---|
| Y(X) | 0.1 |
| dY(X) | 0 |
| Y(1) | te/100 |
| dY(1) | TS |
| Y(0.1) | 0.078 |

`tailslope(x) = −(31/200 + (151/300)x − (109/40)x² + (43/6)x³ − (5/2)x⁴)`. `riegel(x)` (:140) is defined but unused. Julia computes the solve by Cramer's rule with exterior products (Grassmann `composite.jl:722-735`). Any stable solver matches to about 1e-14.

**Modified{t,m,te}** (:153-185):

* Parameters (:173-175): `modified(P) = (t/100, i ≠ 9 ? i : 6√3, (m%10)/10, te/100)` with `i = m÷10`.
* For x ≥ p, `D(x) = (1, 1−x, (1−x)², (1−x)³)`. The rear coefficients d solve `[D(p); dD(p); D(1); dD(1)]·d = [0.1, 0, te, tailslope(p)]`.
* For x < p, `A(x)=(√x, x, x², x³)`. The front coefficients a solve `[A(p); dA(p); ddA(p); (1,1,1,1)]·a = [0.1, 0, ddD(p)⋅d, (1/(5t))·sqrt(2·radius(0.2·i/6))]`, where `radius(t) = t²·((0.2969/0.2)²/2)`.
* **The 4th row `(1,1,1,1)` looks like a bug**: the intent is `(1,0,0,0)` to pin a₀. As written, NACA 0012-64 has **negative thickness near the LE** (see `notes/applied-misc-plots/fg_airfoils.png`, panel "0012-64"). Port it faithfully.
* **Modified recomputes both solves on every call; precompute them in Lean.**

#### 4.2.2 Camber lines

**NACA4{n}** (:190-219):

* Decoding: `string(n, pad=2)` gives digits M,P, so m=M/100 and p=P/10.
* `naca4(m,p)` solves `[C(p); dC(p); C(0)]·c = (m,0,0)` for the front and `[C(p); dC(p); C(1)]·c = (m,0,0)` for the rear, with `C(x)=(1,x,x²)`.
* The value is `C(x)⋅c_front` if x<p, else `C(x)⋅c_rear`.
* p=0 (NACA 00xx) gives a singular front system: Julia Cramer produces NaN coefficients, which are never used. **Lean must not throw.**
* Oracle, `naca4coeffs(24)`: front `[0.0, 0.09999999999999998, -0.12499999999999997]`, rear `[0.01111111111111111, 0.044444444444444446, -0.05555555555555556]`.

**NACA5{n}** (:224-268). Digits C,P,R give `m=C/2` and `p=P/20`.

* Standard (R=0): `r = approx(p,(−1/250, 359/300, 7/10, 10/3, 0))`, `k1 = approx(p,(284037/200, −3296847/100, 4296829/15, −1087744, 4544800/3))`, `k1k2 = 0`.
* Reflexed (R=1): `r = approx(p,(17/500, 26/15, −2, 32/3))`, `k1 = approx(p,(72269/250, −583261/150, 89864/5, 83920/3))`, `k1k2 = approx(p,(10763/50000, 12081/25000, −87457/2500, 10691/125))`. **These fits do not reproduce the tabulated values: 231 gives y≈1.3.** Port them faithfully.
* The decode returns `(m·k1, r, k1k2)`. With `P=r`:

```text
y  = mk1*(P^3*(1-x) + (x<P ? (x-P)^3 - (k1k2≠0 ? k1k2*x*(1-P)^3 : 0)
                             : (k1k2≠0 ? k1k2*((x-P)^3 - x*(1-P)^3) : 0)))/6
dy = mk1*(-P^3 + (x<P ? 3(P-x)^2 - (k1k2≠0 ? k1k2*(1-P)^3 : 0)
                       : (k1k2≠0 ? 3k1k2*((P-x)^2-(1-P)^3) : 0)))
```

The dy expression is Julia-literal; note it **has no /6 in the slope**, whereas the true derivative carries a 1/6 factor. Oracle: `naca5(230) = (15.95699999999988, 0.20250000000000004, 0)`.

**NACA6** (:280-317). Decoding (:299-305), with `a1 = 1−a` and `a12 = a1²/2`:

```text
g = −((a²)(log(a)/2 − 1/4) + 1/4)/a1
h = (a12·log(a1) − a12/2)/a1 + g
return (Cl/(2π(1+a)), a, h, g)
```

For a=1, g and h are NaN (0/0) but unused.

* Value (:308-312): `sum(Cla .* naca6.(x,a,g′,h′))`, where the destructuring **swaps g and h**: the value path binds `(Cla,a,g′,h′) = (Cla,a,h,g)`.
* Kernel with a=1: `−((1−x)log(1−x) + x log x)`.
* Kernel with a≠1: `((ax²·log|ax| − x1²·log x1) + (x1²−ax²)/2)/(2a1) − x log x + g′ − h′x`.
* Slope (:313-317) destructures `(Cla,a,h)` correctly. Kernel with a=1: `log(1−x) − log x`. Kernel with a≠1: `(x1·log x1 − ax·log(ax))/(1−a) − log x − 1 − h`. It uses **`log(ax)` without abs**, so Julia throws DomainError for x>a.
* Guard: x<1e-7 or x>1−1e-7 returns 0.

**NACA6A{c}** (:327-338). For x ≥ 0.87437: `(c/(36π))·(0.34173943292855025 − 2.773248454778759·(x−0.87437))`, slope `−0.0245209c`. For x < 0.87437 it **throws** (Float + Values MethodError). The recommended Lean behaviour is in §8.4.

**ParabolicArc{t}**: `(t/25)x(1−x)`, slope `(1−2x)t/400`. **The slope is inconsistent with the value** (the true slope is (t/25)(1−2x)); port it faithfully.

**CircularArc{T}** (:87-100):

```text
t=T/100; r=(t + 1/(4t))/2           # Julia `1/4t` = 1/(4t)
y  = r*(sin(acos((x−1/2)/r)) − 1) + t
dy = −xc/sqrt((1 + t*t4)^2 − xc^2),  with t4=4t, xc=t4(2x−1)
```

y(0) ≈ −9.7e-17, not 0.

#### 4.2.3 Airfoil assembly

All forms use default c=1 and x0=0.

* **American** (airfoils.jl:142-146):
  * Inputs: `x = interval(camber,c,x0)`, `yc = c·camber(x_unit)`, `dyc = camberslope(x_unit)` (slope is not rescaled), `yt = c·thickness(x_unit)`.
  * `U = x + i·yc + i·e^{i·atan(dyc)}·yt`, so `U = (x − yt sinθ) + i(yc + yt cosθ)`.
  * `L = (x + yt sinθ) + i(yc − yt cosθ)`.
  * Then `U[end] = L[end] = 1+0i`.
  * With c≠1 and x0≠0 the x-range is `range(x0,c)`, which is inconsistent with the y scaling by c. The oracle key `upper_c2_x0_1` records this.
* **SymmetricArc** and **Profile** forms: `U = x + i·c·y(x)`, `L = x − i·c·y(x)`, then `[end]=1`.
* **British** (thickness ⟂ chord) is intended as `U = x + i(yc + yt)`, `L = x + i(yc − yt)`. **It throws in Julia.** See §8.4.

#### 4.2.4 NACA string grammar

The regexes are at airfoils.jl:152-155. They are tried in the order n5, n4, n16, n6A. Each is an **unanchored search** (the first match anywhere in the string). `D` denotes a digit and `NUM2 = DD(\.D+)?`.

| Family | Pattern | Result |
|---|---|---|
| **n5** | `(DD[01])(NUM2)-?` and, if a '-' was consumed, optionally `(NUM2)` | `British(NACA5{g1}, g3===nothing ? ClarkY{g2} : Modified{g2,g3})` |
| **n4** | `(DD)(NUM2)-?(NUM2)?` (same conditional) | `American(NACA4{g1}, g3 ? Modified{g2,g3} : ClarkY{g2})` |
| **n16** | `1(D)-` then an optionally parenthesised `(D(\.D+)?)` then an optionally parenthesised `(NUM2)` | `American(NACA6{g2}, Modified{g1,g3})` |
| **n6A** | `6(D)A`, then optionally parenthesised `(D(\.D+)?)` and `(NUM2)` | `American(NACA6A{g2}, Modified{g1,g3})` |

* Groups are converted by `Meta.parse`: "00" becomes 0, "12.5" becomes 12.5, and "010" becomes 10.
* The sample count is fixed at p=150, so the airfoil P is 298.
* On failure the macro throws `error("not valid")`, which surfaces as a LoadError at macro expansion.
* **The 16- and 6A-series map the parameters wrongly**: `Modified{t=g1 (the min-pressure digit), m=g3 (the thickness)}`. Port this faithfully and flag it.

Parse results (oracle `airfoils/*/type`):

| Input | Result |
|---|---|
| `2412` | `American{NACA4{24,150},ClarkY{12,0.21,150},298}` |
| `0012` | `American{NACA4{0,150},ClarkY{12,0.21,150},298}` |
| `23012` | `British{NACA5{230,150},ClarkY{12,0.21,150},298}` |
| `0012-64` | `American{NACA4{0,150},Modified{12,64,0.2,150},298}` |
| `24012-34` | `British{NACA5{240,150},Modified{12,34,0.2,150},298}` |
| `16-212` and `16-(2)(12)` | `American{NACA6{2.0,1,150},Modified{6,12,0.2,150},298}` |
| `65A012` | `American{NACA6A{0,150},Modified{5,12,0.2,150},298}` |
| `63A415` | `American{NACA6A{4,150},Modified{3,15,0.2,150},298}` |
| `2412.5` | `American{NACA4{24,150},ClarkY{12.5,0.21,150},298}` |
| `abc` | error |

#### 4.2.5 Rectangle triangulation

FlowGeometry.jl:86-99:

```text
rectangletriangle(i,m): i' = ((i-1) % (2(m-1))) + 1;  j = ((i-1) ÷ (2(m-1))) + 1
rectangletriangle(i',j,m): k = (j-1)*m + (i'÷2) + 1; n = m+k
                           odd i'  → (k, n, k+1)
                           even i' → (k, n-1, n)
rectanglebounds(n,JL): b = [1:JL:JL*n ; JL*(n-1)+2 : JL*n ; JL*(n-1) : -JL : JL ; JL-1 : -1 : 2 ; 1]
                       edges (b[i], b[i+1]), i = 1..len-1
```

Goldens: `rectangletriangles(3,3) = [[1,4,2],[2,4,5],[2,5,3],[3,5,6],[4,7,5],[5,7,8],[5,8,6],[6,8,9]]` and `rectanglebounds(3,3) = [[1,4],[4,7],[7,8],[8,9],[9,6],[6,3],[3,2],[2,1]]`. **Note the argument asymmetry:** `rectangletriangles(m,JL)` emits 2(m−1)(JL−1) triangles but calls `rectangletriangle(i,JL)`.

#### 4.2.6 rectcirc

FlowGeometry.jl:56-80: boundary points of a rectangle, spaced at equal angles about centre c. The default c is the homogeneous origin `(1,0,0)`.

```text
X = [yn, xm, ym, xn]; R = rectangle corners (ll, lr, ur, ul); rc = R − c
at_i = atan(rc_i.y/rc_i.x) + [π, 2π, 0, π]_i
out = []
for i in 1..4:
  push R_i
  Δ = ((at[i%4+1] − at[i] + 2π) rem 2π)/(n−1)
  for k in 1..n−2:
    θ = at[i] + k*Δ
    if i odd:  v = X[i] − c.y; push (1, v/tan θ, X[i])      # bug: missing + c.x
    else:      v = X[i] − c.x; push (1, X[i], v*tan θ)      # bug: missing + c.y
```

This gives 4(n−1) points. Golden: `rectcirc(4,−1,2,−1,1)` gives x,y = (−1,−1), (−0.155792,−1), (0.515917,−1), (2,−1), (2,−0.311583), (2,0.311583), (2,1), (0.515917,1), (−0.155792,1), (−1,1), (−1,0.267949), (−1,−0.267949).

#### 4.2.7 Rakich stretching

FlowGeometry.jl:107-142:

```text
RakichNewton(D,JL,Δy): κ=1; j=1/(JL−1)
  repeat 10 times: eκ=exp(κ); ejκ=exp(j*κ)
                   κ -= (((ejκ−1)*D − (eκ−1)*Δy)*(eκ−1)) / ((ejκ*(eκ*(j−1) − j) + eκ)*D)
  return κ
Rakich(κ,j,y0,D,JL) = y0 + (D−y0)*(exp(κ*(j−1)/(JL−1)) − 1)/(exp(κ) − 1)
RakichLine(y,D,JL,Δy) = [Rakich(κ,j,y,D,JL) for j in 1..JL], κ = RakichNewton(D−y,JL,Δy)
RakichPlate(P::Profile{n},D,JL):
  x = interval(n)
  r = RakichLine(−x[1], D, ((JL−n)÷2)+1, step(x))
  [−reverse(r); x[2:end−1]; r .+ ((x[1]>0 ? 2 : −1)*x[1] + x[end])]
rakichpoints(P::CircularArc{T,m},D,n,JL):
  t=T/100; x=RakichPlate(P,D,n); y=RakichLine(0,D,JL,t/10); s=P.(x)   (0 outside [0,1])
  κ_i = s_i≠0 ? RakichNewton(D−s_i,JL,t/10) : 0
  point k = (1, x[xk], s[xk]≠0 ? Rakich(κ[xk],yk,s[xk],y[end],JL) : y[yk])
            with xk=(k−1)÷JL+1, yk=(k−1)%JL+1
```

`ℯ^κ` is `exp(κ)`. Goldens: `RakichNewton(50,51,6e-3)=7.157340807983087` and `RakichLine(0,50,5,0.1)=[0.0, 0.09999999999999995, 0.8571738511896172, 6.590296260442787, 50.0]`.

#### 4.2.8 Wing surface

`wing(N,λ,σ)` (FlowGeometry.jl:195-217), with `U = imag(upper(N))`, `L = imag(lower(N))`, `np = length(U)`, `int = interval(N)` and `rint = reverse(int)`. It fills np×(2np−1) arrays:

| Columns | out1 | out2 | out3 |
|---|---|---|---|
| i < np | `σ·int[i] + (λ+(1−λ)rint[i])·int` | `int[i]` | `rint[i]·U` |
| i = np | `σ·int[np] + λ·rint[np]·int` | `int[np]` | 0 |
| i+np, i=1..np−1 | `σ·rint[i+1] + (λ+(1−λ)int[i+1])·int` | `rint[i+1]` | `int[i+1]·L` |

It returns `TensorField(int ⊕ (−1:step:1), Chain.(out1,out2,out3))`. This is a low-priority port.

#### 4.2.9 convhull

FlowGeometry.jl:219-280. For each ordered pair i≠j, keep the edge (i,j) iff no k∉{i,j} has either:

* `det[p_i,p_j,p_k] > 0` (the wedge trivector coefficient of the homogeneous points), or
* `det == 0` with `|(p_i+p_j)/2 − p_k| < |p_i − p_j|`.

`isapprox(x,0)` with default tolerances means exactly 0. Output is ordered by i, then j, and edges are clockwise. The `(p,r)` variant ignores k with `|avg−p_k| > r`. Golden for the square: `[[1,4],[2,1],[3,2],[4,3]]`.

#### 4.2.10 Sphere subdivision and Joukowski

**Sphere subdivision** (FlowGeometry.jl:175-193). For each face (v0,v1,v2), append the three edge midpoints `circlemid(p_a+p_b, r)`. Emit faces `(v0,v3,v5)`, `(v3,v1,v4)`, `(v4,v2,v5)`, `(v3,v4,v5)`, where v3..v5 are the new indices. Shared-edge midpoints are **duplicated**.

**Joukowski:** `w = z + b²/z` with `z = R e^{iθ} − f + i g`. Golden for `Joukowski{1.1,0.1,0.1,1.0,5}`, first samples: `1.99009900990099+0.000990099009900991i`, `1.2288885644313832+0.1641447281627615i`, … (9 samples).

### 4.3 Clifford: intended semantics

Spec for an optional port:

* **`SparseChain` densify rule:** for G∉{0,N}, keep dense storage if `nnz/binomial(N,G) > 1 − fill_limit`, i.e. fewer than 50% zeros.
* **`SparseChain ± SparseChain`:** sparse add; the result keeps the grade.
* **`MultiGrade ± MultiGrade`:** a two-pointer merge of grade-sorted term lists, adding terms of equal grade, with mask `A|B`.
* **`MultiGrade ± graded X` of grade B:** add to the existing grade-B term or insert it sorted; mask `A | (1<<B)`.
* **Scalar `*`:** termwise.
* **Involutions (`reverse`, `involute`, `conj`, `±`):** termwise, keeping the MultiGrade structure. The Julia code wrongly returns a SparseChain.
* **Complement:** termwise, grade g ↦ N−g, with the mask bit-reversed over N+1 bits. The Julia code XORs the mask instead.
* **`- a` for `(TensorTerm|Chain) − SparseChain`** must negate b; the Julia code is buggy.
* **Mixing with dense `MultiVector`:** scatter into the dense array at offset `binomsum(N,G) + index`, giving a dense MultiVector.
* **Accessors:** `scalar` returns the grade-0 term or 0; `vector` the grade-1 term; `volume` the grade-N term.

Everything else (products) was never implemented in Clifford.jl.

---

## 5. Display and printing

Julia float printing is shortest round-trip (Ryu) digits. The format is **plain decimal iff 1e-4 ≤ |x| < 1e6 or x == 0**; otherwise it is `d.ddde±N` with no `+` and no zero-padding (`1.0e6`, `7.249095243641474e-6`, `9.9e-5`, `0.0001`, `999999.0`, `-0.0`). Integer-valued floats print with `.0`. Type parameters that were Ints print as Ints (e.g. `Tμ=107`, `Planet{0, 2.4397e6, …}`). Arrays print as `[x, y, z]`. The LeanPlot/Grassmann port needs a `Float.toJuliaString` anyway; share it.

### 5.1 Geophysics

**`display(A::Atmosphere)`** (Geophysics.jl:456-461) prints:

```text
Atmosphere{11, Planet{0.0033528106647474805, 6.378137e6, 86164.098903691, 3.986004418e14}(), Metric}
 a = [-0.0065, 0.0, 0.001, 0.0028, 0.0, -0.0028, -0.002, 0.0, -Inf, 0.012, Inf]
 h = [-0.0, 11000.0, 20000.0, 32000.0, 47000.0, 51000.0, 71000.0, 86000.0, 91000.0, 110000.0, 120000.0]
 m = [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
```

The header is `typeof(A)`; the unit system prints as `Metric` (or `English`).

**`display(W::Weather)`** (:556-563) prints `typeof(W)`, then ` a = `, ` h = `, ` T = `, ` P = ` (capital P), ` ρ = `. For the Standard atmosphere the header is:

`Weather{0.7941186147990025, Geophysics.Mixture{28.965696264700004, 4, (DiatomicGas{M=0.028013000000000003,ν=3290.0031276899135,μ=7.249095243641474e-6,Tμ=107,k=0.01377350691159802,Tk=150}, DiatomicGas{M=0.031999,ν=2471.0992879624314,μ=1.0290352056080399e-5,Tμ=139,k=0.021184868801903053,Tk=240}, AtomicGas{M=0.039948000000000004,μ=1.1592952516691442e-5,Tμ=144,k=0.01052074197167278,Tk=170}, TriatomicGas{M=0.04401,ν₁=3075.3855767218033,ν₂=1774.491482864822,μ=0.00011227167433131875,Tμ=222,k=0.14307922297784512,Tk=1800})}([0.7808093, 0.2094552, 0.009338, 0.0003975]), 11, Planet{0.0033528106647474805, 6.378137e6, 86164.098903691, 3.986004418e14}(), Metric}`

The full text is in the oracle keys `weather/_display_Earth1959`, `_display_US76` and `_display_Earth1976English`.

**`show(io, G::MoleGas)`** (chemistry.jl:94, gastext :247-250) prints `gastext(G)` followed by `μ=$(viscosity(G)),Tμ=$(sutherlandviscosity(G)),k=$(thermalconductivity(G)),Tk=$(sutherlandconductivity(G))}`:

| Gas type | gastext prefix |
|---|---|
| AtomicGas | `AtomicGas{M=$(molarmass(G)),` (molarmass in kg/mol, e.g. `0.039948000000000004`) |
| DiatomicGas | `DiatomicGas{M=…,ν=$(vibration(G)),`. **The label "ν" holds the vibrational temperature in K**, e.g. `3290.0031276899135`. |
| TriatomicGas | `TriatomicGas{M=…,ν₁=…,ν₂=…,` |
| SutherlandGas | `Gas{M=…,cᵥ=…,cₚ=…,` (**StackOverflow**) |
| PentatomicGas | Fallback `gastext(::MoleGas)` at :92 references the undefined `G` (**UndefVarError**) |

Note `μ=` shows the internal half-prefactor (`viscond` output), e.g. N₂ `7.249095243641474e-6`, not the reference viscosity.

**Mixture** uses default struct show: `Geophysics.Mixture{M, N, (gas1, gas2, …)}([f1, f2, …])`.

**Planet** uses default show: `Planet{0.0033528106647474805, 6.378137e6, 86164.098903691, 3.986004418e14}()`.

**FluidState** uses default show.

Lean recommendation: implement `Repr`/`ToString` reproducing these strings (module-qualified `Geophysics.Mixture` included) for goldens. A nicer Lean-native format can sit behind a flag.

### 5.2 FlowGeometry

There is no custom `show`. Types print Julia-style, e.g. `American{NACA4{24, 150}, ClarkY{12, 0.21, 150}, 298}`; British prints module-qualified as `FlowGeometry.British{…}` when UnitSystems' `British` is also in scope. Homogeneous points print as Grassmann Chains, e.g. `1.0v₁ + 0.00533397v₂ + 0.0146749v₃`; that printer belongs to the Grassmann port.

With the UnicodePlots extension, `display(N)` prints the type, then a 40×15 braille lineplot. For an Airfoil it draws the closed outline plus the camber line. Exact text goldens (`:color=>false`) are `oracle/applied-misc/unicodeplot_*.txt`. The y-axis labels are UnicodePlots' rounded limits (e.g. `0.1`/`-0.1` for NACA 2412, `0.07`/`0` for ClarkY{12,40}).

### 5.3 Clifford

`show(::SparseChain)` (multivectors.jl:36-59):

* Print the first nonzero value, then `printindices(V, blade)`.
* Each further nonzero prints as `" + " value` or `" - " abs(value)`, depending on `signbit`, followed by its indices.
* Symbolic values (the `parsym` types) are parenthesised unless they are TensorTerms.

`show(::MultiGrade)` (:98-105) prints the terms joined by `" + "`.

---

## 6. Examples with expected outputs

### 6.1 Geophysics README (README.md:17-33, docs/src/index.md:17-33)

The README lists `h = 1000`, `gravity(h)`, `temperature(h)`, `pressure(h)` and `sonicspeed(h)`. **These values are stale** (≈1e-6 relative drift from an older version). Use the current oracle values as goldens:

| Expression | README (stale) | **Current oracle (golden)** |
|---|---|---|
| `gravity(1000)` | 9.803565306802405 | **9.803570410328458** |
| `temperature(1000)` | 281.66102237169474 | **281.6610206800807** |
| `pressure(1000)` | 89876.28158431675 | **89876.36320119529** |
| `sonicspeed(1000)` | 336.4347118683662 | **336.50428292372095** |

Also at h=1000: `density(1000)=1.1116511693111748`, `viscosity(1000)=1.767550795500286e-5`, `thermalconductivity(1000)=0.024586565889807482`, `kinematic(1000)=1.5900228815443372e-5`.

### 6.2 Docstring examples

These are the `$(…)` interpolations in Geophysics.jl:84-359, evaluated now:

| Expression | Value |
|---|---|
| `1/flattening(Earth)` | 298.257223563 |
| `semimajor(Earth)` | 6.378137e6 |
| `period(Earth)` | 86164.098903691 |
| `gravitation(Earth)` | 3.986004418e14 |
| `mass(Earth)` | 5.972166613228325e24 |
| `frequency(Earth)` | 1.1605761711936886e-5 |
| `angularfrequency(Earth)` | 7.292115146706924e-5 |
| `semiminor(Earth)` | 6.356752314245179e6 |
| `eccentricity(Earth)` | 0.08181919084262149 |
| `eccentricity2(Earth)` | 0.08209443794969568 |
| `aspectratio(Earth)` | 0.9966471893352525 |
| `speed(0,Earth)` | 465.1010942547186 |
| `oblateness(Earth)` | 0.003449786645650386 |
| `dynamicformfactor(Earth)` | 0.0010826297750872816 |
| `secondzonalharmonic(Earth)` | -0.000484166754312094 |
| `gravity(0,Earth)` | 9.780325333855085 |
| `gravity(π/2,Earth)` | 9.832184939227085 |

Extra values:

| Expression | Value |
|---|---|
| `lineareccentricity(Earth)` | 521854.00842338527 |
| `q0(Earth)` | 7.334625787080995e-5 |
| `q01(Earth)` | 0.0026880413004335413 |
| `meanradius(Earth)` | 6.371008771415059e6 |
| `authalicradius(Earth)` | 6.371007180918474e6 |
| `gravity(Earth)` (GM/a²) | 9.7982854791873 |
| `latitudegeodetic(π/4)` | 0.7887565820736097 |
| `latitudegeocentric(π/4)` | 0.7820397447212868 |
| `latitudeparametric(π/4)` | 0.7837189445894065 |
| `deflection(1000,π/4)` | 0.003346663443643893 |
| `radius(π/4,Earth)` | 6.3674177249666825e6 |
| `radiusgeodetic(π/4)` | 6.367489468874128e6 |
| `speed(π/4,Earth)` | 328.3234192700388 |
| `centripetal(π/4)` | 0.02394172178677658 |
| `oblateness(π/4)` | 0.0034555747257357106 |
| `semimajor(Earth,English)` | 2.0925646325459316e7 |
| `gravity(Earth,English)` | 0.9991470562513498 |

### 6.3 Geophysics tests (test/runtests.jl:1-19)

The tests are equalities between the no-argument defaults and the `Standard(0)` FluidState: `gravity()==gravity(0)`, `temperature()==temperature(Standard(0))`, `pressure()==pressure(Standard(0))`, and similarly for thermalconductivity, elasticity, viscosity, specificenergy, specificenthalpy and sonicspeed. Density, specificvolume, heatcapacity, thermaldiffusivity, prandtl and specificimpedance are commented out (they are not bit-identical). Defaults: `gravity()=9.80665`, `temperature()=288.16`, `pressure()=101325.0`, `density()=1.2249904535333715`, `sonicspeed()=340.35269326515146`, `viscosity()=1.7995711613000002e-5`.

### 6.4 Planets

Selected oracle values:

| Body | g_eq = GM/a² | J2 | g(ϕ=0) | g(ϕ=π/2) |
|---|---|---|---|---|
| Mars | 3.713171690162161 | 0.0023948796967583385 | 3.7095333306736937 | 3.7302207920888844 |
| Jupiter | 24.786520258758614 | 0.014528944635550932 | 23.1240559136831 | 26.976777016698684 |
| Saturn | 10.442942201367597 | 0.015927052810586106 | 9.031256445774009 | 12.065940912192431 |

Venus (f=0, retrograde t): ω=−2.9923691869737844e-7, J2=0.

### 6.5 English and cross-unit evaluation

| Expression | Value |
|---|---|
| `temperature(1000.0 ft, Earth1959English)` | 515.1243706851109 °R |
| `pressure(1000.0 ft, Earth1959English)` | 2040.8413578766783 |
| `density(1000.0 ft, Earth1959English)` | 0.07426002316679299 lbm/ft³ |
| `sonicspeed(1000.0 ft, Earth1959English)` | 1112.812273217821 ft/s |
| `gravity(1000.0 ft, Earth1959English)` | 0.9999042677515543 lbf/lbm |
| `temperature(1000.0, Standard, English, Metric)` | 506.9898372241452 |
| `temperature(Earth1959English)` | 288.16111111111115 (default U=Metric) |

### 6.6 FlowGeometry

No README examples exist; test/runtests.jl only checks `1 == 1.0`. Oracle profile values at x = 0, 0.0125, 0.1, 0.25, 0.3, 0.4, 0.5, 0.75, 0.9, 1.0 (values outside [0,1] are 0.0):

| Profile | y at those x |
|---|---|
| ParabolicArc{6,5} | 0.0, 0.0029625000000000003, 0.0216, 0.045, 0.05039999999999999, 0.0576, 0.06, 0.045, 0.021599999999999994, 0.0 |
| CircularArc{6,5} | -9.71445146547012e-17, 0.003003586477663446, 0.02179986185626174, 0.045160835774071525, 0.05051499242063548, 0.05763274355605572, 0.06, 0.045160835774071525, 0.02179986185626174, -9.71445146547012e-17 |
| ClarkY{12,5} | 0.0, 0.018939026652836723, 0.04682770423823951, 0.059412421874999996, 0.060017266393970294, 0.05803010847647903, 0.0529402520005716, 0.03160306230515993, 0.01447717271471856, 0.0012600000000000527 |
| Thickness{12,4,5} | 0.0, 0.022768635007381372, 0.04680000000000004, 0.057085423029504034, 0.05868680145403634, 0.05999999999999998, 0.058537948336307134, 0.040124041971716824, 0.018583626714100885, 0.0007200000000000872 |
| Modified{12,64,5} | 0.0, **-0.015237135417225576**, 0.013524865239485, 0.05180860425884699, 0.05696836669517609, 0.06000000000000002, 0.05826944444444446, 0.03939618055555556, 0.01868055555555555, 0.0012 |
| NACA4{24,5} | 0.0, 0.0012304687499999998, 0.008749999999999999, 0.017187499999999994, 0.018749999999999996, 0.019999999999999997, 0.019444444444444445, 0.01319444444444444, 0.006111111111111102, -6.938893903907228e-18 |
| NACA5{230,5} | 0.0, 0.0035663058711913804, 0.017011487594531128, 0.01656289850976551, 0.015458705275781142, 0.013250318807812406, 0.011041932339843673, 0.0055209661699218366, 0.002208386467968734, 0.0 |
| NACA6{2,5} | 0.0, 0.0010694715670078072, 0.005173856213026007, 0.008949841794037917, 0.009722207323041694, 0.010711313356303983, 0.01103178000763258, 0.008949841794037917, 0.005173856213026007, 0.0 |

`profileslope(ClarkY{12,5},·)` at the same points: Inf, 0.7158717826173752, 0.16874587119119752, 0.02523750000000002, −7.777267671615628e-5, −0.03724796440440118, −0.06311099799942836, −0.10410582304655996, −0.12451497626960076, −0.1403099999999999.

`profile(NACA4{24,5}(),0.6,2.0,0.2)=0.029999999999999992`, with slope 0.049999999999999996 and angle 0.04995839572194276.

NACA"2412" upper surface, first 5 of 150 points: `0.0+0.0i, 0.005333974046626442+0.01467492128290537i, 0.01153868521297778+0.02081530920909271i, 0.017896354420254345+0.025527639276026793i, 0.024336871290905997+0.02948700849277576i`. The last point is `1.0+0.0i`. The lower surface starts `0.0+0.0i, 0.008088844745319866-0.013343900157730827i, …`.

Small American(NACA4{24,9},ClarkY{12,9}) `complex` loop (17 samples): `[0,0], [0.12153259407104543,0.06098187033024826], [0.24777359906788016,0.07655819152319546], …, [1,0], [0.874075286464025,-0.0100556102722749], …, [0,0]`.

---

## 7. Dependencies on other chakravala packages

| Package | Depends on | Symbols used |
|---|---|---|
| Geophysics | **UnitSystems 0.3.3+** (tested at 0.3.9) | `UnitSystem`/`US`, `Metric`, `English`, `British`, `Quantity` (identity), `normal` (identity), `units`, `Constants` tuple, `Physics` tuple, `Convert` list, dimension symbols `L,T,F,M,Θ`. Conversion functions `length, time, temperature, pressure, density, lapserate, specificenergy, specificentropy, viscosity, thermalconductivity, wavenumber` (both `f(U,S)` factor and `f(v,U,S)` forms). Constants `molarmass(U)`, `avogadro(U)`, `universal(U)` (=`molargas`), `gravity(U)` (g_c), `gravitation(U)` (G), `lightspeed(U)`, `planck(U)`, `boltzmann(U)`, `atm`, `g₀`. Geophysics *extends* many UnitSystems generic functions (`temperature`, `pressure`, `density`, `viscosity`, `gravity`, `mass`, `frequency`, `speed`, `intensity`, …) with new methods. |
| Geophysics | **StaticVectors 1** | `Values{n,Float64}` (immutable static vector), `Variables` (mutable), `zeros(Values{n})`, `⋅` (dot, left-to-right unrolled), `norm` (LinearAlgebra) |
| Geophysics | Similitude (optional) | Only if `usingSimilitude` is true; hard-coded false. |
| FlowGeometry | **Grassmann 0.8** | `Chain{V,G}`, `Submanifold(ℝ^n)`, `ℝ3/ℝ4/ℝ5`, `Values`, `⋅` (Chain dot, returns grade-0; `[1]` extracts), `transpose` + `\` (Cramer solve via `∧`, composite.jl:722), `∧` (wedge for orientation), `Λ(V).v1`, `Grassmann.unit`, `abs` (norm), `Real(...)`, `value` |
| FlowGeometry | **Cartan 0.4** | `TensorField`, `fiber`, `base`, `points`, `PointCloud`, `initpoints`, `initedges`, `edges`, `SimplexTopology`, `SimplexBundle` (callable `p(topology)`), `fullpoints`, `topology`, `Manifold`, `gradient`, `⊕` (product interval), `∂`, `TorusTopology` (from **MeshTopology**, not imported → bug) |
| FlowGeometry | Requires (legacy) | |
| FlowGeometry | Weak deps (external) | Makie, UnicodePlots, MiniQhull, TetGen, MATLAB |
| Clifford | Leibniz, DirectSum, Grassmann 0.7, AbstractTensors 0.6 | Old API: `TensorGraded`, `TensorMixed`, `TensorTerm`, `Simplex`, `MultiVector`, `mdims`, `rank`, `indexbasis`, `basisindex`, `bladeindex`, `binomsum`, `bits`, `fill_limit`, `printindices`, `parsym`, `parval`, `mvec`, `addmulti!`, `generate_mutators`, `insert_expr`, `bcast`, `add_val`, `FixedVector`, `SymField`, `FieldsBig`, `ExprField`, `@computed` (ComputedFieldTypes) |
| Heisenberg | none | |

---

## 8. Lean 4 porting notes

### 8.1 Dependent-type indices vs runtime values

| Julia type param | Lean choice | Rationale |
|---|---|---|
| `Planet{f,a,t,Gm}` (Float) | Runtime `structure Planet where f a t Gm : Float`, with `def Earth : Planet` etc. | Float cannot be a useful type index (opaque in the kernel, no decidable eq). All functions are O(1) arithmetic; `@[inline]` on the constant planets gives the same folding. |
| Gas params (M, ν, μ, Tμ, k, Tk, cᵥ) | Runtime `inductive MoleGas \| atomic p \| diatomic p ν \| triatomic p ν1 ν2 \| pentatomic p \| sutherland p cv`, where `p : SutherlandParams` | Same reasoning. The singleton-type "every gas is its own type" pattern is Julia-specific. |
| `Mixture{M,N,C}` | `structure Mixture where comps : Array (Float × MoleGas)` plus cached `M` | N as an index buys nothing; mixtures are built by `+`. |
| `Atmosphere{n,P,U}` | `structure Atmosphere (n : Nat) [NeZero n] where a h : Vector Float n; planet : Planet; units : Units` | **n as an index: zero cost, and it gives `layer : Float → Fin n` totality and `Weather n` array sizes by construction.** |
| `Weather{ϕ,f,n,P,U}` | `structure Weather (n) where atm : Atmosphere n; phi : Float; fluid : Fluid; T p rho : Vector Float n; Tc ha : Float` | ϕ is runtime; n is shared with the Atmosphere. |
| `U::UnitSystem` | Runtime value from the UnitSystems port. Geophysics only needs Metric and English: `inductive GeoUnits \| metric \| english` with a factor table (§3.1), bridged to the UnitSystems port when it lands. | Julia folds these at compile time; Lean inlines constants. |
| `Profile{p}` (sample count) | `(p : Nat)` index on sampled outputs: `profile : Profile → (p : Nat) → Vector Float p` | Zero cost. It lets the airfoil sizes be proven: `upper : Vector ℂ p`, `complex : Vector ℂ (2*p-1)`, `points : Vector (Float×Float) (2*p-2)`, and `DoubleArc` has P+Q−2. All discharge with `omega`. |
| Profile params (t, te, m, n, c; may be Float) | Runtime `inductive Profile` with constructor args; `Profile.compile : Profile → CompiledProfile` precomputes coefficients | Julia gets the speed from `@generated`/`@pure` folding; Lean gets it by explicit precompute. |
| `Joukowski{R,f,g,b,p}` | Runtime fields plus the p index | |
| Clifford `SparseChain{V,G}` | Would reuse the Grassmann-port `Manifold` index V and `G : Fin (N+1)` | Only if ported. |

### 8.2 Proofs that pay for themselves

These are programming-side proofs, mostly `omega`/`simp`/`decide` on Nat:

1. **Mesh index bounds.** `rectangletriangle (i : Fin (2*(m-1)*(JL-1))) : Fin (m*JL) × Fin (m*JL) × Fin (m*JL)`. Prove the Julia 1-based formula lands in `[1, m·JL]` (omega after unfolding `/` and `%`). Also prove `rectanglebounds` has length `2(n−1)+2(JL−1)` and is a closed cycle. These are real bug catchers.
2. **`layer` totality and correctness.** Return `Fin n`. With a runtime-checked `Sorted h` certificate (`Array.isSorted`), prove `h[layer x] < x ≤ h[layer x + 1]` for interior x as a spec lemma over an abstract ordered type (not Float). Keep Float instances trusting the check.
3. **Size lemmas for airfoils:** `(complex N).size = 2*p-1` and `(points N).size = 2*p-2` (needs `p ≥ 2` as a hypothesis in the structure).
4. **NACA parser** as a total function `String → Except String NacaSpec`. Round-trip property tests (plausible or `#eval` suites) against the table in §4.2.4.
5. **Unit round-trip** `convert U→S→U = id` is only approximate in Float; state it as a test, not a theorem.
6. Real-analysis identities (e.g. `altgeometric ∘ altgeopotent = id` over ℝ, Somigliana ≡ Hirvonen at the poles) are optional and need Mathlib. Skip unless the project already imports Mathlib.

Avoid `native_decide` on Float tables unless the project accepts it. Prefer a smart constructor `Atmosphere.mk? : Array Float → Array Float → Except String (Σ n, Atmosphere n)`.

### 8.3 Performance hot paths and how Julia gets its speed

* The Geophysics per-altitude call costs about 1 `pow`/`exp`, a few divisions and one `findfirst` over ≤21 entries. Julia's speed comes from `@pure` plus type-parameter constants: every Planet/gas/unit constant is folded, so only the transcendental calls remain. Lean equivalent:
  * Precompute a `Weather` "compiled" record with `g`, `R`, `g/R`, `r`, and per-layer `-g/R/a`.
  * Use `FloatArray` for the tables and binary search for `layer` when n>8 (only US62 has n=21; linear scan is fine).
  * Vectorised grid evaluation (`profileOnGrid : Weather → FloatArray → FloatArray`) is the natural LeanPlot feed.
* FlowGeometry: Julia `@pure`/`@generated` fold `naca4(n)` (a **string parse!**), `naca5(n)` and the Thickness 5×5 solve. `Modified` is *not* folded upstream: it does two 4×4 solves per point. Lean: precompute everything at construction (`CompiledProfile` holding the coefficient arrays) and sample into `FloatArray`. The complex outline is stored as two `FloatArray`s (re, im) or `Array (Float×Float)`.
* Linear solves: a tiny dense Gaussian elimination with partial pivoting on `Array (Array Float)` or a 5×5 `FloatArray` is enough. **It must not throw on singular input** (NACA 00xx front system): return NaN coefficients like Julia's Cramer.

### 8.4 Tricky semantics

Faithful-port checklist with golden-matching behaviour. For each, pick "faithful" (default, required for goldens) and optionally add a `fixed` variant behind a flag or separate name.

1. `Air` is the Nitrox **Mixture**, not the SutherlandGas `air`. Mixture thermal properties are mole-fraction averages of per-mass quantities.
2. `vibration(G)` includes the `/1.2`. The DiatomicGas display label "ν" is actually θ_v.
3. **US76 above 91 km is broken** (§4.1.6). Port the arithmetic literally, including reading the still-zero `T[i]`.
4. **`gravity(h,W)` switches models at 0.007·r_W**, a discontinuity.
5. `specificweight` uses gravity at hG. `geopotential(h) = g(h)·h`.
6. `op(W)` defaults to **Metric** output even for English W. `op(h,W)` defaults to W's units.
7. `NACA6` value path g/h swap. `NACA6` slope `log(ax)` without abs. `NACA6A` x<0.87437 throws: for the Lean behaviour, choose between returning NaN (faithful to "no value") and implementing the scalar intent `naca6(x,0.8,0,0)` behind `NACA6A.fixed`. Mark it **no golden**.
8. `NACA5` reflexed fits are wrong. `NACA5` slope lacks the /6.
9. `ParabolicArc` slope uses t/400 instead of t/25. `Modified` 4th row is `(1,1,1,1)`.
10. `NACA"…"`: the 16- and 6A-series map `Modified{t,m}` parameters wrongly. The n5 pattern is tried before n4, and the search is unanchored.
11. `upper`/`lower` force the last point to `1+0i` even when c≠1 or x0≠0. `interval(p,c,x0)` ends at **c**.
12. The British airfoil and the `SymmetricArc`/`DoubleArc` `complex` are broken upstream. **Recommended Lean behaviour:**
    * Implement British as the evident intent (dyc≡0 ⇒ `U=x+i(yc+yt)`).
    * Give SymmetricArc/DoubleArc `interval = interval(profile)` (for DoubleArc, use the upper profile's interval, require equal P for `complex`, and generalise later).
    * Mark all of these "**no Julia golden**". The upper/lower goldens for SymmetricArc/DoubleArc do exist.
13. Dispatch-overloaded names must become distinct Lean names:
    * `gravity`: Planet GM/a², Somigliana(ϕ), (h,θ) component norm, Weather sea level, Weather(h), and UnitSystems g_c. Suggested names: `Planet.gravitySpherical`, `Planet.gravityNormal`, `Planet.gravityAt`, `Weather.gravity0`, `Weather.gravity`.
    * Also split `radius`, `frequency` (Planet vs gas), `temperature`/`pressure` (FluidState vs Weather), `latitudegeocentric` (2- vs 4-arg), and `_gravity` (two unrelated methods).
14. **Name clash:** `British` (UnitSystem) vs `FlowGeometry.British` (airfoil). Use namespaces `Geophysics.Units.english` and `FlowGeometry.Airfoil.british`.
15. `Planet{0}` special cases dispatch on Int `0`. In Lean, test `f == 0.0`.
16. Negative-zero base altitudes (−0.0) are harmless, but `repr` prints `-0.0`.
17. Float-level exactness:
    * Julia `x^2` and `x^3` with literal exponents are `x*x` and `x*x*x`.
    * `x^4` and higher (Y(x) basis, `dY`) use Julia's power-by-squaring with compensation, so there can be 1-ulp differences vs `x*x*x*x`.
    * Float^Float `t^gRa` is `pow`.
    * Julia's `exp/log/atan/sin/cos/acos/sqrt` are Julia-native libm, while Lean uses the C libm, so expect ≤1–2 ulp differences.
    * **Recommended golden tolerance:** rel 1e-12 (abs 1e-300 for tiny values). The exact-match candidates are `gravity(Standard)=9.80665`, the Mixture M, layer indices, mesh indices and the parse table.
18. `range(x0,c,length=p)` elements come from Julia's TwicePrecision. Use `x0 + (c-x0)*(k/(p-1))`, or better `(k*c + (p-1-k)*x0)/(p-1)`. Compare with 1-ulp tolerance.
19. Julia errors (DomainError from `sqrt`/`log`/`^` on negatives) become NaN in Lean. The oracle marks them.

### 8.5 Julia-specific parts: skip or redesign

* `@pure`, `@generated`, `Requires`/extensions, and the `usingSimilitude` toggle.
* The ENV-driven `Standard`: redesign as `def Standard := Earth1959` plus an explicit `standard (year) (units)` function. Optionally add a `set_option`-style config.
* `display` side effects: replace with `ToString`/`Repr`.
* MATLAB `decsg`, TetGen and MiniQhull: out of scope. Keep `decsg` as a pure data builder returning the geometry matrix if wanted.
* Makie/UnicodePlots extensions: replace with LeanPlot adapters:
  * `Profile.toSeries : Profile → Nat → Array (Float×Float)`
  * `Airfoil.outline : … → Array (Float×Float)` (closed)
  * `Weather.profile : Weather n → (op) → FloatArray → Series`
* Clifford.jl: do not port the code. If sparse storage is wanted in the Grassmann port, design it fresh from §4.3.
* Heisenberg.jl: nothing to port.

### 8.6 Suggested Lean module decomposition

Rough LOC including docstrings; not counting tests unless stated.

| Module | Contents | LOC |
|---|---|---|
| `Chakravala/Geophysics/Units.lean` | Metric/English factor and constant table, or a bridge to the UnitSystems port | 80 |
| `Chakravala/Geophysics/Planet.lean` | Planet structure, 13 bodies, shape constants, latitudes, radius, speed, J2, Somigliana, Hirvonen, components | 230 |
| `Chakravala/Geophysics/Gas.lean` | MoleGas inductive, Sutherland, heat capacities, Einstein, Mixture (`HMul Float Gas`, `HAdd`), FluidState and derived properties | 320 |
| `Chakravala/Geophysics/Atmosphere.lean` | `Atmosphere n`, `Weather n`, integration, `layer : Fin n`, altitude conversions, ~21 ops + 20 ratios (generated with a macro or a `Op` enum dispatcher), English/Metric | 380 |
| `Chakravala/Geophysics/Data.lean` | Gas constants, the 14 atmosphere tables, 14 presets, `Standard` | 170 |
| `Chakravala/Geophysics/Repr.lean` | Julia-compatible display strings (uses the shared `JuliaFloat` formatter) | 70 |
| `Chakravala/FlowGeometry/LinSolve.lean` | Small dense solver (no-throw) | 60 |
| `Chakravala/FlowGeometry/Profile.lean` | Profile inductive, compiled coefficients, eval/slope for 10 families, sampling (`Vector Float p`) | 430 |
| `Chakravala/FlowGeometry/Airfoil.lean` | American/British/Symmetric/Double/Joukowski/UpperArc, upper/lower/complex/points with size proofs | 260 |
| `Chakravala/FlowGeometry/NACA.lean` | Hand-written parser equivalent to the 4 regexes, `NACA!"2412"`-style term elaborator or macro | 170 |
| `Chakravala/FlowGeometry/Mesh.lean` | rectangletriangle(s) with Fin proofs, bounds, FittedPoint, Rakich*, rectangle/box/cube/icosahedron/sphere, circlemid, sphere subdivision, rectcirc, convhull, edgeslist, wing | 300 |
| `Chakravala/FlowGeometry/Plot.lean` | LeanPlot adapters (series, closed outlines, mesh wireframe) | 90 |
| `Chakravala/Clifford/Sparse.lean` (optional, deferred) | SparseChain/MultiGrade on top of the Grassmann port | 350 |
| `Tests/Golden/Geophysics.lean`, `Tests/Golden/FlowGeometry.lean` | JSON golden readers and tolerance checks | 300 |

Total ≈ 2,860 (≈ 2,510 without the optional Clifford module).

---

## 9. Oracle test plan

### 9.1 Generation

Already written and run:

```text
julia --startup-file=no --project=scratchpad/juliaenv-applied \
      scratchpad/oracle/applied-misc/oracle_applied_misc.jl scratchpad/oracle/applied-misc
julia --startup-file=no --project=scratchpad/juliaenv-applied \
      scratchpad/oracle/applied-misc/plots_applied_misc.jl scratchpad/notes/applied-misc-plots scratchpad/oracle/applied-misc
```

Encoding:

* Float64 values are JSON numbers written with shortest round-trip repr.
* `NaN`/`Inf`/`-Inf` are strings.
* Complex values are `[re, im]`.
* Grassmann Chains are arrays of coefficients, e.g. `[1.0, x, y]` for homogeneous points.
* Julia exceptions become `{"error": "<Type>: <message prefix>"}`.

The oracle patches the FlowGeometry `TorusTopology` bug (see §2.2.4) so that `complex(::Airfoil)` works. Everything else is unpatched.

### 9.2 `geophysics.json`

* **`planets.<Name>`** covers all 13 bodies:
  * `params` (f,a,t,Gm), 16 derived scalars, and English variants.
  * Over `angles_rad` (deg 0,10,15,30,45,45.5,60,75,89,90): `radius_theta`, `radiusgeodetic_phi`, the three latitude conversions, `speed`, `centripetal`, `oblateness_theta`, `somigliana`, `normalgravity_internal` (the Hirvonen `_gravity`).
  * Over `h_grid` (0,1e3,1e4,1e5) × angles: `deflection`, `latitudegeocentric_h`, `gravitygeodetic`, `gravitycomponents` (2-vectors), `gravity_h_theta`.
* **`units`**: the conversion factors and constants in §3.1.
* **`gases.<Name>`** covers N2, O2, Ar, CO2, H2, He, Ne, Kr, Xe, CH4, air_SutherlandGas, Nitrox, AirMix, Traces, MainGases, TraceGases:
  * `show`, scalar properties, and `fractions` (Mixtures only).
  * The 10 T-functions over T ∈ {100,150,200,216.65,250,273.15,288.15,288.16,300,500,1000,2000} K, plus `_English` variants at 1.8·T °R.
  * `_vibration_einstein` over x ∈ {0.01…800}, including the overflow to NaN.
  * Expected errors: CH4 (no heatvolume), air_SutherlandGas (StackOverflow), `fractions` of pure gases, `wavenumber`/`vibration` of atomic gases and mixtures.
* **`fluidstate`**: Air FluidStates at (288.15,101325), (216.65,22632), (300,5e4), (1000,1). All 22 properties, Metric and English. `intensity` is an expected error.
* **`weather.<Earth19xx[English]>`** covers all 14 presets:
  * Layer tables `a,h,m,T_layers,p_layers,rho_layers`, plus `Tc`, `ha`, `radius`, `gravity0`, `gasconstant`, `molecularmass`, `latitude`.
  * Over 51 geometric altitudes (−2 km … 800 km, including every layer boundary ±, the 0.007r gravity switch at 44,571 m, and US76's 86/91/110/120 km; English grids are the same values /0.3048 ft): `hG`, `altgeometric_of_hG`, `altabs`, `layer_of_hG` (1-based), `gravity`, `geopotential`, `lapserate`, all 21 ops and all 20 ratio ops.
  * `_cross_units`: `op(h,W,U,S)` for 3 unit combinations.
  * `_defaults` and `_display_*` strings.
  * Expected errors: Earth1976English at h ≥ 200 km (DomainError, i.e. NaN in Lean).

### 9.3 `flowgeometry.json`

* **`profiles._x`** holds 112 x values: 101 uniform points in [0,1], plus −0.1, −1e-9, 0.0125, 0.003, 0.87, 0.87437, 0.9, 1−1e-8, 1+1e-9, 1.1.
* **`profiles.<P>`** covers 43 profile instances spanning every family, including defaults, Float params, and reflexed/multi-a variants. Each has:
  * `y`, `dy` at `_x`;
  * scaled forms `profile(p,x,2,0.5)`, `profileslope`, `profileangle`;
  * the sampled `profile_field` and `profileslope_field` (p=5);
  * `interval`.
  * Expected errors: NACA6A (all x<0.87437), and NACA6 with a<1 for x>a (DomainError).
* **`profiles._internals`** holds the precomputed coefficient goldens: `clarky`, `tailslope`, `riegel`, `radius`, `modified` (params and both coefficient vectors), `naca4` decode and coefficients, `naca5` decode, `naca6` decode. **Test these first**; they localise errors.
* **`airfoils.<NACA string>`** covers 23 strings, including invalid "abc" (`parse_error`). Each has `type`, `interval`, `upper`, `lower`, `upper_base`, `complex` (2p−1) and `points` (2p−2) at p=150. British-family strings record `upperlower_error`.
* **`airfoils.<small constructors>`** use p=9 for compact tests: American (NACA4+ClarkY, NACA4+Modified, NACA6+ClarkY), British (error), SymmetricArc ×2, DoubleArc ×2 (equal and unequal p). Each has upper/lower at (c,x0)=(1,0) and (2,1), `complex`, `points`.
* **`airfoils.Joukowski{R,f,g,b,p}`**: 4 parameter sets.
* **`mesh`** contains:
  * `rectangletriangle` for m=3,4;
  * `rectangletriangles(3,3)`, `(4,3)`; `rectanglebounds(3,3)`, `(4,3)`;
  * `FittedPoint`; `RakichNewton` for 5 parameter sets;
  * `RakichLine` ×2, `Rakich`, `RakichPlate` ×2, `rakichpoints(CircularArc{6,5},50,11,5)` (55 points);
  * `rectangle`, `square`, `box`, `cube`, `icosahedron`, `sphere` ×2, `circlemid`, `rectcirc` ×2;
  * `edgeslist`, `convhull(square)`, `chord`, `interval(5,2,1)`, `interval(150)[1:4]`, `doubleinterval`.

### 9.4 Visual and text goldens (LeanPlot co-development)

* `notes/applied-misc-plots/fg_airfoils.png`: 6 NACA outlines + camber. It visibly shows the 0012-64 LE self-intersection bug.
* `fg_profiles.png`: camber families and thickness families.
* `fg_joukowski.png`.
* `fg_rakich_mesh.png`: the stretched structured mesh wireframe.
* `geo_atmosphere.png`: T(h), and p(h) on a log axis, for 6 models. It shows the US76 >91 km artefact.
* `geo_gravity.png`: Somigliana vs latitude, and g(h) with the 0.007r jump.
* `oracle/applied-misc/unicodeplot_*.txt`: exact braille lineplots (40×15 canvas). These are good byte-exact tests for a LeanPlot text backend implementing UnicodePlots' braille rasteriser and autoscaled tick labels.

### 9.5 Tolerances and test strategy

1. **Exact:**
   * integer outputs (layer, mesh indices, parse types as structured records);
   * `gravity(Standard)=9.80665`;
   * Mixture `M` values;
   * `naca4` decode;
   * `profile(FlatPlate)`;
   * Values that pass through only +, −, ×, ÷ and sqrt, in the same operation order: interval with k/(p−1), ParabolicArc, NACA4 polynomials after the coefficients. Try exact first and fall back to 1 ulp.
2. **Relative 1e-12:** everything involving exp/log/pow/atan/trig, chained atmosphere layers, and linear solves (Cramer vs LU).
3. **Error entries:** Lean should produce NaN or an `Except.error`, whichever the port chose; the test harness maps both to "matches Julia error".
4. **Input distributions to add as the ports mature:**
   * random x ~ U[0,1] (1,000 samples, seeded; dump the inputs into the JSON);
   * random h ~ U[−2 km, 300 km] per model;
   * random latitudes ~ U[−π/2, π/2];
   * random Planet params (f ∈ [0,0.1], a ∈ [1e5,1e8], t ∈ ±[1e4,1e7], GM ∈ [1e10,1e20]);
   * random NACA strings from the grammar in §4.2.4, including decimals, parentheses, and invalid tokens.

   Extend `oracle_applied_misc.jl` by adding keys; keep existing keys stable.

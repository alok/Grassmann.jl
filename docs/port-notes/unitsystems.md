# UnitSystems.jl + FieldConstants.jl: Lean 4 porting spec

**Sources.** `UnitSystems.jl` v0.3.9 (clone `/Users/alokbeniwal/chakravala/UnitSystems.jl`, HEAD `78685a0`, 2025-09-22; the core standard was last revised 2023-01, commit `e38ab04`). `FieldConstants.jl` v0.1.1 (clone `/Users/alokbeniwal/chakravala/FieldConstants.jl`, HEAD `853eac7`, 2022-10-04). **Oracle:** Julia 1.13.0 with the registered UnitSystems 0.3.9 and FieldConstants 0.1.1. This is the same code as the clones.

**How this spec was verified.** Every value quoted here was produced by the Julia oracle. The dimension/exponent tables were not transcribed from docs. They were recovered numerically by evaluating every function on 31 random synthetic unit systems and solving an exact log-linear fit (residuals ≤ 1e-15; see §4.6 and `dims.jl`).

## 0. Artifact index (all under `scratchpad/notes/unitsystems_oracle/`)

| file | what |
|---|---|
| `dump.jl` | main oracle dump: systems, 1-arg functions, module constants, all-pairs conversions, value conversions |
| `dims.jl` | recovers the exact exponent vector of every quantity/function over the 11 defining constants and maps it to USQ dims |
| `docs.jl` | extracts rendered docstrings (outputs are interpolated at load time) and parses `julia>` examples |
| `verify_docs.jl` | re-evaluates each doc example and marks it `verified` when `repr(value)` equals the doc text |
| `fieldconstants.jl` | FieldConstants operator table: value, payload type, and whether the result is still a `Constant` |
| `constructors.jl` | random-argument goldens for every UnitSystem constructor |
| `analyze.py` | compares the all-pairs table against candidate Lean strategies (§4.10) |
| `jsonw.jl`, `params.jl` | dependency-free JSON writer; a quick parameter printer |
| `goldens/meta.json` | category tuples (`Systems`, `Convert`, …) in exact Julia order |
| `goldens/systems.json` | 48 systems: 19 slots (value + Int/Float64 type), `show`, `display`, `isrationalized`, full `typeof` |
| `goldens/aliases.json` | alias → `show` name |
| `goldens/scalars.json` | every 1-arg function (Dimensionless ∪ Constants ∪ Physics ∪ Derived ∪ prefixes ∪ extras) × 48 systems |
| `goldens/module_constants.json` | every module-level numeric constant (value, payload type, Constant-or-plain) |
| `goldens/convert_pairs.json` | `q(U,S)` for all 131 quantities × 48 × 48 (301,824 entries, `types` string I/F/E per row) |
| `goldens/convert_one_arg.json` | `q(U)` (= `q(Natural,U)`) for all 131 × 48 |
| `goldens/convert_values.json` | `q(v,U,S)` and `q(v,U)` for 16 quantities × 11 system pairs × 4 values |
| `goldens/convert_exponents.tsv`, `goldens/scalar_exponents.tsv` | exact exponent vectors and USQ dimensions (Appendix tables below) |
| `goldens/docstrings.json`, `goldens/doc_examples.json`, `goldens/doc_examples.tsv` | 439 rendered docstrings; 1720 examples (1658 distinct) |
| `goldens/doc_goldens.json` | 1658 distinct doc examples with `status` ∈ {verified (1638), mismatch (10), error (10)} |
| `goldens/fieldconstants_ops.json` | 878 FieldConstants operator rows |
| `goldens/constructors.json` | 108 constructor rows |

Regenerate (≈6 min total, most of it the all-pairs table):
```
cd scratchpad
J="julia --startup-file=no --project=juliaenv"
$J notes/unitsystems_oracle/dump.jl notes/unitsystems_oracle/goldens
$J notes/unitsystems_oracle/dims.jl
$J notes/unitsystems_oracle/docs.jl notes/unitsystems_oracle/goldens
$J notes/unitsystems_oracle/verify_docs.jl
$J notes/unitsystems_oracle/fieldconstants.jl
$J notes/unitsystems_oracle/constructors.jl
```

---

## 1. Purpose & scope

**UnitSystems.jl.** This is Reed's "Unified System of Quantities" (USQ). A *unit system* is fixed by **11 dimensional constants** plus a dimensionless `Coupling` (the "Universe"). The constants are:

| slot | symbol | meaning | accessor |
|---|---|---|---|
| 1 | `kB` | Boltzmann constant | `boltzmann` |
| 2 | `ħ` | reduced Planck constant | `planckreduced` |
| 3 | `𝘤` | speed of light | `lightspeed` |
| 4 | `μ₀` | vacuum permeability | `vacuumpermeability` / `permeability` |
| 5 | `mₑ` | electron mass | `electronmass` / `mass` |
| 6 | `Mᵤ` | molar-mass constant | `molarmass` |
| 7 | `Kcd` | luminous efficacy | `luminousefficacy` |
| 8 | `θ` | radian (angle unit) | `radian` / `angle` |
| 9 | `λ` | Gauss rationalization | `rationalization` |
| 10 | `αL` | Lorentz constant | `lorentz` |
| 11 | `g₀` | gravity/force reference | `gravity` |

From these it defines:

- **48 named unit systems** (Metric, SI2019, CGS family, English family, astronomical, natural).
- **131 derived quantities** (`length`, `energy`, `charge`, …). Each converts between *any* two systems, with factor `q(U,S)`.
- **28 physics constants** (`gravitation`, `elementarycharge`, `hartree`, …) and **6 dimensionless couplings**, expressed in any system.
- **196 standardized units** (`foot`, `calorie`, `gauss`, …; 193 actually defined) expressed in any system.
- SI/binary prefixes and ~180 numeric constants.

Everything is carried in *type parameters* as `FieldConstants.Constant{N}` values. All of it is constant-folded at compile time (`@pure`), so a runtime conversion is a single `v * K`.

**FieldConstants.jl.** A 112-line package defining `Constant{N} <: Real`. This is a `Val`-like singleton whose payload `N` (an Int or Float64) is a compile-time number. Arithmetic between `Constant`s is closed and computed at compile time. Mixing a `Constant` with ordinary numbers falls back to plain arithmetic.

**In scope:** all executable code in `src/UnitSystems.jl`, `initdata.jl`, `kinematic.jl`, `electromagnetic.jl`, `thermodynamic.jl`, `physics.jl`, `derived.jl`, `systems.jl` (constants and exports), `text.jl` (name tables), `test/runtests.jl`, README, plus all of FieldConstants.

**Summarized only:**
- `*docs.jl` files (7019 LOC of `@doc` strings). Their only semantic content is the example values (harvested as goldens, §6) and the unit-name comments.
- The Wolfram `Kernel/*.wl` paclet. It is an independent re-implementation. It is useful as a cross-reference for exact rational constant definitions (`Kernel/systems.wl:12-76`) and for the dimension table of the constants (`Kernel/systems.wl:89-100`).
- `src/lib.rs` and `printunits.rs`. The README calls this Rust port "unmaintained". It is stale: 8 constants only, `KCD = 683.002`, `LD = 384402e3`. Do not use it as an oracle.

**Downstream.** Similitude.jl (dimensioned `Quantity`), MeasureSystems.jl (Measurements uncertainty), and Geophysics.jl re-use this code by instantiating the type parameters with other number types. The hooks are `isquantity`, `evaldim`, `measure`, `cache`, `normal`, `Quantity`, and `similitude()`; see §7. The Lean design in §8 keeps that genericity.

---

## 2. Public API inventory

656 names are exported. 419 come from the category tuples (`Systems` 48, `Dimensionless` 6, `Constants` 12, `Physics` 28, `Derived` 196, `Convert` 131; overlaps removed). The other 237 come from explicit `export` lines at `initdata.jl:45-46,159-160` and `systems.jl:15-24,79-83`. The loop that exports the tuples is at `UnitSystems.jl:310-312`.

**Exported but undefined** (a reference raises `UndefVarError`): `neper`, `bel`, `decibel` (their definitions are commented out at `derived.jl:228-230`), `CGS2019`, `EE2019`, `Λ`. Consequence: `UnitSystems.derived(U)` (`initdata.jl:32`) always throws `UndefVarError: neper`.

### 2.1 FieldConstants (`FieldConstants.jl/src/FieldConstants.jl`)

Exports only `Constant` and `constant` (line 17). UnitSystems imports `Constant, constant, isconstant, logdb, expdb, dB, param, measure, cache` (`UnitSystems.jl:65,70`). UnitSystems does **not** re-export `Constant` or `constant`.

| symbol | signature | semantics | line |
|---|---|---|---|
| `Constant{N} <: Real` | `struct Constant{N}; Constant{N}() = new{N}() end` | zero-field singleton; the payload `N` lives in the type | 21-23 |
| `Constant(N::Constant)` | → `N` | idempotent | 28 |
| `Constant(N::Irrational)` | → `Constant(float(N))` | π etc. become Float64 payloads | 29 |
| `Constant(N::Float64)`, `Constant(N::Int)` | → `Constant{N}()` | `@pure` | 30-31 |
| `Constant(x)` | → `x` | non-numbers pass through unchanged (`Constant("x") == "x"`) | 33 |
| `Constant(N::Number)` | → `Constant{N}()` | e.g. `Constant(1//2)` keeps a Rational payload | 34 |
| `isconstant(x)` | `false`; `true` for `Constant` | not exported | 25-26 |
| `constant(::Constant{N})` | → `N` (the plain payload) | exported | 46 |
| `param(::Constant{N})` | → `N` | same as `constant` | 57 |
| `measure(x)`, `cache(x)` | identity | hooks overridden by MeasureSystems | 47-48 |
| `logdb(x)` | `10log10(x)` | decibel | 50 |
| `expdb(x)` | `exp10(0.1)^x` | inverse decibel. **Note:** `exp10(0.1)^x`, not `10^(x/10)`, so `expdb(20) = 100.00000000000011` | 51 |
| `dB` | `= logdb` | alias | 52 |
| `Base.Int(::Constant{N})` | → `Constant(Int(N))` | **returns a Constant, not an Int** | 54 |
| `Base.show(io, ::Constant{N})` | `show(io, N)` | prints like the bare payload (`2`, `2.99792458e8`) | 55 |
| `abs`, `inv`, `sqrt`, `cbrt`, `log`, `log2`, `log10`, `log(b,x)`, `exp`, `exp2`, `exp10`, `logdb` | `Constant{f(N)}()` | closed (result is a Constant) | 58, 61, 76-85 |
| `float(c)`, `convert(Float64,c)` | `float(N)` | plain Float64 | 59-60 |
| `<` | `(Real,Constant)`, `(Constant,Real)` | compares payloads; there is no `(Constant,Constant)` method | 62-63 |
| `+`, `-` | `(Constant,Constant)` → `Constant(a+b)`; `(Number,Constant)` / `(Constant,Number)` → **plain** | 64-69 |
| `*` | `(Constant{A},Constant{B})` → `Constant{A*B}()`; `(Real,Constant)` / `(Constant,Real)` → **plain** | 70-72 |
| `/` | `(Constant{A},Constant{B})` → `Constant{A/B}()`; `(Number,Constant)` → `a*inv(b)` = plain `a*(1/N)`; `(Constant,Number)` → `a*inv(b)` → plain | 73-75 |
| `^` | `(Number,Constant{N})` → `Constant{a^N}()` (**closed even for a plain base**); `(Constant{N},Number)`, `(Constant{N},Integer)`, `(Constant{N},Rational{Int})` → `Constant{N^b}()` | 86-89 |
| `Irrational` mixing | `^ * / + -` with an `Irrational` operand promote the Irrational via `Constant(float(x))`, then use the closed op | 91-100 |
| `isone`, `iszero` | on the payload | 102-103 |
| `==` | `(Real,Constant)`, `(Constant,Real)`, `(Constant,Constant)` compare payloads | 105-107 |
| `isapprox` | same three combinations, default tolerances | 108-110 |

Oracle-confirmed edge behaviour (`goldens/fieldconstants_ops.json`):
- `Constant(10)^Constant(-3)` and `Constant(-3)^Constant(2)` throw **MethodError: ambiguous**. There is no Constant^Constant method.
- `Constant(2)^70 == Constant{0}`. Int64 wraps silently; this is why `zebi`/`yobi` are computed as `(Constant(1.0)*𝟐)^70`.
- `Constant(2)+2 === 4::Int` (plain), whereas `2^Constant(3) === Constant{8}`.

### 2.2 Types

| name | definition | notes | src |
|---|---|---|---|
| `UnitSystems.Coupling{αG,α,μₑᵤ,μₚᵤ,ΩΛ}` | empty struct; five dimensionless type parameters | not exported | `UnitSystems.jl:107` |
| `Coupling(αG,α,μₑᵤ,μₚᵤ,ΩΛ)` | → `Coupling{cache(αG),…}()` | | `:109` |
| `Coupling{αG,α,μₑᵤ,μₚᵤ}()` | 4-parameter form; **ΩΛ defaults to the global `ΩΛ = 0.6889`** (the method body refers to the global) | | `:108` |
| `UnitSystem{kB,ħ,𝘤,μ₀,mₑ,Mᵤ,extra}` | empty struct. `extra` is a 14-tuple `(Kcd,θ,λ,αL,g₀,C,τ,𝟐,𝟑,𝟓,𝟕,𝟏𝟏,𝟏𝟗,𝟒𝟑)` | exported; aliases `US`, `units` | `:145-147` |
| `UnitSystem(kB,ħ,𝘤,μ₀,mₑ,Mᵤ=𝟏,Kcd=𝟏,θ=𝟏,λ=𝟏,αL=𝟏,g=𝟏,C=Universe,τ=τ,x=𝟐,y=𝟑,z=𝟓,w=𝟕,u=𝟏𝟏,v=𝟏𝟗,q=𝟒𝟑)` | → `unitsystem(...)` | positional arguments stored as given. With plain `Int`s the result is a *different type* from the Constant-based `Natural`, so `UnitSystem(1,1,1,1,1) !== Natural` and it shows as `Unknown` | `:148-150` |
| `UnitSystems.unitsystem(...)` | same signature → `UnitSystem{cache(kB),…,(cache(Kcd),…,C,cache(τ),…)}()` | internal constructor | `initdata.jl:37-39` |
| `Universe` | `Coupling(αG, α, μₑᵤ, μₚᵤ, ΩΛ)` = `Coupling{1.751809945750515e-45, 0.0072973525692838015, 0.0005485799090649074, 1.007276466621, 0.6889}()` | exported | `initdata.jl:35` |

### 2.3 Accessors

All are `@pure` and return the stored type parameter (`measure(x) = x`).

| function | returns | src |
|---|---|---|
| `boltzmann(U)` | `kB` | `UnitSystems.jl:151` |
| `planckreduced(U)` | `ħ` | `:152` |
| `lightspeed(U)` | `𝘤` | `:153` |
| `vacuumpermeability(U)`, `permeability(U)` | `μ₀` | `:154-155` |
| `electronmass(U)` | `mₑ` | `:156` |
| `molarmass(U)` | `Mᵤ` | `:157` |
| `luminousefficacy(U)` | `extra[1]` Kcd | `:158` |
| `angle(U)`, `radian(U)` | `extra[2]` θ | `:159-160` |
| `rationalization(U)` | `extra[3]` λ | `:161` |
| `lorentz(U)` | `extra[4]` αL | `:162` |
| `gravity(U)` | `extra[5]` g₀ | `:163` |
| `universe(U)` | `extra[6]` Coupling (exported) | `:164` |
| `tau(U)` | `extra[7]` (always `Constant(2π)`) | `:165` |
| `two(U)`, `three(U)`, `five(U)`, `seven(U)`, `eleven(U)`, `nineteen(U)`, `fourtythree(U)` | `extra[8..14]` (always the Int Constants 2, 3, 5, 7, 11, 19, 43) | `:166-172` |
| `coupling(C)`, `finestructure(C)`, `electronunit(C)`, `protonunit(C)`, `darkenergydensity(C)` | Coupling slots | `:110-115` |
| `protonelectron(C)` | `protonunit(C)/electronunit(C)` | `:114` |
| `coupling(U)`, `finestructure(U)`, … (all 6 Dimensionless names) | `f(universe(U))` | `:291-293` |

**Callable constants.** `tau`, `two`, `three`, `five`, `seven`, `eleven`, `nineteen`, `fourtythree`, every SI/binary prefix name, `slug`, `rankine`, `kelvin`, `zetta`, `zepto`, `yotta` and `yocto` are simultaneously a **`Constant` value** and **callable on a `UnitSystem`**. Julia attaches a call method to the singleton type (`methods(slug)` → `(::Constant{14.593902937206362})(U::UnitSystem)`).

- `slug == 14.593902937206362` (kg per slug), while `slug(U)` = one slug expressed in `U`.
- `kelvin == 1.8` (= `K` = °R per K), while `kelvin(Metric) == 1`.
- `rankine == 5/9`, while `rankine(English) == 1`.
- `mega == 1000000::Int` (module constant), while `mega(U) == 1.0e6::Float64` (function).

The Lean port must give these distinct names (see §8).

### 2.4 UnitSystem constructors

All are exported. Pseudocode is in §4.2.

| constructor | signature | src |
|---|---|---|
| `MetricSystem` | `(Mu=Mᵤ, μ0=μ₀, Ru=Rᵤ, g0=𝟏, θ=𝟏, h=𝘩, me=αinv^2*R∞*𝟐*h/𝘤)` | `initdata.jl:62` |
| `ConventionalSystem` | `(klitz, joseph, Ru=Rᵤ, g0=𝟏, θ=𝟏)` | `initdata.jl:71` |
| `RankineSystem` | `(u, l, m, g0=𝟏)` | `initdata.jl:84` |
| `EntropySystem` | `(u, t, l, m, θ=one(u))` and `(u, t, l, m, θ, μ0, Mu=molarmass(u)/m, g0=gravity(u), e=m*l*l/(t*t), λ=one(u), αL=one(u), Kcd=luminousefficacy(u)*e/t*g0)` | `UnitSystems.jl:251-264` |
| `AstronomicalSystem` | `(u, t, l, m, e=m*lightspeed(u)^2)` | `UnitSystems.jl:272-274` |
| `ElectricSystem` | `(u, Ω, V)` | `UnitSystems.jl:228` |
| `GaussSystem` | `(u, μ0, λ, αL=one(u), l=inv((two(u)*five(u))^2), m=inv((two(u)*five(u))^3), g0=gravity(u))` | `UnitSystems.jl:237-239` |
| callable rescale | `(U::UnitSystem)(JK, Js, ms, Hm, kg)` | `UnitSystems.jl:205-221` |
| callable no-op | `(U::UnitSystem)(x, D)` → `x`; also `Quantity(D,U,x) = x`, `Quantity(x) = x` | `UnitSystems.jl:203, 95-96` |
| `UnitSystems.constant(U)` | rebuilds `U` with every slot wrapped in `Constant(…)`, `Universe`, and default primes | `initdata.jl:41-43` |
| `UnitSystems.normal(U)` | rebuilds with `normal(slot)`; identity in UnitSystems (Similitude strips Quantity wrappers) | `UnitSystems.jl:181-184` |

### 2.5 The 48 named systems (`const`, all exported) and aliases

Tuple order (`UnitSystems.Systems`, `UnitSystems.jl:22`), which is also the matrix index order in `convert_pairs.json`:

`Metric, SI2019, SI1976, CODATA, Conventional, International, InternationalMean, MetricTurn, MetricSpatian, MetricGradian, MetricDegree, MetricArcminute, MetricArcsecond, Engineering, Gravitational, MTS, EMU, ESU, Gauss, LorentzHeaviside, FPS, IPS, British, English, Survey, FFF, MPH, KKH, Nautical, Meridian, IAU☉, IAUE, IAUJ, Hubble, Cosmological, CosmologicalQuantum, Planck, PlanckGauss, Stoney, Hartree, Rydberg, Schrodinger, Electronic, Natural, NaturalGauss, QCD, QCDGauss, QCDoriginal`

| system | definition (exact source) | src |
|---|---|---|
| `SI2019` | `MetricSystem()` | `initdata.jl:88` |
| `Metric` | `MetricSystem(milli, τ/𝟐^6/𝟓^7)` (μ₀ = 4π·10⁻⁷ exactly as τ/5e6) | `:89` |
| `Engineering` | `MetricSystem(milli, τ/𝟐^6/𝟓^7/g₀, Rᵤ, g₀)` | `:91` |
| `MetricTurn` | `MetricSystem(milli, τ/𝟐^6/𝟓^7, Rᵤ, 𝟏, 𝟏/τ)` | `:92` |
| `MetricSpatian` | `… , 𝟏, 𝟏/ς)` with ς = √(2τ) = √(4π) | `:93` |
| `MetricGradian` | `… , 𝟏, 𝟐^4*𝟓^2/τ)` (θ = 400/τ) | `:94` |
| `MetricDegree` | `… , 𝟏, 𝟐^3*𝟑^2*𝟓/τ)` (θ = 360/τ) | `:95` |
| `MetricArcminute` | `… , 𝟏, 𝟐^5*𝟑^3*𝟓^2/τ)` (θ = 21600/τ) | `:96` |
| `MetricArcsecond` | `… , 𝟏, 𝟐^7*𝟑^4*𝟓^3/τ)` (θ = 1296000/τ) | `:97` |
| `SI1976` | `MetricSystem(milli, τ/𝟐^6/𝟓^7, Constant(8.31432))` | `:98` |
| `CODATA` | `ConventionalSystem(RK2014, KJ2014, Rᵤ2014)` | `:99` |
| `Conventional` | `ConventionalSystem(RK1990, KJ1990)` | `:100` |
| `International` | `ElectricSystem(Metric, Ωᵢₜ, Vᵢₜ)` | `:101` |
| `InternationalMean` | `ElectricSystem(Metric, Constant(1.00049), Constant(1.00034))` | `:102` |
| `EMU` | `GaussSystem(Metric, 𝟏, 𝟐*τ)` | `:104` |
| `ESU` | `GaussSystem(Metric, (hecto*𝘤)^-2, 𝟐*τ)` | `:105` |
| `Gauss` | `GaussSystem(Metric, 𝟏, 𝟐*τ, centi/𝘤)` | `:106` |
| `LorentzHeaviside` | `GaussSystem(Metric, 𝟏, 𝟏, centi/𝘤)` | `:107` |
| `British` | `RankineSystem(Metric, ft, lb*g₀/ft)` | `:111` |
| `Survey` | `RankineSystem(Metric, ftUS, lb, g₀/ftUS)` | `:113` |
| `English` | `RankineSystem(Metric, ft, lb, g₀/ft)` | `:115` |
| `FPS` | `RankineSystem(Metric, ft, lb)` | `:117` |
| `IPS` | `RankineSystem(Metric, ft/𝟐^2/𝟑, lb*g₀*𝟐^2*𝟑/ft)` | `:119` |
| `Hubble` | `AstronomicalSystem(Metric, th, 𝘤*th, mₑ)` | `:123` |
| `Cosmological` | `AstronomicalSystem(Metric, lc/𝘤, lc, mc)` | `:124` |
| `CosmologicalQuantum` | `AstronomicalSystem(Metric, tcq, lcq, mcq)` | `:125` |
| `Nautical` | `EntropySystem(Metric, HOUR, nm, em^3, 𝟏, τ*𝟑^3/𝟐^10/𝟓^12, milli)` | `:129` |
| `Meridian` | `EntropySystem(Metric, 𝟏, em, em^3, 𝟏, τ/𝟐^6/𝟓^7, milli)` | `:130` |
| `Gravitational` | `EntropySystem(Metric, 𝟏, 𝟏, g₀)` | `:133` |
| `IAU☉` | `EntropySystem(Metric, DAY, au, GM☉/G)` | `:135` |
| `IAUE` | `EntropySystem(Metric, DAY, LD, GME/G)` | `:136` |
| `IAUJ` | `EntropySystem(Metric, DAY, JD, GMJ/G)` | `:137` |
| `MTS` | `EntropySystem(Metric, 𝟏, 𝟏, kilo)` | `:138` |
| `KKH` | `EntropySystem(Metric, HOUR, kilo, 𝟏)` | `:139` |
| `MPH` | `EntropySystem(FPS, HOUR, mi, 𝟏)` (**built on FPS, not Metric**) | `:140` |
| `FFF` | `EntropySystem(Metric, 𝟕*𝟐*DAY, fur, (𝟐*𝟑^2*𝟓)*lb, °R, Constant(0.), 𝟏)` (fortnight, furlong, firkin = 90 lb; **μ₀ = 0.0**) | `:141` |
| `Planck` | `unitsystem(𝟏, 𝟏, 𝟏, 𝟏, √(𝟐*τ*αG))` | `:145` |
| `PlanckGauss` | `unitsystem(𝟏, 𝟏, 𝟏, 𝟐*τ, √αG)` | `:146` |
| `Stoney` | `unitsystem(𝟏, αinv, 𝟏, 𝟐*τ, √(αG*αinv))` | `:147` |
| `Hartree` | `unitsystem(𝟏, 𝟏, αinv, 𝟐*τ*α^2, 𝟏)` | `:148` |
| `Rydberg` | `unitsystem(𝟏, 𝟏, 𝟐*αinv, τ/𝟐*α^2, inv(𝟐))` | `:149` |
| `Schrodinger` | `unitsystem(𝟏, 𝟏, αinv, 𝟐*τ*α^2, √(αG*αinv))` | `:150` |
| `Electronic` | `unitsystem(𝟏, αinv, 𝟏, 𝟐*τ, 𝟏)` | `:151` |
| `Natural` | `unitsystem(𝟏, 𝟏, 𝟏, 𝟏, 𝟏)` | `:152` |
| `NaturalGauss` | `unitsystem(𝟏, 𝟏, 𝟏, 𝟐*τ, 𝟏)` | `:153` |
| `QCD` | `unitsystem(𝟏, 𝟏, 𝟏, 𝟏, inv(μₚₑ))` | `:154` |
| `QCDGauss` | `unitsystem(𝟏, 𝟏, 𝟏, 𝟐*τ, inv(μₚₑ))` | `:155` |
| `QCDoriginal` | `unitsystem(𝟏, 𝟏, 𝟏, 𝟐*τ*α, inv(μₚₑ))` | `:156` |

Every system is wrapped in `Quantity(...)`, which is the identity (`UnitSystems.jl:95`). Commented-out systems are not exported: `SI2019Engineering`, `Thomson`, `Kennelly`, `British2019`, `Survey2019`, `English2019`, `FPS2019`, `IPS2019`, `Astronomical`, `EMU2019`/`ESU2019` (as SI2019-based), `Mixed`, `MeridianEngineering`, `GravitationalSI2019`, `GravitationalMeridian`. The Wolfram kernel still defines several of them (`Kernel/systems.wl:141,160,173-175`).

**Aliases** (`initdata.jl:158-167`, `systems.jl:26`): `SI = SI2019`, `MKS = Metric`, `ME = MetricEngineering = Engineering`, `GM = GravitationalMetric = Gravitational`, `IAU = IAU☉`, `CGS = Gauss`, `CGSm = EMU`, `CGSe = ESU`, `HLU = LorentzHeaviside`, `EnglishEngineering = EE = English`, `BritishGravitational = BG = British`, `EnglishUS = Survey`, `AbsoluteEnglish = AE = FPS`. The aliases **`EMU2019 = EMU`, `ESU2019 = ESU`** are misleading (they are *not* SI2019-based). They are unexported. `show` of an alias prints the canonical name (`string(IAU) == "IAU☉"`, `string(CGS) == "Gauss"`).

`unitname(::typeof(normal(u))) = "u"` is defined for every name in `Systems` (`initdata.jl:169-171`). All 48 systems are pairwise distinct types, so every `show` is unique. Any other system prints `Unknown` (`UnitSystems.jl:186`).

### 2.6 Category tuples (`UnitSystems.jl:22-53`, in order)

- `Dimensionless` (6): `coupling, finestructure, electronunit, protonunit, protonelectron, darkenergydensity`
- `Constants` (12): `lightspeed, planck, planckreduced, electronmass, molarmass, boltzmann, vacuumpermeability, rationalization, lorentz, luminousefficacy, gravity, radian`
- `Physics` (28): `turn, spat, dalton, protonmass, planckmass, gravitation, gaussgravitation, einstein, hartree, rydberg, bohr, electronradius, avogadro, molargas, stefan, radiationdensity, vacuumpermittivity, electrostatic, magnetostatic, biotsavart, elementarycharge, faraday, vacuumimpedance, conductancequantum, klitzing, josephson, magneticfluxquantum, magneton`
- `Derived` (196): see the table in §2.9 (order is exactly `meta.json:Derived`)
- `Kinematic` (28), `Mechanical` (37), `Electromagnetic` (36), `Thermodynamic` (10), `Molar` (12), `Photometric` (7)
- `Mechanics = [Kinematic..., Mechanical...]`
- `Convert = [:dimensionless, Mechanics..., Electromagnetic..., Thermodynamic..., Molar..., Photometric...]` (131; order in §2.8)

### 2.7 Generated method families (metaprogramming loops)

| loop | methods generated | src |
|---|---|---|
| `for unit ∈ Dimensionless` | `unit(U::UnitSystem) = unit(universe(U))` | `UnitSystems.jl:291-293` |
| `for unit ∈ (boltzmann, planckreduced, lightspeed, vacuumpermeability, permeability, electronmass, molarmass, radian)` | `unit(U::UnitSystem, C::Coupling) = unit(U)`. This is the **fallback**; specialised methods override it (§4.7) | `:294-296` |
| `for unit ∈ (Constants..., permeability)` | `unit(U::UnitSystem, S::UnitSystem) = isquantity(U,S) ? evaldim(unit)(U,S) : unit(unit(S)/unit(U))` | `:297-299` |
| `for unit ∈ Convert` | `unit(v::Real, U) = isquantity(U) ? … : unit(v, U, Metric)`; `unit(v::Real, U, S) = isquantity(U,S) ? … : (u = unit(U,S); isone(u) ? v : v/u)`; `unit(v::Real, U::T, S::T) = v` when U, S are the *same type* | `:300-305` |
| same loop, `unit ∉ (Constants..., angle, permeability)` | `unit(U::UnitSystem) = isquantity(U) ? … : unit(Natural, U)` | `:306-308` |
| `for u ∈ Systems` | `unitname(::typeof(normal(u))) = "u"` | `initdata.jl:169-171` |

`isquantity(…)` is always `false` in UnitSystems (`UnitSystems.jl:176-178`), so the `evaldim` branches are dead here. They exist for Similitude (`function evaldim end`, `:175`).

### 2.8 The 131 conversion quantities (`Convert`)

Each quantity `q` has four call forms (§2.7). **The direction convention is the most important thing to get right:**

- `q(U, S)`: the conversion factor, i.e. how many **S**-units make one **U**-unit. Example: `length(English, Metric) == 0.3048` (metres per foot).
- `q(v, U, S)`: converts a value `v` **expressed in S** into **U**. It returns `v / q(U,S)`, or `v` unchanged when `q(U,S)` is exactly one. Example: `length(1, Metric, English) == 0.3048`, i.e. 1 ft expressed in metres.
- `q(v, U)` = `q(v, U, Metric)`: converts a Metric value into U. Example: `length(1, English) == 3.280839895013123`.
- `q(U)` = `q(Natural, U)`: one natural unit expressed in U. Example: `length(Metric) == 3.8615926795842105e-13` (the reduced Compton wavelength in m). This form is **not** defined for `Constants`, `angle`, or `permeability`; for those, `q(U)` is the accessor.

**Reading the table.**

- Columns 3–4 give the verbatim Julia definition of the two-system factor and its file:line.
- Column 5 is the exact exponent vector over the ratios `r_k = c_k(S)/c_k(U)` of the 11 constants, recovered by oracle fit: `q(U,S) = Π r_k^{e_k}`, up to `unit` snapping. Exponent `1/2` appears for charge-like quantities.
- Column 6 is the resulting USQ dimension (basis `F M L T Q Θ N J A Λ C`, §4.6).
- Column 7 is the oracle value `q(Metric, English)`, i.e. how many English units make one Metric unit.

Every definition is wrapped in `unit(…)` (§4.4), except those that forward to another `q` with swapped arguments. Those "reciprocal" definitions (`compressibility = pressure(S,U)`, `frequency = time(S,U)`, …) rely on `q(S,U) = 1/q(U,S)`.

| # | quantity | Julia definition `q(U,S) =` | src | exponents over constants | USQ dims | Metric→English `q(Metric,English)` | notes |
|---|---|---|---|---|---|---|---|
| 1 | `dimensionless` | `one(a)*one(b)` | UnitSystems.jl:279 | 1 | 1 | 1 |  |
| 2 | `angle` | `unit(radian(S)/radian(U))` | UnitSystems.jl:281 | θ | A | 1 |  |
| 3 | `solidangle` | `unit(angle(U,S)^2)` | UnitSystems.jl:282 | θ^2 | A^2 | 1 |  |
| 4 | `time` | `unit(length(U,S)/lightspeed(U,S),1)  [3rd arg t IGNORED]` | kinematic.jl:95 | ħ·c^-2·mₑ^-1·θ·g₀ | T | 1 |  |
| 5 | `angulartime` | `unit(time(U,S)*angle(S,U))` | kinematic.jl:124 | ħ·c^-2·mₑ^-1·g₀ | T·A^-1 | 1 |  |
| 6 | `length` | `unit((turn(S)/turn(U))*(ħS·meU·cU·gS)/(ħU·meS·cS·gU), l)  [3rd arg l=1 snaps]` | kinematic.jl:71 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 3.280839895013123 |  |
| 7 | `angularlength` | `unit(length(U,S)*angle(S,U))` | kinematic.jl:112 | ħ·c^-1·mₑ^-1·g₀ | L·A^-1 | 3.280839895013123 |  |
| 8 | `area` | `unit(length(U,S)^2)` | kinematic.jl:113 | ħ^2·c^-2·mₑ^-2·θ^2·g₀^2 | L^2 | 10.76391041670972 |  |
| 9 | `angulararea` | `unit(area(U,S)*solidangle(S,U))` | kinematic.jl:114 | ħ^2·c^-2·mₑ^-2·g₀^2 | L^2·A^-2 | 10.76391041670972 |  |
| 10 | `volume` | `unit(length(U,S)^3)` | kinematic.jl:115 | ħ^3·c^-3·mₑ^-3·θ^3·g₀^3 | L^3 | 35.31466672148858 |  |
| 11 | `wavenumber` | `unit(length(S,U))` | kinematic.jl:116 | ħ^-1·c·mₑ·θ^-1·g₀^-1 | L^-1 | 0.3048 |  |
| 12 | `angularwavenumber` | `unit(angle(U,S)*length(S,U))` | kinematic.jl:117 | ħ^-1·c·mₑ·g₀^-1 | L^-1·A | 0.3048 |  |
| 13 | `fuelefficiency` | `area(S,U)` | kinematic.jl:122 | ħ^-2·c^2·mₑ^2·θ^-2·g₀^-2 | L^-2 | 0.09290304 |  |
| 14 | `numberdensity` | `volume(S,U)` | kinematic.jl:123 | ħ^-3·c^3·mₑ^3·θ^-3·g₀^-3 | L^-3 | 0.028316846592000004 |  |
| 15 | `frequency` | `time(S,U)` | kinematic.jl:125 | ħ^-1·c^2·mₑ·θ^-1·g₀^-1 | T^-1 | 1 |  |
| 16 | `angularfrequency` | `unit(angle(U,S)*time(S,U))` | kinematic.jl:126 | ħ^-1·c^2·mₑ·g₀^-1 | T^-1·A | 1 |  |
| 17 | `frequencydrift` | `unit(time(S,U)^2)` | kinematic.jl:127 | ħ^-2·c^4·mₑ^2·θ^-2·g₀^-2 | T^-2 | 1 |  |
| 18 | `stagnance` | `lightspeed(S,U)` | kinematic.jl:129 | c^-1 | L^-1·T | 0.3048 |  |
| 19 | `speed` | `lightspeed(U,S)` | kinematic.jl:128 | c | L·T^-1 | 3.280839895013123 |  |
| 20 | `acceleration` | `unit(speed(U,S)/time(U,S))` | kinematic.jl:130 | ħ^-1·c^3·mₑ·θ^-1·g₀^-1 | L·T^-2 | 3.280839895013123 |  |
| 21 | `jerk` | `unit(speed(U,S)/time(U,S)^2)` | kinematic.jl:131 | ħ^-2·c^5·mₑ^2·θ^-2·g₀^-2 | L·T^-3 | 3.280839895013123 |  |
| 22 | `snap` | `unit(speed(U,S)/time(U,S)^3)` | kinematic.jl:132 | ħ^-3·c^7·mₑ^3·θ^-3·g₀^-3 | L·T^-4 | 3.280839895013123 |  |
| 23 | `crackle` | `unit(speed(U,S)/time(U,S)^4)` | kinematic.jl:133 | ħ^-4·c^9·mₑ^4·θ^-4·g₀^-4 | L·T^-5 | 3.280839895013123 |  |
| 24 | `pop` | `unit(speed(U,S)/time(U,S)^5)` | kinematic.jl:134 | ħ^-5·c^11·mₑ^5·θ^-5·g₀^-5 | L·T^-6 | 3.280839895013123 |  |
| 25 | `volumeflow` | `unit(area(U,S)*speed(U,S))` | kinematic.jl:135 | ħ^2·c^-1·mₑ^-2·θ^2·g₀^2 | L^3·T^-1 | 35.31466672148858 |  |
| 26 | `etendue` | `unit(area(U,S)*solidangle(U,S))` | kinematic.jl:118 | ħ^2·c^-2·mₑ^-2·θ^4·g₀^2 | L^2·A^2 | 10.76391041670972 |  |
| 27 | `photonintensity` | `unit(frequency(U,S)/solidangle(U,S))` | kinematic.jl:119 | ħ^-1·c^2·mₑ·θ^-3·g₀^-1 | T^-1·A^-2 | 1 |  |
| 28 | `photonirradiance` | `unit(length(S,U)*speed(S,U))` | kinematic.jl:120 | ħ^-1·mₑ·θ^-1·g₀^-1 | L^-2·T | 0.09290304 | dims L⁻²T (=1/(length·speed)); SI expects L⁻²T⁻¹. Same in Wolfram kernel (Wavenumber/Speed). |
| 29 | `photonradiance` | `unit(photonirradiance(U,S)/solidangle(U,S))` | kinematic.jl:121 | ħ^-1·mₑ·θ^-3·g₀^-1 | L^-2·T·A^-2 | 0.09290304 | inherits photonirradiance quirk |
| 30 | `inertia` | `unit(mass(U,S)/gravity(U,S))` | kinematic.jl:139 | mₑ·g₀^-1 | F·L^-1·T^2 | 0.06852176585679176 |  |
| 31 | `mass` | `electronmass(U,S)` | UnitSystems.jl:284 | mₑ | M | 2.2046226218487757 |  |
| 32 | `massflow` | `unit(mass(U,S)/time(U,S))` | kinematic.jl:167 | ħ^-1·c^2·mₑ^2·θ^-1·g₀^-1 | M·T^-1 | 2.2046226218487757 |  |
| 33 | `lineardensity` | `unit(mass(U,S)/length(U,S))` | kinematic.jl:166 | ħ^-1·c·mₑ^2·θ^-1·g₀^-1 | M·L^-1 | 0.6719689751395069 |  |
| 34 | `areadensity` | `unit(mass(U,S)/area(U,S))` | kinematic.jl:154 | ħ^-2·c^2·mₑ^3·θ^-2·g₀^-2 | M·L^-2 | 0.2048161436225217 |  |
| 35 | `density` | `unit(mass(U,S)/volume(U,S))` | kinematic.jl:155 | ħ^-3·c^3·mₑ^4·θ^-3·g₀^-3 | M·L^-3 | 0.06242796057614463 |  |
| 36 | `specificweight` | `unit(force(U,S)/volume(U,S))` | kinematic.jl:156 | ħ^-4·c^6·mₑ^5·θ^-4·g₀^-5 | F·L^-3 | 0.0063658803542641605 |  |
| 37 | `specificvolume` | `unit(volume(U,S)/mass(U,S))` | kinematic.jl:157 | ħ^3·c^-3·mₑ^-4·θ^3·g₀^3 | M^-1·L^3 | 16.018463373960135 |  |
| 38 | `force` | `unit(inertia(U,S)*acceleration(U,S))` | kinematic.jl:143 | ħ^-1·c^3·mₑ^2·θ^-1·g₀^-2 | F | 0.22480894309971047 |  |
| 39 | `specificforce` | `unit(acceleration(U,S)/gravity(U,S))` | kinematic.jl:144 | ħ^-1·c^3·mₑ·θ^-1·g₀^-2 | F·M^-1 | 0.10197162129779283 |  |
| 40 | `gravityforce` | `unit(gravity(U,S))` | kinematic.jl:145 | g₀ | F^-1·M·L·T^-2 | 32.17404855643044 |  |
| 41 | `pressure` | `unit(force(U,S)/area(U,S))` | kinematic.jl:146 | ħ^-3·c^5·mₑ^4·θ^-3·g₀^-4 | F·L^-2 | 0.02088543423315013 |  |
| 42 | `compressibility` | `pressure(S,U)` | kinematic.jl:170 | ħ^3·c^-5·mₑ^-4·θ^3·g₀^4 | F^-1·L^2 | 47.88025898033584 |  |
| 43 | `viscosity` | `unit(force(U,S)/speed(U,S)/length(U,S))` | kinematic.jl:165 | ħ^-2·c^3·mₑ^3·θ^-2·g₀^-3 | F·L^-2·T | 0.020885434233150132 |  |
| 44 | `diffusivity` | `unit(speed(U,S)*length(U,S))` | kinematic.jl:164 | ħ·mₑ^-1·θ·g₀ | L^2·T^-1 | 10.76391041670972 |  |
| 45 | `rotationalinertia` | `unit(mass(U,S)*area(U,S))` | kinematic.jl:172 | ħ^2·c^-2·mₑ^-1·θ^2·g₀^2 | M·L^2 | 23.73036040423193 |  |
| 46 | `impulse` | `unit(force(U,S)*time(U,S))` | kinematic.jl:150 | c·mₑ·g₀^-1 | F·T | 0.22480894309971047 |  |
| 47 | `momentum` | `unit(mass(U,S)*speed(U,S))` | kinematic.jl:151 | c·mₑ | M·L·T^-1 | 7.233013851209893 |  |
| 48 | `angularmomentum` | `unit(impulse(U,S)*length(U,S)/angle(U,S))` | kinematic.jl:152 | ħ | F·L·T·A^-1 | 0.7375621492772653 |  |
| 49 | `yank` | `unit(mass(U,S)*jerk(U,S))` | kinematic.jl:153 | ħ^-2·c^5·mₑ^3·θ^-2·g₀^-2 | M·L·T^-3 | 7.233013851209893 |  |
| 50 | `energy` | `unit(mass(U,S)*specificenergy(U,S))` | kinematic.jl:141 | c^2·mₑ·g₀^-1 | F·L | 0.7375621492772653 |  |
| 51 | `specificenergy` | `unit(speed(U,S)^2/gravity(U,S))` | kinematic.jl:140 | c^2·g₀^-1 | F·M^-1·L | 0.33455256331296856 |  |
| 52 | `action` | `unit(energy(U,S)*time(U,S))` | kinematic.jl:158 | ħ·θ | F·L·T | 0.7375621492772653 |  |
| 53 | `fluence` | `unit(energy(U,S)/area(U,S))` | kinematic.jl:171 | ħ^-2·c^4·mₑ^3·θ^-2·g₀^-3 | F·L^-1 | 0.06852176585679176 |  |
| 54 | `power` | `unit(energy(U,S)/time(U,S))` | kinematic.jl:142 | ħ^-1·c^4·mₑ^2·θ^-1·g₀^-2 | F·L·T^-1 | 0.7375621492772653 |  |
| 55 | `powerdensity` | `unit(power(U,S)/volume(U,S))` | kinematic.jl:169 | ħ^-4·c^7·mₑ^5·θ^-4·g₀^-5 | F·L^-2·T^-1 | 0.020885434233150132 |  |
| 56 | `irradiance` | `unit(power(U,S)/area(U,S))` | kinematic.jl:160 | ħ^-3·c^6·mₑ^4·θ^-3·g₀^-4 | F·L^-1·T^-1 | 0.06852176585679176 |  |
| 57 | `radiance` | `unit(irradiance(U,S)/solidangle(U,S))` | kinematic.jl:161 | ħ^-3·c^6·mₑ^4·θ^-5·g₀^-4 | F·L^-1·T^-1·A^-2 | 0.06852176585679176 |  |
| 58 | `radiantintensity` | `unit(power(U,S)/solidangle(U,S))` | kinematic.jl:162 | ħ^-1·c^4·mₑ^2·θ^-3·g₀^-2 | F·L·T^-1·A^-2 | 0.7375621492772653 |  |
| 59 | `spectralflux` | `unit(power(U,S)/length(U,S))` | kinematic.jl:168 | ħ^-2·c^5·mₑ^3·θ^-2·g₀^-3 | F·T^-1 | 0.22480894309971047 |  |
| 60 | `spectralexposure` | `unit(force(U,S)/speed(U,S))` | kinematic.jl:163 | ħ^-1·c^2·mₑ^2·θ^-1·g₀^-2 | F·L^-1·T | 0.06852176585679176 |  |
| 61 | `soundexposure` | `unit(time(U,S)*pressure(U,S)^2)` | kinematic.jl:176 | ħ^-5·c^8·mₑ^7·θ^-5·g₀^-7 | F^2·L^-4·T | 0.0004362013631072393 |  |
| 62 | `impedance` | `unit(specificimpedance(U,S)/area(U,S))` | kinematic.jl:178 | ħ^-5·c^6·mₑ^6·θ^-5·g₀^-6 | F·L^-5·T | 0.0005914096371874175 |  |
| 63 | `specificimpedance` | `unit(pressure(U,S)/speed(U,S))` | kinematic.jl:177 | ħ^-3·c^4·mₑ^4·θ^-3·g₀^-4 | F·L^-3·T | 0.00636588035426416 |  |
| 64 | `admittance` | `unit(area(U,S)/specificimpedance(U,S))` | kinematic.jl:179 | ħ^5·c^-6·mₑ^-6·θ^5·g₀^6 | F^-1·L^5·T^-1 | 1690.875388429121 |  |
| 65 | `compliance` | `unit(time(U,S)^2/mass(U,S))` | kinematic.jl:180 | ħ^2·c^-4·mₑ^-3·θ^2·g₀^2 | M^-1·T^2 | 0.45359237 |  |
| 66 | `inertance` | `unit(mass(U,S)/length(U,S)^4)` | kinematic.jl:181 | ħ^-4·c^4·mₑ^5·θ^-4·g₀^-4 | M·L^-4 | 0.019028042383608886 |  |
| 67 | `charge` | `unit(sqrt((turn(S)/turn(U))*(ħS·μ₀U·cU·λU·αLU²)/(ħU·μ₀S·cS·λS·αLS²)))` | electromagnetic.jl:15 | ħ^1/2·c^-1/2·μ₀^-1/2·θ^1/2·λ^-1/2·αL^-1 | Q | 1 |  |
| 68 | `chargedensity` | `unit(charge(U,S)/volume(U,S))` | electromagnetic.jl:32 | ħ^-5/2·c^5/2·μ₀^-1/2·mₑ^3·θ^-5/2·λ^-1/2·αL^-1·g₀^-3 | L^-3·Q | 0.02831684659200001 |  |
| 69 | `linearchargedensity` | `unit(charge(U,S)/length(U,S))` | electromagnetic.jl:30 | ħ^-1/2·c^1/2·μ₀^-1/2·mₑ·θ^-1/2·λ^-1/2·αL^-1·g₀^-1 | L^-1·Q | 0.3048 |  |
| 70 | `exposure` | `unit(charge(U,S)/mass(U,S))` | electromagnetic.jl:38 | ħ^1/2·c^-1/2·μ₀^-1/2·mₑ^-1·θ^1/2·λ^-1/2·αL^-1 | M^-1·Q | 0.45359237 |  |
| 71 | `mobility` | `unit(length(U,S)*speed(U,S)*electricpotential(U,S))` | electromagnetic.jl:41 | ħ^1/2·c^5/2·μ₀^1/2·θ^1/2·λ^1/2·αL | F·L^3·T^-1·Q^-1 | 7.939052901576365 |  |
| 72 | `current` | `unit(charge(U,S)/time(U,S))` | electromagnetic.jl:17 | ħ^-1/2·c^3/2·μ₀^-1/2·mₑ·θ^-1/2·λ^-1/2·αL^-1·g₀^-1 | T^-1·Q | 1 |  |
| 73 | `currentdensity` | `unit(current(U,S)/area(U,S))` | electromagnetic.jl:33 | ħ^-5/2·c^7/2·μ₀^-1/2·mₑ^3·θ^-5/2·λ^-1/2·αL^-1·g₀^-3 | L^-2·T^-1·Q | 0.09290304000000002 |  |
| 74 | `resistance` | `unit(electricpotential(U,S)/current(U,S))` | electromagnetic.jl:22 | c·μ₀·λ·αL^2 | F·L·T·Q^-2 | 0.7375621492772653 |  |
| 75 | `conductance` | `unit(current(U,S)/electricpotential(U,S))` | electromagnetic.jl:23 | c^-1·μ₀^-1·λ^-1·αL^-2 | F^-1·L^-1·T^-1·Q^2 | 1.3558179483314006 |  |
| 76 | `resistivity` | `unit(resistance(U,S)*length(U,S))` | electromagnetic.jl:39 | ħ·μ₀·mₑ^-1·θ·λ·αL^2·g₀ | F·L^2·T·Q^-2 | 2.4198233244004763 |  |
| 77 | `conductivity` | `unit(conductance(U,S)/length(U,S))` | electromagnetic.jl:34 | ħ^-1·μ₀^-1·mₑ·θ^-1·λ^-1·αL^-2·g₀^-1 | F^-1·L^-2·T^-1·Q^2 | 0.4132533106514109 |  |
| 78 | `capacitance` | `unit(charge(U,S)/electricpotential(U,S))` | electromagnetic.jl:21 | ħ·c^-3·μ₀^-1·mₑ^-1·θ·λ^-1·αL^-2·g₀ | F^-1·L^-1·Q^2 | 1.3558179483314006 |  |
| 79 | `inductance` | `unit(magneticflux(U,S)/current(U,S)*lorentz(U,S))` | electromagnetic.jl:26 | ħ·c^-1·μ₀·mₑ^-1·θ·λ·αL^2·g₀ | F·L·T^2·Q^-2 | 0.7375621492772653 |  |
| 80 | `reluctance` | `unit(rationalization(U,S)*lorentz(U,S)^2/inductance(U,S))` | electromagnetic.jl:42 | ħ^-1·c·μ₀^-1·mₑ·θ^-1·g₀^-1 | F^-1·L^-1·T^-2·Q^2·Λ·C^-2 | 1.3558179483314006 |  |
| 81 | `permeance` | `reluctance(S,U)` | electromagnetic.jl:56 | ħ·c^-1·μ₀·mₑ^-1·θ·g₀ | F·L·T^2·Q^-2·Λ^-1·C^2 | 0.7375621492772654 |  |
| 82 | `permittivity` | `unit(capacitance(U,S)*rationalization(U,S)/length(U,S))` | electromagnetic.jl:35 | c^-2·μ₀^-1·αL^-2 | F^-1·L^-2·Q^2·Λ | 0.4132533106514109 |  |
| 83 | `permeability` | `unit(permeability(S)/permeability(U))` | UnitSystems.jl:297-299 (Constants loop) | μ₀ | F·T^2·Q^-2·Λ^-1·C^2 | 0.22480894309971045 |  |
| 84 | `susceptibility` | `unit(rationalization(S,U))` | electromagnetic.jl:46 | λ^-1 | Λ^-1 | 1 |  |
| 85 | `specificsusceptibility` | `unit(magneticdipolemoment(U,S)/magneticfield(U,S)/mass(U,S))` | electromagnetic.jl:57 | ħ^3·c^-3·mₑ^-4·θ^2·λ^-1·g₀^3 | M^-1·L^3·A^-1·Λ^-1 | 16.018463373960135 |  |
| 86 | `demagnetizingfactor` | `unit(rationalization(U,S))` | electromagnetic.jl:66 | λ | Λ | 1 |  |
| 87 | `vectorpotential` | `unit(magneticflux(U,S)/length(U,S))` | electromagnetic.jl:43 | ħ^-1/2·c^3/2·μ₀^1/2·mₑ·θ^-1/2·λ^1/2·g₀^-1 | F·T·Q^-1·C | 0.22480894309971047 |  |
| 88 | `electricpotential` | `unit(energy(U,S)/charge(U,S))` | electromagnetic.jl:19 | ħ^-1/2·c^5/2·μ₀^1/2·mₑ·θ^-1/2·λ^1/2·αL·g₀^-1 | F·L·Q^-1 | 0.7375621492772653 |  |
| 89 | `magneticpotential` | `unit(magneticflux(U,S)*reluctance(U,S))` | electromagnetic.jl:54 | ħ^-1/2·c^3/2·μ₀^-1/2·mₑ·θ^-1/2·λ^1/2·g₀^-1 | T^-1·Q·Λ·C^-1 | 1 |  |
| 90 | `electricfield` | `unit(electricpotential(U,S)/length(U,S))` | electromagnetic.jl:36 | ħ^-3/2·c^7/2·μ₀^1/2·mₑ^2·θ^-3/2·λ^1/2·αL·g₀^-2 | F·Q^-1 | 0.22480894309971047 |  |
| 91 | `magneticfield` | `unit(current(U,S)*rationalization(U,S)*lorentz(U,S)/length(U,S))` | electromagnetic.jl:37 | ħ^-3/2·c^5/2·μ₀^-1/2·mₑ^2·θ^-3/2·λ^1/2·g₀^-2 | L^-1·T^-1·Q·Λ·C^-1 | 0.3048 |  |
| 92 | `electricflux` | `unit(electricpotential(U,S)*length(U,S))` | electromagnetic.jl:52 | ħ^1/2·c^3/2·μ₀^1/2·θ^1/2·λ^1/2·αL | F·L^2·Q^-1 | 2.4198233244004763 |  |
| 93 | `magneticflux` | `unit(energy(U,S)/lorentz(U,S)/current(U,S))` | electromagnetic.jl:24 | ħ^1/2·c^1/2·μ₀^1/2·θ^1/2·λ^1/2 | F·L·T·Q^-1·C | 0.7375621492772653 |  |
| 94 | `electricdisplacement` | `unit(charge(U,S)*rationalization(U,S)/area(U,S))` | electromagnetic.jl:31 | ħ^-3/2·c^3/2·μ₀^-1/2·mₑ^2·θ^-3/2·λ^1/2·αL^-1·g₀^-2 | L^-2·Q·Λ | 0.09290304000000002 |  |
| 95 | `magneticfluxdensity` | `unit(magneticflux(U,S)/area(U,S))` | electromagnetic.jl:25 | ħ^-3/2·c^5/2·μ₀^1/2·mₑ^2·θ^-3/2·λ^1/2·g₀^-2 | F·L^-1·T·Q^-1·C | 0.06852176585679176 |  |
| 96 | `electricdipolemoment` | `unit(charge(U,S)*length(U,S))` | electromagnetic.jl:53 | ħ^3/2·c^-3/2·μ₀^-1/2·mₑ^-1·θ^3/2·λ^-1/2·αL^-1·g₀ | L·Q | 3.280839895013123 |  |
| 97 | `magneticdipolemoment` | `unit(current(U,S)*lorentz(U,S)*area(U,S)/angle(U,S))` | electromagnetic.jl:40 | ħ^3/2·c^-1/2·μ₀^-1/2·mₑ^-1·θ^1/2·λ^-1/2·g₀ | L^2·T^-1·Q·A^-1·C^-1 | 10.76391041670972 |  |
| 98 | `electricpolarizability` | `unit(electricdipolemoment(U,S)/electricfield(U,S))` | electromagnetic.jl:59 | ħ^3·c^-5·μ₀^-1·mₑ^-3·θ^3·λ^-1·αL^-2·g₀^3 | F^-1·L·Q^2 | 14.593902937206364 |  |
| 99 | `magneticpolarizability` | `unit(magneticdipolemoment(U,S)/magneticfield(U,S))` | electromagnetic.jl:60 | ħ^3·c^-3·mₑ^-3·θ^2·λ^-1·g₀^3 | L^3·A^-1·Λ^-1 | 35.31466672148858 |  |
| 100 | `magneticmoment` | `unit(magneticflux(U,S)*length(U,S))` | electromagnetic.jl:44 | ħ^3/2·c^-1/2·μ₀^1/2·mₑ^-1·θ^3/2·λ^1/2·g₀ | F·L^2·T·Q^-1·C | 2.4198233244004763 | tests mark as uncertain ("prefer: 1e3") |
| 101 | `specificmagnetization` | `unit(magneticmoment(S,U)/mass(S,U))` | electromagnetic.jl:65 | ħ^-3/2·c^1/2·μ₀^-1/2·mₑ^2·θ^-3/2·λ^-1/2·g₀^-1 | F^-1·M·L^-2·T^-1·Q·C^-1 | 0.911067597216 | inverted: mass/magneticmoment (tests: "prefer: 1") |
| 102 | `polestrength` | `unit(magneticdipolemoment(U,S)/length(U,S))` | electromagnetic.jl:55 | ħ^1/2·c^1/2·μ₀^-1/2·θ^-1/2·λ^-1/2 | L·T^-1·Q·A^-1·C^-1 | 3.280839895013123 |  |
| 103 | `temperature` | `unit((kB_U·me_S·c_S²·g_U)/(kB_S·me_U·c_U²·g_S))` | thermodynamic.jl:43 | kB^-1·c^2·mₑ·g₀^-1 | Θ | 1.7999999999999998 |  |
| 104 | `entropy` | `unit(energy(U,S)/temperature(U,S))` | thermodynamic.jl:44 | kB | F·L·Θ^-1 | 0.40975674959848074 |  |
| 105 | `specificentropy` | `unit(specificenergy(U,S)/temperature(U,S))` | thermodynamic.jl:45 | kB·mₑ^-1 | F·M^-1·L·Θ^-1 | 0.18586253517387144 |  |
| 106 | `volumeheatcapacity` | `unit(entropy(U,S)/volume(U,S))` | thermodynamic.jl:46 | kB·ħ^-3·c^3·mₑ^3·θ^-3·g₀^-3 | F·L^-2·Θ^-1 | 0.011603019018416741 |  |
| 107 | `thermalconductivity` | `unit(force(U,S)/time(U,S)/temperature(U,S))` | thermodynamic.jl:47 | kB·ħ^-2·c^3·mₑ^2·θ^-2·g₀^-2 | F·T^-1·Θ^-1 | 0.12489385727761694 |  |
| 108 | `thermalconductance` | `unit(thermalconductivity(U,S)*length(U,S))` | thermodynamic.jl:48 | kB·ħ^-1·c^2·mₑ·θ^-1·g₀^-1 | F·L·T^-1·Θ^-1 | 0.40975674959848074 |  |
| 109 | `thermalresistivity` | `thermalconductivity(S,U)` | thermodynamic.jl:49 | kB^-1·ħ^2·c^-3·mₑ^-2·θ^2·g₀^2 | F^-1·T·Θ | 8.006798907468898 |  |
| 110 | `thermalresistance` | `thermalconductance(S,U)` | thermodynamic.jl:50 | kB^-1·ħ·c^-2·mₑ^-1·θ·g₀ | F^-1·L^-1·T·Θ | 2.4404723069965204 |  |
| 111 | `thermalexpansion` | `temperature(S,U)` | thermodynamic.jl:51 | kB·c^-2·mₑ^-1·g₀ | Θ^-1 | 0.5555555555555556 |  |
| 112 | `lapserate` | `unit(temperature(U,S)/length(U,S))` | thermodynamic.jl:52 | kB^-1·ħ^-1·c^3·mₑ^2·θ^-1·g₀^-2 | L^-1·Θ | 0.54864 |  |
| 113 | `molarmass` | `unit(molarmass(S)/molarmass(U))` | UnitSystems.jl:297-299 (Constants loop) | Mᵤ | M·N^-1 | 1000.0 |  |
| 114 | `molality` | `molarmass(S,U)` | thermodynamic.jl:56 | Mᵤ^-1 | M^-1·N | 0.001 |  |
| 115 | `molaramount` | `unit(mass(U,S)*molality(U,S))` | thermodynamic.jl:57 | mₑ·Mᵤ^-1 | N | 0.002204622621848776 |  |
| 116 | `molarity` | `unit(molaramount(U,S)/volume(U,S))` | thermodynamic.jl:58 | ħ^-3·c^3·mₑ^4·Mᵤ^-1·θ^-3·g₀^-3 | L^-3·N | 6.242796057614463e-5 |  |
| 117 | `molarvolume` | `unit(volume(U,S)/molaramount(U,S))` | thermodynamic.jl:59 | ħ^3·c^-3·mₑ^-4·Mᵤ·θ^3·g₀^3 | L^3·N^-1 | 16018.463373960134 |  |
| 118 | `molarentropy` | `unit(entropy(U,S)/molaramount(U,S))` | thermodynamic.jl:60 | kB·mₑ^-1·Mᵤ | F·L·Θ^-1·N^-1 | 185.86253517387144 |  |
| 119 | `molarenergy` | `unit(energy(U,S)/molaramount(U,S))` | thermodynamic.jl:61 | c^2·Mᵤ·g₀^-1 | F·L·N^-1 | 334.5525633129685 |  |
| 120 | `molarconductivity` | `unit(conductivity(U,S)*area(U,S)/molaramount(U,S))` | thermodynamic.jl:62 | ħ·c^-2·μ₀^-1·mₑ^-2·Mᵤ·θ·λ^-1·αL^-2·g₀ | F^-1·T^-1·Q^2·N^-1 | 2017.679384751238 |  |
| 121 | `molarsusceptibility` | `unit(specificsusceptibility(U,S)*molarmass(U,S))` | thermodynamic.jl:63 | ħ^3·c^-3·mₑ^-4·Mᵤ·θ^2·λ^-1·g₀^3 | L^3·N^-1·A^-1·Λ^-1 | 16018.463373960134 |  |
| 122 | `catalysis` | `unit(molaramount(U,S)/time(U,S))` | thermodynamic.jl:64 | ħ^-1·c^2·mₑ^2·Mᵤ^-1·θ^-1·g₀^-1 | T^-1·N | 0.002204622621848776 |  |
| 123 | `specificity` | `unit(volume(U,S)/molaramount(U,S)/time(U,S))` | thermodynamic.jl:65 | ħ^2·c^-1·mₑ^-3·Mᵤ·θ^2·g₀^2 | L^3·T^-1·N^-1 | 16018.463373960134 |  |
| 124 | `diffusionflux` | `unit(molaramount(U,S)*photonirradiance(U,S))` | thermodynamic.jl:66 | ħ^-1·mₑ^2·Mᵤ^-1·θ^-1·g₀^-1 | L^-2·T·N | 0.00020481614362252172 | inherits photonirradiance quirk (L⁻²·T·N) |
| 125 | `luminousflux` | `unit(frequency(U,S)*luminousenergy(U,S))` | thermodynamic.jl:70 | ħ^-1·c^4·mₑ^2·Kcd·θ^-1·g₀^-2 | J | 1 |  |
| 126 | `luminousintensity` | `unit(luminousflux(U,S)/solidangle(U,S))` | thermodynamic.jl:71 | ħ^-1·c^4·mₑ^2·Kcd·θ^-3·g₀^-2 | J·A^-2 | 1 |  |
| 127 | `luminance` | `unit(luminousintensity(U,S)/area(U,S))` | thermodynamic.jl:73 | ħ^-3·c^6·mₑ^4·Kcd·θ^-5·g₀^-4 | L^-2·J·A^-2 | 0.09290304000000002 |  |
| 128 | `illuminance` | `unit(luminousflux(U,S)/area(U,S))` | thermodynamic.jl:72 | ħ^-3·c^6·mₑ^4·Kcd·θ^-3·g₀^-4 | L^-2·J | 0.09290304000000002 |  |
| 129 | `luminousenergy` | `unit(frequency(U,S)*(luminousefficacy(S)*planck(S))/(luminousefficacy(U)*planck(U)))` | thermodynamic.jl:74 | c^2·mₑ·Kcd·g₀^-1 | T·J | 1 |  |
| 130 | `luminousexposure` | `unit(illuminance(U,S)*time(U,S))` | thermodynamic.jl:75 | ħ^-2·c^4·mₑ^3·Kcd·θ^-2·g₀^-3 | L^-2·T·J | 0.09290304000000002 |  |
| 131 | `luminousefficacy` | `unit(luminousefficacy(S)/luminousefficacy(U))` | UnitSystems.jl:297-299 (Constants loop) | Kcd | F^-1·L^-1·T·J | 1.3558179483314003 |  |

### 2.9 One-argument functions: Dimensionless, Constants, Physics, Derived units

Every entry is `f(U::UnitSystem)`, and returns the named constant or unit **expressed in U**. Physics functions also accept an explicit `C::Coupling` second argument, defaulting to `universe(U)`.

Column meanings:
- **f(Natural)** is the exact oracle value in the `Natural` system, where all 11 constants are 1. It is the pure number multiplying the monomial.
- **exps over U constants** gives `f(U) = f(Natural) · Π c_k(U)^{e_k}`, fitted on random systems with residual < 1e-15.
- **USQ dims** is the dimension that follows from those exponents.
- **Metric** and **English** are oracle values.

`NOT-A-MONOMIAL` marks functions with a `log` or another non-multiplicative structure. Rows whose notes start with **BUG** or describe dimension quirks are catalogued in §4.11. `Derived` entries are units: for example, `foot(U)` is one foot expressed in U, defined as `length(one(U), U, English)`, i.e. "1 English length unit converted into U".

#### Dimensionless (6)

| name | Julia definition `f(U) =` | src | f(Natural) | exps over U constants | USQ dims | Metric | English | notes |
|---|---|---|---|---|---|---|---|---|
| `coupling` | `coupling(universe(U))` | UnitSystems.jl:110-115,291-293 | 1.751809945750515e-45 | 1 | 1 | 1.751809945750515e-45 | 1.751809945750515e-45 |  |
| `finestructure` | `finestructure(universe(U))` | UnitSystems.jl:110-115,291-293 | 0.0072973525692838015 | 1 | 1 | 0.0072973525692838015 | 0.0072973525692838015 |  |
| `electronunit` | `electronunit(universe(U))` | UnitSystems.jl:110-115,291-293 | 0.0005485799090649074 | 1 | 1 | 0.0005485799090649074 | 0.0005485799090649074 |  |
| `protonunit` | `protonunit(universe(U))` | UnitSystems.jl:110-115,291-293 | 1.007276466621 | 1 | 1 | 1.007276466621 | 1.007276466621 |  |
| `protonelectron` | `protonelectron(universe(U))` | UnitSystems.jl:110-115,291-293 | 1836.152673432705 | 1 | 1 | 1836.152673432705 | 1836.152673432705 |  |
| `darkenergydensity` | `darkenergydensity(universe(U))` | UnitSystems.jl:110-115,291-293 | 0.6889 | 1 | 1 | 0.6889 | 0.6889 |  |

#### Constants (12)

| name | Julia definition `f(U) =` | src | f(Natural) | exps over U constants | USQ dims | Metric | English | notes |
|---|---|---|---|---|---|---|---|---|
| `lightspeed` | `type-parameter accessor` | UnitSystems.jl:151-172 | 1 | c | L·T^-1 | 2.99792458e8 | 9.835710564304461e8 |  |
| `planck` | `turn(U)*planckreduced(U,C)` | UnitSystems.jl:287 | 6.283185307179586 | ħ·θ | F·L·T | 6.62607015e-34 | 4.887138541095932e-34 |  |
| `planckreduced` | `type-parameter accessor` | UnitSystems.jl:151-172 | 1 | ħ | F·L·T·A^-1 | 1.0545718176461565e-34 | 7.778122563903315e-35 |  |
| `electronmass` | `me param (e[5])` | UnitSystems.jl:156 | 1 | mₑ | M | 9.109383701558256e-31 | 2.0082753379555867e-30 |  |
| `molarmass` | `type-parameter accessor` | UnitSystems.jl:151-172 | 1 | Mᵤ | M·N^-1 | 0.001 | 1 |  |
| `boltzmann` | `type-parameter accessor` | UnitSystems.jl:151-172 | 1 | kB | F·L·Θ^-1 | 1.3806489995254104e-23 | 5.657302463819266e-24 |  |
| `vacuumpermeability` | `type-parameter accessor` | UnitSystems.jl:151-172 | 1 | μ₀ | F·T^2·Q^-2·Λ^-1·C^2 | 1.2566370614359173e-6 | 2.8250324964133447e-7 |  |
| `rationalization` | `type-parameter accessor` | UnitSystems.jl:151-172 | 1 | λ | Λ | 1 | 1 |  |
| `lorentz` | `type-parameter accessor` | UnitSystems.jl:151-172 | 1 | αL | C^-1 | 1 | 1 |  |
| `luminousefficacy` | `type-parameter accessor` | UnitSystems.jl:151-172 | 1 | Kcd | F^-1·L^-1·T·J | 683.01969009009 | 926.0503548878946 |  |
| `gravity` | `type-parameter accessor` | UnitSystems.jl:151-172 | 1 | g₀ | F^-1·M·L·T^-2 | 1 | 32.17404855643044 |  |
| `radian` | `type-parameter accessor` | UnitSystems.jl:151-172 | 1 | θ | A | 1 | 1 |  |

#### Physics (28)

| name | Julia definition `f(U) =` | src | f(Natural) | exps over U constants | USQ dims | Metric | English | notes |
|---|---|---|---|---|---|---|---|---|
| `turn` | `tau(U)*radian(U)` | UnitSystems.jl:280 | 6.283185307179586 | θ | A | 6.283185307179586 | 6.283185307179586 |  |
| `spat` | `two(U)*turn(U)*radian(U)` | UnitSystems.jl:283 | 12.566370614359172 | θ^2 | A^2 | 12.566370614359172 | 12.566370614359172 |  |
| `dalton` | `electronmass(U,C)/electronunit(C)` | physics.jl:16 | 1822.8884862090001 | mₑ | M | 1.6605390666030467e-27 | 3.660861990696727e-27 |  |
| `protonmass` | `protonelectron(C)*electronmass(U,C)` | physics.jl:17 | 1836.152673432705 | mₑ | M | 1.6726219236940502e-27 | 3.6875001307761195e-27 |  |
| `planckmass` | `electronmass(U,C)/√coupling(C)` | UnitSystems.jl:286 | 2.3892220059055127e22 | mₑ | M | 2.176434e-8 | 4.798215631360818e-8 |  |
| `gravitation` | `lightspeed(U,C)*planck(U,C)/tau(U)/planckmass(U,C)^2` | UnitSystems.jl:288 | 1.7518099457505147e-45 | ħ·c·mₑ^-2·θ | F·M^-2·L^2 | 6.674302101972535e-11 | 3.322928526687524e-11 |  |
| `gaussgravitation` | `sqrt(normal(gravitation(IAU)))*radian(U)/day(U)` | physics.jl:18 | 2.564563512212796e-28 | ħ^-1·c^2·mₑ·g₀^-1 | T^-1·A | 1.9909836764714663e-7 | 1.9909836764714663e-7 |  |
| `einstein` | `two(U)^2*tau(U)*gravitation(U,C)/lightspeed(U,C)^4` | physics.jl:19 | 4.402778604844281e-44 | ħ·c^-3·mₑ^-2·θ | F·M^-2·L^-2·T^4 | 2.0766480968545148e-43 | 8.92355487628696e-46 |  |
| `hartree` | `electronmass(U,C)/gravity(U)*(lightspeed(U,C)*finestructure(C))^2` | physics.jl:34 | 5.3251354520432896e-5 | c^2·mₑ·g₀^-1 | F·L | 4.359744722207211e-18 | 3.2155826876113645e-18 |  |
| `rydberg` | `hartree(U,C)/(two(U)*planck(U,C))/lightspeed(U,C)` | physics.jl:35 | 4.23760814913292e-6 | ħ^-1·c·mₑ·θ^-1·g₀^-1 | L^-1 | 1.0973731568160104e7 | 3.3447933819751996e6 |  |
| `bohr` | `planckreduced(U,C)*gravity(U)/electronmass(U,C)/lightspeed(U,C)/finestructure(C)` | physics.jl:36 | 137.035999084 | ħ·c^-1·mₑ^-1·g₀ | L·A^-1 | 5.291772109022829e-11 | 1.7361457050599832e-10 |  |
| `electronradius` | `finestructure(C)*planckreduced(U,C)*gravity(U)/electronmass(U,C)/lightspeed(U,C)` | physics.jl:38 | 0.0072973525692838015 | ħ·c^-1·mₑ^-1·g₀ | L·A^-1 | 2.8179403261891358e-15 | 9.24521104392761e-15 |  |
| `avogadro` | `molarmass(U,C)*electronunit(C)/electronmass(U,C)` | physics.jl:15 | 0.0005485799090649074 | mₑ^-1·Mᵤ | N^-1 | 6.022140762070074e23 | 2.731597100740971e26 |  |
| `molargas` | `boltzmann(U,C)*avogadro(U,C)` | physics.jl:21 | 0.0005485799090649074 | kB·mₑ^-1·Mᵤ | F·L·Θ^-1·N^-1 | 8.314462618153241 | 1545.3471008183458 |  |
| `stefan` | `tau(U)^5/two(U)^4*boltzmann(U,C)^4/(three(U)*five(U)*planck(U,C)^3*lightspeed(U,C)^2)` | physics.jl:22 | 0.16449340668482265 | kB^4·ħ^-3·c^-2·θ^-3 | F·L^-1·T^-1·Θ^-4 | 5.670374411387805e-8 | 3.701265696325433e-10 |  |
| `radiationdensity` | `two(U)^2*stefan(U,C)/lightspeed(U,C)` | physics.jl:23 | 0.6579736267392906 | kB^4·ħ^-3·c^-3·θ^-3 | F·L^-2·Θ^-4 | 7.565733239877308e-16 | 1.5052357110864903e-18 |  |
| `vacuumpermittivity` | `inv(vacuumpermeability(U,C)*(lightspeed(U,C)*lorentz(U))^2)` | physics.jl:24 | 1.0 | c^-2·μ₀^-1·αL^-2 | F^-1·L^-2·Q^2·Λ | 8.854187817620389e-12 | 3.659022428761017e-12 |  |
| `electrostatic` | `rationalization(U)/(two(U)*tau(U))/vacuumpermittivity(U,C)` | physics.jl:25 | 0.07957747154594767 | c^2·μ₀·λ·αL^2 | F·L^2·Q^-2 | 8.987551787368177e9 | 2.1748287444330708e10 |  |
| `magnetostatic` | `lorentz(U)*biotsavart(U)` | physics.jl:27 | 0.07957747154594767 | μ₀·λ·αL^2 | F·T^2·Q^-2 | 1.0000000000000001e-7 | 2.2480894309971046e-8 |  |
| `biotsavart` | `vacuumpermeability(U,C)*lorentz(U)*(rationalization(U)/(two(U)*tau(U)))` | physics.jl:26 | 0.07957747154594767 | μ₀·λ·αL | F·T^2·Q^-2·C | 1.0000000000000001e-7 | 2.2480894309971046e-8 |  |
| `elementarycharge` | `sqrt(two(U)*planck(U)/(vacuumpermeability(U)/finestructure(C))/(lightspeed(U)*rationalization(U)*lorentz(U)^2))` | UnitSystems.jl:289 | 0.30282212087175264 | ħ^1/2·c^-1/2·μ₀^-1/2·θ^1/2·λ^-1/2·αL^-1 | Q | 1.6021766344367608e-19 | 1.6021766344367613e-19 |  |
| `faraday` | `elementarycharge(U,C)*avogadro(U,C)` | physics.jl:29 | 0.00016612213153066848 | ħ^1/2·c^-1/2·μ₀^-1/2·mₑ^-1·Mᵤ·θ^1/2·λ^-1/2·αL^-1 | Q·N^-1 | 96485.33218277861 | 4.376501049502383e7 |  |
| `vacuumimpedance` | `vacuumpermeability(U,C)*lightspeed(U,C)*rationalization(U)*lorentz(U)^2` | physics.jl:28 | 1 | c·μ₀·λ·αL^2 | F·L·T·Q^-2 | 376.73031346177066 | 277.8620196947614 |  |
| `conductancequantum` | `two(U)*elementarycharge(U,C)^2/planck(U,C)` | physics.jl:33 | 0.029189410277135206 | c^-1·μ₀^-1·λ^-1·αL^-2 | F^-1·L^-1·T^-1·Q^2 | 7.748091734087984e-5 | 0.00010505001838394657 |  |
| `klitzing` | `planck(U,C)/elementarycharge(U,C)^2` | physics.jl:32 | 68.517999542 | c·μ₀·λ·αL^2 | F·L·T·Q^-2 | 25812.80744523112 | 19038.549738184855 |  |
| `josephson` | `two(U)*elementarycharge(U,C)*lorentz(U)/planck(U,C)` | physics.jl:30 | 0.09639127482862168 | ħ^-1/2·c^-1/2·μ₀^-1/2·θ^-1/2·λ^-1/2 | F^-1·L^-1·T^-1·Q·C^-1 | 4.835978485488147e14 | 6.556706428369334e14 |  |
| `magneticfluxquantum` | `inv(josephson(U,C))` | physics.jl:31 | 10.374382969599107 | ħ^1/2·c^1/2·μ₀^1/2·θ^1/2·λ^1/2 | F·L·T·Q^-1·C | 2.067833847898228e-15 | 1.5251559772040946e-15 |  |
| `magneton` | `elementarycharge(U,C)*planckreduced(U,C)*lorentz(U)/(two(U)*electronmass(U,C))` | physics.jl:39 | 0.15141106043587632 | ħ^3/2·c^-1/2·μ₀^-1/2·mₑ^-1·θ^1/2·λ^-1/2 | F·M^-1·L·T·Q·A^-1·C^-1 | 9.274010080830994e-24 | 3.1026438447323213e-24 |  |

#### Derived (196)

| name | Julia definition `f(U) =` | src | f(Natural) | exps over U constants | USQ dims | Metric | English | notes |
|---|---|---|---|---|---|---|---|---|
| `hyperfine` | `frequency(ΔνCs,U,Metric)` | physics.jl:41 | 1.1840924813774081e-11 | ħ^-1·c^2·mₑ·θ^-1·g₀^-1 | T^-1 | 9.19263177e9 | 9.19263177e9 |  |
| `loschmidt` | `P/T/boltzmann(U)` with defaults `P=atmosphere(U)`, `T=T₀*temperature(SI2019,U)` (3-arg form public) | physics.jl:44 | 1.5471467609767825e-12 | ħ^-3·c^3·mₑ^3·θ^-3·g₀^-3 | L^-3 | 2.6867801117984435e25 | 7.608114025223316e23 |  |
| `wienwavelength` | `planck(U)*lightspeed(U)/boltzmann(U)/Constant(4.965114231744276303)` | physics.jl:46 | 1.265466415054113 | kB^-1·ħ·c·θ | L·Θ | 0.002897771956181264 | 0.017112826512881478 |  |
| `wienfrequency` | `Constant(2.821439372122078893)*boltzmann(U)/planck(U)` | physics.jl:47 | 0.44904602270732236 | kB·ħ^-1·θ^-1 | T^-1·Θ^-1 | 5.87892575562598e10 | 3.2660698642366558e10 |  |
| `mechanicalheat` | `molargas(U)*normal(calorie(Metric)/molargas(Metric))` | physics.jl:53 | 0.0002762367317679899 | kB·mₑ^-1·Mᵤ | F·L·Θ^-1·N^-1 | 4.186737323211058 | 778.1576129990754 |  |
| `eddington` | `mass(one(U),U,Cosmological)` | physics.jl:48 | 2.8043173241332094e82 | mₑ | M | 2.554560252645652e52 | 5.631841321858328e52 |  |
| `solarmass` | `mass(GM☉/G,U,Metric)` | physics.jl:49 | 2.1828142426007966e60 | mₑ | M | 1.9884092485076926e30 | 4.383692010753383e30 |  |
| `jupitermass` | `mass(GMJ/G,U,Metric)` | physics.jl:51 | 2.0837019513806445e57 | mₑ | M | 1.8981240594811976e27 | 4.1846472406076795e27 |  |
| `earthmass` | `mass(GME/G,U,Metric)` | physics.jl:50 | 6.5560600023981e54 | mₑ | M | 5.972166613228324e24 | 1.316637361697315e25 |  |
| `lunarmass` | `earthmass(U)/μE☾` | physics.jl:52 | 8.06397810455408e52 | mₑ | M | 7.345787071534757e22 | 1.6194688353189796e23 |  |
| `earthradius` | `sqrt(earthmass(U)*gravitation(U)/gforce(U))` | derived.jl:50 | 1.6509810466016434e19 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 6.375416323689184e6 | 2.0916720222077377e7 |  |
| `greatcircle` | `normal(turn(U))*earthradius(U)` | derived.jl:52 | 1.0373419854439422e20 | ħ·c^-1·mₑ^-1·θ^2·g₀ | L·A | 4.005792217215677e7 | 1.3142362917374271e8 | normal(turn(U))*earthradius ⇒ L·A |
| `radarmile` | `two(U)*nauticalmile(U)/lightspeed(U)` | derived.jl:36 | 9.605018383740206e15 | ħ·c^-2·mₑ^-1·θ·g₀ | T | 1.2372115337845802e-5 | 1.2372115337845805e-5 |  |
| `hubble` | `time(one(U),Hubble,U)` | physics.jl:42 | 2.8244065359403743e-39 | ħ^-1·c^2·mₑ·θ^-1·g₀^-1 | T^-1 | 2.1927112672380577e-18 | 2.192711267238058e-18 |  |
| `cosmological` | `three(U)*darkenergydensity(C)*(hubble(U)/lightspeed(U,C))^2` | physics.jl:43 | 1.648662862161893e-77 | ħ^-2·c^2·mₑ^2·θ^-2·g₀^-2 | L^-2 | 1.1056022912824226e-52 | 1.0271381389110262e-53 |  |
| `steradian` | `solidangle(one(U),U,Metric)` | derived.jl:17 | 1 | θ^2 | A^2 | 1 | 1 |  |
| `spatian` | `angle(one(U),U,MetricSpatian)` | derived.jl:18 | 3.544907701811032 | θ | A | 3.544907701811032 | 3.544907701811032 |  |
| `degree` | `angle(one(U),U,MetricDegree)` | derived.jl:20 | 0.017453292519943295 | θ | A | 0.017453292519943295 | 0.017453292519943295 |  |
| `squaredegree` | `solidangle(one(U),U,MetricDegree)` | derived.jl:21 | 0.00030461741978670857 | θ^2 | A^2 | 0.00030461741978670857 | 0.00030461741978670857 |  |
| `gradian` | `angle(one(U),U,MetricGradian)` | derived.jl:19 | 0.015707963267948967 | θ | A | 0.015707963267948967 | 0.015707963267948967 |  |
| `bradian` | `angle(turn(U)/two(U)^8,U,Metric)` | derived.jl:24 | 0.02454369260617026 | θ^2 | A^2 | 0.02454369260617026 | 0.02454369260617026 | BUG: angle(turn(U)/2^8,U,Metric) double-applies θ ⇒ A²; wrong when radian≠1 |
| `arcminute` | `angle(one(U),U,MetricArcminute)` | derived.jl:22 | 0.0002908882086657216 | θ | A | 0.0002908882086657216 | 0.0002908882086657216 |  |
| `arcsecond` | `angle(one(U),U,MetricArcsecond)` | derived.jl:23 | 4.84813681109536e-6 | θ | A | 4.84813681109536e-6 | 4.84813681109536e-6 |  |
| `second` | `time(one(U),U,Metric)` | derived.jl:31 | 7.763440706342947e20 | ħ·c^-2·mₑ^-1·θ·g₀ | T | 1 | 1 |  |
| `minute` | `two(U)^2*three(U)*five(U)*second(U)` | derived.jl:32 | 4.658064423805769e22 | ħ·c^-2·mₑ^-1·θ·g₀ | T | 60 | 60 |  |
| `hour` | `two(U)^2*three(U)*five(U)*minute(U)` | derived.jl:33 | 2.7948386542834614e24 | ħ·c^-2·mₑ^-1·θ·g₀ | T | 3600 | 3600 |  |
| `day` | `two(U)^3*three(U)*hour(U)` | derived.jl:34 | 6.707612770280308e25 | ħ·c^-2·mₑ^-1·θ·g₀ | T | 86400 | 86400 |  |
| `gaussianmonth` | `tau(U)*sqrt(LD^3/GME)*time(Metric,U)` | physics.jl:56 | 1.8413595335735227e27 | ħ·c^-2·mₑ^-1·θ·g₀ | T | 2.3718343492584163e6 | 2.3718343492584163e6 |  |
| `siderealmonth` | `gaussianmonth(U)/normal(sqrt(earthmass(IAUE)+lunarmass(IAUE)))` | physics.jl:57 | 1.8301385467754828e27 | ħ·c^-2·mₑ^-1·θ·g₀ | T | 2.3573807233179593e6 | 2.3573807233179593e6 |  |
| `synodicmonth` | `inv(inv(siderealmonth(U))-inv(siderealyear(U)))` | physics.jl:58 | 1.977885805891537e27 | ħ·c^-2·mₑ^-1·θ·g₀ | T | 2.5476922935413797e6 | 2.5476922935413797e6 |  |
| `year` | `aⱼ*day(U)` | derived.jl:35 | 2.4499555643448823e28 | ħ·c^-2·mₑ^-1·θ·g₀ | T | 3.15576e7 | 3.15576e7 |  |
| `gaussianyear` | `turn(U)/gaussgravitation(U)` | physics.jl:54 | 2.450001833551095e28 | ħ·c^-2·mₑ^-1·θ·g₀ | T | 3.1558195988402087e7 | 3.1558195988402087e7 |  |
| `siderealyear` | `gaussianyear(U)/normal(sqrt(solarmass(IAU)+earthmass(IAU)+lunarmass(IAU)))` | physics.jl:55 | 2.449998109026753e28 | ħ·c^-2·mₑ^-1·θ·g₀ | T | 3.1558148013226096e7 | 3.1558148013226096e7 |  |
| `jovianyear` | `day(U)*sqrt(normal(jupiterdistance(U)^3/solarmass(U)/gravitation(U)))*turn(U)/radian(U)/normal(sqrt(solarmass(IAU)+jupitermass(IAU)))` | physics.jl:59 | 1.9498869741990095e55 | ħ^2·c^-4·mₑ^-2·θ^2·g₀^5/2 | F^-1/2·M^1/2·L^1/2·T | 3.235198684088133e13 | 1.8350749790257906e14 | BUG: only correct in IAU-family (day(U)=1); dims F^-½M^½L^½T |
| `angstrom` | `hecto(U)*pico(U)*meter(U)` | derived.jl:43 | 258.9605074835788 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 1.0e-10 | 3.280839895013123e-10 |  |
| `inch` | `length(one(U),U,IPS)` | derived.jl:45 | 6.5775968900829025e10 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 0.025400000000000002 | 0.08333333333333334 |  |
| `foot` | `length(one(U),U,English)` | derived.jl:44 | 7.893116268099481e11 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 0.3048 | 1 |  |
| `surveyfoot` | `length(one(U),U,Survey)` | derived.jl:48 | 7.89313205436359e11 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 0.3048006096012192 | 1.000002000004 |  |
| `yard` | `three(U)*foot(U)` | derived.jl:47 | 2.367934880429844e12 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 0.9144000000000001 | 3 |  |
| `meter` | `length(one(U),U,Metric)` | derived.jl:40 | 2.589605074835788e12 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 1 | 3.280839895013123 |  |
| `earthmeter` | `length(one(U),U,Meridian)` | derived.jl:41 | 2.5933549636098555e12 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 1.0014480543039195 | 3.2855907293435678 |  |
| `mile` | `length(two(U)^5*three(U)*five(U)*eleven(U),U,English)` | derived.jl:59 | 4.167565389556526e15 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 1609.3440000000003 | 5280 |  |
| `statutemile` | `length(two(U)^5*three(U)*five(U)*eleven(U),U,Survey)` | derived.jl:49 | 4.1675737247039755e15 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 1609.3472186944375 | 5280.01056002112 |  |
| `meridianmile` | `length(two(U)^4*five(U)^5/three(U)^3,U,Metric)` | derived.jl:61 | 4.795564953399607e15 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 1851.851851851852 | 6075.629435209487 |  |
| `admiraltymile` | `length(two(U)^6*five(U)*nineteen(U),U,English)` | derived.jl:60 | 4.799014691004484e15 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 1853.1840000000002 | 6080 |  |
| `nauticalmile` | `length(one(U),U,Nautical)` | derived.jl:54 | 4.802509191870103e15 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 1854.5334338961468 | 6084.427276562163 |  |
| `lunardistance` | `length(𝟏,U,IAUE)` | derived.jl:57 | 9.95441601161802e20 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 3.8439900000000006e8 | 1.2611515748031495e9 |  |
| `astronomicalunit` | `length(𝟏,U,IAU)` | derived.jl:56 | 3.873994051493481e23 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 1.495978707e11 | 4.9080666240157477e11 |  |
| `jupiterdistance` | `length(𝟏,U,IAUJ)` | derived.jl:58 | 2.015953169053089e24 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 7.784789999999999e11 | 2.554064960629921e12 |  |
| `lightyear` | `year(U)*lightspeed(U)` | derived.jl:62 | 2.4499555643448823e28 | ħ·c^-1·mₑ^-1·θ·g₀ | L | 9.4607304725808e15 | 3.103914197040945e16 |  |
| `parsec` | `astronomicalunit(U)*two(U)^7*three(U)^4*five(U)^3/turn(U)` | derived.jl:63 | 7.990686324337067e28 | ħ·c^-1·mₑ^-1·g₀ | L·A^-1 | 3.085677581491367e16 | 1.0123614112504485e17 | divides by turn(U) ⇒ L·A⁻¹ |
| `barn` | `area((two(U)*five(U))^-28,U,Metric)` | derived.jl:67 | 0.0006706054443615276 | ħ^2·c^-2·mₑ^-2·θ^2·g₀^2 | L^2 | 1.0000000000000015e-28 | 1.0763910416709738e-27 |  |
| `hectare` | `area(hecto(U)*hecto(U),U,Metric)` | derived.jl:68 | 6.706054443615267e28 | ħ^2·c^-2·mₑ^-2·θ^2·g₀^2 | L^2 | 10000 | 107639.10416709722 |  |
| `acre` | `area(two(U)^-7/five(U),U,MPH)` | derived.jl:69 | 2.713843949410851e28 | ħ^2·c^-2·mₑ^-2·θ^2·g₀^2 | L^2 | 4046.856422400001 | 43560.00000000002 |  |
| `surveyacre` | `area(two(U)^3*three(U)^2*five(U)*eleven(U)^2,U,Survey)` | derived.jl:70 | 2.7138548048192138e28 | ħ^2·c^-2·mₑ^-2·θ^2·g₀^2 | L^2 | 4046.8726098742522 | 43560.17424052271 |  |
| `liter` | `volume(inv((two(U)*five(U))^3),U,Metric)` | derived.jl:77 | 1.736603261931118e34 | ħ^3·c^-3·mₑ^-3·θ^3·g₀^3 | L^3 | 0.001 | 0.035314666721488586 |  |
| `gallon` | `volume(three(U)*seven(U)*eleven(U),U,IPS)` | derived.jl:76 | 6.573758451846897e34 | ħ^3·c^-3·mₑ^-3·θ^3·g₀^3 | L^3 | 0.003785411784000002 | 0.1336805555555556 |  |
| `quart` | `gallon(U)/two(U)^2` | derived.jl:78 | 1.6434396129617242e34 | ħ^3·c^-3·mₑ^-3·θ^3·g₀^3 | L^3 | 0.0009463529460000005 | 0.0334201388888889 |  |
| `pint` | `quart(U)/two(U)` | derived.jl:79 | 8.217198064808621e33 | ħ^3·c^-3·mₑ^-3·θ^3·g₀^3 | L^3 | 0.00047317647300000024 | 0.01671006944444445 |  |
| `cup` | `pint(U)/two(U)` | derived.jl:80 | 4.1085990324043106e33 | ħ^3·c^-3·mₑ^-3·θ^3·g₀^3 | L^3 | 0.00023658823650000012 | 0.008355034722222225 |  |
| `fluidounce` | `cup(U)/two(U)^3` | derived.jl:81 | 5.135748790505388e32 | ħ^3·c^-3·mₑ^-3·θ^3·g₀^3 | L^3 | 2.9573529562500015e-5 | 0.0010443793402777782 |  |
| `teaspoon` | `five(U)*milli(U)*liter(U)` | derived.jl:82 | 8.68301630965559e31 | ħ^3·c^-3·mₑ^-3·θ^3·g₀^3 | L^3 | 5.0e-6 | 0.00017657333360744293 |  |
| `tablespoon` | `three(U)*teaspoon(U)` | derived.jl:83 | 2.6049048928966772e32 | ħ^3·c^-3·mₑ^-3·θ^3·g₀^3 | L^3 | 1.5000000000000002e-5 | 0.0005297200008223288 |  |
| `bubnoff` | `meter(U)/year(U)` | derived.jl:88 | 1.0570008340246155e-16 | c | L·T^-1 | 3.168808781402895e-8 | 1.0396354269694536e-7 |  |
| `ips` | `inch(U)/second(U)` | derived.jl:89 | 8.472528018033064e-11 | c | L·T^-1 | 0.025400000000000002 | 0.08333333333333334 |  |
| `fps` | `foot(U)/second(U)` | derived.jl:90 | 1.0167033621639674e-9 | c | L·T^-1 | 0.3048 | 1.0 |  |
| `fpm` | `foot(U)/minute(U)` | derived.jl:91 | 1.6945056036066124e-11 | c | L·T^-1 | 0.00508 | 0.016666666666666666 |  |
| `ms` | `meter(U)/second(U)` | derived.jl:92 | 3.335640951981521e-9 | c | L·T^-1 | 1.0 | 3.280839895013123 |  |
| `kmh` | `kilo(U)*meter(U)/hour(U)` | derived.jl:93 | 9.265669311059779e-10 | c | L·T^-1 | 0.2777777777777778 | 0.9113444152814231 |  |
| `mph` | `mile(U)/hour(U)` | derived.jl:94 | 1.4911649311738188e-9 | c | L·T^-1 | 0.4470400000000001 | 1.4666666666666666 |  |
| `knot` | `nauticalmile(U)/hour(U)` | derived.jl:95 | 1.718349352478584e-9 | c | L·T^-1 | 0.515148176082263 | 1.690118687933934 |  |
| `mps` | `mile(U)/second(U)` | derived.jl:96 | 5.368193752225749e-6 | c | L·T^-1 | 1609.3440000000003 | 5280.0 |  |
| `grain` | `milli(U)*pound(U)/seven(U)` | derived.jl:100 | 7.113424148432289e25 | mₑ | M | 6.479891000000001e-5 | 0.00014285714285714287 |  |
| `gram` | `mass(one(U),U,Gauss)` | derived.jl:101 | 1.097769105750743e27 | mₑ | M | 0.001 | 0.002204622621848776 |  |
| `earthgram` | `mass(milli(U),U,Meridian)` | derived.jl:102 | 1.1025449025274052e27 | mₑ | M | 0.0010043504565319281 | 0.0022142137367344343 |  |
| `kilogram` | `mass(one(U),U,Metric)` | derived.jl:103 | 1.0977691057507429e30 | mₑ | M | 1 | 2.2046226218487757 |  |
| `tonne` | `mass(kilo(U),U,Metric)` | derived.jl:104 | 1.097769105750743e33 | mₑ | M | 1000 | 2204.622621848776 |  |
| `ton` | `mass(two(U)*kilo(U),U,English)` | derived.jl:105 | 9.958793807805203e32 | mₑ | M | 907.18474 | 2000 |  |
| `pound` | `mass(one(U),U,English)` | derived.jl:106 | 4.979396903902602e29 | mₑ | M | 0.45359237 | 1 |  |
| `ounce` | `mass(two(U)^-4,U,English)` | derived.jl:107 | 3.1121230649391262e28 | mₑ | M | 0.028349523125 | 0.0625 |  |
| `slug` | `mass(one(U),U,British)` | derived.jl:108 | 1.602073577679017e31 | mₑ | M | 14.593902937206364 | 32.17404855643044 |  |
| `slinch` | `mass(one(U),U,IPS)` | derived.jl:109 | 1.92248829321482e32 | mₑ | M | 175.12683524647633 | 386.0885826771652 |  |
| `hyl` | `mass(one(U),U,Gravitational)` | derived.jl:110 | 1.0765437400910523e31 | mₑ | M | 9.80665 | 21.619962434553297 |  |
| `dyne` | `force(one(U),U,Gauss)` | derived.jl:114 | 4.716676179378232e-5 | ħ^-1·c^3·mₑ^2·θ^-1·g₀^-2 | F | 1.0e-5 | 2.2480894309971053e-6 |  |
| `newton` | `force(one(U),U,Metric)` | derived.jl:115 | 4.716676179378234 | ħ^-1·c^3·mₑ^2·θ^-1·g₀^-2 | F | 1 | 0.2248089430997105 |  |
| `poundal` | `force(one(U),U,FPS)` | derived.jl:116 | 0.6521038499863038 | ħ^-1·c^3·mₑ^2·θ^-1·g₀^-2 | F | 0.13825495437600002 | 0.031080950171567256 |  |
| `poundforce` | `force(one(U),U,English)` | derived.jl:117 | 20.980820933294567 | ħ^-1·c^3·mₑ^2·θ^-1·g₀^-2 | F | 4.4482216152605005 | 1 |  |
| `kilopond` | `force(one(U),U,Engineering)` | derived.jl:118 | 46.25479245449956 | ħ^-1·c^3·mₑ^2·θ^-1·g₀^-2 | F | 9.80665 | 2.2046226218487757 |  |
| `psi` | `pressure(one(U),U,IPS)` | derived.jl:125 | 4.849399562844834e-21 | ħ^-3·c^5·mₑ^4·θ^-3·g₀^-4 | F·L^-2 | 6894.757293168356 | 143.99999999999997 |  |
| `pascal` | `pressure(one(U),U,Metric)` | derived.jl:122 | 7.0334594194488095e-25 | ħ^-3·c^5·mₑ^4·θ^-3·g₀^-4 | F·L^-2 | 1 | 0.02088543423315013 |  |
| `bar` | `pressure(hecto(U)*kilo(U),U,Metric)` | derived.jl:123 | 7.033459419448809e-20 | ħ^-3·c^5·mₑ^4·θ^-3·g₀^-4 | F·L^-2 | 100000 | 2088.5434233150127 |  |
| `barye` | `pressure(one(U),U,Gauss)` | derived.jl:124 | 7.033459419448801e-26 | ħ^-3·c^5·mₑ^4·θ^-3·g₀^-4 | F·L^-2 | 0.09999999999999996 | 0.002088543423315013 |  |
| `technicalatmosphere` | `kilopond(U)/(centi(U)*meter(U))^2` | derived.jl:126 | 6.897467481573766e-20 | ħ^-3·c^5·mₑ^4·θ^-3·g₀^-4 | F·L^-2 | 98066.49999999999 | 2048.161436225217 |  |
| `atmosphere` | `pressure(atm,U,Metric)` | derived.jl:127 | 7.126652756756506e-20 | ħ^-3·c^5·mₑ^4·θ^-3·g₀^-4 | F·L^-2 | 101325.0 | 2116.2166236739367 |  |
| `inchmercury` | `pressure(inHg,U,Metric)` | derived.jl:128 | 2.0769791714563236e-28 | ħ^-3·c^5·mₑ^4·θ^-3·g₀^-4 | F·L^-2 | 0.0002952998016471232 | 6.1674645863632695e-6 | BUG: inHg=Constant(1/3386.389) is inverted (gives 2.95e-4 Pa, should be 3386.389 Pa) |
| `torr` | `pressure(atm/(two(U)^3*five(U)*nineteen(U)),U,Metric)` | derived.jl:129 | 9.377174679942771e-23 | ħ^-3·c^5·mₑ^4·θ^-3·g₀^-4 | F·L^-2 | 133.32236842105263 | 2.784495557465706 |  |
| `electronvolt` | `elementarycharge(U)*electricpotential(one(U),U,SI2019)` | derived.jl:133 | 1.9569511835613585e-6 | c^2·mₑ·g₀^-1 | F·L | 1.6021766339999997e-19 | 1.1817048416948545e-19 |  |
| `erg` | `energy(one(U),U,Gauss)` | derived.jl:134 | 1.2214328570474947e6 | c^2·mₑ·g₀^-1 | F·L | 1.0e-7 | 7.375621492772653e-8 |  |
| `joule` | `energy(one(U),U,Metric)` | derived.jl:135 | 1.221432857047495e13 | c^2·mₑ·g₀^-1 | F·L | 1 | 0.7375621492772654 |  |
| `footpound` | `poundforce(U)*foot(U)` | derived.jl:136 | 1.656040590266695e13 | c^2·mₑ·g₀^-1 | F·L | 1.3558179483314006 | 1 |  |
| `calorie` | `kilocalorie(U)/(two(U)*five(U))^3` | derived.jl:139 | 5.113818530397062e13 | c^2·mₑ·g₀^-1 | F·L | 4.186737323211057 | 3.087978978566891 |  |
| `kilocalorie` | `energy(two(U)^5*five(U)^4*three(U)^2/fourtythree(U),U,International)` | derived.jl:138 | 5.1138185303970616e16 | c^2·mₑ·g₀^-1 | F·L | 4186.737323211057 | 3087.9789785668913 |  |
| `meancalorie` | `energy(two(U)^2*five(U)*three(U)^2/fourtythree(U),U,InternationalMean)` | derived.jl:137 | 5.1139463306195445e13 | c^2·mₑ·g₀^-1 | F·L | 4.186841954605035 | 3.088056150722716 |  |
| `earthcalorie` | `molaramount(temperature(calorie(U),Metric,Meridian),Metric,Meridian)` | derived.jl:140 | 5.136065975625723e13 | c^2·mₑ·g₀^-1 | F·L | 4.204951541946288 | 3.1014130968846545 |  |
| `thermalunit` | `mass(temperature(kilocalorie(U),Metric,English),Metric,English)` | derived.jl:141 | 1.2886605927515114e16 | c^2·mₑ·g₀^-1 | F·L | 1055.0400583348664 | 778.1576129990754 |  |
| `gasgallon` | `two(U)*three(U)*nineteen(U)*kilo(U)*thermalunit(U)` | derived.jl:143 | 1.469073075736723e21 | c^2·mₑ·g₀^-1 | F·L | 1.2027456665017478e8 | 8.870996788189459e7 |  |
| `tontnt` | `giga(U)*calorie(U)` | derived.jl:142 | 5.113818530397062e22 | c^2·mₑ·g₀^-1 | F·L | 4.186737323211057e9 | 3.087978978566891e9 |  |
| `watt` | `power(one(U),U,Metric)` | derived.jl:147 | 1.5733138221169772e-8 | ħ^-1·c^4·mₑ^2·θ^-1·g₀^-2 | F·L·T^-1 | 1 | 0.7375621492772654 |  |
| `horsepower` | `power(two(U)*five(U)^2*eleven(U),U,British)` | derived.jl:152 | 1.1732199151112402e-5 | ħ^-1·c^4·mₑ^2·θ^-1·g₀^-2 | F·L·T^-1 | 745.6998715822704 | 550 |  |
| `horsepowerwatt` | `power(two(U)^4*three(U)^3/five(U)*normal(tau(U)),U,British)` | derived.jl:153 | 1.1580047684850647e-5 | ħ^-1·c^4·mₑ^2·θ^-1·g₀^-2 | F·L·T^-1 | 736.0291076111621 | 542.8672105403163 |  |
| `horsepowermetric` | `power(three(U)*five(U)^2,U,Gravitational)` | derived.jl:154 | 1.157170349524759e-5 | ħ^-1·c^4·mₑ^2·θ^-1·g₀^-2 | F·L·T^-1 | 735.49875 | 542.4760388407421 |  |
| `electricalhorsepower` | `power(Constant(746),U,Metric)` | derived.jl:155 | 1.173692111299265e-5 | ħ^-1·c^4·mₑ^2·θ^-1·g₀^-2 | F·L·T^-1 | 746 | 550.22136336084 |  |
| `tonsrefrigeration` | `frequency(two(U)*five(U)/three(U),U,Metric)*thermalunit(U)` | derived.jl:148 | 5.5330303555511565e-5 | ħ^-1·c^4·mₑ^2·θ^-1·g₀^-2 | F·L·T^-1 | 3516.800194449555 | 2593.858709996918 |  |
| `boilerhorsepower` | `frequency(Constant(1339)/(two(U)^4*three(U)^2),U,Metric)*thermalunit(U)` | derived.jl:149 | 0.00015434849262672913 | ħ^-1·c^4·mₑ^2·θ^-1·g₀^-2 | F·L·T^-1 | 9810.407209099903 | 7235.785026428902 |  |
| `coulomb` | `charge(one(U),U,Metric)` | derived.jl:159 | 1.8900670148532567e18 | ħ^1/2·c^-1/2·μ₀^-1/2·θ^1/2·λ^-1/2·αL^-1 | Q | 1 | 1 |  |
| `earthcoulomb` | `charge(one(U),U,Meridian)` | derived.jl:188 | 1.8955448174126807e18 | ħ^1/2·c^-1/2·μ₀^-1/2·θ^1/2·λ^-1/2·αL^-1 | Q | 1.0028982054691058 | 1.0028982054691058 |  |
| `ampere` | `current(one(U),U,Metric)` | derived.jl:160 | 0.0024345739039508853 | ħ^-1/2·c^3/2·μ₀^-1/2·mₑ·θ^-1/2·λ^-1/2·αL^-1·g₀^-1 | T^-1·Q | 1 | 1 |  |
| `volt` | `electricpotential(one(U),U,Metric)` | derived.jl:161 | 6.462378568848395e-6 | ħ^-1/2·c^5/2·μ₀^1/2·mₑ·θ^-1/2·λ^1/2·αL·g₀^-1 | F·L·Q^-1 | 1 | 0.7375621492772654 |  |
| `henry` | `inductance(one(U),U,Metric)` | derived.jl:162 | 2.0607422415798659e18 | ħ·c^-1·μ₀·mₑ^-1·θ·λ·αL^2·g₀ | F·L·T^2·Q^-2 | 1 | 0.7375621492772654 |  |
| `ohm` | `resistance(one(U),U,Metric)` | derived.jl:163 | 0.0026544187294380724 | c·μ₀·λ·αL^2 | F·L·T·Q^-2 | 1 | 0.7375621492772654 |  |
| `siemens` | `conductance(one(U),U,Metric)` | derived.jl:164 | 376.7303134617707 | c^-1·μ₀^-1·λ^-1·αL^-2 | F^-1·L^-1·T^-1·Q^2 | 1 | 1.3558179483314003 |  |
| `farad` | `capacitance(one(U),U,Metric)` | derived.jl:165 | 2.924723450842449e23 | ħ·c^-3·μ₀^-1·mₑ^-1·θ·λ^-1·αL^-2·g₀ | F^-1·L^-1·Q^2 | 1 | 1.3558179483314003 |  |
| `weber` | `magneticflux(one(U),U,Metric)` | derived.jl:166 | 5.017029284119592e15 | ħ^1/2·c^1/2·μ₀^1/2·θ^1/2·λ^1/2 | F·L·T·Q^-1·C | 1 | 0.7375621492772654 |  |
| `tesla` | `magneticfluxdensity(one(U),U,Metric)` | derived.jl:167 | 7.481342906328818e-10 | ħ^-3/2·c^5/2·μ₀^1/2·mₑ^2·θ^-3/2·λ^1/2·g₀^-2 | F·L^-1·T·Q^-1·C | 1 | 0.06852176585679176 |  |
| `abcoulomb` | `charge(one(U),U,EMU)` | derived.jl:168 | 1.890067014853257e19 | ħ^1/2·c^-1/2·μ₀^-1/2·θ^1/2·λ^-1/2·αL^-1 | Q | 10.0 | 10.000000000000004 |  |
| `abampere` | `current(one(U),U,EMU)` | derived.jl:169 | 0.024345739039508846 | ħ^-1/2·c^3/2·μ₀^-1/2·mₑ·θ^-1/2·λ^-1/2·αL^-1·g₀^-1 | T^-1·Q | 10.0 | 10.000000000000004 |  |
| `abvolt` | `electricpotential(one(U),U,EMU)` | derived.jl:170 | 6.462378568848395e-14 | ħ^-1/2·c^5/2·μ₀^1/2·mₑ·θ^-1/2·λ^1/2·αL·g₀^-1 | F·L·Q^-1 | 9.999999999999999e-9 | 7.375621492772652e-9 |  |
| `abhenry` | `inductance(one(U),U,EMU)` | derived.jl:171 | 2.0607422415798664e9 | ħ·c^-1·μ₀·mₑ^-1·θ·λ·αL^2·g₀ | F·L·T^2·Q^-2 | 9.999999999999999e-10 | 7.375621492772648e-10 |  |
| `abohm` | `resistance(one(U),U,EMU)` | derived.jl:172 | 2.6544187294380724e-12 | c·μ₀·λ·αL^2 | F·L·T·Q^-2 | 9.999999999999999e-10 | 7.375621492772648e-10 |  |
| `abmho` | `conductance(one(U),U,EMU)` | derived.jl:173 | 3.767303134617706e11 | c^-1·μ₀^-1·λ^-1·αL^-2 | F^-1·L^-1·T^-1·Q^2 | 1.0000000000000001e9 | 1.355817948331401e9 |  |
| `abfarad` | `capacitance(one(U),U,EMU)` | derived.jl:174 | 2.92472345084245e32 | ħ·c^-3·μ₀^-1·mₑ^-1·θ·λ^-1·αL^-2·g₀ | F^-1·L^-1·Q^2 | 1.0000000000000001e9 | 1.355817948331401e9 |  |
| `maxwell` | `magneticflux(one(U),U,EMU)` | derived.jl:175 | 5.017029284119592e7 | ħ^1/2·c^1/2·μ₀^1/2·θ^1/2·λ^1/2 | F·L·T·Q^-1·C | 9.999999999999999e-9 | 7.375621492772652e-9 |  |
| `gauss` | `magneticfluxdensity(one(U),U,EMU)` | derived.jl:176 | 7.481342906328813e-14 | ħ^-3/2·c^5/2·μ₀^1/2·mₑ^2·θ^-3/2·λ^1/2·g₀^-2 | F·L^-1·T·Q^-1·C | 9.999999999999995e-5 | 6.852176585679173e-6 |  |
| `oersted` | `magneticfield(one(U),U,EMU)` | derived.jl:177 | 7.481342906328813e-14 | ħ^-3/2·c^5/2·μ₀^-1/2·mₑ^2·θ^-3/2·λ^1/2·g₀^-2 | L^-1·T^-1·Q·Λ·C^-1 | 79.57747154594766 | 24.25521332720486 |  |
| `gilbert` | `abampere(U)/two(U)/turn(U)` | derived.jl:178 | 0.0019373723556815826 | ħ^-1/2·c^3/2·μ₀^-1/2·mₑ·θ^-3/2·λ^-1/2·αL^-1·g₀^-1 | T^-1·Q·A^-1 | 0.7957747154594768 | 0.795774715459477 | abampere/2/turn(U) ⇒ T⁻¹QA⁻¹ |
| `statcoulomb` | `charge(one(U),U,ESU)` | derived.jl:179 | 6.304584936733987e8 | ħ^1/2·c^-1/2·μ₀^-1/2·θ^1/2·λ^-1/2·αL^-1 | Q | 3.3356409519815207e-10 | 3.335640951981521e-10 |  |
| `statampere` | `current(one(U),U,ESU)` | derived.jl:180 | 8.120864414644093e-13 | ħ^-1/2·c^3/2·μ₀^-1/2·mₑ·θ^-1/2·λ^-1/2·αL^-1·g₀^-1 | T^-1·Q | 3.3356409519815207e-10 | 3.335640951981521e-10 |  |
| `statvolt` | `electricpotential(one(U),U,ESU)` | derived.jl:181 | 0.0019373723556815826 | ħ^-1/2·c^5/2·μ₀^1/2·mₑ·θ^-1/2·λ^1/2·αL·g₀^-1 | F·L·Q^-1 | 299.792458 | 221.11556965959429 |  |
| `stathenry` | `inductance(one(U),U,ESU)` | derived.jl:182 | 1.852102761661624e30 | ħ·c^-1·μ₀·mₑ^-1·θ·λ·αL^2·g₀ | F·L·T^2·Q^-2 | 8.987551787368176e11 | 6.628878013031998e11 |  |
| `statohm` | `resistance(one(U),U,ESU)` | derived.jl:183 | 2.385672579618472e9 | c·μ₀·λ·αL^2 | F·L·T·Q^-2 | 8.987551787368176e11 | 6.628878013031998e11 |  |
| `statmho` | `conductance(one(U),U,ESU)` | derived.jl:184 | 4.1916900439033617e-10 | c^-1·μ₀^-1·λ^-1·αL^-2 | F^-1·L^-1·T^-1·Q^2 | 1.1126500560536185e-12 | 1.508550916209435e-12 |  |
| `statfarad` | `capacitance(one(U),U,ESU)` | derived.jl:185 | 3.254193711521183e11 | ħ·c^-3·μ₀^-1·mₑ^-1·θ·λ^-1·αL^-2·g₀ | F^-1·L^-1·Q^2 | 1.1126500560536185e-12 | 1.508550916209435e-12 |  |
| `statweber` | `magneticflux(one(U),U,ESU)` | derived.jl:186 | 1.5040675409441933e18 | ħ^1/2·c^1/2·μ₀^1/2·θ^1/2·λ^1/2 | F·L·T·Q^-1·C | 299.792458 | 221.11556965959429 |  |
| `stattesla` | `magneticfluxdensity(one(U),U,ESU)` | derived.jl:187 | 0.0022428501790291793 | ħ^-3/2·c^5/2·μ₀^1/2·mₑ^2·θ^-3/2·λ^1/2·g₀^-2 | F·L^-1·T·Q^-1·C | 2.997924579999999e6 | 205423.08612708075 |  |
| `kelvin` | `temperature(one(U),U,Metric)` | derived.jl:195 | 1.6863700520700874e-10 | kB^-1·c^2·mₑ·g₀^-1 | Θ | 1 | 1.7999999999999998 |  |
| `rankine` | `temperature(one(U),U,English)` | derived.jl:196 | 9.368722511500487e-11 | kB^-1·c^2·mₑ·g₀^-1 | Θ | 0.5555555555555556 | 1 |  |
| `celsius` | `temperature(T₀,U,Metric)` | derived.jl:197 | 4.606319797229443e-8 | kB^-1·c^2·mₑ·g₀^-1 | Θ | 273.15 | 491.66999999999996 |  |
| `fahrenheit` | `temperature(Constant(459.67),U,English)` | derived.jl:198 | 4.306520676861429e-8 | kB^-1·c^2·mₑ·g₀^-1 | Θ | 255.37222222222226 | 459.67 |  |
| `sealevel` | `temperature(T₀+𝟑*𝟓,U,Metric)` | derived.jl:194 | 4.8592753050399567e-8 | kB^-1·c^2·mₑ·g₀^-1 | Θ | 288.15 | 518.67 |  |
| `boiling` | `temperature(T₀+Constant(99.9839),U,Metric)` | derived.jl:193 | 6.292418343721148e-8 | kB^-1·c^2·mₑ·g₀^-1 | Θ | 373.1339 | 671.6410199999999 |  |
| `mole` | `molaramount(one(U),U,Metric)` | derived.jl:204 | 1.097769105750743e27 | mₑ·Mᵤ^-1 | N | 1 | 0.002204622621848776 |  |
| `earthmole` | `molaramount(one(U),U,Meridian)` | derived.jl:205 | 1.1025449025274052e27 | mₑ·Mᵤ^-1 | N | 1.0043504565319281 | 0.0022142137367344343 |  |
| `poundmole` | `molaramount(one(U),U,English)` | derived.jl:206 | 4.979396903902602e29 | mₑ·Mᵤ^-1 | N | 453.59237 | 1 |  |
| `slugmole` | `molaramount(one(U),U,British)` | derived.jl:207 | 1.602073577679017e31 | mₑ·Mᵤ^-1 | N | 14593.902937206363 | 32.17404855643044 |  |
| `slinchmole` | `molaramount(one(U),U,IPS)` | derived.jl:208 | 1.92248829321482e32 | mₑ·Mᵤ^-1 | N | 175126.83524647632 | 386.0885826771652 |  |
| `katal` | `catalysis(one(U),U,Metric)` | derived.jl:242 | 1.4140239454058495e6 | ħ^-1·c^2·mₑ^2·Mᵤ^-1·θ^-1·g₀^-1 | T^-1·N | 1 | 0.002204622621848776 |  |
| `amagat` | `loschmidt(U)/avogadro(U)` | physics.jl:45 | 2.8202760170601246e-9 | ħ^-3·c^3·mₑ^4·Mᵤ^-1·θ^-3·g₀^-3 | L^-3·N | 44.615033390134165 | 0.002785225545582672 |  |
| `lumen` | `luminousflux(one(U),U,Metric)` | derived.jl:212 | 2.303467740306956e-11 | ħ^-1·c^4·mₑ^2·Kcd·θ^-1·g₀^-2 | J | 1 | 1 |  |
| `candela` | `luminousintensity(one(U),U,Metric)` | derived.jl:213 | 2.303467740306956e-11 | ħ^-1·c^4·mₑ^2·Kcd·θ^-3·g₀^-2 | J·A^-2 | 1 | 1 |  |
| `lux` | `illuminance(one(U),U,Metric)` | derived.jl:214 | 3.434907604276987e-36 | ħ^-3·c^6·mₑ^4·Kcd·θ^-3·g₀^-4 | L^-2·J | 1 | 0.09290304 |  |
| `phot` | `illuminance(one(U),U,Gauss)` | derived.jl:216 | 3.434907604276984e-32 | ħ^-3·c^6·mₑ^4·Kcd·θ^-3·g₀^-4 | L^-2·J | 9999.999999999996 | 929.0303999999999 |  |
| `footcandle` | `illuminance(one(U),U,English)` | derived.jl:215 | 3.697303774211252e-35 | ħ^-3·c^6·mₑ^4·Kcd·θ^-3·g₀^-4 | L^-2·J | 10.76391041670972 | 1 |  |
| `nit` | `luminance(one(U),U,Metric)` | derived.jl:217 | 3.434907604276987e-36 | ħ^-3·c^6·mₑ^4·Kcd·θ^-5·g₀^-4 | L^-2·J·A^-2 | 1 | 0.09290304 |  |
| `apostilb` | `luminance(two(U)/turn(U),U,Metric)` | derived.jl:218 | 1.093365048569245e-36 | ħ^-3·c^6·mₑ^4·Kcd·θ^-6·g₀^-4 | L^-2·J·A^-3 | 0.3183098861837907 | 0.029571956088528153 | uses two(U)/turn(U) (U-angle) inside a Metric value ⇒ extra A⁻¹ |
| `stilb` | `luminance(one(U),U,Gauss)` | derived.jl:219 | 3.434907604276984e-32 | ħ^-3·c^6·mₑ^4·Kcd·θ^-5·g₀^-4 | L^-2·J·A^-2 | 9999.999999999996 | 929.0303999999999 |  |
| `lambert` | `luminance(two(U)/turn(U),U,Gauss)` | derived.jl:220 | 1.093365048569244e-32 | ħ^-3·c^6·mₑ^4·Kcd·θ^-6·g₀^-4 | L^-2·J·A^-3 | 3183.098861837906 | 295.7195608852815 | same as apostilb |
| `footlambert` | `luminance(two(U)/turn(U),U,English)` | derived.jl:221 | 1.1768883435560833e-35 | ħ^-3·c^6·mₑ^4·Kcd·θ^-6·g₀^-4 | L^-2·J·A^-3 | 3.42625909963539 | 0.3183098861837907 | same as apostilb |
| `bril` | `centi(U)*nano(U)*lambert(U)` | derived.jl:222 | 1.093365048569244e-43 | ħ^-3·c^6·mₑ^4·Kcd·θ^-6·g₀^-4 | L^-2·J·A^-3 | 3.183098861837906e-8 | 2.9571956088528152e-9 | same as apostilb |
| `talbot` | `luminousenergy(one(U),U,Metric)` | derived.jl:223 | 1.7882835220846832e10 | c^2·mₑ·Kcd·g₀^-1 | T·J | 1 | 1 |  |
| `lumerg` | `luminousenergy(centi(U)^2*milli(U),U,CGS)` | derived.jl:224 | 1788.2835220846832 | c^2·mₑ·Kcd·g₀^-1 | T·J | 1.0000000000000001e-7 | 1.0000000000000001e-7 |  |
| `neper` | `` |  | — | — | — | undef | undef | EXPORTED BUT UNDEFINED |
| `bel` | `` |  | — | — | — | undef | undef | EXPORTED BUT UNDEFINED |
| `decibel` | `` |  | — | — | — | undef | undef | EXPORTED BUT UNDEFINED |
| `hertz` | `one(U)/second(U)` | derived.jl:231 | 1.2880886681893147e-21 | ħ^-1·c^2·mₑ·θ^-1·g₀^-1 | T^-1 | 1.0 | 1.0 |  |
| `apm` | `one(U)/minute(U)` | derived.jl:26 | 2.1468144469821913e-23 | ħ^-1·c^2·mₑ·θ^-1·g₀^-1 | T^-1 | 0.016666666666666666 | 0.016666666666666666 |  |
| `rpm` | `turn(U)/minute(U)` | derived.jl:27 | 1.3488832990519373e-22 | ħ^-1·c^2·mₑ·g₀^-1 | T^-1·A | 0.10471975511965977 | 0.10471975511965977 |  |
| `kayser` | `wavenumber(one(U),U,Gauss)` | derived.jl:232 | 3.86159267958421e-11 | ħ^-1·c·mₑ·θ^-1·g₀^-1 | L^-1 | 99.99999999999999 | 30.48 |  |
| `diopter` | `angularwavenumber(one(U),U,Metric)` | derived.jl:233 | 3.86159267958421e-13 | ħ^-1·c·mₑ·g₀^-1 | L^-1·A | 1 | 0.3048 |  |
| `rayleigh` | `deka(U)*giga(U)*photonirradiance(one(U),U,Metric)` | derived.jl:225 | 1.157676361207357e6 | ħ^-1·mₑ·θ^-1·g₀^-1 | L^-2·T | 1.0e10 | 9.290304000000002e8 | inherits photonirradiance quirk |
| `flick` | `giga(U)*radiance(deka(U),U,Metric)*length(one(U),Metric,U)` | derived.jl:226 | 9.059719376361404e-36 | ħ^-4·c^7·mₑ^5·θ^-6·g₀^-5 | F·L^-2·T^-1·A^-2 | 1.0e10 | 2.088543423315013e8 |  |
| `gforce` | `specificforce(one(U),U,English)` | derived.jl:234 | 4.21352652503978e-29 | ħ^-1·c^3·mₑ·θ^-1·g₀^-2 | F·M^-1 | 9.80665 | 1 |  |
| `galileo` | `specificforce(one(U),U,Gauss)` | derived.jl:235 | 4.296601311395613e-32 | ħ^-1·c^3·mₑ·θ^-1·g₀^-2 | F·M^-1 | 0.01 | 0.0010197162129779284 |  |
| `eotvos` | `specificforce(nano(U),U,Gauss)/length(one(U),U,Gauss)` | derived.jl:236 | 1.6591724171177214e-51 | ħ^-2·c^4·mₑ^2·θ^-2·g₀^-3 | F·M^-1·L^-1 | 9.999999999999999e-10 | 3.108095017156726e-11 |  |
| `darcy` | `area(milli(U)/normal(atmosphere(Metric)),U,Gauss)` | derived.jl:237 | 6.618361158268218e12 | ħ^2·c^-2·mₑ^-2·θ^2·g₀^2 | L^2 | 9.869232667160132e-13 | 1.062315363109768e-11 |  |
| `poise` | `viscosity(one(U),U,Gauss)` | derived.jl:238 | 5.460384516336008e-5 | ħ^-2·c^3·mₑ^3·θ^-2·g₀^-3 | F·L^-2·T | 0.09999999999999998 | 0.002088543423315013 |  |
| `reyn` | `viscosity(one(U),U,IPS)` | derived.jl:239 | 3.764802596751128 | ħ^-2·c^3·mₑ^3·θ^-2·g₀^-3 | F·L^-2·T | 6894.757293168358 | 144.0 |  |
| `stokes` | `diffusivity(one(U),U,Gauss)` | derived.jl:240 | 0.8637992737081428 | ħ·mₑ^-1·θ·g₀ | L^2·T^-1 | 0.00010000000000000002 | 0.0010763910416709723 |  |
| `rayl` | `specificimpedance(one(U),U,Metric)` | derived.jl:241 | 2.1085780875998117e-16 | ħ^-3·c^4·mₑ^4·θ^-3·g₀^-4 | F·L^-3·T | 1 | 0.00636588035426416 |  |
| `mpge` | `mile(U)/gasgallon(U)` | derived.jl:243 | 2.8368673134020516e-6 | ħ·c^-3·mₑ^-2·θ·g₀^2 | F^-1 | 1.3380584481180183e-5 | 5.95198051140049e-5 |  |
| `langley` | `calorie(U)/(centi(U)*meter(U))^2` | derived.jl:244 | 7.625674043350261e-8 | ħ^-2·c^4·mₑ^3·θ^-2·g₀^-3 | F·L^-1 | 41867.37323211057 | 2868.8263456495906 |  |
| `jansky` | `fluence((Constant(1.0)*deci(U))^26,U,Metric)` | derived.jl:245 | 1.8213882206256236e-38 | ħ^-2·c^4·mₑ^3·θ^-2·g₀^-3 | F·L^-1 | 1.0000000000000015e-26 | 6.852176585679186e-28 |  |
| `solarflux` | `hecto(U)^2*jansky(U)` | derived.jl:246 | 1.8213882206256236e-34 | ħ^-2·c^4·mₑ^3·θ^-2·g₀^-3 | F·L^-1 | 1.0000000000000015e-22 | 6.852176585679186e-24 |  |
| `curie` | `Constant(37)*giga(U)*hertz(U)` | derived.jl:247 | 4.7659280723004644e-11 | ħ^-1·c^2·mₑ·θ^-1·g₀^-1 | T^-1 | 3.7e10 | 3.7e10 |  |
| `gray` | `energy(one(U),U,Metric)/mass(one(U),U,Metric)` | derived.jl:248 | 1.1126500560536187e-17 | c^2·g₀^-1 | F·M^-1·L | 1.0 | 0.3345525633129686 |  |
| `roentgen` | `chargedensity(one(U),U,ESU)/density(Constant(1.293),U,Metric)` | derived.jl:250 | 4.441676973532423e-16 | ħ^1/2·c^-1/2·μ₀^-1/2·mₑ^-1·θ^1/2·λ^-1/2·αL^-1 | M^-1·Q | 0.0002579768717696457 | 0.00011701634067117976 |  |
| `rem` | `centi(U)*gray(U)` | derived.jl:249 | 1.1126500560536186e-19 | c^2·g₀^-1 | F·M^-1·L | 0.01 | 0.003345525633129686 |  |

#### Unexported/extra (2)

| name | Julia definition `f(U) =` | src | f(Natural) | exps over U constants | USQ dims | Metric | English | notes |
|---|---|---|---|---|---|---|---|---|
| `sackurtetrode` | `normal(log((Constant(exp(5/2))*kB*sqrt(kB/g₀/turn/ħ^2)^3)*(T/P*sqrt(m*T)^3)))  (P=atmosphere(U),T=kelvin(U),m=dalton(U))` | initdata.jl:30 | -1.1648705244382895 | 1 | 1 | -1.1648705244382895 | -1.16487052443829 | not a monomial (log); depends on angle unit |
| `thermalconductivity_water` | `thermalconductivity((two(U)^2*three(U)*five(U))^2/thermalunit(U),U,Metric)` | derived.jl:151 | 1.0064515947638718e-23 | kB·ħ^-2·c·mₑ·θ^-2·g₀^-1 | L^-1·T^-1·Θ^-1 | 3.4121927139731136 | 0.5777979662327809 | mixes U-valued thermalunit into Metric value |

### 2.10 Prefix functions of a system (`UnitSystems.jl:346-373`)

These are unexported **methods** attached to the exported callable prefix Constants. They return a Constant.

| function | definition | result (any system) |
|---|---|---|
| `deka(U)` | `two(U)*five(U)` | `10` (Int) |
| `hecto(U)`, `kilo(U)` | `deka(U)^2`, `deka(U)^3` | `100`, `1000` (Int) |
| `mega(U)` … `yotta(U)` | `(Constant(1.0)*kilo(U))^n`, n = 2…8 | `1.0e6` … `1.0e24` (**Float**, unlike the Int module constants `mega` … `exa`) |
| `deci`, `centi`, `milli` | `inv(deka(U))`, `inv(hecto(U))`, `inv(kilo(U))` | `0.1`, `0.01`, `0.001` |
| `micro` … `yocto` | `inv(mega(U))` … `inv(yotta(U))` | `1.0e-6` … `1.0e-24` |
| `kibi` … `exbi` | `two(U)^10` … `two(U)^60` | Int |
| `zebi`, `yobi` | `(Constant(1.0)*two(U))^70`, `^80` | `1.1805916207174113e21`, `1.2089258196146292e24` |

### 2.11 Module-level numeric constants

All are `const`. The full value table (178 Constant + 15 plain) is `goldens/module_constants.json`; the curated table below gives definitions. Evaluation is in Float64, **left to right in the written order**. The order matters for bit parity, e.g. `mₑ = ((((αinv^2)*R∞)*2)*𝘩)/𝘤`.

| name(s) | src | definition | value(s) (ᶦ = Int payload) | notes |
|---|---|---|---|---|
| g₀ (g0) | UnitSystems.jl:316 | `Constant(9.80665)` | g₀=9.80665; g0=9.80665 | standard gravity m/s² |
| atm | UnitSystems.jl:316 | `Constant(101325.0)` | atm=101325.0 | standard atmosphere Pa |
| T₀ | UnitSystems.jl:316 | `Constant(273.15)` | T₀=273.15 | ice point K |
| ft | UnitSystems.jl:317 | `Constant(0.3048)` | ft=0.3048 | international foot m |
| ftUS | UnitSystems.jl:317 | `Constant(1200/3937)` | ftUS=0.3048006096012192 | US survey foot m |
| lb | UnitSystems.jl:317 | `Constant(0.45359237)` | lb=0.45359237 | pound kg |
| inHg | UnitSystems.jl:318 | `Constant(1/3386.389)` | inHg=0.0002952998016471232 | **inverted** (should be 3386.389 Pa); see §4.11 |
| Ωᵢₜ, Vᵢₜ | UnitSystems.jl:318 | `Constant(1.000495), Constant(1.00033)` | Ωᵢₜ=1.000495; Vᵢₜ=1.00033 | international ohm/volt |
| ΔνCs | UnitSystems.jl:319 | `Constant(9192631770.0)` | ΔνCs=9.19263177e9 | Cs hyperfine Hz |
| Kcd | UnitSystems.jl:319 | `Constant(683*555.016/555)` | Kcd=683.01969009009 | luminous efficacy lm/W (evaluated in Float64 left to right) |
| mP | UnitSystems.jl:319 | `Constant(2.176434e-8)` | mP=2.176434e-8 | Planck mass kg (measured input) |
| αinv (ainv) | UnitSystems.jl:320 | `Constant(137.035999084)` | αinv=137.035999084; ainv=137.035999084 | inverse fine structure |
| R∞ | UnitSystems.jl:320 | `Constant(10973731.5681601)` | R∞=1.09737315681601e7 | Rydberg m⁻¹ |
| NA | UnitSystems.jl:321 | `Constant(6.02214076e23)` | NA=6.02214076e23 | Avogadro |
| kB | UnitSystems.jl:321 | `Constant(1.380649e-23)` | kB=1.380649e-23 | Boltzmann |
| 𝘩 (hh) | UnitSystems.jl:321 | `Constant(6.62607015e-34)` | 𝘩=6.62607015e-34; hh=6.62607015e-34 | Planck |
| 𝘤 (cc) | UnitSystems.jl:322 | `Constant(299792458.)` | 𝘤=2.99792458e8; cc=2.99792458e8 | light speed |
| 𝘦 (ee) | UnitSystems.jl:322 | `Constant(1.602176634e-19)` | 𝘦=1.602176634e-19; ee=1.602176634e-19 | elementary charge |
| α | UnitSystems.jl:322 | `inv(αinv)` | α=0.0072973525692838015 | fine structure (unexported) |
| μₑᵤ (meu) | UnitSystems.jl:323 | `Constant(1/1822.888486209)` | μₑᵤ=0.0005485799090649074; meu=0.0005485799090649074 | electron/atomic-mass ratio |
| μₚᵤ (mpu) | UnitSystems.jl:323 | `Constant(1.007276466621)` | μₚᵤ=1.007276466621; mpu=1.007276466621 | proton/atomic-mass ratio |
| μE☾ | UnitSystems.jl:323 | `Constant(81.300568)` | μE☾=81.300568 | Earth/Moon mass ratio (unexported) |
| RK1990, KJ1990 | UnitSystems.jl:324 | `Constant(25812.807), Constant(4.835979e14)` | RK1990=25812.807; KJ1990=4.835979e14 | conventional 1990 |
| Rᵤ2014 | UnitSystems.jl:324 | `Constant(8.3144598)` | Rᵤ2014=8.3144598 | CODATA 2014 gas constant |
| RK2014, KJ2014 | UnitSystems.jl:325 | `Constant(25812.8074555), Constant(4.835978525e14)` | RK2014=25812.8074555; KJ2014=4.835978525e14 | CODATA 2014 |
| GME, GMJ | UnitSystems.jl:326 | `Constant(398600441.8e6), Constant(1.26686534e17)` | GME=3.986004418e14; GMJ=1.26686534e17 | geocentric/Jovian GM m³/s² |
| kG | UnitSystems.jl:327 | `Constant(3548.18761)` | kG=3548.18761 | Gaussian grav. constant, arcsec/day (unexported) |
| H0 | UnitSystems.jl:327 | `Constant(67.66)` | H0=67.66 | Hubble km/s/Mpc (unexported) |
| ΩΛ | UnitSystems.jl:327 | `Constant(0.6889)` | ΩΛ=0.6889 | dark energy density (unexported) |
| aⱼ | UnitSystems.jl:328 | `Constant(365.25)` | aⱼ=365.25 | Julian year days (unexported) |
| au | UnitSystems.jl:328 | `Constant(149597870.7e3)` | au=1.495978707e11 | astronomical unit m (unexported) |
| LD, JD | UnitSystems.jl:329 | `Constant(384399e3), Constant(778479e6)` | LD=3.84399e8; JD=7.78479e11 | lunar / Jupiter distance m |
| zetta, zepto, yotta, yocto | UnitSystems.jl:330-331 | `Constant(1e21), Constant(1e-21), Constant(1e24), Constant(1e-24)` | zetta=1.0e21; zepto=1.0e-21; yotta=1.0e24; yocto=1.0e-24 | Float prefixes (also callable) |
| 𝟏 𝟐 𝟑 𝟓 𝟕 𝟏𝟏 𝟏𝟗 𝟒𝟑 (two three five seven eleven nineteen fourtythree) | UnitSystems.jl:71,73 | `Constant.((1,2,3,5,7,11,19,43))` | 𝟏=1ᶦ; 𝟐=2ᶦ; 𝟑=3ᶦ; 𝟓=5ᶦ | Int generators (also callable) |
| τ (tau) | UnitSystems.jl:72-73 | `Constant(2π)` | τ=6.283185307179586; tau=6.283185307179586 | turn |
| 𝟙 F M L T Q Θ N J A R C | UnitSystems.jl:72 | `𝟏` | 𝟙=1ᶦ; F=1ᶦ; M=1ᶦ; L=1ᶦ | dimension placeholders, all Constant{1} (Similitude redefines them); `Λ` is exported but undefined; `R` is defined but not exported |
| deka, byte, sixty | initdata.jl:15 | `𝟐*𝟓, 𝟐^3, 𝟐^2*𝟑*𝟓` | deka=10ᶦ; byte=8ᶦ; sixty=60ᶦ | Int 10, 8, 60 |
| hecto, kilo, 𝟏𝟎, 𝟔𝟎 | initdata.jl:16 | `deka^2, deka^3, deka, sixty` | hecto=100ᶦ; kilo=1000ᶦ; 𝟏𝟎=10ᶦ; 𝟔𝟎=60ᶦ | Int |
| mega giga tera peta exa | initdata.jl:17 | `kilo^2 … kilo^6` | mega=1000000ᶦ; giga=1000000000ᶦ; tera=1000000000000ᶦ; peta=1000000000000000ᶦ | **Int** (exa = 10¹⁸ fits Int64) |
| deci centi milli micro nano pico femto atto | initdata.jl:18 | `inv.((deka,hecto,kilo,mega,giga,tera,peta,exa))` | deci=0.1; centi=0.01; milli=0.001; micro=1.0e-6 | Float |
| kibi … exbi, zebi, yobi | initdata.jl:19 | `𝟐^10 … 𝟐^60, (Constant(1.0)*𝟐)^70, (Constant(1.0)*𝟐)^80` | kibi=1024ᶦ; exbi=1152921504606846976ᶦ; zebi=1.1805916207174113e21; yobi=1.2089258196146292e24 | Int … Int, Float, Float |
| fur | initdata.jl:21 | `𝟔𝟎*𝟏𝟏*ft` | fur=201.168 | furlong m |
| °R | initdata.jl:21 | `𝟓/𝟑^2` | °R=0.5555555555555556 | K per °R (0.5556) |
| K | initdata.jl:21 | `𝟑^2/𝟓` | K=1.8 | °R per K (1.8) |
| HOUR | initdata.jl:21 | `𝟔𝟎^2` | HOUR=3600ᶦ | Int 3600 |
| k | initdata.jl:21 | `kG*τ/(𝟐^7*𝟑^4*𝟓^3)` | k=0.017202098964713468 | Gaussian constant rad/day (unexported) |
| mₑ (me) | initdata.jl:22 | `αinv^2*R∞*𝟐*𝘩/𝘤` | mₑ=9.109383701558256e-31; me=9.109383701558256e-31 | electron mass kg |
| μ₀ (m0) | initdata.jl:22 | `𝟐*𝘩/𝘤*α/𝘦^2` | μ₀=1.256637062121048e-6; m0=1.256637062121048e-6 | SI2019 vacuum permeability |
| ħ | initdata.jl:23 | `𝘩/τ` | ħ=1.0545718176461565e-34 |  |
| μₚₑ (mpe), μₑₚ (mep) | initdata.jl:23 | `μₚᵤ/μₑᵤ, μₑᵤ/μₚᵤ` | μₚₑ=1836.152673432705; mpe=1836.152673432705; μₑₚ=0.0005446170214868302; mep=0.0005446170214868302 |  |
| Rᵤ (Ru) | initdata.jl:23 | `NA*kB` | Rᵤ=8.31446261815324; Ru=8.31446261815324 | molar gas constant |
| αL (aL) | initdata.jl:23 | `centi/𝘤` | αL=3.335640951981521e-11; aL=3.335640951981521e-11 | Gaussian Lorentz constant |
| αG (aG) | initdata.jl:23 | `(mₑ/mP)^2` | αG=1.751809945750515e-45; aG=1.751809945750515e-45 | gravitational coupling |
| Mᵤ (Mu) | initdata.jl:23 | `NA*mₑ/μₑᵤ` | Mᵤ=0.000999999999656256; Mu=0.000999999999656256 | SI2019 molar mass constant |
| pc | initdata.jl:24 | `au*𝟐^7*𝟑^4*𝟓^3/τ` | pc=3.085677581491367e16 | parsec m (unexported) |
| G, GG | initdata.jl:24; UnitSystems.jl:338 | `𝘤*ħ/mP^2` | G=6.674302101972536e-11; GG=6.674302101972536e-11 | Newton constant |
| DAY | initdata.jl:24 | `𝟐^7*𝟑^3*𝟓^2` | DAY=86400ᶦ | Int 86400 |
| nm | initdata.jl:24 | `sqrt(GME/g₀)*τ/𝟐^5/𝟑^3/𝟓^2` | nm=1854.5334338961468 | nautical mile m (Earth radius from GME/g₀, 1 arcminute) |
| GM☉ | initdata.jl:25 | `au^3*k^2/DAY^2` | GM☉=1.3271244026896523e20 | solar GM |
| th | initdata.jl:25 | `𝟏𝟎^3*pc/H0` | th=4.560563969097498e17 | Hubble time s |
| ΛC | initdata.jl:25 | `𝟑*ΩΛ*(th*𝘤)^-2` | ΛC=1.1056022912824222e-52 | cosmological constant m⁻² (unexported) |
| lc | initdata.jl:26 | `𝟐*sqrt(τ/ΛC)` | lc=4.767826737700842e26 | cosmological length |
| mc | initdata.jl:26 | `𝘤^2/(𝟐*G*sqrt(τ*ΛC))` | mc=2.554560252645652e52 | cosmological mass |
| ρΛ | initdata.jl:26 | `ΛC*𝘤^4/(𝟐^2*τ)/G` | ρΛ=5.323975174017547e-10 | vacuum energy density (unexported) |
| 𝘦ₙ | initdata.jl:26 | `𝘦/√α` | 𝘦ₙ=1.8755460377789286e-18 | natural (Gaussian) charge |
| ς | initdata.jl:26 | `√(𝟐*τ)` | ς=3.5449077018110318 | √(4π) spatian |
| lcq, mcq | initdata.jl:27 | `sqrt(sqrt(𝘤*ħ/ρΛ)), sqrt(sqrt(ρΛ*ħ^3/𝘤^5))` | lcq=8.778396854688203e-5; mcq=4.0071928849599166e-39 | cosmological-quantum length/mass |
| 𝘦ᵣ | initdata.jl:27 | `𝘦ₙ/ς` | 𝘦ᵣ=5.290817689895691e-19 | rationalized natural charge |
| tcq | initdata.jl:28 | `lcq*sqrt(mcq/sqrt(sqrt(ρΛ*(𝘤*ħ)^3)))` | tcq=2.9281580041243744e-13 | cosmological-quantum time |
| em | initdata.jl:28 | `sqrt(GME/g₀)*τ/𝟐^9/𝟓^7` | em=1.0014480543039193 | Earth meter (1e-7 of quadrant) |
| mi | initdata.jl:28 | `𝟐^5*𝟑*𝟓*𝟏𝟏` | mi=5280ᶦ | Int 5280 |
| slug | UnitSystems.jl:335 | `lb*g₀/ft` | slug=14.593902937206362 | kg per slug (also callable) |
| lbm, lbmUS | UnitSystems.jl:335 | `g₀/ft, g₀/ftUS` | lbm=32.17404855643044; lbmUS=32.17398420833333 | lbm per slug |
| rankine, kelvin | UnitSystems.jl:335 | `°R, K` | rankine=0.5555555555555556; kelvin=1.8 | **callable** Constants |
| ħ1990, ħ2014 | UnitSystems.jl:336 | `planckreduced(Conventional), planckreduced(CODATA)` | ħ1990=1.054571611438857e-34; ħ2014=1.0545717999940896e-34 | (unexported) |
| mₑ1990, mₑ2014 | UnitSystems.jl:337 | `electronmass(Conventional), electronmass(CODATA)` | mₑ1990=9.109381920341098e-31; mₑ2014=9.10938354907983e-31 |  |
| δμ₀ | UnitSystems.jl:338 | `μ₀-4π*1e-7` | δμ₀=6.851306461996397e-16 | plain Float64 |
| ly | UnitSystems.jl:338 | `aⱼ*𝘤*DAY` | ly=9.4607304725808e15 | light-year m (unexported) |
| mₛ | UnitSystems.jl:338 | `GM☉/G` | mₛ=1.9884092485076926e30 | solar mass (unexported) |
| kcalₜₕ kcal₄ kcal₁₀ kcal₂₀ kcalₘ kcalᵢₜ | UnitSystems.jl:343 | `4184, 4204, 4185.5, 4182, 4190, 4186.8` | kcalₜₕ=4184ᶦ; kcal₄=4204ᶦ; kcal₁₀=4185.5; kcal₂₀=4182ᶦ | plain Int/Float (not Constant) |
| calₜₕ … calᵢₜ | UnitSystems.jl:344 | `(kcal…)./1e3` | calₜₕ=4.184; calᵢₜ=4.1868 | plain Float |
| RK, KJ | UnitSystems.jl:425-426 | `klitzing(SI2019), josephson(SI2019)` | RK=25812.807459304513; KJ=4.835978484169836e14 |  |
| eV | systems.jl:29 | `electronvolt(SI2019)` | eV=1.602176634e-19 |  |
| κ | systems.jl:30 | `einstein(SI2019)` | κ=2.0766480968545148e-43 |  |
| σ (SB) | systems.jl:31 | `stefan(SI2019)` | σ=5.6703744191844314e-8; SB=5.6703744191844314e-8 |  |
| μB | systems.jl:32 | `magneton(SI2019)` | μB=9.274010078302855e-24 |  |
| ε₀ (e0, ϵ₀) | systems.jl:33 | `vacuumpermittivity(SI2019)` | ε₀=8.854187812792999e-12; e0=8.854187812792999e-12; ϵ₀=8.854187812792999e-12 | plain Float (the SI2019 μ₀ coupling override returns plain) |
| kₑ (ke) | systems.jl:34 | `electrostatic(SI2019)` | kₑ=8.98755179226828e9; ke=8.98755179226828e9 | plain |
| mₚ (mp) | systems.jl:35 | `protonmass(SI2019)` | mₚ=1.6726219236940502e-27; mp=1.6726219236940502e-27 |  |
| Da (mu, mᵤ) | systems.jl:36 | `dalton(SI2019)` | Da=1.6605390666030467e-27; mu=1.6605390666030467e-27; mᵤ=1.6605390666030467e-27 |  |
| 𝔉 (FF) | systems.jl:37 | `faraday(SI2019)` | 𝔉=96485.33212331001; FF=96485.33212331001 |  |
| Φ₀ | systems.jl:38 | `magneticfluxquantum(SI2019)` | Φ₀=2.0678338484619295e-15 |  |
| Z₀ (Z0) | systems.jl:39 | `vacuumimpedance(SI2019)` | Z₀=376.73031366716776; Z0=376.73031366716776 | plain |
| G₀ (G0) | systems.jl:40 | `conductancequantum(SI2019)` | G₀=7.748091729863649e-5; G0=7.748091729863649e-5 |  |
| Eₕ (Eh) | systems.jl:41 | `hartree(SI2019)` | Eₕ=4.359744722207211e-18; Eh=4.359744722207211e-18 |  |
| a₀ (a0) | systems.jl:42 | `bohr(SI2019)` | a₀=5.291772109022829e-11; a0=5.291772109022829e-11 |  |
| rₑ (re) | systems.jl:43 | `electronradius(SI2019)` | rₑ=2.8179403261891358e-15; re=2.8179403261891358e-15 |  |
| RH | systems.jl:44 | `R∞*mₚ/(electronmass(SI2019)+mₚ)` | RH=1.096775834028043e7 | hydrogen Rydberg |
| Ry | systems.jl:44 | `𝘩*𝘤*R∞` | Ry=2.1798723611036047e-18 | Rydberg energy |
| ℓP (lP), tP, TP | systems.jl:46-48 | `length/time/temperature(PlanckGauss,SI2019)` | ℓP=1.6162552789315494e-35; lP=1.6162552789315494e-35; tP=5.391247297260392e-44; TP=1.416783939059737e32 |  |
| lS, tS, mS, qS | systems.jl:50-53 | `length/time/mass/charge(Stoney,SI2019)` | lS=1.380678687871542e-36; tS=4.605448372792427e-45; mS=1.859208801066057e-9; qS=1.602176634e-19 |  |
| lA, tA, mA, qA | systems.jl:55-58 | `…(Hartree,SI2019)` | lA=5.291772109022829e-11; tA=2.418884326585658e-17; mA=9.109383701558256e-31; qA=1.6021766340000001e-19 |  |
| lQCD, tQCD, mQCD | systems.jl:60-62 | `…(QCD,SI2019)` | lQCD=2.1030891033504994e-16; tQCD=7.015150138802022e-25; mQCD=1.6726219236940502e-27 |  |
| BTU, BTUftlb | systems.jl:66-67 | `thermalunit(British)` | BTU=778.1576129990755; BTUftlb=778.1576129990755 | (BTU unexported) |
| BTUJ | systems.jl:68 | `thermalunit(SI2019)` | BTUJ=1055.0400583348664 |  |
| HP, gal | systems.jl:69-70 | `horsepower(Metric), gallon(Metric)` | HP=745.6998715822704; gal=0.003785411784000002 | (unexported) |
| kcal, cal | systems.jl:71-72 | `kilocalorie(SI2019), calorie(SI2019)` | kcal=4186.737323211057; cal=4.186737323211057 |  |

### 2.12 Helper functions

| function | signature → semantics | src | example (oracle) |
|---|---|---|---|
| `kilograms` | `(m::Number, U=English) = mass(m, Metric, U)`: converts a mass from U to kg. **The docstring says "from slugs" (factor `lb*g₀/ft` = 14.59), but the default U = English has lbm as its mass unit**, so the default factor is 0.45359237 | `kinematic.jl:20` | `kilograms(1) == 0.45359237`; `kilograms(1,British) == 14.593902937206364` |
| `slugs` | `(m, U=Metric) = mass(m, English, U)`. **Docstring says slugs, but the target is English, whose mass unit is the lbm**, so the result is pounds | `kinematic.jl:27` | `slugs(1) == 2.2046226218487757` |
| `feet` | `(d, U=Metric) = length(d, English, U)` | `kinematic.jl:34` | `feet(1) == 3.280839895013123`; `feet(1,English) === 1` (same system returns `v` unchanged) |
| `meters` | `(d, U=English) = length(d, Metric, U)` | `kinematic.jl:41` | `meters(1) == 0.3048` |
| `moles` | `(N::Number, U=Metric) = N/avogadro(U)` | `thermodynamic.jl:32` | `moles(6.02214076e23) == 0.999999999656256` |
| `molecules` | `(n::Number, U=Metric) = n*avogadro(U)` | `thermodynamic.jl:39` | `molecules(1) == 6.022140762070074e23` |
| `sackurtetrode` | `(U, P=atmosphere(U), T=kelvin(U), m=dalton(U))` = `log((e^{5/2}·kB·(kB/(g₀·turn·ħ²))^{3/2})·(T/P·(m·T)^{3/2}))` | `initdata.jl:30` | `sackurtetrode(Metric) == -1.1648705244382895` |
| `UnitSystems.derived(U)` | `[x => x(U) for x ∈ Derived[2:end]]` via `eval`. **Always throws** (`neper` undefined) | `initdata.jl:32` | — |
| `UnitSystems.constants(U)` | pairs for `(:hyperfine, Constants..., Physics..., :loschmidt, :mechanicalheat, :wienwavelength, :wienfrequency, :sackurtetrode, :eddington, :solarmass, :jupitermass, :earthmass, :gforce, :earthradius, :greatcircle, :nauticalmile, :hubble, :cosmological)`, 56 entries | `initdata.jl:33` | `[:hyperfine => 9.19263177e9, :lightspeed => 2.99792458e8, :planck => 6.62607015e-34, …]` |
| `similitude()` | `haskey(ENV,"SIMILITUDE")`. Build-time toggle for downstream packages | `UnitSystems.jl:62` | `false` |
| `UnitSystems.unit(x, y=1)` | `isapprox(y, x, rtol=eps()^0.9) ? y : x`. Also defined for Constants: `unit(::Constant{x}, y=1) = Constant{unit(x,y)}()`, `unit(x, ::Constant{y})`, `unit(::Constant{x}, ::Constant{y})` | `UnitSystems.jl:276, 66-68` | `unit(1+7e-15) === 1`; `unit(1+1e-14) == 1.00000000000001` |
| `Base.one(U)` | `unit(two(U)/two(U))` → `Constant{1}` (Int) | `:277` | |
| `Base.zero(U)` | `one(U)-one(U)` → `Constant{0}` | `:278` | |
| `UnitSystems.isrationalized(U)` | `rationalization(U) ≠ spat(U)` | `:179` | Metric true, Gauss false, LorentzHeaviside true |
| `UnitSystems.unitname(U)` | name string or `"Unknown"` | `:186`, `initdata.jl:169-171` | |
| `UnitSystems.isquantity` | always `false` here | `:176-178` | |
| `UnitSystems.evaldim` | empty generic function (Similitude hook) | `:175` | |
| `Quantity(D,U,x)`, `Quantity(x)` | identity | `:95-96` | |
| `(U::UnitSystem)(x, D)` | returns `x`; dimension tags are ignored in UnitSystems | `:203` | `Metric(1, energy) === 1` |
| `(U::UnitSystem)(JK,Js,ms,Hm,kg)` | rescaled system, §4.2 | `:205-221` | `boltzmann(Metric(2,3,4,5,6)) == 2.761297999050821e-23` |
| `temp`, `voltage`, `universal`, `atomicmass`, `intensity`, `stiffness` | aliases `temperature`, `electricpotential` (unexported), `molargas`, `dalton`, `irradiance`, `fluence` (unexported) | `UnitSystems.jl:339`, `electromagnetic.jl:20`, `systems.jl:26,73` | |
| `UnitSystems.thermalconductivity_water(U)` | unexported, `derived.jl:151` | | `…(British) == 0.5777979662327808` |

### 2.13 Unicode ↔ ASCII aliases (`systems.jl:77-78`, `initdata.jl:158-165`)

| Unicode | ASCII | | Unicode | ASCII |
|---|---|---|---|---|
| `μₚₑ` | `mpe` | | `ε₀` | `e0`, `ϵ₀` |
| `μₑₚ` | `mep` (unexported) | | `kₑ` | `ke` |
| `μₑᵤ` | `meu` | | `mₑ` | `me` |
| `μₚᵤ` | `mpu` | | `mₚ` | `mp` |
| `αinv` | `ainv` | | `Da` | `mu`, `mᵤ` |
| `αG` | `aG` | | `𝘦` | `ee` |
| `αL` | `aL` | | `𝔉` | `FF` |
| `Mᵤ` | `Mu` | | `Z₀` | `Z0` |
| `Rᵤ` | `Ru`; function `universal` = `molargas` | | `G₀` | `G0` |
| `σ` | `SB` | | `Eₕ` | `Eh` |
| `𝘩` | `hh` | | `a₀` | `a0` |
| `𝘤` | `cc` | | `rₑ` | `re` |
| `μ₀` | `m0` | | `g₀` | `g0` |
| `ℓP` | `lP` | | `IAU☉` | `IAU` |
| `UnitSystem` | `US`, `units` | | `temperature` | `temp` |
| `𝟏 𝟐 𝟑 𝟓 𝟕 𝟏𝟏 𝟏𝟗 𝟒𝟑` | `two three five seven eleven nineteen fourtythree` (𝟏 has no word alias except `𝟙`) | | `τ` | `tau` |
| `𝟏𝟎`, `𝟔𝟎` | `deka`, `sixty` | | `°R`, `K` | `rankine`, `kelvin` (Constants) |

Unit-name comments in the docs use `⋅` (U+22C5) as the product separator and superscript digits/minus (`⁻¹ ² ³`).

### 2.14 Name tables (`text.jl:2-411`, unexported)

`textconstants`, `textderived` and `textquantities` are `Dict{Symbol,String}` giving human-readable names. For example `:gravitation => "Newton gravitation"`, `:apostilb => "abostilb"` (sic), `:statweber => "statfarad"` (sic, copy-paste bug at `text.jl:219`), `:rem => "roentgen equivalent man"`. They are only used by doc generation (and by Similitude/Geophysics display). Port them as a `String` lookup table if a display layer needs them. Keep the typos only behind a `juliaCompat` flag.

---

## 3. Data representations

### 3.1 `UnitSystem` type-parameter layout

```
UnitSystem{kB, ħ, 𝘤, μ₀, mₑ, Mᵤ, extra}
extra = (Kcd, θ, λ, αL, g₀, C::Coupling, τ, 𝟐, 𝟑, 𝟓, 𝟕, 𝟏𝟏, 𝟏𝟗, 𝟒𝟑)
          1   2  3   4   5   6          7  8  9  10 11  12  13  14
```

| slot | name | type of payload | invariant in the 48 named systems |
|---|---|---|---|
| 1–6 | `kB ħ 𝘤 μ₀ mₑ Mᵤ` | `Constant{Int64}` or `Constant{Float64}` (or plain numbers when built with `UnitSystem(…)`) | positive, except FFF where `μ₀ = 0.0` |
| extra[1..5] | `Kcd θ λ αL g₀` | same | `θ, λ, αL, g₀` are `Constant{1}` (Int) unless listed in §3.3 |
| extra[6] | `C` | `Coupling{…}` | always `Universe` |
| extra[7] | `τ` | `Constant{6.283185307179586}` | always |
| extra[8..14] | primes | `Constant{2}` … `Constant{43}` (Int) | always |

- **Compile-time vs runtime.** In Julia *everything* about a system is compile-time: each system is a distinct singleton type, and every accessor is `@pure`. The only runtime datum is the value `v` passed to `q(v,U,S)`.
- **Int vs Float payloads matter for display and for exact 1s.** `unit()` snapping (§4.4) returns the *Int* `1`, so `molarmass(English) === Constant{1}` prints `1`. By contrast `molarmass(MPH)` is `1.0` (Float), because `MPH = EntropySystem(FPS,…,m=𝟏)` computes `molarmass(FPS)/𝟏 = 1/1 = 1.0` (Julia `/` on Ints yields Float) and no snap is applied. The type of every slot is recorded in `goldens/systems.json` (`t: "Int" | "Float64"`).
- **Identity.** Two systems are equal iff they have the same type, i.e. bit-identical payloads *and* the same Int/Float kind. `UnitSystem(1,1,1,1,1) !== Natural`.
- The helpers `normal`, `cache` and `measure` are identities in UnitSystems.

### 3.2 `Coupling`

`Coupling{αG, α, μₑᵤ, μₚᵤ, ΩΛ}` holds payloads that are Float64 Constants in `Universe`:

| slot | accessor | value (`Universe`) |
|---|---|---|
| `αG` | `coupling` | `(mₑ/mP)^2 = 1.751809945750515e-45` |
| `α` | `finestructure` | `inv(αinv) = 0.0072973525692838015` |
| `μₑᵤ` | `electronunit` | `1/1822.888486209 = 0.0005485799090649074` |
| `μₚᵤ` | `protonunit` | `1.007276466621` |
| `ΩΛ` | `darkenergydensity` | `0.6889` |
| derived | `protonelectron = μₚᵤ/μₑᵤ` | `1836.152673432705` |

### 3.3 Parameter table of all 48 systems (oracle values; ᶦ = Int payload, otherwise Float64)

| system | kB | ħ | c | μ₀ | mₑ | Mᵤ | Kcd | θ | λ | αL | g₀ |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Metric | 1.3806489995254104e-23 | 1.0545718176461565e-34 | 2.99792458e8 | 1.2566370614359173e-6 | 9.109383701558256e-31 | 0.001 | 683.01969009009 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| SI2019 | 1.380649e-23 | 1.0545718176461565e-34 | 2.99792458e8 | 1.256637062121048e-6 | 9.109383701558256e-31 | 0.000999999999656256 | 683.01969009009 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| SI1976 | 1.3806253172239044e-23 | 1.0545718176461565e-34 | 2.99792458e8 | 1.2566370614359173e-6 | 9.109383701558256e-31 | 0.001 | 683.01969009009 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| CODATA | 1.3806485084499174e-23 | 1.0545717999940896e-34 | 2.99792458e8 | 1.2566370619358342e-6 | 9.10938354907983e-31 | 0.001 | 683.019701522891 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| Conventional | 1.3806487295581143e-23 | 1.054571611438857e-34 | 2.99792458e8 | 1.2566370397608662e-6 | 9.109381920341098e-31 | 0.001 | 683.0198236454073 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| International | 1.3804211924652808e-23 | 1.0543978133151816e-34 | 2.99792458e8 | 1.2560153338456639e-6 | 9.107880653411075e-31 | 0.000999835000017957 | 683.1324069249657 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| InternationalMean | 1.3803866950098692e-23 | 1.0543714633563797e-34 | 2.99792458e8 | 1.2560216108466024e-6 | 9.10765304265832e-31 | 0.0009998100136127059 | 683.1494791916235 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| MetricTurn | 1.3806489995254104e-23 | 6.62607015e-34 | 2.99792458e8 | 1.2566370614359173e-6 | 9.109383701558256e-31 | 0.001 | 683.01969009009 | 0.15915494309189535 | 1ᶦ | 1ᶦ | 1ᶦ |
| MetricSpatian | 1.3806489995254104e-23 | 3.7383597584867195e-34 | 2.99792458e8 | 1.2566370614359173e-6 | 9.109383701558256e-31 | 0.001 | 683.01969009009 | 0.28209479177387814 | 1ᶦ | 1ᶦ | 1ᶦ |
| MetricGradian | 1.3806489995254104e-23 | 1.6565175375e-36 | 2.99792458e8 | 1.2566370614359173e-6 | 9.109383701558256e-31 | 0.001 | 683.01969009009 | 63.66197723675813 | 1ᶦ | 1ᶦ | 1ᶦ |
| MetricDegree | 1.3806489995254104e-23 | 1.840575041666667e-36 | 2.99792458e8 | 1.2566370614359173e-6 | 9.109383701558256e-31 | 0.001 | 683.01969009009 | 57.29577951308232 | 1ᶦ | 1ᶦ | 1ᶦ |
| MetricArcminute | 1.3806489995254104e-23 | 3.0676250694444446e-38 | 2.99792458e8 | 1.2566370614359173e-6 | 9.109383701558256e-31 | 0.001 | 683.01969009009 | 3437.7467707849396 | 1ᶦ | 1ᶦ | 1ᶦ |
| MetricArcsecond | 1.3806489995254104e-23 | 5.112708449074075e-40 | 2.99792458e8 | 1.2566370614359173e-6 | 9.109383701558256e-31 | 0.001 | 683.01969009009 | 206264.80624709636 | 1ᶦ | 1ᶦ | 1ᶦ |
| Engineering | 1.4078701692478171e-24 | 1.0753639802033891e-35 | 2.99792458e8 | 1.2814131853751459e-7 | 9.109383701558256e-31 | 0.001 | 6698.135043821981 | 1ᶦ | 1ᶦ | 1ᶦ | 9.80665 |
| Gravitational | 1.4078701692478171e-24 | 1.0753639802033891e-35 | 2.99792458e8 | 1.2814131853751459e-7 | 9.288986250715847e-32 | 0.00010197162129779284 | 6698.135043821981 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| MTS | 1.3806489995254105e-26 | 1.0545718176461564e-37 | 2.99792458e8 | 1.2566370614359174e-9 | 9.109383701558256e-34 | 1.0e-6 | 683019.6900900899 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| EMU | 1.3806489995254102e-16 | 1.0545718176461563e-27 | 2.99792458e10 | 1ᶦ | 9.109383701558256e-28 | 1ᶦ | 6.8301969009009e-5 | 1ᶦ | 12.566370614359172 | 1ᶦ | 1ᶦ |
| ESU | 1.3806489995254102e-16 | 1.0545718176461563e-27 | 2.99792458e10 | 1.1126500560536182e-21 | 9.109383701558256e-28 | 1ᶦ | 6.8301969009009e-5 | 1ᶦ | 12.566370614359172 | 1ᶦ | 1ᶦ |
| Gauss | 1.3806489995254102e-16 | 1.0545718176461563e-27 | 2.99792458e10 | 1ᶦ | 9.109383701558256e-28 | 1ᶦ | 6.8301969009009e-5 | 1ᶦ | 12.566370614359172 | 3.335640951981521e-11 | 1ᶦ |
| LorentzHeaviside | 1.3806489995254102e-16 | 1.0545718176461563e-27 | 2.99792458e10 | 1ᶦ | 9.109383701558256e-28 | 1ᶦ | 6.8301969009009e-5 | 1ᶦ | 1ᶦ | 3.335640951981521e-11 | 1ᶦ |
| FPS | 1.8201832416933465e-22 | 2.502536930488925e-33 | 9.835710564304461e8 | 9.089273271309687e-6 | 2.0082753379555867e-30 | 1ᶦ | 28.78252493663283 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| IPS | 6.788762956583119e-23 | 9.333747076683978e-34 | 1.1802852677165354e10 | 2.825032496413345e-7 | 5.201592142482083e-33 | 1ᶦ | 77.17086290732456 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| British | 5.657302463819266e-24 | 7.778122563903315e-35 | 9.835710564304461e8 | 2.825032496413345e-7 | 6.241910570978499e-32 | 1ᶦ | 926.0503548878946 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| English | 5.657302463819266e-24 | 7.778122563903315e-35 | 9.835710564304461e8 | 2.8250324964133447e-7 | 2.0082753379555867e-30 | 1ᶦ | 926.0503548878946 | 1ᶦ | 1ᶦ | 1ᶦ | 32.17404855643044 |
| Survey | 5.65729114921434e-24 | 7.778107007658189e-35 | 9.835690892883334e8 | 2.8250324964133457e-7 | 2.0082753379555867e-30 | 1ᶦ | 926.0522069923085 | 1ᶦ | 1ᶦ | 1ᶦ | 32.17398420833333 |
| FFF | 6.793104372040068e-18 | 7.721326066522303e-35 | 1.8026174997852542e12 | 0.0 | 2.2314170421728741e-32 | 1ᶦ | 6.375788993269434e-10 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| MPH | 8.46159564836783e-23 | 3.2315817800735083e-37 | 6.706166293843951e8 | 1.72145327108138e-9 | 2.0082753379555867e-30 | 1.0 | 0.017198446999173198 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| KKH | 1.789321103384932e-22 | 3.7964585435261634e-37 | 1.0792528488e9 | 1.2566370614359174e-9 | 9.109383701558256e-31 | 0.001 | 0.014639482383618183 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| Nautical | 5.180046617683878e-23 | 1.0990666907335472e-37 | 5.819538375927914e8 | 6.785840131753953e-10 | 9.06992538542115e-31 | 0.001 | 0.050568530951469015 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| Meridian | 1.3706960050349812e-23 | 1.0469694889627603e-34 | 2.9935896995513964e8 | 1.2566370614359173e-6 | 9.06992538542115e-31 | 0.001 | 687.979280828919 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| IAU☉ | 2.3160832669610065e-66 | 2.047544291551459e-82 | 173.14463267424034 | 4.224532713546819e-48 | 4.581241868792794e-61 | 5.029145789532528e-34 | 4.712469960476774e40 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| IAUE | 1.1679233837035083e-55 | 1.0325081534781642e-71 | 67383.2876027253 | 5.473885382987154e-40 | 1.5253063572240283e-55 | 1.6744341957657449e-28 | 9.34519590395274e29 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| IAUJ | 8.959677342845726e-65 | 7.9208448414543e-81 | 33.27266165330086 | 8.50429600927554e-46 | 4.7991508542640076e-58 | 5.268359541648314e-31 | 1.2181769949820595e39 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| Hubble | 1.0 | 2.824406535940374e-39 | 1.0 | 12.566370614359172 | 1.0 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| Cosmological | 1.0 | 2.8881439991247135e-122 | 1.0 | 12.566370614359172 | 3.565930258299465e-83 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| CosmologicalQuantum | 1.0 | 1.0 | 1.0 | 12.566370614359172 | 2.273258104382309e8 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| Planck | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1.4837079572551133e-22 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| PlanckGauss | 1ᶦ | 1ᶦ | 1ᶦ | 12.566370614359172 | 4.1854628725512725e-23 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| Stoney | 1ᶦ | 137.035999084 | 1ᶦ | 12.566370614359172 | 4.899602291219254e-22 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| Hartree | 1ᶦ | 1ᶦ | 137.035999084 | 0.0006691762566203905 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| Rydberg | 1ᶦ | 1ᶦ | 274.071998168 | 0.00016729406415509762 | 0.5 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| Schrodinger | 1ᶦ | 1ᶦ | 137.035999084 | 0.0006691762566203905 | 4.899602291219254e-22 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| Electronic | 1ᶦ | 137.035999084 | 1ᶦ | 12.566370614359172 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| Natural | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| NaturalGauss | 1ᶦ | 1ᶦ | 1ᶦ | 12.566370614359172 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| QCD | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 0.0005446170214868301 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| QCDGauss | 1ᶦ | 1ᶦ | 1ᶦ | 12.566370614359172 | 0.0005446170214868301 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |
| QCDoriginal | 1ᶦ | 1ᶦ | 1ᶦ | 0.09170123688926637 | 0.0005446170214868301 | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ | 1ᶦ |

### 3.4 Ordering conventions

- **Constant slot order** (everywhere: struct, `display`, constructors, Wolfram `UnitSystem[...]`): `kB, ħ, 𝘤, μ₀, mₑ, Mᵤ, Kcd, θ, λ, αL, g₀`.
- **USQ base-dimension order** (Similitude `Unified`, `Similitude.jl:157`; this spec): `F, M, L, T, Q, Θ, N, J, A, Λ(R), C` = force, mass, length, time, charge, temperature, molar amount, luminous flux, angle, rationalization, nonstandard.
- **`Systems`, `Convert`, `Derived`**: the tuple order in `meta.json`. The golden matrices use it as their index order.
- **Coupling slot order**: `αG, α, μₑᵤ, μₚᵤ, ΩΛ`.

---

## 4. Algorithms

### 4.1 Fundamental constant chain (evaluation order = source order)

Inputs are measured/defined decimals (`UnitSystems.jl:316-331`, table §2.11). The derived chain is `initdata.jl:15-28`. The key values (oracle):

```
mₑ  = αinv^2*R∞*𝟐*𝘩/𝘤                        = 9.109383701558256e-31
μ₀  = 𝟐*𝘩/𝘤*α/𝘦^2                             = 1.256637062121048e-6
ħ   = 𝘩/τ                                     = 1.0545718176461565e-34
Rᵤ  = NA*kB                                   = 8.31446261815324
Mᵤ  = NA*mₑ/μₑᵤ                               = 0.000999999999656256
αG  = (mₑ/mP)^2                               = 1.751809945750515e-45
αL  = centi/𝘤                                 = 3.335640951981521e-11
G   = 𝘤*ħ/mP^2                                = 6.674302101972536e-11
k   = kG*τ/(2^7*3^4*5^3)                      = 0.017202098964713468   (rad/day)
GM☉ = au^3*k^2/DAY^2                          = 1.3271244026896523e20
pc  = au*2^7*3^4*5^3/τ                        = 3.085677581491367e16
th  = 10^3*pc/H0                              = 4.560563969097498e17
ΛC  = 3*ΩΛ*(th*𝘤)^-2                          = 1.1056022912824222e-52
lc  = 2*sqrt(τ/ΛC)                            = 4.767826737700842e26
mc  = 𝘤^2/(2*G*sqrt(τ*ΛC))                    = 2.554560252645652e52
ρΛ  = ΛC*𝘤^4/(2^2*τ)/G                        = 5.323975174017547e-10
lcq = sqrt(sqrt(𝘤*ħ/ρΛ))                      = 8.778396854688203e-5
mcq = sqrt(sqrt(ρΛ*ħ^3/𝘤^5))                  = 4.0071928849599166e-39
tcq = lcq*sqrt(mcq/sqrt(sqrt(ρΛ*(𝘤*ħ)^3)))    = 2.9281580041243744e-13
em  = sqrt(GME/g₀)*τ/2^9/5^7                  = 1.0014480543039193
nm  = sqrt(GME/g₀)*τ/2^5/3^3/5^2              = 1854.5334338961468
𝘦ₙ  = 𝘦/√α = 1.8755460377789286e-18;  ς = √(2τ) = 3.5449077018110318;  𝘦ᵣ = 𝘦ₙ/ς = 5.290817689895691e-19
```

All of this is `Constant` arithmetic (closed), so each intermediate is rounded to Float64 exactly as written. Literal integer powers of Constants go through `Base.literal_pow`; see §4.9.

### 4.2 Constructors (pseudocode; `ONE` = `Constant{1}`)

```
unitsystem(kB,ħ,c,μ0,me, Mu=ONE,Kcd=ONE,θ=ONE,λ=ONE,αL=ONE,g=ONE, C=Universe, τ=2π, primes=(2,3,5,7,11,19,43))
    = record of exactly these values                                 # initdata.jl:37-39

MetricSystem(Mu=Mᵤ, μ0=μ₀, Ru=Rᵤ, g0=ONE, θ=ONE, h=𝘩, me=αinv^2*R∞*2*h/𝘤)   # initdata.jl:62
    kB  = Ru*me/Mu/μₑᵤ/g0
    ħ   = h/τ/g0/θ
    c   = 𝘤
    Kcd = Kcd_global*(mₑ/me)^2*(h/𝘩)*g0            # Kcd_global = 683*555.016/555
    return unitsystem(kB, ħ, c, μ0, me, Mu, Kcd, θ, ONE, ONE, g0)

ConventionalSystem(RK, KJ, Ru=Rᵤ, g0=ONE, θ=ONE)                    # initdata.jl:71
    = MetricSystem(milli, 2*RK/𝘤*α, Ru, g0, θ, (2*2)/RK/(KJ*KJ))    # h := 4/(RK·KJ²); me defaults from that h

EntropySystem(u, t, l, m, θT=ONE)                                   # UnitSystems.jl:251-253
    = EntropySystem(u, t, l, m, θT, permeability(u)/(m*l), molarmass(u)/m, gravity(u), m*l*l/(t*t))

EntropySystem(u, t, l, m, θT, μ0, Mu=molarmass(u)/m, g0=gravity(u),
              e=m*l*l/(t*t), λ=ONE, αL=ONE, Kcd=luminousefficacy(u)*e/t*g0)   # UnitSystems.jl:254-264
    return unitsystem(
        boltzmann(u)*θT/e/g0,          # kB
        planckreduced(u)/t/e/g0,       # ħ
        lightspeed(u)*t/l,             # c
        μ0,
        electronmass(u)/m,             # me
        Mu, Kcd,
        radian(u), λ, αL, g0,          # NOTE: λ, αL reset to 1 unless passed
        universe(u), tau(u), primes(u))
    # t,l,m,θT = sizes of the new time/length/mass/temperature units measured in u's units.
    # e = size of the new energy unit in u (default m·l²/t²). Default arguments are evaluated
    # left to right and may refer to earlier arguments (e uses m,l,t; Kcd uses e,t,g0).

AstronomicalSystem(u, t, l, m, e=m*lightspeed(u)^2)                  # UnitSystems.jl:272-274
    = EntropySystem(u, t, l, m, e/boltzmann(u), spat(u), ONE, ONE, e, ONE, ONE, ONE)
    # ⇒ kB = 1.0 (Float), μ0 = spat(u) = 4π·θ², Mu = 1, g0 = 1, λ = αL = Kcd = 1

ElectricSystem(u, Ω, V) = EntropySystem(u, ONE, ONE, V*V/Ω, ONE, vacuumpermeability(u)/Ω)  # UnitSystems.jl:228
    # mass unit rescaled by V²/Ω; e = m; Mu = molarmass(u)/m; g0 = gravity(u)

GaussSystem(u, μ0, λ, αL=ONE, l=inv((2*5)^2), m=inv((2*5)^3), g0=gravity(u))   # UnitSystems.jl:237-239
    = EntropySystem(u, ONE, l, m, ONE, μ0, (m == 1/1000 ? ONE : molarmass(u)/m), g0, m*(l*l), λ, αL)

RankineSystem(u, l, m, g0=ONE)                                       # initdata.jl:84
    = EntropySystem(u, ONE, l, m, °R, vacuumpermeability(u)/(m*l)/g0, unit(kilo*molarmass(u)), g0)
    # temperature unit becomes °R (5/9 K); molar amount becomes the "pound-mole" (Mu snaps to Int 1)

(U::UnitSystem)(JK, Js, ms, Hm, kg)                                  # UnitSystems.jl:205-221
    = unitsystem(kB*JK, ħ*Js, c*ms, μ0*Hm, me*kg, Mu, Kcd, θ, λ,
                 isone(αL) ? αL : αL/ms, g0, C, τ, primes)
```

`constructors.json` holds 108 random-argument goldens for all of the above (bases Metric, SI2019, English, Gauss, FPS).

### 4.3 `unit` snapping (`UnitSystems.jl:276`)

```
unit(x, y=1) = isapprox(y, x; rtol = eps(Float64)^0.9) ? y : x
    # rtol = 8.161992717227193e-15, atol = 0:
    # isapprox(y,x) ≡ x == y || (isfinite(x) && isfinite(y) && |x-y| ≤ rtol·max(|x|,|y|))
unit(::Constant{x}, y=1)  = Constant{unit(x,y)}()
unit(x, ::Constant{y})    = unit(x, y)
unit(::Constant{x}, ::Constant{y}) = Constant{unit(x,y)}()
```

The returned `y` is typically the Int `1`. That is why, e.g., `area(Metric,Metric) === Constant{1}` and a snapped conversion factor is **Int** 1. NaN and Inf never snap (they stay as `x`). **Snapping is applied at every intermediate level** of the composed definitions (§2.8), so parity requires snapping at the same points. `analyze.py` shows that skipping it changes results by ≤ 3.3e-15 relative.

### 4.4 Conversion of values (`UnitSystems.jl:300-305`)

```
q(v::Real, U, S):
    if typeof(U) == typeof(S): return v                  # identical systems: value unchanged, type preserved
    u = q(U, S)                                          # a Constant
    if isone(u): return v                                # exact-1 factor: value unchanged
    if v isa Constant: return Constant{v.N / u.N}()      # true division
    return v * (1 / u.N)                                 # plain v: multiply by the reciprocal (1/u rounded first)
q(v::Real, U)  = q(v, U, Metric)
q(U)           = q(Natural, U)          # for q ∉ Constants ∪ {angle, permeability}
```

`convert_values.json` holds oracle rows for `q(v,U,S)` and `q(v,U)`.

### 4.5 Base two-system factors

The four primitive factors from which every other quantity is composed, besides the constant ratios `c(S)/c(U)` from the `Constants` loop:

```
length(U,S,l=1) = unit( (turn(S)/turn(U)) * (ħ_S·me_U·c_U·g_S) / (ħ_U·me_S·c_S·g_U), l )     # kinematic.jl:71
time(U,S,t=1)   = unit( length(U,S)/lightspeed(U,S), 1 )        # t is IGNORED (bug)             kinematic.jl:95
temperature(U,S)= unit( (kB_U·me_S·c_S²·g_U) / (kB_S·me_U·c_U²·g_S) )                           # thermodynamic.jl:43
charge(U,S)     = unit( sqrt( (turn(S)/turn(U)) * (ħ_S·μ0_U·c_U·λ_U·αL_U²) / (ħ_U·μ0_S·c_S·λ_S·αL_S²) ) )  # electromagnetic.jl:15
luminousenergy(U,S) = unit( frequency(U,S) * (Kcd_S·h_S)/(Kcd_U·h_U) )  # h = planck = turn·ħ       # thermodynamic.jl:74
```

`turn(U) = tau(U)*radian(U)`, and τ is common to all systems, so `turn(S)/turn(U) = θ_S/θ_U`. The remaining 120+ quantities are compositions of these, each `unit`-snapped; the verbatim definitions are in the §2.8 table.

### 4.6 Dimension theory (recovered exactly; enables a generic Lean implementation)

Assign USQ dimensions to the 11 constants. This matches Similitude's `Unified` system (`Similitude.jl:157`) and the Wolfram `MeasureSystem` (`Kernel/systems.wl:89-100`):

| constant | USQ dimension | | constant | USQ dimension |
|---|---|---|---|---|
| kB | F·L·Θ⁻¹ | | Mᵤ | M·N⁻¹ |
| ħ | F·L·T·A⁻¹ | | Kcd | J·T·F⁻¹·L⁻¹ |
| c | L·T⁻¹ | | θ | A |
| μ₀ | F·T²·Q⁻²·Λ⁻¹·C² | | λ | Λ |
| mₑ | M | | αL | C⁻¹ |
| g₀ | M·L·T⁻²·F⁻¹ | | | |

(The Wolfram `DimensionSystem[]` at `Kernel/systems.wl:179` has an extra `A⁻²` on μ₀ and `A²` on λ. That is an older variant; the Julia-consistent choice is the table above.)

Call this 11×11 integer matrix `Dc` (rows = constants, columns = `F M L T Q Θ N J A Λ C`). **det Dc = −2**, and its inverse is the table of *base-unit* exponents. Row *i* gives the size of the natural unit of base dimension *i* as a monomial in the constants; the product was checked to equal the identity exactly:

| base dim | natural unit = monomial in constants | Julia name of that factor |
|---|---|---|
| F | ħ⁻¹·c³·mₑ²·θ⁻¹·g₀⁻² | `force` |
| M | mₑ | `mass` |
| L | ħ·c⁻¹·mₑ⁻¹·θ·g₀ | `length` |
| T | ħ·c⁻²·mₑ⁻¹·θ·g₀ | `time` |
| Q | ħ^½·c^-½·μ₀^-½·θ^½·λ^-½·αL⁻¹ | `charge` |
| Θ | kB⁻¹·c²·mₑ·g₀⁻¹ | `temperature` |
| N | mₑ·Mᵤ⁻¹ | `molaramount` |
| J | ħ⁻¹·c⁴·mₑ²·Kcd·θ⁻¹·g₀⁻² | `luminousflux` |
| A | θ | `angle` |
| Λ | λ | `demagnetizingfactor` |
| C | αL⁻¹ | `1/lorentz` |

**Theorem (verified numerically for all 131 quantities).** For a quantity of USQ dimension `d ∈ ℤ¹¹`,

```
q(U,S) = Π_{i ∈ {F..C}} B_i(U,S)^{d_i},   B_i(U,S) = X_i(S)/X_i(U),   X_i = the monomial in row i above
```

up to rounding and `unit` snapping. Equivalently, `e(q) = d(q)·Dc⁻¹` gives the exponents over the constants; this is column 5 of §2.8.

The Julia code never states dimensions. They are implicit in the composition chains, and the chains contain quirks, so the `d` in §2.8 is *what Julia actually computes*, not what the name suggests (§4.11).

**Numerical hazard.** Evaluating `Π r_k^{e_k}` directly with naive sequential multiplication underflows or overflows for some pairs involving IAUE/IAUJ/FFF/natural systems (errors up to 0.45%, e.g. `specificweight(IAUE,Stoney)`). Julia's composed chains do not, because every intermediate factor is a normal-range number. A Lean generic path must either:
- (a) compute the per-system natural values `X_d(U) = q_d(Natural,U)` (one monomial per system, all normal-range) and return `X_d(S)/X_d(U)`, which matches Julia to ≤ 3.3e-15 on all 297,627 finite entries (`analyze.py`); or
- (b) evaluate in log space with compensated summation.

Use (a).

### 4.7 Physics constants and the `Coupling` overrides

The formulas are in the §2.9 table (source `physics.jl:15-59`, `UnitSystems.jl:285-289`). The ones that take `C::Coupling = universe(U)` call `X(U, C)` for `X ∈ {boltzmann, planckreduced, lightspeed, vacuumpermeability, electronmass, molarmass}`.

Special methods dispatch on **exact type-parameter values**. A method is only *live* if its pattern is a `Constant` (a pattern that evaluates to a plain Float64 can never match a Constant parameter). The oracle confirms which are live:

| method (`UnitSystems.jl`) | pattern | live for | returns |
|---|---|---|---|
| `:377 electronmass(::typeof(Planck), C)` | exact type | Planck | `sqrt(spat(U)*coupling(C))` |
| `:378 electronmass(::typeof(PlanckGauss), C)` | exact type | PlanckGauss | `sqrt(coupling(C))` |
| `:379 electronmass(::UnitSystem{…,√(αG*αinv)}, C)` | me = Constant | Stoney, Schrodinger | `sqrt(coupling(C)/finestructure(C))` |
| `:380 electronmass(::UnitSystem{…,1/μₚₑ}, C)` | `1/μₚₑ` is **plain** | none (dead) | — |
| `:381 vacuumpermeability(::UnitSystem{…,4π/αinv^2}, C)` | plain | dead | — |
| `:382 vacuumpermeability(::UnitSystem{…,π/αinv^2}, C)` | plain | dead | — |
| `:383 lightspeed(::UnitSystem{kB,ħ,αinv}, C)` | Constant | Hartree, Schrodinger | `inv(finestructure(C))` |
| `:384 lightspeed(::UnitSystem{kB,ħ,2αinv}, C)` | plain | dead | — |
| `:385 planckreduced(::UnitSystem{kB,αinv}, C)` | Constant | Stoney, Electronic | `inv(finestructure(C))` |
| `:387 electronmass(::UnitSystem{kB,ħ,𝘤,μ₀,mₑ}, C)` | global Constants 𝘤, mₑ | Metric, SI2019, SI1976, MetricTurn…Arcsecond, Engineering | `electronmass(U)` (pass-through) |
| `:388 …{100𝘤, 1000mₑ}`, `:389 …{𝘤, mₑ/1000}` | plain | dead | — |
| `:390 electronmass(::UnitSystem{…,electronmass(CODATA)}, C)` | Constant | CODATA | `electronmass(planck(U),C)` = `inv(α)^2*R∞*2h/𝘤` → **plain** `9.109383549079828e-31` (stored slot: `9.10938354907983e-31`) |
| `:391 …{electronmass(Conventional)}` | Constant | Conventional | same recomputation |
| `:392 electronmass(::UnitSystem{…,𝘤/ftUS,μ₀,mₑ*ft/lb/g₀}, C)` | Constant, but no system matches | dead | — |
| `:393 vacuumpermeability(::UnitSystem{kB,ħ,𝘤,μ₀}, C)` | global μ₀ | SI2019 | `finestructure(C)*2𝘩/𝘤/𝘦^2` → plain `1.2566370621210484e-6` (slot `1.256637062121048e-6`) |
| `:396 vacuumpermeability(::typeof(CODATA), C)` | type | CODATA | `2RK2014*finestructure(C)/𝘤` |
| `:397 vacuumpermeability(::typeof(Conventional), C)` | type | Conventional | `2RK1990*finestructure(C)/𝘤` |
| `:294-296` fallback | any | all others | stored slot |

With the default `Universe`, these overrides change results by only ~1 ulp. They matter for (1) exact parity of `vacuumpermittivity`, `electrostatic`, `biotsavart`, `vacuumimpedance`, and the `planckmass`-family on the listed systems, and (2) downstream MeasureSystems, where `C` carries uncertainties. `planckmass(Planck) = √(4π) = 3.544907701811032` and `gravitation(Planck) = 1/(4π)`, because Planck is the *rationalized* Planck system; PlanckGauss has `G = mP = 1`.

### 4.8 IAU special cases (`kinematic.jl:45-67`)

These methods dispatch on `lightspeed == DAY*𝘤/au` (IAU☉ only; IAUE/IAUJ have different lengths) against `lightspeed ∈ {𝘤, 100𝘤, 𝘤/ft}`. They call `length(U,S,x)`, which **snaps the result to the exact value** `x ∈ {1/au, au, ft/au, au/ft}`, or `time(U,S,x)` (whose snap argument is ignored).

- **Live:**
  - IAU☉ ↔ every system with `c = 𝘤` exactly (the Metric family, SI2019, CODATA, Conventional, International…);
  - IAU☉ ↔ systems with `c = 𝘤/ft` (English, British, FPS).
  - Result: `length(IAU☉, Metric) === 1.495978707e11` exactly, whereas the generic chain gives `length(IAU☉, Gauss) == 1.4959787070000002e13`.
- **Dead:** the `100𝘤` (CGS) variants, because `100𝘤` evaluates to a plain Float64. Their bodies also reference an undefined `U` (`kinematic.jl:54-55`) and would throw if reached.

### 4.9 Constant arithmetic numerics (what Julia actually computes)

- **Promotion.** Int∘Int stays Int for `+ - * ^(nonneg)` and **wraps on overflow** (`Constant(2)^70 == 0`). `Int/Int` gives Float64. `sqrt`, `inv`, `log` etc. give Float64.
- **Literal integer powers** `x^n` with a Constant `x` lower to `Base.literal_pow` (Julia 1.13, `intfuncs.jl:477-488`):
  - `n ≥ 0`: `^(x, n)`;
  - `n < 0`: `^(inv(x), -n)`.
  - Hence `Constant(10)^-2 == 0.010000000000000002` and `Constant(10)^-28 == 1.0000000000000015e-28` (`inv(10) = 0.1` first).
- **Float64^Int** (`N^b` inside `Constant{N^b}`) uses Julia's compensated power-by-squaring `Base.Math.pow_body`: double-double `two_mul` with FMA, and `x*x*x` for n = 3. It is correctly rounded or nearly so. `x^2` equals `x*x`.
- **Float64^Float64** uses Julia's native `pow`. `sqrt` is IEEE-exact. `exp`, `log`, `log10`, `exp10` are Julia-native implementations and may differ from C libm in the last ulp. (Port status: all of these are ported bit for bit in `JuliaBase.Math`, `JuliaBase.F64.pow`/`exp`/…)
- `Number/Constant` computes `a*inv(b)`, i.e. two roundings. `Constant/Constant` is a single division.

### 4.10 Reproducibility budget (measured)

| comparison | max relative error | count |
|---|---|---|
| Julia `q(U,S)` vs `q(Natural,S)/q(Natural,U)` (table-ratio) | 3.3e-15 | 297,627 finite entries (117,333 bit-identical) |
| Julia vs naive direct monomial | up to 4.5e-3 (subnormal/overflow intermediates) | 33 entries worse than 1e-13 |
| non-finite entries | 197 (NaN 95, Inf 102) | all involve FFF (μ₀ = 0) |
| doc examples reproduced by re-evaluation | 1638/1658 exact string match | the 20 others are doc typos or displayed text that differs from the interpolated expression |

Recommended Lean tolerance: `rtol = 1e-14` for goldens produced by verbatim chains, `1e-13` for the generic path, plus exact equality for entries that Julia snapped to Int 1.

### 4.11 Known bugs and quirks (port faithfully; flag in docs; optionally fix behind `juliaCompat := false`)

1. **Exported but undefined:** `neper`, `bel`, `decibel`, `CGS2019`, `EE2019`, `Λ`. `derived(U)` always throws.
2. **`inchmercury` inverted:** `inHg = Constant(1/3386.389)` (`UnitSystems.jl:318`), so `inchmercury(Metric) == 0.0002952998016471232` Pa (should be 3386.389).
3. **`jovianyear`** (`physics.jl:59`) is correct only in IAU-family systems (`jovianyear(IAU) == 4333.845973840625` days). `jovianyear(Metric) == 3.235198684088133e13` is meaningless, and its fitted dimension is `F^-½·M^½·L^½·T`.
4. **`bradian`** double-applies the angle unit: `bradian(MetricDegree) == 80.57218994027201` (expected 1.40625); dimension A².
5. **`apostilb`, `lambert`, `footlambert`, `bril`** multiply by `two(U)/turn(U)` (a U-angle) inside a value converted from another system. The dimension picks up an extra A⁻¹, so they are wrong in non-radian systems.
6. **`parsec`** divides by `turn(U)` (dimension L·A⁻¹); **`greatcircle`** multiplies by `turn(U)` (L·A).
7. **`photonirradiance = 1/(length·speed)`**, dimension L⁻²·T instead of L⁻²·T⁻¹. `photonradiance`, `diffusionflux` and `rayleigh` inherit this. The Wolfram kernel has the same definition (`Kernel/physics.wl:119`), so it is intentional upstream.
8. **`specificmagnetization`** is inverted (mass/magneticmoment). The tests note "prefer: 1".
9. **`time(U,S,t)`** ignores its third argument, so the IAU time snaps are no-ops. The CGS–IAU special cases are dead code containing an undefined variable.
10. **`slugs` / `kilograms`** docstrings describe slugs, but the code targets `English` (lbm).
11. **`Constant^Constant`** is a MethodError (ambiguity).
12. **`Coupling{αG,α,μₑᵤ,μₚᵤ}()`** silently takes the global `ΩΛ`.
13. **`FFF` has μ₀ = 0.0**, so every electromagnetic conversion involving FFF is NaN/Inf, including `q(FFF,FFF)` for EM quantities (36 diagonal entries ≠ 1).
14. **`thermalconductivity_water`** mixes a U-valued `thermalunit(U)` into a Metric value (it is only right for British).
15. **Name clashes:** `slug`, `rankine`, `kelvin`, the prefixes and the prime names are both numbers and functions, with different meanings (`kelvin == 1.8` vs `kelvin(Metric) == 1`).
16. **`EMU2019`, `ESU2019`** are aliases of `EMU`, `ESU`, not SI2019 variants.
17. **`text.jl`** typos: `:statweber => "statfarad"`, `:apostilb => "abostilb"`.
18. **`LinearAlgebra`** is a declared dependency but never imported.

---

## 5. Display / printing

UnitSystems has no dimension-aware printing (that is Similitude). The complete printing surface:

1. **`show(io, U::UnitSystem)`** prints `unitname(normal(U))`: the canonical name from `Systems`, or `Unknown` (`UnitSystems.jl:187`). Aliases print the canonical name (`IAU` → `IAU☉`, `CGS` → `Gauss`, `SI` → `SI2019`).

2. **`display(U::UnitSystem)`** (`UnitSystems.jl:188-201`) is exactly 12 lines, each ending in `\n`. Labels are left-justified to width 17 followed by `: `:
   ```
   UnitSystem: <name>
     entropy          : <boltzmann>
     angularmomentum  : <planckreduced>
     speed            : <lightspeed>
     permeability     : <vacuumpermeability>
     mass             : <electronmass>
     molarmass        : <molarmass>
     luminousefficacy : <luminousefficacy>
     angle            : <radian>
     rationalization  : <rationalization, or the literal text 4π when it equals Float64(4π)>
     lorentz          : <lorentz>
     gravityforce     : <gravity>
   ```
   Oracle example (`display(Gauss)`), verbatim:
   ```
   UnitSystem: Gauss
     entropy          : 1.3806489995254102e-16
     angularmomentum  : 1.0545718176461563e-27
     speed            : 2.99792458e10
     permeability     : 1
     mass             : 9.109383701558256e-28
     molarmass        : 1
     luminousefficacy : 6.8301969009009e-5
     angle            : 1
     rationalization  : 4π
     lorentz          : 3.335640951981521e-11
     gravityforce     : 1
   ```
   All 48 are in `systems.json:display`.

3. **`display(C::Coupling)`** (`:116`) prints one line:
   `Coupling{αG = 1.751809945750515e-45, α = 0.0072973525692838015, μₑᵤ = 0.0005485799090649074, μₚᵤ = 1.007276466621, ΩΛ = 0.6889}`.
   `show` of a Coupling is Julia's default: `UnitSystems.Coupling{1.751809945750515e-45, …}()`.

4. **`show(io, ::Constant{N})`** is `show(io, N)`: bare Int (`1000`) or Float64 in Julia's shortest round-trip form.

5. **Julia Float64 repr rules** (needed by every golden string):
   - Shortest round-trip digits (Ryu).
   - Plain decimal iff `1e-4 ≤ |x| < 1e6`; otherwise `d.ddde±N` with no `+` and no leading zeros in the exponent.
   - The mantissa always has at least one fractional digit (`1.0e6`, `2.99792458e8`, `100000.0`, `0.0001`, `1.0e-5`, `5.0e-324`).
   - Ints print with no `.0`. Irrationals print as their symbol (`π`, `φ`, `γ`).
   - Reuse the shared `Chakravala/Util/JuliaShow.lean` proposed in the AbstractTensors/Leibniz specs.

6. **Unit-name comments** in docs (e.g. `# J⋅K⁻¹`, `# lbm⋅ft⋅lbf⁻¹⋅s⁻²`) are free text. They are *not* produced by code in UnitSystems, but they are in `doc_goldens.json:unit_comment`, useful for a future Similitude-style unit printer.

---

## 6. Examples with expected outputs (golden candidates)

### 6.1 README

The README has no executable examples beyond `using UnitSystems`. The `Quantity` docstring example `Metric(1, energy)` ⇒ `1 [J] Metric` and `English(1, energy)` ⇒ `1 [lbf⋅ft] English` (`UnitSystems.jl:85-91`) describes **Similitude's** output. In UnitSystems both return the bare value `1`. Do not use them as UnitSystems goldens.

### 6.2 Test suite (`test/runtests.jl`)

**(a) Per-system identities** (lines 3-242). These run for every system except the six Metric angle variants. `FFF` skips the electromagnetic and dimensionless blocks; `Cosmological` skips `stefan`/`radiationdensity`. Comparisons are `≈` (default rtol √eps), and `==` where noted. They are ready-made **property tests**:
```
μₑᵤ ≈ electronmass(U)/dalton(U);  μₚᵤ ≈ protonmass(U)/dalton(U);  μₚₑ ≈ protonmass(U)/electronmass(U)
1/αinv ≈ (elementarycharge(U)/charge(PlanckGauss,U))^2;   αG ≈ (electronmass(U)/mass(PlanckGauss,U))^2
1/αinv ≈ elementarycharge(U)^2*rationalization(U)/4π/vacuumpermittivity(U)/planckreduced(U)/lightspeed(U)
1/αinv ≈ vacuumpermeability(U)*lightspeed(U)*(elementarycharge(U)*lorentz(U))^2*rationalization(U)/4π/planckreduced(U)
1/αinv ≈ electrostatic(U)*elementarycharge(U)^2/planckreduced(U)/lightspeed(U)
1/αinv ≈ lightspeed(U)*vacuumpermeability(U)*rationalization(U)*lorentz(U)^2/2klitzing(U)
1/αinv ≈ elementarycharge(U)^2*vacuumimpedance(U)/2planck(U)
lightspeed(U) ≈ 1/lorentz(U)/sqrt(vacuumpermeability(U)*vacuumpermittivity(U)) ≈ αinv*sqrt(hartree(U)*gravity(U)/electronmass(U))
lightspeed(U) ≈ electronmass(U)^2*gravitation(U)/planckreduced(U)/αG
planck(U) == turn(U)*planckreduced(U);  planck(U) ≈ 4lorentz(U)^2/josephson(U)^2/klitzing(U)
planckmass(U) ≈ sqrt(planckreduced(U)*lightspeed(U)/gravitation(U)) ≈ electronmass(U)/sqrt(αG)
gravitation(U) ≈ einstein(U)*lightspeed(U)^4/8π
hartree(U) ≈ 2rydberg(U)*planck(U)*lightspeed(U);  bohr(U) ≈ electronradius(U)*αinv^2 ≈ 1/αinv/4π/rydberg(U)
molarmass(U) ≈ dalton(U)*avogadro(U);  boltzmann(U) == molargas(U)/avogadro(U);  molargas(U) == boltzmann(U)*avogadro(U)
stefan(U) ≈ 2π^5*boltzmann(U)^4/15planck(U)^3/lightspeed(U)^2;  radiationdensity(U) ≈ 4stefan(U)/lightspeed(U)
rationalization(U) ≈ 4π*electrostatic(U)*vacuumpermittivity(U) ≈ vacuumimpedance(U)*vacuumpermittivity(U)*lightspeed(U)
magnetostatic(U) == lorentz(U)*biotsavart(U);  lorentz(U) == magnetostatic(U)/biotsavart(U);  biotsavart(U) == magnetostatic(U)/lorentz(U)
elementarycharge(U) ≈ sqrt(planck(U)/klitzing(U)) ≈ faraday(U)/avogadro(U);  faraday(U) == elementarycharge(U)*avogadro(U)
klitzing(U) == planck(U)/elementarycharge(U)^2 ≈ vacuumimpedance(U)*αinv/2;  magneticfluxquantum(U) == 1/josephson(U)
conductancequantum(U) ≈ 2/klitzing(U);  magneton(U) ≈ elementarycharge(U)*planckreduced(U)*lorentz(U)/2electronmass(U)
```
There are about 120 relations in total; port all of them from lines 6-240. The `==` relations are exact in Julia. They hold because the defining formula is literally that expression, and the Lean port must keep those exact.

**(b) CGS conversions** (lines 244-373). Here `C = 100𝘤`, and every comparison is `≈`:

| expression | Metric→ESU | Metric→EMU | Metric→Gauss |
|---|---|---|---|
| `charge(Metric,·)` | `C/10` | `1/10` | `C/10` |
| `current` | `C/10` | `1/10` | `C/10` |
| `electricpotential` | `1e8/C` | `1e8` | `1e8/C` |
| `electricfield` | `1e6/C` | `1e6` | `1e6/C` |
| `electricdisplacement` | `4π*C/1e5` | `4π/1e5` | `4π*C/1e5` |
| `electricdipolemoment` | `10C` | `10` | `10C` |
| `magneticdipolemoment` | `1e3*C` | `1e3` | `1e3` |
| `magneticfield` | `4π*C/1e3` | `4π/1e3` | `4π/1e3` |
| `magneticfluxdensity` | `1e4/C` | `1e4` | `1e4` |
| `magneticflux` | `1e8/C` | `1e8` | `1e8` |
| `resistance` | `1e9/C^2` | `1e9` | `1e9/C^2` |
| `resistivity` | `1e11/C^2` | `1e11` | `1e11/C^2` |
| `capacitance` | `C^2/1e9` | `1e-9` | `C^2/1e9` |
| `inductance` | `1e9/C^2` | `1e9` | `1e9/C^2` |
| `conductance` | `C^2/1e9` | `1e-9` | `C^2/1e9` |
| `chargedensity` | `C/1e7` | `1e-7` | `C/1e7` |
| `magneticpotential` | `4π/10*C` | `4π/10` | `4π/10` |
| `susceptibility` | `1/4π` | `1/4π` | `1/4π` |
| `polestrength` | `10C` | `10` | `10` |
| `reluctance` | — | `4π/1e9` | `4π/1e9` |
| `currentdensity` | `C/1e5` | `1e-5` | `C/1e5` |
| `electricpolarizability` | `1e6/4π/ε₀` | `1e-5` | `1e6/4π/ε₀` |
| `magneticpolarizability` | `1e6/4π` | `1e6/4π` | `1e6/4π` |
| `electricflux` | `1e10/C` | `1e10` | `1e10/C` |
| `magneticmoment` (uncertain) | `1e10/C` | `1e10` | `1e10` |

Reverse direction (`q(·,Metric)`):

| expression | ESU | EMU | Gauss |
|---|---|---|---|
| `permittivity(ESU,Metric)` | `ε₀` | | |
| `permeability(·,Metric)` | | `μ₀` | `μ₀` |
| `specificsusceptibility(·,Metric)` | `4π/1e3` | `4π/1e3` | `4π/1e3` |
| `demagnetizingfactor(·,Metric)` | `1/4π` | `1/4π` | `1/4π` |
| `specificmagnetization(·,Metric)` (uncertain) | `1e7/C` | `1e7` | `1e7` |

Also `molarmass(Natural) == molarmass(CGS) == 1000molarmass(Metric)`.

### 6.3 Doc examples (1638 verified by re-evaluation)

`goldens/doc_goldens.json` holds all 1658 distinct `julia>` examples, with `expr`, `unit_comment`, `doc_output` and `eval_repr`, plus `status` (`verified` means byte-equal to Julia's repr). Below is **one verified example per documented binding** (406 lines, verbatim; `⇒` precedes Julia's printed output). The unit comment is Reed's intended unit of the result.

```
angle(CGS,Metric) ⇒ 1   # rad⋅rad⁻¹
thermalunit(British) ⇒ 778.1576129990755   # ft⋅lb
boltzmann(British) ⇒ 5.657302463819266e-24   # ft⋅lb⋅°R⁻¹
boltzmann(CGSe) ⇒ 1.3806489995254102e-16   # erg⋅K⁻¹
boltzmann(CGSm) ⇒ 1.3806489995254102e-16   # erg⋅K⁻¹
josephson(CODATA) ⇒ 4.8359785250000006e14   # Hz⋅V⁻¹
josephson(Conventional) ⇒ 4.8359789999999994e14   # Hz⋅V⁻¹
boltzmann(Cosmological) ⇒ 1.0
boltzmann(CosmologicalQuantum) ⇒ 1.0
boltzmann(EMU) ⇒ 1.3806489995254102e-16   # erg⋅K⁻¹
boltzmann(ESU) ⇒ 1.3806489995254102e-16   # erg⋅K⁻¹
boltzmann(Electronic) ⇒ 1
boltzmann(English) ⇒ 5.657302463819266e-24   # ft⋅lbf⋅°R⁻¹
hartree(SI2019)/elementarycharge(SI2019) ⇒ 27.211386245988724   # eV
boltzmann(FFF) ⇒ 6.793104372040068e-18   # fir⋅fur²⋅ftn⁻²⋅F⁻¹
boltzmann(FPS) ⇒ 1.8201832416933465e-22   # ft⋅pdl⋅°R⁻¹
conductancequantum(SI2019) ⇒ 7.748091729863649e-5   # S
gravitation(English) ⇒ 3.322928526687524e-11   # ft³⋅lbm⁻¹⋅s⁻²
boltzmann(Gauss) ⇒ 1.3806489995254102e-16   # erg⋅K⁻¹
boltzmann(Gravitational) ⇒ 1.4078701692478171e-24   # kgf⋅m⋅K⁻¹
horsepower(British) ⇒ 550   # lb⋅ft⋅s⁻¹
boltzmann(Hartree) ⇒ 1
boltzmann(Hubble) ⇒ 1.0
boltzmann(IAU) ⇒ 2.3160832669610065e-66   # M⊙⋅au²⋅D⁻²⋅K⁻¹
boltzmann(IAUE) ⇒ 1.1679233837035083e-55   # ME⋅LD²⋅D⁻²⋅K⁻¹
boltzmann(IAUJ) ⇒ 8.959677342845726e-65   # MJ⋅JD²⋅D⁻²⋅K⁻¹
boltzmann(IPS) ⇒ 6.788762956583119e-23   # in⋅lb⋅°R⁻¹
resistance(International,Metric) ⇒ 1.0004949999999997   # Ω⋅Ω⁻¹
resistance(InternationalMean,Metric) ⇒ 1.00049   # Ω⋅Ω⁻¹
jupiterdistance(Metric) ⇒ 7.784789999999999e11   # m
boltzmann(KKH) ⇒ 1.789321103384932e-22   # kg⋅km²⋅h⁻²⋅K⁻¹
luminousefficacy(Metric) ⇒ 683.01969009009   # lm⋅W⁻¹
boltzmann(LorentzHeaviside) ⇒ 1.3806489995254102e-16   # erg⋅K⁻¹
mass(CGS,Metric) ⇒ 0.001   # kg⋅g⁻¹
boltzmann(Engineering) ⇒ 1.4078701692478171e-24   # kgf⋅m⋅K⁻¹
boltzmann(MPH) ⇒ 8.46159564836783e-23   # lbf⋅mi²⋅hr⁻²⋅F⁻¹
boltzmann(MTS) ⇒ 1.3806489995254105e-26   # kJ⋅K⁻¹
greatcircle(Meridian) ⇒ 4.000000000000001e7   # em
boltzmann(Metric) ⇒ 1.3806489995254104e-23   # J⋅K⁻¹
boltzmann(MetricArcminute) ⇒ 1.3806489995254104e-23   # J⋅K⁻¹
boltzmann(MetricArcsecond) ⇒ 1.3806489995254104e-23   # J⋅K⁻¹
boltzmann(MetricDegree) ⇒ 1.3806489995254104e-23   # J⋅K⁻¹
boltzmann(MetricGradian) ⇒ 1.3806489995254104e-23   # J⋅K⁻¹
boltzmann(MetricTurn) ⇒ 1.3806489995254104e-23   # J⋅K⁻¹
molarmass(CGS) ⇒ 1   # g⋅mol⁻¹
molaramount(SI2019,Metric) ⇒ 0.9999999996562561   # mol⋅mol⁻¹
boltzmann(Natural) ⇒ 1
boltzmann(NaturalGauss) ⇒ 1
greatcircle(Nautical) ⇒ 21600.0   # nm
boltzmann(Planck) ⇒ 1
boltzmann(PlanckGauss) ⇒ 1
boltzmann(QCD) ⇒ 1
boltzmann(QCDGauss) ⇒ 1
boltzmann(QCDoriginal) ⇒ 1
rydberg(Metric) ⇒ 1.0973731568160104e7   # m⁻¹
boltzmann(Rydberg) ⇒ 1
boltzmann(SI2019) ⇒ 1.380649e-23   # J⋅K⁻¹
boltzmann(SI1976) ⇒ 1.3806253172239044e-23   # J⋅K⁻¹
boltzmann(Schrodinger) ⇒ 1
boltzmann(Stoney) ⇒ 1
boltzmann(Survey) ⇒ 5.65729114921434e-24   # ftUS⋅lbf⋅°R⁻¹
time(IAU,Metric) ⇒ 86400.0   # s⋅day⁻¹
celsius(Metric) ⇒ 273.15   # K
abampere(Metric) ⇒ 10.0   # C⋅s⁻¹
abcoulomb(Metric) ⇒ 10.0   # C
abfarad(Metric) ⇒ 1.0000000000000001e9   # F
abhenry(Metric) ⇒ 9.999999999999999e-10   # H
abmho(Metric) ⇒ 1.0000000000000001e9   # S
abohm(Metric) ⇒ 9.999999999999999e-10   # Ω
abvolt(Metric) ⇒ 9.999999999999999e-9   # V
acceleration(CGS,Metric) ⇒ 0.01   # m⋅s⁻¹⋅gal⁻¹
acre(Metric) ⇒ 4046.856422400001   # m²
action(CGS,Metric) ⇒ 1.0000000000000001e-7   # J⋅erg⁻¹
admiraltymile(Metric) ⇒ 1853.1840000000002   # m
admittance(CGS,Metric) ⇒ 1.0000000000000008e-5   # Ba⋅m³⋅cm⁻³⋅Pa⁻¹
amagat(Metric) ⇒ 44.615033390134165   # mol⋅m⁻³
ampere(Metric) ⇒ 1   # C⋅s⁻¹
angstrom(CGS) ⇒ 9.999999999999999e-9   # cm
angulararea(CGS,Metric) ⇒ 0.00010000000000000005   # m²⋅cm⁻²
angularlength(CGS,Metric) ⇒ 0.010000000000000002   # cm⋅m⁻¹
momentum(CGS,Metric) ⇒ 1.0e-5   # N⋅m⋅dyn⁻¹⋅cm⁻¹
angularwavenumber(CGS,Metric) ⇒ 99.99999999999999   # cm⋅m⁻¹
apm(Metric) ⇒ 0.016666666666666666   # s⁻¹
apostilb(Engineering) ⇒ 0.3183098861837907   # nt
arcminute(Engineering) ⇒ 0.0002908882086657216   # rad
arcsecond(Engineering) ⇒ 4.84813681109536e-6   # rad
area(CGS,Metric) ⇒ 0.00010000000000000005   # m²⋅cm⁻²
areadensity(CGS,Metric) ⇒ 9.999999999999996   # kg⋅cm²⋅g⁻¹⋅m⁻²
atmosphere(Metric) ⇒ 101325.0   # Pa
dalton(Metric) ⇒ 1.6605390666030467e-27   # kg
astronomicalunit(Metric) ⇒ 1.495978707e11   # m
avogadro(SI2019) ⇒ 6.02214076e23   # mol⁻¹
bohr(Metric) ⇒ 5.291772109022829e-11   # m
bar(Metric) ⇒ 100000   # Pa
barn(Metric) ⇒ 1.0000000000000015e-28   # m²
barye(Metric) ⇒ 0.09999999999999996   # Pa
biotsavart(Metric) ⇒ 1.0000000000000001e-7   # H⋅m⁻¹
boilerhorsepower(British) ⇒ 7235.785026428903   # lb⋅ft⋅s⁻¹
boiling(Metric) ⇒ 373.1339   # K
boltzmann(SI2019)/elementarycharge(SI2019) ⇒ 8.617333262145179e-5   # eV⋅K⁻¹
bradian(Engineering) ⇒ 0.02454369260617026   # rad
bril(Engineering) ⇒ 3.183098861837906e-8   # nt
bubnoff(CGS) ⇒ 3.1688087814028946e-6   # cm⋅s⁻¹
calorie(International) ⇒ 4.186046511627907   # J
candela(Engineering) ⇒ 1   # lm⋅rad⁻²
capacitance(EMU,Metric) ⇒ 1.0e9   # F⋅abF⁻¹
catalysis(English,Metric) ⇒ 453.59237   # kat⋅s⋅lb-mol⁻¹
charge(EMU,Metric) ⇒ 10.0   # C⋅abC⁻¹
chargedensity(EMU,Metric) ⇒ 9.999999999999994e6   # C⋅cm³⋅abC⁻¹⋅m⁻³
compliance(CGS,Metric) ⇒ 1000.0   # kg⋅g⁻¹
compressibility(CGS,Metric) ⇒ 10.000000000000004   # Ba⋅Pa⁻¹
conductance(EMU,Metric) ⇒ 1.0e9   # S⋅abS⁻¹
conductivity(EMU,Metric) ⇒ 9.999999999999998e10   # S⋅cm⋅abS⁻¹⋅m⁻¹
cosmological(Metric) ⇒ 1.1056022912824226e-52
coulomb(Metric) ⇒ 1   # C
crackle(CGS,Metric) ⇒ 0.01   # m⋅cm⁻¹
cup(Metric) ⇒ 0.00023658823650000012   # m³
curie(Metric) ⇒ 3.7e10   # Bq
current(EMU,Metric) ⇒ 10.0   # A⋅Bi⁻¹
currentdensity(EMU,Metric) ⇒ 99999.99999999996   # A⋅cm²⋅Bi⁻¹⋅m⁻²
darcy(Metric) ⇒ 9.869232667160132e-13   # m²
day(Metric) ⇒ 86400   # s
degree(Engineering) ⇒ 0.017453292519943295   # rad
demagnetizingfactor(EMU,Metric) ⇒ 0.07957747154594767
density(CGS,Metric) ⇒ 999.9999999999994   # kg⋅cm³⋅g⁻¹⋅m⁻³
diffusionflux(CGS,Metric) ⇒ 9999.999999999998   # cm²⋅m⁻²
diffusivity(CGS,Metric) ⇒ 0.00010000000000000002   # m²⋅cm⁻²
diopter(Metric) ⇒ 1   # m⁻¹
dyne(Metric) ⇒ 1.0e-5   # N
earthcalorie(Meridian) ⇒ 4.174638363474497   # J
earthcoulomb(Metric) ⇒ 1.0028982054691058   # C
earthgram(Meridian) ⇒ 0.001   # keg
earthmass(Metric) ⇒ 5.972166613228324e24   # kg
earthmeter(CGS) ⇒ 100.14480543039193   # cm
earthmole(Metric) ⇒ 1.0043504565319281   # mol
earthradius(KKH) ⇒ 6375.416323689185   # km
𝟐^2^2^3/α ⇒ 0.0   # mₚ
electricalhorsepower(British) ⇒ 550.22136336084   # lb⋅ft⋅s⁻¹
electricdipolemoment(EMU,Metric) ⇒ 0.10000000000000002   # C⋅m⋅abC⁻¹⋅cm⁻¹
electricdisplacement(EMU,Metric) ⇒ 7957.747154594764   # C⋅cm²⋅abC⁻¹⋅m⁻²
electricfield(EMU,Metric) ⇒ 9.999999999999997e-7   # V⋅cm⋅abV⁻¹⋅m⁻¹
electricflux(EMU,Metric) ⇒ 1.0000000000000002e-10   # V⋅m⋅abV⁻¹⋅cm⁻¹
electricpolarizability(EMU,Metric) ⇒ 100000.00000000004   # C⋅m²⋅abV⋅abC⁻¹⋅cm⁻²⋅V⁻¹
electricpotential(EMU,Metric) ⇒ 1.0e-8   # V⋅abV⁻¹
electronmass(Metric)/dalton(Metric) ⇒ 0.0005485799090649074   # Da
electronvolt(SI2019) ⇒ 1.602176634e-19   # J
electrostatic(Metric) ⇒ 8.987551787368177e9   # N⋅m²⋅C⁻²
elementarycharge(SI2019) ⇒ 1.602176634e-19   # C
energy(CGS,Metric) ⇒ 1.0000000000000001e-7   # J⋅erg⁻¹
entropy(Metric,SI2019) ⇒ 1.000000000343744   # K⋅K⁻¹
eotvos(Metric) ⇒ 9.999999999999999e-10   # s⁻²
erg(Metric) ⇒ 1.0e-7   # J
etendue(CGS,Metric) ⇒ 0.00010000000000000005   # m²⋅cm⁻²
byte ⇒ 8   # 𝟐^3
exposure(EMU,Metric) ⇒ 10000.0   # C⋅g⋅abC⁻¹⋅kg
fahrenheit(Metric) ⇒ 255.37222222222226   # K
farad(Metric) ⇒ 1   # F
faraday(SI2019) ⇒ 96485.33212331001   # C⋅mol⁻¹
flick(Metric) ⇒ 1.0e10   # W⋅m⁻³
fluence(CGS,English) ⇒ 6.852176585679174e-5   # lb⋅g⁻¹
fluidounce(Metric) ⇒ 2.9573529562500015e-5   # m³
foot(Metric) ⇒ 0.3048   # m
footcandle(Metric) ⇒ 10.76391041670972   # lx
footlambert(Engineering) ⇒ 3.426259099635391   # nt
footpound(Metric) ⇒ 1.3558179483314006   # J
force(CGS,Metric) ⇒ 1.0e-5   # N⋅dyn⁻¹
fpm(CGS) ⇒ 0.508   # cm⋅s⁻¹
fps(Metric) ⇒ 0.3048   # m⋅s⁻¹
fuelefficiency(CGS,Metric) ⇒ 9999.999999999996   # cm²⋅m⁻²
galileo(Metric) ⇒ 0.01   # m⋅s⁻²
gallon(Metric) ⇒ 0.003785411784000002   # m³
gasgallon(Metric) ⇒ 1.2027456665017478e8   # J
gauss(Metric) ⇒ 9.999999999999995e-5   # T
gaussgravitation(Engineering) ⇒ 1.9909836764714663e-7
gaussianmonth(Metric) ⇒ 2.3718343492584163e6   # s
gaussianyear(Metric) ⇒ 3.1558195988402087e7   # s
gilbert(Metric) ⇒ 0.7957747154594768   # A⋅rad⁻¹
golden ⇒ φ   # φ
gradian(Engineering) ⇒ 0.015707963267948967   # rad
grain(Metric) ⇒ 6.479891000000001e-5   # kg
gram(Metric) ⇒ 0.001   # kg
gravity(Metric) ⇒ 1
gravityforce(Metric,CGS) ⇒ 1
gray(Metric) ⇒ 1.0   # Gy
greatcircle(KKH) ⇒ 40057.92217215678   # km
hectare(Metric) ⇒ 10000   # m²
henry(Metric) ⇒ 1   # H
hertz(Engineering) ⇒ 1.0   # rad⋅s⁻¹
horsepowermetric(British) ⇒ 542.4760388407421   # lb⋅ft⋅s⁻¹
horsepowerwatt(British) ⇒ 542.8672105403163   # lb⋅ft⋅s⁻¹
hour(Metric) ⇒ 3600   # s
hubble(Metric) ⇒ 2.1927112672380577e-18
hyl(Metric) ⇒ 9.80665   # kg
hyperfine(Metric) ⇒ 9.19263177e9   # Hz
illuminance(CGS,Metric) ⇒ 9999.999999999996   # lx⋅ph⁻¹
impedance(CGS,Metric) ⇒ 99999.99999999991   # Pa⋅cm³⋅m⁻³⋅Ba⁻¹
impulse(CGS,Metric) ⇒ 1.0e-5   # N⋅dyn⁻¹
inch(Metric) ⇒ 0.025400000000000002   # m
inchmercury(English) ⇒ 6.1674645863632695e-6   # lb⋅ft⁻²
inductance(EMU,Metric) ⇒ 1.0e-9   # H⋅abH⁻¹
inertance(CGS,Metric) ⇒ 99999.99999999991   # kg⋅cm⁴⋅g⁻¹⋅m⁻⁴
inertia(CGS,Metric) ⇒ 0.001   # kg⋅g⁻¹
irradiance(CGS,Metric) ⇒ 0.0009999999999999996   # kg⋅g⁻¹
ips(CGS) ⇒ 2.5400000000000005   # cm⋅s⁻¹
jansky(Metric) ⇒ 1.0000000000000015e-26   # kg⋅s⁻²
jerk(CGS,Metric) ⇒ 0.01   # m⋅cm⁻¹
josephson(SI2019) ⇒ 4.835978484169836e14   # Hz⋅V⁻¹
joule(Metric) ⇒ 1   # J
jovianyear(Metric) ⇒ 3.235198684088133e13   # s
jupitermass(Metric) ⇒ 1.8981240594811976e27   # kg
katal(Metric) ⇒ 1   # mol⋅s⁻¹
kayser(Metric) ⇒ 99.99999999999999   # m⁻¹
kilocalorie(International) ⇒ 4186.046511627907   # J
kelvin(Metric) ⇒ 1   # K
kilogram(Metric) ⇒ 1   # kg
kilopond(Metric) ⇒ 9.80665   # N
klitzing(SI2019) ⇒ 25812.807459304513   # Ω
magnetostatic(Metric) ⇒ 1.0000000000000001e-7   # H⋅m⁻¹
kmh(Metric) ⇒ 0.2777777777777778   # m⋅s⁻¹
knot(Metric) ⇒ 0.515148176082263   # m⋅s⁻¹
lambert(Engineering) ⇒ 3183.098861837906   # nt
langley(Metric) ⇒ 41867.37323211057   # kg⋅s⁻²
lapserate(Metric,SI2019) ⇒ 0.9999999996562562   # K⋅K⁻¹
gforce(CGS) ⇒ 980.6649999999998   # gal
length(CGS,Metric) ⇒ 0.010000000000000002   # m⋅cm⁻¹
linearchargedensity(EMU,Metric) ⇒ 999.9999999999998   # C⋅cm⋅abC⁻¹⋅m⁻¹
lineardensity(CGS,Metric) ⇒ 0.09999999999999998   # kg⋅cm¹⋅g⁻¹⋅m⁻¹
liter(Metric) ⇒ 0.001   # m³
lorentz(Metric) ⇒ 1
loschmidt(SI2019) ⇒ 2.686780111798444e25   # m⁻³
lumen(Metric) ⇒ 1   # lm
lumerg(CGS) ⇒ 1.0000000000000001e-7   # lm⋅s
luminance(CGS,Metric) ⇒ 9999.999999999996   # lx⋅ph⁻¹
luminousefficacy(CGS,Metric) ⇒ 1.0e7   # erg⋅s⁻¹⋅W⁻¹
luminousenergy(IAU,Metric) ⇒ 86399.99999999997   # s⋅day⁻¹
luminousexposure(CGS,Metric) ⇒ 9999.999999999996   # lx⋅ph⁻¹
lunardistance(Metric) ⇒ 3.8439900000000006e8   # m
lunarmass(Metric) ⇒ 7.345787071534757e22   # kg
lux(Metric) ⇒ 1   # lx
lightyear(Metric) ⇒ 9.4607304725808e15   # m
magneticdipolemoment(EMU,Metric) ⇒ 0.0010000000000000005   # J⋅G⋅T⁻¹⋅erg⁻¹
magneticfield(EMU,Metric) ⇒ 79.57747154594766   # A⋅m⁻¹⋅Oe⁻¹
magneticflux(EMU,Metric) ⇒ 1.0e-8   # Wb⋅Mx⁻¹
magneticfluxdensity(EMU,Metric) ⇒ 9.999999999999995e-5   # T⋅G⁻¹
magneticmoment(EMU,Metric) ⇒ 1.0000000000000002e-10   # Wb⋅m⋅Mx⁻¹⋅cm⁻¹
magneticpotential(EMU,Metric) ⇒ 0.7957747154594768   # A⋅Gb⁻¹
massflow(CGS,Metric) ⇒ 0.001   # kg⋅g⁻¹
maxwell(Metric) ⇒ 9.999999999999999e-9   # Wb
meancalorie(InternationalMean) ⇒ 4.186046511627907   # J
mechanicalheat(Metric) ⇒ 4.186737323211058   # J
meridianmile(Metric) ⇒ 1851.851851851852   # m
meter(CGS) ⇒ 99.99999999999999   # cm
μₑᵤ ⇒ 0.0005485799090649074   # electronunit(Universe)
mile(Metric) ⇒ 1609.3440000000003   # m
minute(Metric) ⇒ 60   # s
mobility(EMU,Metric) ⇒ 1.0000000000000002e-12   # C⋅g⋅abC⁻¹⋅kg
molality(CGS,Metric) ⇒ 1000.0   # kg⋅g⁻¹
molarconductivity(EMU,Metric) ⇒ 1.0000000000000004e7   # S⋅m²⋅abΩ⋅cm⁻²
molarenergy(CGS,Metric) ⇒ 1.0000000000000001e-7   # J⋅erg⁻¹
molarentropy(CGS,Metric) ⇒ 1.0000000000000001e-7   # J⋅erg⁻¹
molargas(SI2019) ⇒ 8.31446261815324   # J⋅K⁻¹⋅mol⁻¹
molarity(CGS,Metric) ⇒ 999999.9999999994   # cm³⋅m⁻³
molarmass(CGS,Metric) ⇒ 0.001   # kg⋅g⁻¹
molarsusceptibility(CGS,Metric) ⇒ 1.256637061435918e-5   # m³⋅cm⁻³
molarvolume(CGS,Metric) ⇒ 1.0000000000000006e-6   # m³⋅cm⁻³
mole(Metric) ⇒ 1   # mol
mpge(Metric) ⇒ 1.3380584481180183e-5   # N⁻¹
mph(Metric) ⇒ 0.4470400000000001   # m⋅s⁻¹
mps(KKH) ⇒ 5793.6384   # km⋅h⁻¹
ms(KKH) ⇒ 3.599999999999999   # km⋅h⁻¹
protonmass(Metric) ⇒ 1.6726219236940502e-27   # kg
solarmass(Metric) ⇒ 1.9884092485076926e30   # kg
newton(Metric) ⇒ 1   # N
nit(Engineering) ⇒ 1   # nt
nauticalmile(Metric) ⇒ 1854.5334338961468   # m
numberdensity(CGS,Metric) ⇒ 999999.9999999995   # cm³⋅m⁻³
oersted(Metric) ⇒ 79.57747154594766   # A⋅m⁻¹
ohm(Metric) ⇒ 1   # Ω
ounce(Metric) ⇒ 0.028349523125   # kg
parsec(Metric) ⇒ 3.085677581491367e16   # m
pascal(Metric) ⇒ 1   # Pa
permeability(EMU,Metric) ⇒ 1.2566370614359173e-6   # H⋅cm⋅abH⁻¹⋅m⁻¹
permeance(EMU,Metric) ⇒ 1.256637061435917e-8   # abH⋅H⁻¹
permittivity(EMU,Metric) ⇒ 7.957747154594766e9   # F⋅cm⋅abF⁻¹⋅m⁻¹
phot(Metric) ⇒ 9999.999999999996   # lx
photonirradiance(CGS,Metric) ⇒ 9999.999999999998   # cm²⋅m⁻²
photonradiance(CGS,Metric) ⇒ 9999.999999999998   # cm²⋅m⁻²
pint(Metric) ⇒ 0.00047317647300000024   # m³
planckmass(PlanckGauss) ⇒ 1.0   # mP
poise(Metric) ⇒ 0.09999999999999998   # kg⋅m⁻¹⋅s⁻¹
polestrength(EMU,Metric) ⇒ 0.10000000000000002   # A⋅m⋅pole⁻¹
pop(CGS,Metric) ⇒ 0.01   # m⋅cm⁻¹
pound(Metric) ⇒ 0.45359237   # kg
poundal(Metric) ⇒ 0.13825495437600002   # N
poundforce(Metric) ⇒ 4.4482216152605005   # N
poundmole(Metric) ⇒ 453.59237   # mol
power(CGS,Metric) ⇒ 1.0000000000000001e-7   # W⋅s⋅erg⁻¹
powerdensity(CGS,Metric) ⇒ 0.09999999999999995   # kg⋅cm⋅g⁻¹⋅m⁻¹
pressure(CGS,Metric) ⇒ 0.09999999999999996   # Pa⋅Ba⁻¹
psi(Metric) ⇒ 6894.757293168356   # Pa
quart(Metric) ⇒ 0.0009463529460000005   # m³
radarmile(Metric) ⇒ 1.2372115337845802e-5
radian(Engineering) ⇒ 1   # rad
radiance(CGS,Metric) ⇒ 0.0009999999999999996   # kg⋅g⁻¹
radiantintensity(CGS,Metric) ⇒ 1.0000000000000001e-7   # W⋅s⋅erg⁻¹
radiationdensity(Metric) ⇒ 7.565733239877308e-16   # J⋅m⁻³⋅K⁻⁴
rankine(Metric) ⇒ 0.5555555555555556   # K
rayl(Metric) ⇒ 1   # kg⋅m⁻²⋅s⁻¹
rayleigh(Metric) ⇒ 1.0e10   # Hz⋅m⁻²
reluctance(EMU,Metric) ⇒ 7.957747154594767e7   # abH⋅H⁻¹
rem(Metric) ⇒ 0.01   # Sv
resistance(EMU,Metric) ⇒ 1.0e-9   # Ω⋅abΩ⁻¹
reyn(Metric) ⇒ 6894.757293168358   # kg⋅m⁻¹⋅s⁻¹
roentgen(Metric) ⇒ 0.0002579768717696457   # C⋅kg⁻¹
rotationalinertia(CGS,Metric) ⇒ 1.0000000000000005e-7   # kg⋅m²⋅g⁻¹⋅cm⁻²
rpm(Engineering) ⇒ 0.10471975511965977   # rad⋅s⁻¹
electronradius(Metric) ⇒ 2.8179403261891358e-15   # m
sackurtetrode(Metric) ⇒ -1.1648705244382895
sealevel(Metric) ⇒ 288.15   # K
second(Metric) ⇒ 1   # s
two ⇒ 2   # 𝟐
siderealmonth(Metric) ⇒ 2.3573807233179593e6   # s
siderealyear(Metric) ⇒ 3.1558148013226096e7   # s
siemens(Metric) ⇒ 1   # S
slinch(Metric) ⇒ 175.12683524647633   # kg
slinchmole(Metric) ⇒ 175126.83524647632   # mol
slug(Metric) ⇒ 14.593902937206364   # kg
slugmole(Metric) ⇒ 14593.902937206363   # mol
snap(CGS,Metric) ⇒ 0.01   # m⋅cm⁻¹
solarflux(Metric) ⇒ 1.0000000000000015e-22   # kg⋅s⁻²
solidangle(CGS,Metric) ⇒ 1   # rad²⋅rad⁻²
soundexposure(CGS,Metric) ⇒ 0.009999999999999993   # Pa²⋅Ba⁻²
spat(Engineering) ⇒ 12.566370614359172   # rad²
spatian(Engineering) ⇒ 3.544907701811032   # rad
specificenergy(CGS,Metric) ⇒ 0.0001   # m²⋅cm⁻²
specificentropy(Metric,SI2019) ⇒ 1.000000000343744   # m²⋅K⋅K⁻¹⋅cm⁻²
specificforce(CGS,Metric) ⇒ 0.01
specificimpedance(CGS,Metric) ⇒ 9.999999999999996   # Pa⋅cm⋅m⁻¹⋅Ba⁻¹
specificity(CGS,Metric) ⇒ 1.0000000000000006e-6   # m³⋅cm⁻³
specificmagnetization(EMU,Metric) ⇒ 1.0e7   # Wb⋅m⋅g⋅Mx⁻¹⋅cm⁻¹⋅kg⁻¹
specificsusceptibility(EMU,Metric) ⇒ 0.01256637061435918   # m³⋅g⋅kg⁻¹⋅cm⁻³
specificvolume(CGS,Metric) ⇒ 0.0010000000000000007   # g⋅m³⋅kg⁻¹⋅cm⁻³
specificweight(CGS,Metric) ⇒ 9.999999999999995   # N⋅cm³⋅dyn⁻¹⋅m⁻³
spectralexposure(CGS,Metric) ⇒ 0.001   # kg⋅g⁻¹
spectralflux(CGS,Metric) ⇒ 9.999999999999999e-6   # kg⋅m⋅g⁻¹⋅cm⁻¹
speed(CGS,Metric) ⇒ 0.01   # m⋅cm⁻¹
squaredegree(Engineering) ⇒ 0.00030461741978670857   # rad²
stagnance(CGS,Metric) ⇒ 100.0   # cm⋅m⁻¹
statampere(Metric) ⇒ 3.3356409519815207e-10   # C⋅s⁻¹
statcoulomb(Metric) ⇒ 3.3356409519815207e-10   # C
statfarad(Metric) ⇒ 1.1126500560536185e-12   # F
stathenry(Metric) ⇒ 8.987551787368176e11   # H
statmho(Metric) ⇒ 1.1126500560536185e-12   # S
statohm(Metric) ⇒ 8.987551787368176e11   # Ω
stattesla(Metric) ⇒ 2.997924579999999e6   # T
statutemile(Metric) ⇒ 1609.3472186944375   # m
statvolt(Metric) ⇒ 299.792458   # V
statweber(Metric) ⇒ 299.792458   # Wb
steradian(Engineering) ⇒ 1   # rad²
stilb(Engineering) ⇒ 9999.999999999996   # nt
stokes(Metric) ⇒ 0.00010000000000000002   # m²⋅s⁻¹
surveyacre(Metric) ⇒ 4046.8726098742522   # m²
surveyfoot(Metric) ⇒ 0.3048006096012192   # m
susceptibility(EMU,Metric) ⇒ 12.566370614359172
synodicmonth(Metric) ⇒ 2.5476922935413797e6   # s
tablespoon(Metric) ⇒ 1.5000000000000002e-5   # m³
talbot(Metric) ⇒ 1   # lm⋅s
teaspoon(Metric) ⇒ 5.0e-6   # m³
technicalatmosphere(Metric) ⇒ 98066.49999999999   # Pa
temperature(Metric,SI2019) ⇒ 0.9999999996562562   # K⋅K⁻¹
deka ⇒ 10   # 𝟏𝟎
tesla(Metric) ⇒ 1   # T
thermalconductance(Metric,SI2019) ⇒ 1.000000000343744   # K⋅K⁻¹
thermalconductivity(Metric,SI2019) ⇒ 1.000000000343744   # K⋅K⁻¹
thermalexpansion(Metric,SI2019) ⇒ 1.000000000343744   # K⋅K⁻¹
thermalresistance(Metric,SI2019) ⇒ 0.9999999996562561   # K⋅K⁻¹
ton(Metric) ⇒ 907.18474   # kg
tonne(Metric) ⇒ 1000   # kg
tonsrefrigeration(British) ⇒ 2593.858709996918   # lb⋅ft⋅s⁻¹
tontnt(Metric) ⇒ 4.186737323211057e9   # J
torr(English) ⇒ 2.784495557465706   # lb⋅ft⁻²
turn(Engineering) ⇒ 6.283185307179586   # rad
vacuumimpedance(Metric) ⇒ 376.73031346177066   # Ω
vacuumpermittivity(Metric) ⇒ 8.854187817620389e-12   # F⋅m⁻¹
vectorpotential(EMU,Metric) ⇒ 9.999999999999997e-7   # Wb⋅cm⋅Mx⁻¹⋅m⁻¹
viscosity(CGS,Metric) ⇒ 0.09999999999999998   # Pa⋅Ba⁻¹
volt(Metric) ⇒ 1   # V
volume(CGS,Metric) ⇒ 1.0000000000000006e-6   # m³⋅cm⁻³
volumeflow(English,Metric) ⇒ 0.028316846592000004   # m³⋅ft⁻³
volumeheatcapacity(Metric,SI2019) ⇒ 1.000000000343744   # K⋅K⁻¹
watt(Metric) ⇒ 1   # W
wavenumber(CGS,Metric) ⇒ 99.99999999999999   # cm⋅m⁻¹
weber(Metric) ⇒ 1   # Wb
wienfrequency(Metric) ⇒ 5.87892575562598e10   # Hz⋅K⁻¹
wienwavelength(Metric) ⇒ 0.002897771956181264   # m⋅K
yank(CGS,Metric) ⇒ 1.0e-5   # N⋅dyn⁻¹
yard(Metric) ⇒ 0.9144000000000001   # m
year(Metric) ⇒ 3.15576e7   # s
deci ⇒ 0.1   # 𝟏𝟎^-1
planckreduced(SI2019)*lightspeed(SI2019) ⇒ 3.1615267734966903e-26   # J⋅m⋅rad⁻¹
rationalization(Metric) ⇒ 1
magneticfluxquantum(SI2019) ⇒ 2.0678338484619295e-15   # Wb
einstein(Metric) ⇒ 2.0766480968545148e-43   # s²⋅m⁻¹⋅kg⁻¹
magneton(SI2019) ⇒ 9.274010078302855e-24   # J⋅T⁻¹
stefan(SI2019) ⇒ 5.6703744191844314e-8   # W⋅m⁻²⋅K⁻⁴
planck(SI2019) ⇒ 6.62607015e-34   # J⋅s
```

### 6.4 Hand-probed edge cases (oracle, verbatim `repr`)

```
length(Gauss, IAU☉)            ⇒ 6.684587122268445e-14      # generic chain (CGS special case is dead)
length(IAU☉, Gauss)            ⇒ 1.4959787070000002e13
length(IAU☉, Metric)           ⇒ 1.495978707e11             # snapped exactly to au by the IAU special case
time(IAU☉, Metric)             ⇒ 86400.0
length(English, IAU☉)          ⇒ 2.0374621548674225e-12
planckmass(Planck)             ⇒ 3.544907701811032          # √(4π): rationalized Planck
planckmass(PlanckGauss)        ⇒ 1.0
gravitation(Planck)            ⇒ 0.07957747154594766        # 1/(4π)
gravitation(PlanckGauss)       ⇒ 1.0
electronmass(CODATA, Universe) ⇒ 9.109383549079828e-31      # override, plain Float64 (slot: 9.10938354907983e-31)
vacuumpermeability(SI2019, Universe) ⇒ 1.2566370621210484e-6 # override (slot: 1.256637062121048e-6)
Metric(1, energy)              ⇒ 1
Metric(1.0,1.0,1.0,1.0,1.0)    ⇒ Unknown                    # rescaled system, not a named one
UnitSystems.UnitSystem(1,1,1,1,1) === Natural ⇒ false
kilograms(1) ⇒ 0.45359237;  slugs(1) ⇒ 2.2046226218487757;  feet(1) ⇒ 3.280839895013123;  meters(1) ⇒ 0.3048
feet(1, English) ⇒ 1 (Int, value returned unchanged)
moles(6.02214076e23) ⇒ 0.999999999656256;  molecules(1) ⇒ 6.022140762070074e23
length(1, Metric, English) ⇒ 0.3048;  length(1, English) ⇒ 3.280839895013123
one(Metric) ⇒ 1;  zero(Metric) ⇒ 0;  dimensionless(Metric,English) ⇒ 1
angle(Metric,MetricDegree) ⇒ 57.29577951308232;  solidangle(Metric,MetricDegree) ⇒ 3282.806350011744
length(Metric) ⇒ 3.8615926795842105e-13;  time(Metric) ⇒ 1.2880886681893147e-21;  temperature(Metric) ⇒ 5.929896577399839e9
charge(Gauss) ⇒ 1.586147240516102e-9;  energy(English) ⇒ 6.038499333153158e-14
UnitSystems.unit(1.0+1e-14) ⇒ 1.00000000000001;  UnitSystems.unit(1.0+7e-15) ⇒ 1
Constant(2)^70 ⇒ 0;  Constant(10)^-28 ⇒ 1.0000000000000015e-28;  Constant(10)^-2 ⇒ 0.010000000000000002
UnitSystems.logdb(100) ⇒ 20.0;  UnitSystems.expdb(20) ⇒ 100.00000000000011
slug ⇒ 14.593902937206362;  slug(Metric) ⇒ 14.593902937206364;  kelvin ⇒ 1.8;  kelvin(Metric) ⇒ 1;  kelvin(English) ⇒ 1.7999999999999998
inchmercury(Metric) ⇒ 0.0002952998016471232  (BUG);  torr(Metric) ⇒ 133.32236842105263;  atmosphere(Metric) ⇒ 101325.0
fahrenheit(Metric) ⇒ 255.37222222222226;  celsius(Metric) ⇒ 273.15;  boiling(Metric) ⇒ 373.1339;  sealevel(English) ⇒ 518.67
jovianyear(IAU) ⇒ 4333.845973840625;  siderealyear(IAU) ⇒ 365.2563427456724;  synodicmonth(IAU) ⇒ 29.48717932339559
hyperfine(Metric) ⇒ 9.19263177e9;  hubble(Metric) ⇒ 2.1927112672380577e-18;  cosmological(Metric) ⇒ 1.1056022912824226e-52
```

`goldens/coupling_perturbed.json` has 32 Coupling-aware functions × 48 systems evaluated with both `Universe` and a perturbed `C` (αG×1.01, α×1.001, μₑᵤ×1.0001, μₚᵤ×0.9999, ΩΛ = 0.7). It is the only way to observe the live overrides of §4.7. For example `lightspeed(Hartree, C) = 136.899099984016`, while `vacuumpermeability(Hartree, C)` stays `0.0006691762566203905` (its override is dead), so Hartree becomes internally inconsistent under a perturbed Coupling.

---

## 7. Dependencies on other chakravala packages

**Upstream.** Only `FieldConstants` (compat 0.1). Symbols used: `Constant`, `constant`, `isconstant`, `logdb`, `expdb`, `dB`, `param`, `measure`, `cache` (`UnitSystems.jl:64-70`). `LinearAlgebra` appears in `Project.toml` but is never imported. From Base it imports `@pure`, `length`, `time`, `angle`, `rem` (methods are added to these Base functions) and `MathConstants.eulergamma, golden, φ` (re-exported).

**Downstream contract** (what Similitude, MeasureSystems and Geophysics rely on; keep these seams in the Lean design):

| hook | UnitSystems behaviour | downstream override |
|---|---|---|
| type parameters of `UnitSystem`/`Coupling` | Constants | Similitude: `Quantity{D}` constants carrying dimensions (`Similitude.jl:106-157`, `Unified`); MeasureSystems: `Measurement`s |
| `measure(x)`, `cache(x)` | identity | MeasureSystems stores cached measurements |
| `normal(x)` | identity | strips Quantity wrappers |
| `isquantity(U)`, `evaldim(f)` | `false`, no methods | Similitude dispatches every conversion through dimension evaluation |
| `Quantity(D,U,v)`, `(U)(v,D)` | return `v` | build dimensioned quantities |
| `similitude()` / `ENV["SIMILITUDE"]` | build-time toggle | chooses the backend in MeasureSystems/Geophysics |
| `unitname`, `textconstants`, `textderived`, `textquantities` | name tables | display |
| `constant(U)` | rewrap as Constants | used when converting back from Measure/Quantity systems |

In Lean these seams become a **scalar-type parameter** (`UnitSystem α`) plus a small interface class (§8.1). Similitude and MeasureSystems then *instantiate* the same code, as they do in Julia.

---

## 8. Lean 4 porting notes

### 8.1 Architecture: one generic core, several scalar backends

Julia gets its genericity by stuffing *values* of arbitrary number types into type parameters. The Lean equivalent is to make the core **polymorphic in the scalar type**, with the systems as ordinary structures:

```lean
namespace Chakravala.UnitSystems

/-- What the chains need from a scalar. -/
class UnitField (α : Type) extends Mul α, Div α, Inv α, Add α, Sub α where
  zero    : α
  one     : α                  -- (extending both OfNat α 0 and OfNat α 1 would clash on `ofNat`)
  ofFloat : Float → α          -- literal constants
  ofInt   : Int → α
  sqrt    : α → α
  pow     : α → Int → α        -- Julia literal_pow / pow_body semantics for Float
  snap    : α → α → α          -- Julia `unit(x,y)`; identity in exact/exponent models
  isOne   : α → Bool

structure Coupling (α : Type) where
  αG α μeu μpu ΩΛ : α

inductive SysKind  -- replaces Julia's value-dispatch overrides (§4.7)
  | generic | planck | planckGauss | stoneyLike | hartreeLike | electronicLike
  | metricPassThrough | si2019 | codata | conventional
  deriving DecidableEq, Repr

structure UnitSystem (α : Type := Float) where
  kB ħ c μ0 me Mu Kcd θ rat αL g0 : α     -- `λ` is a Lean keyword: the rationalization slot is `rat`
  C    : Coupling α
  kind : SysKind := .generic
```

Backends:

| instance | purpose |
|---|---|
| `Float` | the fast path; parity with Julia |
| `JNum` (`int : Int64` / `flt : Float`) | Julia promotion rules; needed only for exact `display`/doc-string parity (`1` vs `1.0`) and the Int-snap semantics |
| `CExp` (11 half-integer exponents over the constants, stored ×2 as `Int`) | the **exponent model**: `*` ↦ `+`, `/` ↦ `−`, `sqrt` ↦ halve, `snap` ↦ id, numeric literals ↦ 0. Used for proofs (§8.7) |
| `Measurement`, `Quantity` | future MeasureSystems/Similitude ports |

Write every chain (the 131 conversions, 28 physics functions, 196 derived units) **once**, generic in `α`, and mark it `@[specialize]` so that the `Float` instance compiles to straight-line double arithmetic.

### 8.2 What becomes a type index vs a runtime value

| Julia (all type-level) | Lean | cost |
|---|---|---|
| dimension (implicit in function name) | `Dim` index: `structure Dim where F M L T Q Θ N J A Λ C : Int` (USQ, §4.6), with `Mul/Div/Inv/HPow Int` as exponent arithmetic | erased; zero runtime cost |
| unit system identity | index of `Quantity (U : UnitSystem) (d : Dim)`, where `U` is a term (named `def`s) | erased. Named-system arguments make the factor a closed term (§8.3) |
| the 11 constants, Coupling | runtime fields of `UnitSystem`; named systems are closed `def`s | computed once at module init |
| τ and the 7 primes (`extra[7..14]`) | **drop from the struct**; they never vary. Keep `two U` etc. only as compat functions returning literals, and let exact backends provide them via `UnitField` | none |
| Int vs Float payload | `JNum` only in the display/compat layer | none on the fast path |
| `Constant{N}` wrapper | not needed: the Lean compiler's closed-term extraction plus optional elaboration-time evaluation give the same effect | — |

```lean
structure Quantity (U : UnitSystem) (d : Dim) where
  val : Float        -- single-field structure: unboxed at runtime; U and d are erased

def Quantity.to (S : UnitSystem) (q : Quantity U d) : Quantity S d :=
  ⟨q.val * factor d U S⟩                     -- `factor` = natural-value ratio (§4.6), `@[inline]`
instance : HMul (Quantity U d₁) (Quantity U d₂) (Quantity U (d₁ * d₂)) := ⟨fun a b => ⟨a.val * b.val⟩⟩
instance : Add (Quantity U d) := ⟨fun a b => ⟨a.val + b.val⟩⟩     -- only same-dimension addition typechecks
```

**Do not index by `Float` literals expecting defeq.** Float arithmetic is opaque to the kernel. Indices compare nominally (same `def`), which matches Julia, where systems compare by type identity. Dimension equalities such as `Dim.length * Dim.time⁻¹ = Dim.speed` *do* reduce (Int arithmetic), so `rfl`/`decide` handle them. Provide `Quantity.cast (h : d = d')` for the rest.

One dimension is not integral: `jovianyear`'s fitted dimension has halves (bug §4.11-3). Expose it untyped (`Float`), or keep `Dim` over half-integers. Recommendation: `Int` dims, plus an untyped escape hatch for quirk functions.

### 8.3 How Julia is fast, and the Lean equivalents

- **Julia.** Every system is a singleton *type* whose parameters are `Constant`s. Every accessor, factor and derived unit is `@pure`, so the compiler constant-folds the entire chain. `length(v, English, Metric)` compiles to `v * 3.280839895013123`. There are no caches or tables: specialization *is* the cache (one compiled method instance per `(q,U,S)`, about 0.7 ms of compile each, as measured).
- **Lean, static systems.** Write `factor d Metric English` (or a whole verbatim chain) with named-system arguments. It is a closed term, so the compiler's closed-term extraction (`extractClosed` in LCNF) hoists it into a module-init constant and the runtime cost is one load plus one `fmul`. Verify with `set_option trace.Compiler.result true`. For guaranteed zero-cost and **bit-identical** literals, add a term elaborator `conv% length Metric English`. It evaluates the Float at elaboration time (`evalExpr`) and emits `Float.ofBits 0x…`. This is the Lean analogue of `@pure` + `Constant`, and the same C doubles are used, so results match the runtime path exactly.
- **Lean, dynamic systems** (runtime `UnitSystem` values). Use the natural-value approach (§4.6 option a):
  - `X d U = Π_i base_i(U)^{d_i}`, with `base_i(U)` computed once per system (11 monomials, the §4.6 table);
  - `factor d U S = snap (X d S / X d U)`, with a short-circuit to `1` when `U == S` (structure `BEq` on the fields, mirroring Julia's type identity).
  - For the 131 named quantities, precompute a `48 × 131` `FloatArray` of `q(Natural,U)` lazily (`Thunk`). Do **not** precompute all 301k pairs (2.4 MB).
- **Specialization.** Mark generic chains `@[specialize]` and tiny accessors `@[inline]`. Avoid `partial`. Use `Float` (not `Float32`) everywhere.

### 8.4 Numeric parity strategy

1. Implement the **verbatim chains** from §2.8/§2.9 in the exact Julia operation order, with `snap` exactly where Julia calls `unit`. This gives parity at rtol ≤ 1e-14 (mostly bit-exact).
2. Implement the **generic Dim path** separately, and property-test it against the verbatim chains (rtol 1e-13) for all 131 × 48².
3. `pow`:
   - Literal negative exponents on computed constants mean `inv` then power.
   - Positive integer powers follow Julia's `pow_body`: `x*x` for n = 2, `x*x*x` for n = 3, compensated squaring otherwise. Emulate `two_mul` with Veltkamp splitting if no FMA is exposed; alternatively accept ≤ 2-ulp differences and rely on tolerance.
   - The integer powers that actually occur are ≤ 12 (`𝟓^12` in Nautical's μ₀; `pop` has `time^5`).
4. Julia's `exp`, `log`, `log10`, `exp10` (used only in `sackurtetrode`, `logdb`, `expdb`, `Constant(exp(5/2))`) may differ from libm by 1 ulp. Test them at rtol 1e-15. (Port status: `JuliaBase.Math` reproduces them bit for bit, and the tests are exact.)
5. Keep Julia's IEEE behaviour for FFF (μ₀ = 0 gives Inf/NaN). Do not "fix" it in compat mode.

### 8.5 Tricky-semantics checklist

- [ ] `q(U,S)` = S-units per U-unit; `q(v,U,S)` converts **from S to U** (§4.4); `q(v,U)` is from Metric; `q(U)` is from Natural.
- [ ] Identity shortcuts: same system gives `v` unchanged; a factor that is exactly 1 gives `v` unchanged.
- [ ] `v / u` for plain `v` is `v * (1/u)` (two roundings); for a constant `v` it is a single division.
- [ ] `snap` rtol = `8.161992717227193e-15`, compared against `y` (default 1). Snapping returns exactly `y`.
- [ ] `EntropySystem` resets `λ` and `αL` to 1 unless passed. Default-argument formulas depend on earlier arguments.
- [ ] `GaussSystem` molar mass is `1` iff `m == 1/1000`. `RankineSystem` molar mass is `snap(1000·Mu)`.
- [ ] Mass-type distinctions: `MPH` is built on FPS; English's mass unit is lbm (`g₀ = g₀/ft`); British's is the slug; Survey uses `ftUS` but `lb`.
- [ ] Coupling overrides by `SysKind` (§4.7), including the recomputed values for CODATA, Conventional and SI2019.
- [ ] IAU☉ special snapping for `length` against `c = 𝘤` and `c = 𝘤/ft` systems (§4.8). The CGS variants are dead.
- [ ] `time(U,S,t)` ignores `t`.
- [ ] `hubble(U) = time(1, Hubble, U)`. `eddington(U) = mass(1, U, Cosmological)`. `hyperfine(U) = frequency(ΔνCs, U, Metric)`.
- [ ] Callable Constants: give the value and the function different Lean names (`Const.slug : Float` vs `slug (U) : Float`; `Const.kelvin = 1.8` vs `kelvin U`).
- [ ] `display` prints `4π` when `λ == Float(4π)`, and Int payloads without `.0`.
- [ ] `Coupling` 4-argument constructor defaults `ΩΛ = 0.6889`.
- [ ] The undefined exports (`neper`, `bel`, `decibel`): either omit them, or define them properly (`neper = 1`, `bel = log10`-based) behind `juliaCompat := false`, documented as a deliberate deviation.

### 8.6 Julia-specific pieces to skip or redesign

- `@pure`, `Constant`-as-type-parameter, `cache`/`measure`/`normal`/`Quantity` identity hooks, `isquantity`/`evaldim`. These are replaced by the scalar-type parameter and the `Quantity` structure.
- `similitude()` and `ENV["SIMILITUDE"]`: backend choice becomes a Lake option or simply a different import.
- `eval`-based `derived(U)`/`constants(U)`: replace with a static `Array (String × (UnitSystem → Float))` registry. Julia's `derived` is broken anyway.
- Doc-generation helpers (`convertext`, `unitext`, `systext`, `cgstext`, `textunits`, every `*docs.jl`): replace with Verso docs whose examples are `#eval`-checked against `doc_goldens.json`.
- The metaprogrammed `for unit ∈ Convert` loops: replace with a small `macro`/`elab` (`declare_conversion length := …`) that emits the four call forms, or with plain explicit definitions (131 one-liners).
- Wolfram `Kernel/` and Rust `src/lib.rs`: ignore.

### 8.7 Proofs that pay for themselves

1. **Exponent-model dimension checking.** Instantiate the generic chains at `α := CExp`, then prove, one line per quantity:
   `theorem length_dim : (Convert.length (U := sym) (S := sym')).exp = (Dim.L).toCExp := by decide`.
   Generate the 131 + 241 statements from `convert_exponents.tsv`/`scalar_exponents.tsv` by a macro. Every regression in a chain then becomes a compile error. The quirks (§4.11) are recorded as theorems with the *actual* dims, e.g. `photonirradiance_dim : … = L⁻² * T`, so they are documented and cannot drift silently.
2. **`Dc` is invertible** (`det = −2`), and `Einv * Dc = 1` over half-integers by `decide`. This gives the canonical `Dim ↔ CExp` bijection used by the generic path. Corollary: `factor d U S * factor d S U = 1` in the exponent model (`simp`/`ring`-free `decide`).
3. **Homomorphism:** `factor (d₁ * d₂) U S = factor d₁ U S * factor d₂ U S` and `factor d U U = 1`, proved in the exponent model. For Float they become property tests.
4. **Test-suite identities (§6.2a)** in the exponent model: both sides have identical exponent vectors, by `decide`. The Julia `==` ones (`planck = turn*planckreduced`, `magnetostatic = lorentz*biotsavart`, …) hold by `rfl` if implemented literally, even for `Float`.
5. **Natural-system sanity:** `(lightspeed Natural == 1.0) = true := by native_decide`. Also the display formatter's round-trip on the 48 display strings.
6. **Dim algebra:** `Dim` is a `CommGroup` (as multiplicative notation over `ℤ¹¹`). If Mathlib is available, `grind`/`simp` close most equalities automatically; otherwise use `decide`.

### 8.8 Suggested module decomposition (namespace `Chakravala`)

| module | contents | LOC |
|---|---|---|
| `Chakravala/FieldConstants.lean` | `JNum` (Int64 ⊕ Float) with Julia promotion (`/` always Float, Int wraparound), `pow` (literal_pow and pow_body), `logdb`/`expdb`/`dB`, `ToString` via `JuliaShow` | 220 |
| `Chakravala/UnitSystems/Dim.lean` | `Dim` (USQ ℤ¹¹), group ops, named base dims, pretty printer (`F·L·T⁻¹`), `CExp` (half-integer exponents over constants), `Dc`/`Einv` matrices | 200 |
| `Chakravala/UnitSystems/Scalar.lean` | `UnitField` class; instances `Float`, `JNum`, `CExp`; `snap` (Julia `unit`) | 180 |
| `Chakravala/UnitSystems/Constants.lean` | measured inputs and the derived chain of §4.1 (≈110 named constants, exact op order); ASCII aliases | 220 |
| `Chakravala/UnitSystems/System.lean` | `Coupling`, `Universe`, `UnitSystem α`, `SysKind`, accessors, `MetricSystem`, `ConventionalSystem`, `EntropySystem`, `AstronomicalSystem`, `ElectricSystem`, `GaussSystem`, `RankineSystem`, `rescale` | 260 |
| `Chakravala/UnitSystems/Systems.lean` | the 48 named systems, aliases, registry, `unitname`, `isrationalized` | 170 |
| `Chakravala/UnitSystems/Convert/Base.lean` | four call forms, direction semantics, identity shortcuts, IAU special cases | 120 |
| `Chakravala/UnitSystems/Convert/Kinematic.lean`, `Mechanical.lean`, `Electromagnetic.lean`, `Thermodynamic.lean`, `Molar.lean`, `Photometric.lean` | 131 verbatim chains, generic in α | 480 |
| `Chakravala/UnitSystems/Quantity.lean` | `Quantity U d`, `to`, arithmetic, generic `factor` via natural-value table, `conv%` elaborator | 260 |
| `Chakravala/UnitSystems/Physics.lean` | 28 physics constants, 6 dimensionless, Coupling overrides, `sackurtetrode`, `loschmidt`, etc. | 220 |
| `Chakravala/UnitSystems/Derived.lean` | 193 derived units, prefix functions, `kilograms`/`slugs`/`feet`/`meters`/`moles`/`molecules` | 380 |
| `Chakravala/UnitSystems/Show.lean` | `show`/`display`/Coupling display (uses `Chakravala/Util/JuliaShow.lean`) | 90 |
| `Chakravala/UnitSystems/Names.lean` | `text.jl` tables (data) | 420 |
| `Chakravala/UnitSystems/Proofs/Dims.lean` | §8.7 items 1–3 (macro-generated statements) | 350 |
| `Chakravala/UnitSystems/Proofs/Identities.lean` | §8.7 item 4 (~120 identities) | 250 |
| `Tests/Oracle/UnitSystems.lean` | JSON golden loaders and comparators (parse floats from the JSON text; the goldens use Julia shortest repr), per-file tolerances | 380 |

Total ≈ **4,000 LOC**: ~2,600 code, ~600 proofs, ~420 data, ~380 tests. FieldConstants alone is ≈ 220.

---

## 9. Oracle test plan

The goldens already exist (§0). The Lean test runner should do the following.

| golden | Lean check | tolerance |
|---|---|---|
| `systems.json` | 48 × 19 slots of each named system | bit-exact for slots computed with identical op order; otherwise rtol 1e-15. Int/Float kind must match in the `JNum` layer |
| `systems.json:display`, `:show`, `aliases.json` | exact string equality | exact |
| `module_constants.json` | every named constant | rtol 1e-15 (most bit-exact) |
| `scalars.json` | 48 systems × (6 + 12 + 28 + 193 + 3 extras + 30 prefixes/aliases) 1-arg functions | rtol 1e-14; undefined names skipped |
| `convert_pairs.json` | all 131 × 48 × 48. Verbatim path rtol 1e-14; generic path rtol 1e-13 | NaN/Inf positions exact; `types == 'I'` entries must be exactly integral in `JNum` mode |
| `convert_one_arg.json` | `q(U)` | rtol 1e-14 |
| `convert_values.json` | `q(v,U,S)`, `q(v,U)` for v ∈ {1.0, 2.5, −3.0, 1e10}: checks direction and the identity shortcuts | rtol 1e-15 |
| `constructors.json` | 108 random-argument constructor calls on bases Metric, SI2019, English, Gauss, FPS (t, l, m, θ, … log-normal, 6 significant digits, seed `0x5eed`) | rtol 1e-14 |
| `coupling_perturbed.json` | 32 physics functions × 48 with `Universe` and a perturbed Coupling: validates `SysKind` overrides | rtol 1e-14 |
| `fieldconstants_ops.json` | 878 rows: value, payload type (Int64/Float64/Bool), Constant-ness; `err` rows must raise | exact type; value rtol 0 (bit-exact) except transcendental functions (1 ulp) |
| `doc_goldens.json` | 1638 `verified` rows: evaluate `expr` via a Lean lookup table of the call, render with `JuliaShow`, compare to `doc_output` as a string. The 20 non-verified rows are skipped | exact string (this also tests the printer) |
| `convert_exponents.tsv`, `scalar_exponents.tsv` | compile-time theorems (§8.7) plus a runtime check that the generic path uses the same `Dim` | exact |
| test-suite identities (§6.2a) | property tests over all 48 systems, with the same `FFF`/`Cosmological` skips | Julia `≈` default: rtol √eps ≈ 1.49e-8 |
| CGS table (§6.2b) | exact list | rtol 1e-12 |

**Input distributions for new goldens** (if the implementer needs more):
- Random synthetic systems with each of the 11 constants log-normal (σ = 2 in log space), as in `dims.jl`. These avoid accidental matches with the value-dispatch overrides and exercise the generic path. They are also self-checking in Lean: verbatim chain vs generic factor, with no Julia needed.
- Constructor arguments log-normal with 6 significant digits, as in `constructors.json`.
- Value conversions: {±1, 2.5, 1e±10, subnormal 5e-324, 0.0, NaN, Inf} to pin down `v * (1/u)` edge behaviour.
- Couplings: ±0.1% perturbations of each slot separately (`coupling.jl` perturbs all at once).

**Commands** are in §0. `analyze.py` reproduces the reproducibility-budget numbers of §4.10 and should be rerun whenever the goldens are regenerated.

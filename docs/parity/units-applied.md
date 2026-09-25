# Parity matrix: units-applied (FieldConstants, FieldAlgebra, UnitSystems, Similitude, MeasureSystems, Geophysics)

Audit of the Lean port at `/Users/alokbeniwal/Grassmann` (master `0ac54fdd`, 2026-09-25) against the
Julia packages in `/Users/alokbeniwal/chakravala/<Pkg>.jl`.

**How the rows were produced.** Every exported symbol comes from `names(Pkg)` evaluated in the oracle
Julia environment (`parity/names_*.jl`; Geophysics is `include`d from the v0.3.8 checkout the same way
`oracle/geophysics/gen.jl` does). Lean equivalents were found by reading every `.lean` file of the six
libraries and the registries (`UnitSystems/Registry.lean`, `Similitude/Derived.lean` `Units.table`),
plus the test suites under `Tests/` and goldens under `oracle/golden/`. A generator
(`parity/gen_matrix.py`) applies the per-category mapping; every unmatched symbol was classified by hand.

**Status legend.** DONE = implemented and checked against the Julia oracle (a repo golden unless the row
says otherwise). PARTIAL = implemented but missing methods/aliases/options, or untested, or slower than
Julia. MISSING = no Lean equivalent. SKIP = Julia-specific or undefined in Julia (justified per row).
IN_PROGRESS = in-flight work (for this package set only the Bench/Harness applies; the perf rows below are
reported as PARTIAL because the fixes themselves are not in flight).

**Ad-hoc verification done for this audit** (scratch only, master untouched; the scratch scripts link the
prebuilt `.lake/build/ir/*.c.o.export` objects):

* `probe1.lean`, `probe2.lean`: README/doc examples and MeasureSystems displays evaluated in Lean.
* `msdump.lean` vs `msdump.jl`: all 193 Similitude derived units + 6 English physics constants printed
  by Lean `MeasureSystems.measured` and by Julia MeasureSystems, in their own system and in Metric:
  194/199 identical, the 5 differences all come from `μE☾` being exact in Lean.
* `bench.lean`/`bench_us.jl`/`bench_sim.jl` and `geobench.lean` vs `oracle/geophysics/bench.jl`:
  compiled (`leanc -O3`) timings on this machine.

**Current test status** (prebuilt `.lake/build/bin/tests FieldAlgebra UnitSystems Similitude MeasureSystems Geophysics`,
run read-only): FieldAlgebra+FieldConstants 24 526 / 0 failed, UnitSystems 125 050 / 0, Similitude 58 572 / 0,
MeasureSystems 8 535 / 0, Geophysics 679 602 / 0 (Julia-defect entries skipped per `oracle/defects.toml`).

## Counts

| package | rows | DONE | PARTIAL | MISSING | IN_PROGRESS | SKIP |
|---|---|---|---|---|---|---|
| FieldConstants.jl | 8 | 5 | 1 | 0 | 0 | 2 |
| FieldAlgebra.jl | 21 | 4 | 5 | 6 | 0 | 6 |
| UnitSystems.jl | 666 | 587 | 60 | 9 | 0 | 10 |
| Similitude.jl | 488 | 448 | 23 | 11 | 0 | 6 |
| MeasureSystems.jl | 695 | 571 | 84 | 16 | 0 | 24 |
| Geophysics.jl | 187 | 156 | 28 | 0 | 0 | 3 |
| **total** | 2065 | 1771 | 201 | 42 | 0 | 51 |

Counts are per matrix row: exported symbols plus the method-level rows appended to each package
(callable forms, internal-but-documented helpers, and PERF rows).

## Performance parity (compiled Lean `-O3` vs Julia 1.13, same machine, same grids)

| operation | Lean ns/call | Julia ns/call | ratio | note |
|---|---|---|---|---|
| UnitSystems `energy(v, English, Metric)` → `Conv.convert .energy v (English Num) (Metric Num)` | 7 286 | 0.58 | 12 500× slower | Julia folds `q(U,S)` into a constant; Lean recomputes the chain (with `unit` snaps and the 11-slot `ident` test) on every call |
| UnitSystems `energy(U, Metric)`, `U` chosen at runtime from 4 systems | 6 057 | 74 | 82× slower | Julia pays dynamic dispatch; Lean recomputes the chain |
| Similitude `English(x, energy)(Metric)` → `(Sys.English.qty Dim.energy x).to .Metric` (Float values) | 1.24 | 3 041 | 2 450× faster | Lean hoists `Quantity.factor` as a closed term |
| Similitude `ratio(energy, English, Metric)` evaluated at runtime | 269 784 | 2 617 | 103× slower | exact `Vector Rat 44` group arithmetic per call |
| Geophysics `temperature(h, Earth1959)` | 8.2 | 3.6 | 2.3× slower | |
| Geophysics `pressure(h)` | 24.3 | 14.7 | 1.7× slower | |
| Geophysics `density(h)` | 24.3 | 15.2 | 1.6× slower | |
| Geophysics `sonicspeed(h)` | 79.7 | 198.8 | 2.5× faster | |
| Geophysics `viscosity(h)` | 16.2 | 54.7 | 3.4× faster | |
| Geophysics `kinematic(h)` | 31.6 | 76.1 | 2.4× faster | |
| Geophysics `gravity(ϕ, Earth)` | 19.2 | 2.8 | 6.8× slower | Somigliana constants recomputed per call |

No in-repo benchmark covers UnitSystems/Similitude/MeasureSystems yet (Bench/Harness is IN_PROGRESS);
`Tests/Geophysics/Bench.lean` exists but its Lean numbers are not recorded in `docs/PERF.md`.

## Documented behaviour (README / docs examples)

| package | example | expressible in Lean? | result |
|---|---|---|---|
| FieldAlgebra README | `@ring xyz x y z; x*y^2 ⇒ xy²; ans/x ⇒ y²` | yes, as `Group` on a hand-built `Basis` | matches |
| FieldAlgebra README | `x+y^2 ⇒ x + y²` | **no** (`Ring` missing) | MISSING |
| Geophysics README | `gravity(1000)`, `temperature`, `pressure`, `sonicspeed` | `Standard.gravity 1000.0` … | equal to Julia v0.3.8 bit for bit; README's printed numbers are stale in Julia too (9.803565306802405 in README vs 9.803570410328458 from the package) |
| UnitSystems/Similitude/MeasureSystems READMEs | lists of constants, units and conversions (`neper`, `bel`, `decibel` included) | all except `neper`/`bel`/`decibel` (undefined in UnitSystems, LogGroup-valued in Similitude) | see rows |
| UnitSystems port notes §6.4 edge cases | `kilograms(1)`, `slugs(1)`, `feet(1)`, `meters(1)`, `moles`, `molecules`, `feet(1,English)`, `length(1,Metric,English)` | yes | probe values equal the oracle; no repo golden |
| UnitSystems port notes §6.4 | `Metric(1.0,1.0,1.0,1.0,1.0) ⇒ Unknown` | **no** (callable rescale constructor missing) | MISSING |
| MeasureSystems docs `similitude.md` | `Metric(1,energy)(English)`, `Gauss(charge)`, `Metric(electricflux)` | `(Sys.Metric.qty Dim.energy 1).to .English`, `naturalUnit .Gauss Dim.charge` | matches (probe + extras.json) |
| MeasureSystems derived units | `lunarmass`, `siderealyear`, `siderealmonth`, `synodicmonth`, `jovianyear` | yes, but uncertainty of `μE☾` dropped | PARTIAL |
| MeasureSystems | `δμ₀ ⇒ 6.9e-16 ± 1.9e-16` | no | MISSING |
| UnitSystems docstrings | 1658 `julia>` examples | values yes (scalars/conversions goldens) | corpus not replayed as a test |

## Consolidated gap list (the per-symbol rows below roll up into these)

| # | prio | pkg | symbols | status | fix | files | effort |
|---|---|---|---|---|---|---|---|
| 1 | P0 | UnitSystems | `q(v,U,S)` / `q(U,S)` hot path (`Conv.convert`, `Conv.factor`) | PARTIAL (perf) | Make `Conv.convert` `@[inline]` and route the factor through a `@[noinline]` `Conv.factorOf q U S` so literal `(q,U,S)` become hoisted closed terms (the trick `Similitude.Quantity.factor` already uses, 1.24 ns); add a lazily filled `Sys`-indexed table `(Conv × Sys × Sys) → Thunk Num` with a `Conv.convertSys q (v : Float) U S : Float` fast path; hoist the 11-slot `ident` test into the same table. Add a bench row. | UnitSystems/Convert.lean, UnitSystems/Systems.lean, Bench/ | S |
| 2 | P0 | FieldAlgebra | `@ring`, `Ring` | MISSING | New `FieldAlgebra/Ring.lean`: sorted monomial list over `Group B` with Julia's merge rules (`add`/`add2`, `ring.jl:89-228`), `Group + Group → Ring`, `Ring ± Ring`, `Ring * Group`, distributive `Ring * Ring`, `/ Group`, evaluation, `show` (`x + y²`, `x² + y²⋅-1`); a `ring` command (shares #3). Goldens: add the README cases and random rings to `oracle/similitude/fieldalgebra.jl`. | FieldAlgebra/Ring.lean (new), FieldAlgebra.lean, oracle/similitude/fieldalgebra.jl, Tests/FieldAlgebra/Groups.lean | M |
| 3 | P1 | FieldAlgebra | `@group`, `@group2`, `@constgroup` | PARTIAL | `group`/`group2` command elaborator: `group XYZ x y z` emits `def XYZ : Basis` and `def x : Group XYZ := Group.gen ⟨0, _⟩ …`; the `begin a = v … end` form also emits a numeric `GroupValues XYZ` instance (generalising `Similitude.GenValue`/`Consts.product`) that drives `product`, `float`, the ` = value` display and `factorize`. | FieldAlgebra/Command.lean (new), FieldAlgebra/Group.lean | M |
| 4 | P1 | Similitude, MeasureSystems | `Quantity` | PARTIAL | (a) negative-`Int` and `Rat` powers (`Quantity.zpow`, `Quantity.qpow` with `Dim.HasRoot` side condition); (b) `HMul (Quantity U d α) (ConvertUnit U S d)`; (c) `Quantity U A / Quantity V B ↦ ConvertUnit`; (d) dimensionless `q ± x` via `Quantity U USQ.one α`; (e) user-built systems: a `Sys.custom` index (or a `SysLike` class) carrying `UnitSystem Scalar` with Metric's homomorphism as Julia's default. | Similitude/Quantity.lean, Similitude/Ratio.lean, UnitSystems/Systems.lean | M (e: L) |
| 5 | P1 | Similitude, MeasureSystems | `neper`, `bel`, `decibel`, `logdb`/`expdb`/`dB` on quantities | MISSING / PARTIAL | Add a log-dimension quantity (`LogQuantity U (b : LogBase) d α`, or a log flag in `Dim`) with `Quantity.log/log10/logdb`; define `neper U = U.qty (log 𝟙) 1` etc.; registry display `log(𝟙)`/`dB(𝟙)`; stop skipping them in Tests/Similitude/Derived.lean. | Similitude/Quantity.lean, Similitude/Derived.lean, Similitude/Registry.lean, Tests/Similitude/Derived.lean | M |
| 6 | P1 | Similitude, MeasureSystems | `dimensions`, `Dimension` | MISSING | `def Quantity.dimensions (_ : Quantity U d α) : USQGroup := d.toGroup`, `ConvertUnit.dimensions`, `abbrev Dimension := …`. | Similitude/Quantity.lean, Similitude/Ratio.lean | S |
| 7 | P1 | Similitude | runtime `ratio(D,U,S)` (270 µs vs Julia 2.6 µs) | PARTIAL (perf) | Memoise per `(Conv, U, S)` in a lazy `Thunk` table like `pairTable`, and for arbitrary `Dim` key a `Std.HashMap` cache; represent exact exponents as twelfths (`Vector Int`) instead of `Vector Rat 44` in `Group.mul/zpow` (no gcd per op). | Similitude/Ratio.lean, FieldAlgebra/Group.lean | M |
| 8 | P1 | MeasureSystems | `lunarmass`, `siderealmonth`, `synodicmonth`, `siderealyear`, `jovianyear`, `RH` | PARTIAL | Make `μE☾ = measurement("81.300568(3)")` measured and let a group carry a measured coefficient (`MValue.grpM (g : Consts) (c : Measurement)` or a `Coef.meas` case); evaluate the affected Similitude formulas over that scalar. Add a measured derived-unit golden (the other 194 already match Julia exactly). | MeasureSystems/Measures.lean, MeasureSystems/Measurement.lean, oracle/measuresystems/gen.jl, Tests/MeasureSystems/Goldens.lean | M |
| 9 | P1 | Geophysics | `gravity(ϕ, P)` (19.2 vs 2.8 ns); `temperature`/`pressure`/`density` (1.6-2.3× slower) | PARTIAL (perf) | Cache the Somigliana constants (γₑ, γₚ, k, e²) per planet at construction (`Planet.of` fills them, like `Column.build`); split `Column.eval` into per-`Op` specialised closures so the hot ops avoid the `match` and re-derived layer data; record Lean numbers in docs/PERF.md. | Geophysics/Planet.lean, Geophysics/Atmosphere.lean, docs/PERF.md | S |
| 10 | P1 | UnitSystems | `q(U,S)` with a runtime-chosen `UnitSystem Num` (6.1 µs vs 74 ns) | PARTIAL (perf) | Beyond #1: an unboxed `Float` evaluation path (`UnitAlg Float` or a `NumF` scalar) for arbitrary systems, keeping `Num` only for bit-exact goldens. | UnitSystems/Alg.lean, UnitSystems/Convert.lean | M |
| 11 | P1/P2 | UnitSystems, Similitude, MeasureSystems | system aliases `SI`, `CGS`, `CGSm`, `CGSe` (P1); `MKS`, `ME`, `GM`, `HLU`, `EE`, `EnglishEngineering`, `BG`, `BritishGravitational`, `EnglishUS`, `AE`, `AbsoluteEnglish` (P2) | PARTIAL | `abbrev SI (α) [UnitAlg α] := SI2019 α` etc. in Systems.lean plus `@[match_pattern] abbrev Sys.SI : Sys := .SI2019` so both value and `Sys` spellings work. | UnitSystems/Systems.lean | S |
| 12 | P2 | UnitSystems, MeasureSystems | ASCII aliases (`Mu Ru SB hh cc m0 e0 ke me mp mu mᵤ ee FF Z0 G0 Eh a0 re g0 lP aL ϵ₀ mpe meu mpu ainv aG`), `BTUftlb`, `atomicmass`, `intensity`, `temp`, `universal`, `US`, `units`, `GG` | PARTIAL | Alias keys in `moduleConstants` and `abbrev`s (`abbrev atomicmass := dalton`, `abbrev universal := molargas`, `abbrev Convert.intensity := Convert.irradiance`, `abbrev US := UnitSystem`, …). | UnitSystems/Registry.lean, UnitSystems/System.lean, UnitSystems/Convert.lean, UnitSystems/Derived.lean | S |
| 13 | P2 | UnitSystems, MeasureSystems | `calᵢₜ`, `calₜₕ`, `kcalᵢₜ`, `kcalₜₕ`, `eulergamma`, `golden`, `φ`, `δμ₀` | MISSING | Plain constants (`.p (.int 4184)`, `.p (.float 4186.8)`, `/1e3`); Float irrationals; `δμ₀ = productM μ₀ - 4π·1e-7` as a Measurement; golden rows. | UnitSystems/Registry.lean, MeasureSystems/Measures.lean, oracle/unitsystems/systems.jl | S |
| 14 | P2 | UnitSystems | callable rescale `(U)(JK,Js,ms,Hm,kg)`; `show`/`unitname` of an arbitrary system | MISSING / PARTIAL | `UnitSystem.rescale` per `UnitSystems.jl:205-221`; `Sys.ofSystem? : UnitSystem Num → Option Sys` by `ident` and a `show` that prints the name or `Unknown`. | UnitSystems/System.lean, UnitSystems/Show.lean | S |
| 15 | P2 | UnitSystems | `kilograms slugs feet meters moles molecules`; docstring corpus; `text.jl` tables | PARTIAL / MISSING | Oracle rows for the helpers (port notes §6.4) in `oracle/unitsystems/extras.jl`; replay `doc_goldens.json` in a test; generate `UnitSystems/Text.lean` name tables. | oracle/unitsystems/extras.jl, Tests/UnitSystems/Extras.lean, UnitSystems/Text.lean (new) | S-M |
| 16 | P2 | FieldConstants | `Constant` extras | PARTIAL | Rational payload (or a documented non-goal), `exp2`, `log(b,x)`, closed `x^Constant`, `Constant^Rational`, `Int(::Constant)`, default `isapprox`; extend `constant_ops` in floats.json. | FieldConstants/JNum.lean, FieldConstants/Num.lean, oracle/unitsystems/floats.jl | S |
| 17 | P2 | FieldAlgebra | `LogGroup`/`ExpGroup` inverses, `isonezero`, `Field`, `Composite`, `Polynomial` | PARTIAL / MISSING | `LogGroup.exp` for any base as `ExpGroup`, `ExpGroup.log/log2/log10/logb`, `b ^ LogGroup`; `isonezero`; port field.jl/polynomial.jl last (experimental, undocumented). | FieldAlgebra/LogExp.lean, FieldAlgebra/Field.lean (new) | S (L for Field) |
| 18 | P2 | Similitude, MeasureSystems | `Quantities`, `Unified` as a system, `ConvertUnit` composition/log, `d(v,U,S)` for any `Dim`, `morphism`, `display(::UnitSystem)`, LaTeX/markdown helpers, `@unitdim`/`@unitgroup` | MISSING / PARTIAL | `QScalar` instance for `Values n Float`; `Sys.Unified` (hom = `usqMap`); `ConvertUnit.mul/div`; `Dim.convert v U S`; `Sys.morphism`; `UnitSystem Scalar` printer; `Similitude/Latex.lean`; runtime registry extension (`IO.Ref`) for `@unitdim`. | Similitude/Quantity.lean, Similitude/Ratio.lean, Similitude/Registry.lean, Similitude/Latex.lean (new) | M |
| 19 | P2 | MeasureSystems | named measured constants (`eV κ σ μB ε₀ kₑ mₚ Da 𝔉 Φ₀ Z₀ G₀ Eₕ a₀ rₑ Ry BTUJ BTUftlb kcal cal`), `sackurtetrode`, derived-unit golden | PARTIAL | `MeasureSystems/Constants.lean` with typed defs (`def eV := measured Units.electronvolt`, …); `sackurtetrode` over `MValue` (needs `Measurement.log`); golden from this audit's probe. | MeasureSystems/Constants.lean (new), MeasureSystems/Measurement.lean, Tests/MeasureSystems/Goldens.lean | S |
| 20 | P2 | Geophysics | 20 named `*ratio` functions, `N₂ O₂ CO₂ CH₄ H₂`, user-built unit systems | PARTIAL | Generate `Weather.temperatureratio h U := W.ratio .temperature h U` …; `abbrev N₂ := N2` …; thread `Units` built from any `UnitSystem Num` instead of `Sys`. | Geophysics/Atmosphere.lean, Geophysics/Data.lean, Geophysics/Units.lean | S (M for custom systems) |

## FieldConstants.jl (v0.1.1): 3 exports + load-bearing internals

| Julia symbol | Lean name(s) + file | status | gap / evidence | effort | prio |
|---|---|---|---|---|---|
| `Constant` | `FieldConstants.Constant := JNum`, `FieldConstants.Num` (FieldConstants/JNum.lean, Num.lean) | PARTIAL | Int64/Float64 payloads with Julia promotion, wrapping, literal_pow, snap: tested (floats.json constant_ops). Missing: Rational payload (`Constant(1//2)`), `exp2`, `log(b,x)`, closed `Number^Constant`, `Constant^Rational`, `Int(::Constant)` returning a Constant, default-tolerance `isapprox` | S | P2 |
| `constant` | identity on `JNum` / `Num.v` | DONE | payload extraction | — | — |
| `FieldConstants` | `FieldConstants` (lib) | SKIP | module name | — | — |
| `isconstant (unexported)` | `Num.const` | DONE | Constant-vs-plain tracking drives bit-exact mixed arithmetic | — | — |
| `logdb / expdb / dB (unexported, used by UnitSystems)` | `FieldConstants.logdb`, `expdb`, `dB` (JNum.lean) | DONE | floats.json constant_ops | — | — |
| `param (unexported)` | identity on `JNum` | DONE | same as `constant` | — | — |
| `measure / cache (unexported hooks)` | — | SKIP | identity hooks for MeasureSystems' `Measure{N}` interning | — | — |
| `show(::Constant)` | `JNum.toString` (Julia float repr via JuliaBase) | DONE | floats.json show/parse | — | — |

## FieldAlgebra.jl (v0.1.10): 19 exports

| Julia symbol | Lean name(s) + file | status | gap / evidence | effort | prio |
|---|---|---|---|---|---|
| `@group` | `FieldAlgebra.Basis` + `Group.gen` built by hand | PARTIAL | no Lean command that declares a named basis and binds its generator names (and, with values, derives `product`/`factorize`); `GroupProduct` only yields a display string for user bases | M | P1 |
| `@group2` | same as `@group` | PARTIAL | as `@group` (plain `Group` bindings) | M | P1 |
| `@constgroup` | same as `@group` | PARTIAL | as `@group` | M | P2 |
| `@ring` | — | MISSING | `@ring` and `Ring` (sums of monomials) absent; README example `x+y^2 ⇒ x + y²` and `(x+y)*(x-y) ⇒ x² + y²⋅-1` cannot be expressed | M | P0 |
| `Ring` | — | MISSING | sparse Laurent-polynomial `Ring{G,T,S,N,M}` (ring.jl): `+`, `-`, `*`, `/` by group, evaluation, show | M | P0 |
| `Field` | — | MISSING | experimental rational functions over rings (field.jl); undocumented | L | P2 |
| `Composite` | — | MISSING | experimental monomial over arbitrary factors (field.jl); undocumented | M | P2 |
| `AbstractModule` | — | SKIP | Julia abstract supertype; Lean uses concrete `Group B` | — | — |
| `AbelianGroup` | — | SKIP | Julia abstract supertype; Lean uses concrete `Group B` | — | — |
| `Group` | `FieldAlgebra.Group B` (FieldAlgebra/Group.lean) | DONE | mul/div/inv/^Int/^Rat/^Float/sqrt display on char- and string-named bases vs fieldalgebra.json; minor gaps `abs`, `signbit`, `one(g)/zero(g)`, `Real*Group` factorize for user bases | — | — |
| `LogGroup` | `FieldAlgebra.LogGroup B` (FieldAlgebra/LogExp.lean) | PARTIAL | log/log2/log10/log(b)/logdb, `+`, `-`, `*y`, `/y`, show tested; missing `exp2/exp10/exp(b)` inverses for non-ℯ bases, `b^LogGroup`, `zero(g)=log(one)` | S | P2 |
| `ExpGroup` | `FieldAlgebra.ExpGroup B` (FieldAlgebra/LogExp.lean) | PARTIAL | exp/exp2/exp10/b^g, `*`, `/`, `^n` (Julia bug fixed), show tested; missing `log/log2/log10/log(b,·)` of ExpGroup and `ExpGroup^ExpGroup` | S | P2 |
| `value` | field `.v` of Group/LogGroup/ExpGroup | DONE | structure projection | — | — |
| `base` | field `.base` (LogBase) | DONE | structure projection | — | — |
| `islog` | — | SKIP | LogGroup vs Group is a type distinction in Lean | — | — |
| `isonezero` | — | MISSING | `isone(x) or iszero(x)` helper not defined (trivial) | S | P2 |
| `isexp` | — | SKIP | exported but never defined in Julia | — | — |
| `dimensions` | — | SKIP | exported but not defined in FieldAlgebra (Similitude defines it) | — | — |
| `FieldAlgebra` | `FieldAlgebra` (lib) | SKIP | module name | — | — |
| `printexpo/makeint/findpower/print_special/special_print/latexpo (internal, load-bearing)` | FieldAlgebra/Superscript.lean | DONE | fieldalgebra.json prims | — | — |
| `Polynomial (master only)` | — | MISSING | `Polynomial{G,N,T}` (polynomial.jl; `*` is buggy in Julia) | S | P2 |

## UnitSystems.jl (v0.3.9): 656 exports

| Julia symbol | Lean name(s) + file | status | gap / evidence | effort | prio |
|---|---|---|---|---|---|
| `A` | `USQ.A` (UnitSystems/Dim.lean) | DONE | Julia binds these to `Constant{1}` in UnitSystems (doc markers); Lean gives them their Similitude meaning as type-level dimensions | — | — |
| `AE` | `Sys.ofName? "AE"` → `Sys.FPS` (UnitSystems/Systems.lean) | PARTIAL | alias only resolvable by string; no Lean identifier `UnitSystems.AE`/`Sys.AE` (Julia docs use it as a value, e.g. `boltzmann(AE)`) | S | P2 |
| `AbsoluteEnglish` | `Sys.ofName? "AbsoluteEnglish"` → `Sys.FPS` (UnitSystems/Systems.lean) | PARTIAL | alias only resolvable by string; no Lean identifier `UnitSystems.AbsoluteEnglish`/`Sys.AbsoluteEnglish` (Julia docs use it as a value, e.g. `boltzmann(AbsoluteEnglish)`) | S | P2 |
| `AstronomicalSystem` | `UnitSystems.AstronomicalSystem` (UnitSystems/System.lean) | DONE | random-argument goldens (extras.json constructors) | — | — |
| `BG` | `Sys.ofName? "BG"` → `Sys.British` (UnitSystems/Systems.lean) | PARTIAL | alias only resolvable by string; no Lean identifier `UnitSystems.BG`/`Sys.BG` (Julia docs use it as a value, e.g. `boltzmann(BG)`) | S | P2 |
| `BTUJ` | `moduleConstants` entry `thermalunit (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `BTUftlb` | `thermalunit (British N)` (registry key `BTU` only) | PARTIAL | alias `BTUftlb = thermalunit(British)` missing | S | P2 |
| `British` | `UnitSystems.British α`, `Sys.British` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `BritishGravitational` | `Sys.ofName? "BritishGravitational"` → `Sys.British` (UnitSystems/Systems.lean) | PARTIAL | alias only resolvable by string; no Lean identifier `UnitSystems.BritishGravitational`/`Sys.BritishGravitational` (Julia docs use it as a value, e.g. `boltzmann(BritishGravitational)`) | S | P2 |
| `C` | `USQ.C` (UnitSystems/Dim.lean) | DONE | Julia binds these to `Constant{1}` in UnitSystems (doc markers); Lean gives them their Similitude meaning as type-level dimensions | — | — |
| `CGS` | `Sys.ofName? "CGS"` → `Sys.Gauss` (UnitSystems/Systems.lean) | PARTIAL | alias only resolvable by string; no Lean identifier `UnitSystems.CGS`/`Sys.CGS` (Julia docs use it as a value, e.g. `boltzmann(CGS)`) | S | P1 |
| `CGS2019` | — | SKIP | exported but undefined in Julia (UndefVarError); nothing to port | — | — |
| `CGSe` | `Sys.ofName? "CGSe"` → `Sys.ESU` (UnitSystems/Systems.lean) | PARTIAL | alias only resolvable by string; no Lean identifier `UnitSystems.CGSe`/`Sys.CGSe` (Julia docs use it as a value, e.g. `boltzmann(CGSe)`) | S | P1 |
| `CGSm` | `Sys.ofName? "CGSm"` → `Sys.EMU` (UnitSystems/Systems.lean) | PARTIAL | alias only resolvable by string; no Lean identifier `UnitSystems.CGSm`/`Sys.CGSm` (Julia docs use it as a value, e.g. `boltzmann(CGSm)`) | S | P1 |
| `CODATA` | `UnitSystems.CODATA α`, `Sys.CODATA` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `Conventional` | `UnitSystems.Conventional α`, `Sys.Conventional` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `ConventionalSystem` | `UnitSystems.ConventionalSystem` (UnitSystems/System.lean) | DONE | random-argument goldens (extras.json constructors) | — | — |
| `Cosmological` | `UnitSystems.Cosmological α`, `Sys.Cosmological` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `CosmologicalQuantum` | `UnitSystems.CosmologicalQuantum α`, `Sys.CosmologicalQuantum` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `DAY` | `moduleConstants` entry `DAY Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `Da` | `moduleConstants` entry `dalton (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `EE` | `Sys.ofName? "EE"` → `Sys.English` (UnitSystems/Systems.lean) | PARTIAL | alias only resolvable by string; no Lean identifier `UnitSystems.EE`/`Sys.EE` (Julia docs use it as a value, e.g. `boltzmann(EE)`) | S | P2 |
| `EE2019` | — | SKIP | exported but undefined in Julia (UndefVarError); nothing to port | — | — |
| `EMU` | `UnitSystems.EMU α`, `Sys.EMU` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `ESU` | `UnitSystems.ESU α`, `Sys.ESU` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `Eh` | value exists as `Eₕ` (`moduleConstants`) | PARTIAL | ASCII alias of `Eₕ` has no Lean name or registry key | S | P2 |
| `ElectricSystem` | `UnitSystems.ElectricSystem` (UnitSystems/System.lean) | DONE | random-argument goldens (extras.json constructors) | — | — |
| `Electronic` | `UnitSystems.Electronic α`, `Sys.Electronic` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `Engineering` | `UnitSystems.Engineering α`, `Sys.Engineering` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `English` | `UnitSystems.English α`, `Sys.English` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `EnglishEngineering` | `Sys.ofName? "EnglishEngineering"` → `Sys.English` (UnitSystems/Systems.lean) | PARTIAL | alias only resolvable by string; no Lean identifier `UnitSystems.EnglishEngineering`/`Sys.EnglishEngineering` (Julia docs use it as a value, e.g. `boltzmann(EnglishEngineering)`) | S | P2 |
| `EnglishUS` | `Sys.ofName? "EnglishUS"` → `Sys.Survey` (UnitSystems/Systems.lean) | PARTIAL | alias only resolvable by string; no Lean identifier `UnitSystems.EnglishUS`/`Sys.EnglishUS` (Julia docs use it as a value, e.g. `boltzmann(EnglishUS)`) | S | P2 |
| `EntropySystem` | `UnitSystems.EntropySystem` (UnitSystems/System.lean) (both Julia methods: `EntropySystem` and the 11-arg `EntropySystem'`) | DONE | random-argument goldens (extras.json constructors) | — | — |
| `Eₕ` | `moduleConstants` entry `hartree (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `F` | `USQ.F` (UnitSystems/Dim.lean) | DONE | Julia binds these to `Constant{1}` in UnitSystems (doc markers); Lean gives them their Similitude meaning as type-level dimensions | — | — |
| `FF` | value exists as `𝔉` (`moduleConstants`) | PARTIAL | ASCII alias of `𝔉` has no Lean name or registry key | S | P2 |
| `FFF` | `UnitSystems.FFF α`, `Sys.FFF` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `FPS` | `UnitSystems.FPS α`, `Sys.FPS` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `G` | `moduleConstants` entry `G Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `G0` | value exists as `G₀` (`moduleConstants`) | PARTIAL | ASCII alias of `G₀` has no Lean name or registry key | S | P2 |
| `GG` | `moduleConstants` entry `G Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `GM` | `Sys.ofName? "GM"` → `Sys.Gravitational` (UnitSystems/Systems.lean) | PARTIAL | alias only resolvable by string; no Lean identifier `UnitSystems.GM`/`Sys.GM` (Julia docs use it as a value, e.g. `boltzmann(GM)`) | S | P2 |
| `GME` | `moduleConstants` entry `ms Num .GME` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `GMJ` | `moduleConstants` entry `ms Num .GMJ` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `GM☉` | `moduleConstants` entry `GMsun Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `Gauss` | `UnitSystems.Gauss α`, `Sys.Gauss` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `GaussSystem` | `UnitSystems.GaussSystem` (UnitSystems/System.lean) | DONE | random-argument goldens (extras.json constructors) | — | — |
| `Gravitational` | `UnitSystems.Gravitational α`, `Sys.Gravitational` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `G₀` | `moduleConstants` entry `conductancequantum (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `HLU` | `Sys.ofName? "HLU"` → `Sys.LorentzHeaviside` (UnitSystems/Systems.lean) | PARTIAL | alias only resolvable by string; no Lean identifier `UnitSystems.HLU`/`Sys.HLU` (Julia docs use it as a value, e.g. `boltzmann(HLU)`) | S | P2 |
| `HOUR` | `moduleConstants` entry `HOUR Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `Hartree` | `UnitSystems.Hartree α`, `Sys.Hartree` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `Hubble` | `UnitSystems.Hubble α`, `Sys.Hubble` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `IAU` | `UnitSystems.IAU α`, `Sys.IAU` (UnitSystems/Systems.lean) | DONE | Lean's canonical name for IAU☉; `Sys.ofName? "IAU☉"` also resolves | — | — |
| `IAUE` | `UnitSystems.IAUE α`, `Sys.IAUE` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `IAUJ` | `UnitSystems.IAUJ α`, `Sys.IAUJ` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `IAU☉` | `UnitSystems.IAU α`, `Sys.IAU` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `IPS` | `UnitSystems.IPS α`, `Sys.IPS` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `International` | `UnitSystems.International α`, `Sys.International` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `InternationalMean` | `UnitSystems.InternationalMean α`, `Sys.InternationalMean` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `J` | `USQ.J` (UnitSystems/Dim.lean) | DONE | Julia binds these to `Constant{1}` in UnitSystems (doc markers); Lean gives them their Similitude meaning as type-level dimensions | — | — |
| `JD` | `moduleConstants` entry `ms Num .JD` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `KJ` | `moduleConstants` entry `josephson (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `KJ1990` | `moduleConstants` entry `ms Num .KJ1990` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `KJ2014` | `moduleConstants` entry `ms Num .KJ2014` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `KKH` | `UnitSystems.KKH α`, `Sys.KKH` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `Kcd` | `moduleConstants` entry `ms Num .Kcd` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `L` | `USQ.L` (UnitSystems/Dim.lean) | DONE | Julia binds these to `Constant{1}` in UnitSystems (doc markers); Lean gives them their Similitude meaning as type-level dimensions | — | — |
| `LD` | `moduleConstants` entry `ms Num .LD` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `LorentzHeaviside` | `UnitSystems.LorentzHeaviside α`, `Sys.LorentzHeaviside` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `M` | `USQ.M` (UnitSystems/Dim.lean) | DONE | Julia binds these to `Constant{1}` in UnitSystems (doc markers); Lean gives them their Similitude meaning as type-level dimensions | — | — |
| `ME` | `Sys.ofName? "ME"` → `Sys.Engineering` (UnitSystems/Systems.lean) | PARTIAL | alias only resolvable by string; no Lean identifier `UnitSystems.ME`/`Sys.ME` (Julia docs use it as a value, e.g. `boltzmann(ME)`) | S | P2 |
| `MKS` | `Sys.ofName? "MKS"` → `Sys.Metric` (UnitSystems/Systems.lean) | PARTIAL | alias only resolvable by string; no Lean identifier `UnitSystems.MKS`/`Sys.MKS` (Julia docs use it as a value, e.g. `boltzmann(MKS)`) | S | P2 |
| `MPH` | `UnitSystems.MPH α`, `Sys.MPH` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `MTS` | `UnitSystems.MTS α`, `Sys.MTS` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `Meridian` | `UnitSystems.Meridian α`, `Sys.Meridian` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `Metric` | `UnitSystems.Metric α`, `Sys.Metric` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `MetricArcminute` | `UnitSystems.MetricArcminute α`, `Sys.MetricArcminute` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `MetricArcsecond` | `UnitSystems.MetricArcsecond α`, `Sys.MetricArcsecond` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `MetricDegree` | `UnitSystems.MetricDegree α`, `Sys.MetricDegree` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `MetricGradian` | `UnitSystems.MetricGradian α`, `Sys.MetricGradian` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `MetricSpatian` | `UnitSystems.MetricSpatian α`, `Sys.MetricSpatian` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `MetricSystem` | `UnitSystems.MetricSystem` (UnitSystems/System.lean) | DONE | random-argument goldens (extras.json constructors) | — | — |
| `MetricTurn` | `UnitSystems.MetricTurn α`, `Sys.MetricTurn` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `Mu` | value exists as `Mᵤ` (`moduleConstants`) | PARTIAL | ASCII alias of `Mᵤ` has no Lean name or registry key | S | P2 |
| `Mᵤ` | `moduleConstants` entry `Mᵤ Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `N` | `USQ.N` (UnitSystems/Dim.lean) | DONE | Julia binds these to `Constant{1}` in UnitSystems (doc markers); Lean gives them their Similitude meaning as type-level dimensions | — | — |
| `NA` | `moduleConstants` entry `ms Num .NA` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `Natural` | `UnitSystems.Natural α`, `Sys.Natural` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `NaturalGauss` | `UnitSystems.NaturalGauss α`, `Sys.NaturalGauss` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `Nautical` | `UnitSystems.Nautical α`, `Sys.Nautical` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `Planck` | `UnitSystems.Planck α`, `Sys.Planck` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `PlanckGauss` | `UnitSystems.PlanckGauss α`, `Sys.PlanckGauss` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `Q` | `USQ.Q` (UnitSystems/Dim.lean) | DONE | Julia binds these to `Constant{1}` in UnitSystems (doc markers); Lean gives them their Similitude meaning as type-level dimensions | — | — |
| `QCD` | `UnitSystems.QCD α`, `Sys.QCD` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `QCDGauss` | `UnitSystems.QCDGauss α`, `Sys.QCDGauss` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `QCDoriginal` | `UnitSystems.QCDoriginal α`, `Sys.QCDoriginal` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `RH` | `moduleConstants` entry `(see Registry.lean)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `RK` | `moduleConstants` entry `klitzing (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `RK1990` | `moduleConstants` entry `ms Num .RK1990` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `RK2014` | `moduleConstants` entry `ms Num .RK2014` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `RankineSystem` | `UnitSystems.RankineSystem` (UnitSystems/System.lean) | DONE | random-argument goldens (extras.json constructors) | — | — |
| `Ru` | value exists as `Rᵤ` (`moduleConstants`) | PARTIAL | ASCII alias of `Rᵤ` has no Lean name or registry key | S | P2 |
| `Ry` | `moduleConstants` entry `ms Num .hh * ms Num .cc * ms Num .Rinf` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `Rydberg` | `UnitSystems.Rydberg α`, `Sys.Rydberg` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `Rᵤ` | `moduleConstants` entry `Rᵤ Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `Rᵤ2014` | `moduleConstants` entry `ms Num .Rᵤ2014` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `R∞` | `moduleConstants` entry `ms Num .Rinf` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `SB` | value exists as `σ` (`moduleConstants`) | PARTIAL | ASCII alias of `σ` has no Lean name or registry key | S | P2 |
| `SI` | `Sys.ofName? "SI"` → `Sys.SI2019` (UnitSystems/Systems.lean) | PARTIAL | alias only resolvable by string; no Lean identifier `UnitSystems.SI`/`Sys.SI` (Julia docs use it as a value, e.g. `boltzmann(SI)`) | S | P1 |
| `SI1976` | `UnitSystems.SI1976 α`, `Sys.SI1976` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `SI2019` | `UnitSystems.SI2019 α`, `Sys.SI2019` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `Schrodinger` | `UnitSystems.Schrodinger α`, `Sys.Schrodinger` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `Stoney` | `UnitSystems.Stoney α`, `Sys.Stoney` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `Survey` | `UnitSystems.Survey α`, `Sys.Survey` (UnitSystems/Systems.lean) | DONE | all 11 slots, name, display, isrationalized vs oracle/golden/unitsystems/systems.json | — | — |
| `T` | `USQ.T` (UnitSystems/Dim.lean) | DONE | Julia binds these to `Constant{1}` in UnitSystems (doc markers); Lean gives them their Similitude meaning as type-level dimensions | — | — |
| `TP` | `moduleConstants` entry `Convert.temperature (PlanckGauss Num) (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `T₀` | `moduleConstants` entry `ms Num .T₀` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `US` | `UnitSystems.UnitSystem` | PARTIAL | type alias `US`/`units` not defined | S | P2 |
| `UnitSystem` | `UnitSystems.UnitSystem α` + `unitsystem` (UnitSystems/System.lean) | DONE | generic scalar slot type; τ and the prime slots are fixed literals (they never vary in Julia's systems) | — | — |
| `UnitSystems` | `UnitSystems` (lib) | SKIP | module name | — | — |
| `Universe` | `UnitSystems.Universe α` (UnitSystems/System.lean) | DONE | display golden (systems.json coupling) | — | — |
| `Vᵢₜ` | `moduleConstants` entry `ms Num .Vᵢₜ` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `Z0` | value exists as `Z₀` (`moduleConstants`) | PARTIAL | ASCII alias of `Z₀` has no Lean name or registry key | S | P2 |
| `Z₀` | `moduleConstants` entry `vacuumimpedance (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `a0` | value exists as `a₀` (`moduleConstants`) | PARTIAL | ASCII alias of `a₀` has no Lean name or registry key | S | P2 |
| `aG` | value exists as `αG` (`moduleConstants`) | PARTIAL | ASCII alias of `αG` has no Lean name or registry key | S | P2 |
| `aL` | value exists as `αL` (`moduleConstants`) | PARTIAL | ASCII alias of `αL` has no Lean name or registry key | S | P2 |
| `abampere` | `UnitSystems.abampere` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `abcoulomb` | `UnitSystems.abcoulomb` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `abfarad` | `UnitSystems.abfarad` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `abhenry` | `UnitSystems.abhenry` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `abmho` | `UnitSystems.abmho` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `abohm` | `UnitSystems.abohm` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `abvolt` | `UnitSystems.abvolt` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `acceleration` | `Conv.acceleration` / `Convert.acceleration` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `acre` | `UnitSystems.acre` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `action` | `Conv.action` / `Convert.action` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `admiraltymile` | `UnitSystems.admiraltymile` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `admittance` | `Conv.admittance` / `Convert.admittance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `ainv` | value exists as `αinv` (`moduleConstants`) | PARTIAL | ASCII alias of `αinv` has no Lean name or registry key | S | P2 |
| `amagat` | `UnitSystems.amagat` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `ampere` | `UnitSystems.ampere` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `angle` | `Conv.angle` / `Convert.angle` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `angstrom` | `UnitSystems.angstrom` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `angulararea` | `Conv.angulararea` / `Convert.angulararea` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `angularfrequency` | `Conv.angularfrequency` / `Convert.angularfrequency` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `angularlength` | `Conv.angularlength` / `Convert.angularlength` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `angularmomentum` | `Conv.angularmomentum` / `Convert.angularmomentum` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `angulartime` | `Conv.angulartime` / `Convert.angulartime` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `angularwavenumber` | `Conv.angularwavenumber` / `Convert.angularwavenumber` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `apm` | `UnitSystems.apm` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `apostilb` | `UnitSystems.apostilb` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `arcminute` | `UnitSystems.arcminute` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `arcsecond` | `UnitSystems.arcsecond` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `area` | `Conv.area` / `Convert.area` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `areadensity` | `Conv.areadensity` / `Convert.areadensity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `astronomicalunit` | `UnitSystems.astronomicalunit` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `atm` | `moduleConstants` entry `ms Num .atm` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `atmosphere` | `UnitSystems.atmosphere` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `atomicmass` | `dalton` exists | PARTIAL | alias `atomicmass = dalton` not defined | S | P2 |
| `atto` | `moduleConstants` entry `atto Num` (UnitSystems/Registry.lean); callable form `UnitSystems.attoU` | DONE | constants.json (bit-exact) | — | — |
| `avogadro` | `UnitSystems.avogadro` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `a₀` | `moduleConstants` entry `bohr (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `bar` | `UnitSystems.bar` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `barn` | `UnitSystems.barn` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `barye` | `UnitSystems.barye` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `bel` | — | SKIP | exported but undefined in Julia (UndefVarError); nothing to port | — | — |
| `biotsavart` | `UnitSystems.biotsavart` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `bohr` | `UnitSystems.bohr` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `boilerhorsepower` | `UnitSystems.boilerhorsepower` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `boiling` | `UnitSystems.boiling` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `boltzmann` | `UnitSystems.boltzmann` (UnitSystems/System.lean); two-system form `Convert.constRatio boltzmann` | DONE | scalars.json × 48; Coupling-aware variants in extras.json | — | — |
| `bradian` | `UnitSystems.bradian` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `bril` | `UnitSystems.bril` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `bubnoff` | `UnitSystems.bubnoff` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `byte` | `moduleConstants` entry `byte Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `cal` | `moduleConstants` entry `calorie (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `calorie` | `UnitSystems.calorie` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `calᵢₜ` | — | MISSING | plain Julia numbers `kcalₜₕ=4184`, `kcalᵢₜ=4186.8`, `cal* = kcal*/1e3` (UnitSystems.jl:343-344) not defined | S | P2 |
| `calₜₕ` | — | MISSING | plain Julia numbers `kcalₜₕ=4184`, `kcalᵢₜ=4186.8`, `cal* = kcal*/1e3` (UnitSystems.jl:343-344) not defined | S | P2 |
| `candela` | `UnitSystems.candela` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `capacitance` | `Conv.capacitance` / `Convert.capacitance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `catalysis` | `Conv.catalysis` / `Convert.catalysis` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `cc` | value exists as `𝘤` (`moduleConstants`) | PARTIAL | ASCII alias of `𝘤` has no Lean name or registry key | S | P2 |
| `celsius` | `UnitSystems.celsius` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `centi` | `moduleConstants` entry `centi Num` (UnitSystems/Registry.lean); callable form `UnitSystems.centiU` | DONE | constants.json (bit-exact) | — | — |
| `charge` | `Conv.charge` / `Convert.charge` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `chargedensity` | `Conv.chargedensity` / `Convert.chargedensity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `compliance` | `Conv.compliance` / `Convert.compliance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `compressibility` | `Conv.compressibility` / `Convert.compressibility` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `conductance` | `Conv.conductance` / `Convert.conductance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `conductancequantum` | `UnitSystems.conductancequantum` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `conductivity` | `Conv.conductivity` / `Convert.conductivity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `cosmological` | `UnitSystems.cosmological` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `coulomb` | `UnitSystems.coulomb` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `coupling` | `UnitSystems.coupling`, `Coupling.coupling` (UnitSystems/System.lean) | DONE | scalars.json × 48 systems | — | — |
| `crackle` | `Conv.crackle` / `Convert.crackle` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `cup` | `UnitSystems.cup` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `curie` | `UnitSystems.curie` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `current` | `Conv.current` / `Convert.current` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `currentdensity` | `Conv.currentdensity` / `Convert.currentdensity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `dalton` | `UnitSystems.dalton` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `darcy` | `UnitSystems.darcy` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `darkenergydensity` | `UnitSystems.darkenergydensity`, `Coupling.darkenergydensity` (UnitSystems/System.lean) | DONE | scalars.json × 48 systems | — | — |
| `day` | `UnitSystems.day` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `deci` | `moduleConstants` entry `deci Num` (UnitSystems/Registry.lean); callable form `UnitSystems.deciU` | DONE | constants.json (bit-exact) | — | — |
| `decibel` | — | SKIP | exported but undefined in Julia (UndefVarError); nothing to port | — | — |
| `degree` | `UnitSystems.degree` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `deka` | `moduleConstants` entry `deka Num` (UnitSystems/Registry.lean); callable form `UnitSystems.dekaU` | DONE | constants.json (bit-exact) | — | — |
| `demagnetizingfactor` | `Conv.demagnetizingfactor` / `Convert.demagnetizingfactor` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `density` | `Conv.density` / `Convert.density` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `diffusionflux` | `Conv.diffusionflux` / `Convert.diffusionflux` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `diffusivity` | `Conv.diffusivity` / `Convert.diffusivity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `dimensionless` | `Conv.dimensionless` / `Convert.dimensionless` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `diopter` | `UnitSystems.diopter` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `dyne` | `UnitSystems.dyne` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `e0` | value exists as `ε₀` (`moduleConstants`) | PARTIAL | ASCII alias of `ε₀` has no Lean name or registry key | S | P2 |
| `eV` | `moduleConstants` entry `electronvolt (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `earthcalorie` | `UnitSystems.earthcalorie` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `earthcoulomb` | `UnitSystems.earthcoulomb` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `earthgram` | `UnitSystems.earthgram` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `earthmass` | `UnitSystems.earthmass` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `earthmeter` | `UnitSystems.earthmeter` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `earthmole` | `UnitSystems.earthmole` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `earthradius` | `UnitSystems.earthradius` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `eddington` | `UnitSystems.eddington` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `ee` | value exists as `𝘦` (`moduleConstants`) | PARTIAL | ASCII alias of `𝘦` has no Lean name or registry key | S | P2 |
| `einstein` | `UnitSystems.einstein` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `electricalhorsepower` | `UnitSystems.electricalhorsepower` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `electricdipolemoment` | `Conv.electricdipolemoment` / `Convert.electricdipolemoment` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `electricdisplacement` | `Conv.electricdisplacement` / `Convert.electricdisplacement` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `electricfield` | `Conv.electricfield` / `Convert.electricfield` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `electricflux` | `Conv.electricflux` / `Convert.electricflux` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `electricpolarizability` | `Conv.electricpolarizability` / `Convert.electricpolarizability` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `electricpotential` | `Conv.electricpotential` / `Convert.electricpotential` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `electronmass` | `UnitSystems.electronmass` (UnitSystems/System.lean); two-system form `Convert.constRatio electronmass` | DONE | scalars.json × 48; Coupling-aware variants in extras.json | — | — |
| `electronradius` | `UnitSystems.electronradius` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `electronunit` | `UnitSystems.electronunit`, `Coupling.electronunit` (UnitSystems/System.lean) | DONE | scalars.json × 48 systems | — | — |
| `electronvolt` | `UnitSystems.electronvolt` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `electrostatic` | `UnitSystems.electrostatic` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `elementarycharge` | `UnitSystems.elementarycharge` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `eleven` | `UnitSystems.eleven U` accessor + `c11 α` constant (UnitSystems/System.lean) | DONE | callable constant: both forms exist (scalars/constants goldens) | — | — |
| `em` | `moduleConstants` entry `em Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `energy` | `Conv.energy` / `Convert.energy` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `entropy` | `Conv.entropy` / `Convert.entropy` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `eotvos` | `UnitSystems.eotvos` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `erg` | `UnitSystems.erg` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `etendue` | `Conv.etendue` / `Convert.etendue` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `eulergamma` | Similitude generators `Consts.gen 33/34` only | MISSING | re-exported `Base.MathConstants` irrationals have no UnitSystems-level value | S | P2 |
| `exa` | `moduleConstants` entry `exa Num` (UnitSystems/Registry.lean); callable form `UnitSystems.exaU` | DONE | constants.json (bit-exact) | — | — |
| `exbi` | `moduleConstants` entry `exbi Num` (UnitSystems/Registry.lean); callable form `UnitSystems.exbiU` | DONE | constants.json (bit-exact) | — | — |
| `exposure` | `Conv.exposure` / `Convert.exposure` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `fahrenheit` | `UnitSystems.fahrenheit` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `farad` | `UnitSystems.farad` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `faraday` | `UnitSystems.faraday` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `feet` | `UnitSystems.feet` (UnitSystems/Derived.lean) | PARTIAL | implemented; spot-checked equal to Julia by this audit, but no oracle golden in Tests/UnitSystems | S | P2 |
| `femto` | `moduleConstants` entry `femto Num` (UnitSystems/Registry.lean); callable form `UnitSystems.femtoU` | DONE | constants.json (bit-exact) | — | — |
| `finestructure` | `UnitSystems.finestructure`, `Coupling.finestructure` (UnitSystems/System.lean) | DONE | scalars.json × 48 systems | — | — |
| `five` | `UnitSystems.five U` accessor + `c5 α` constant (UnitSystems/System.lean) | DONE | callable constant: both forms exist (scalars/constants goldens) | — | — |
| `flick` | `UnitSystems.flick` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `fluence` | `Conv.fluence` / `Convert.fluence` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `fluidounce` | `UnitSystems.fluidounce` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `foot` | `UnitSystems.foot` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `footcandle` | `UnitSystems.footcandle` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `footlambert` | `UnitSystems.footlambert` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `footpound` | `UnitSystems.footpound` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `force` | `Conv.force` / `Convert.force` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `fourtythree` | `UnitSystems.fourtythree U` accessor + `c43 α` constant (UnitSystems/System.lean) | DONE | callable constant: both forms exist (scalars/constants goldens) | — | — |
| `fpm` | `UnitSystems.fpm` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `fps` | `UnitSystems.fps` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `frequency` | `Conv.frequency` / `Convert.frequency` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `frequencydrift` | `Conv.frequencydrift` / `Convert.frequencydrift` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `ft` | `moduleConstants` entry `ms Num .ft` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `ftUS` | `moduleConstants` entry `ms Num .ftUS` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `fuelefficiency` | `Conv.fuelefficiency` / `Convert.fuelefficiency` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `fur` | `moduleConstants` entry `fur Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `g0` | value exists as `g₀` (`moduleConstants`) | PARTIAL | ASCII alias of `g₀` has no Lean name or registry key | S | P2 |
| `galileo` | `UnitSystems.galileo` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `gallon` | `UnitSystems.gallon` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `gasgallon` | `UnitSystems.gasgallon` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `gauss` | `UnitSystems.gauss` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `gaussgravitation` | `UnitSystems.gaussgravitation` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `gaussianmonth` | `UnitSystems.gaussianmonth` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `gaussianyear` | `UnitSystems.gaussianyear` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `gforce` | `UnitSystems.gforce` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `gibi` | `moduleConstants` entry `gibi Num` (UnitSystems/Registry.lean); callable form `UnitSystems.gibiU` | DONE | constants.json (bit-exact) | — | — |
| `giga` | `moduleConstants` entry `giga Num` (UnitSystems/Registry.lean); callable form `UnitSystems.gigaU` | DONE | constants.json (bit-exact) | — | — |
| `gilbert` | `UnitSystems.gilbert` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `golden` | Similitude generators `Consts.gen 33/34` only | MISSING | re-exported `Base.MathConstants` irrationals have no UnitSystems-level value | S | P2 |
| `gradian` | `UnitSystems.gradian` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `grain` | `UnitSystems.grain` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `gram` | `UnitSystems.gram` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `gravitation` | `UnitSystems.gravitation` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `gravity` | `UnitSystems.gravity` (UnitSystems/System.lean); two-system form `Convert.constRatio gravity` | DONE | scalars.json × 48; Coupling-aware variants in extras.json | — | — |
| `gravityforce` | `Conv.gravityforce` / `Convert.gravityforce` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `gray` | `UnitSystems.gray` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `greatcircle` | `UnitSystems.greatcircle` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `g₀` | `moduleConstants` entry `ms Num .g₀` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `hartree` | `UnitSystems.hartree` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `hectare` | `UnitSystems.hectare` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `hecto` | `moduleConstants` entry `hecto Num` (UnitSystems/Registry.lean); callable form `UnitSystems.hectoU` | DONE | constants.json (bit-exact) | — | — |
| `henry` | `UnitSystems.henry` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `hertz` | `UnitSystems.hertz` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `hh` | value exists as `𝘩` (`moduleConstants`) | PARTIAL | ASCII alias of `𝘩` has no Lean name or registry key | S | P2 |
| `horsepower` | `UnitSystems.horsepower` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `horsepowermetric` | `UnitSystems.horsepowermetric` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `horsepowerwatt` | `UnitSystems.horsepowerwatt` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `hour` | `UnitSystems.hour` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `hubble` | `UnitSystems.hubble` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `hyl` | `UnitSystems.hyl` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `hyperfine` | `UnitSystems.hyperfine` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `illuminance` | `Conv.illuminance` / `Convert.illuminance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `impedance` | `Conv.impedance` / `Convert.impedance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `impulse` | `Conv.impulse` / `Convert.impulse` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `inch` | `UnitSystems.inch` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `inchmercury` | `UnitSystems.inchmercury` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `inductance` | `Conv.inductance` / `Convert.inductance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `inertance` | `Conv.inertance` / `Convert.inertance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `inertia` | `Conv.inertia` / `Convert.inertia` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `intensity` | `irradiance` exists | PARTIAL | alias `intensity = irradiance` not defined | S | P2 |
| `ips` | `UnitSystems.ips` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `irradiance` | `Conv.irradiance` / `Convert.irradiance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `jansky` | `UnitSystems.jansky` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `jerk` | `Conv.jerk` / `Convert.jerk` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `josephson` | `UnitSystems.josephson` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `joule` | `UnitSystems.joule` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `jovianyear` | `UnitSystems.jovianyear` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `jupiterdistance` | `UnitSystems.jupiterdistance` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `jupitermass` | `UnitSystems.jupitermass` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `kB` | `moduleConstants` entry `ms Num .kB` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `katal` | `UnitSystems.katal` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `kayser` | `UnitSystems.kayser` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `kcal` | `moduleConstants` entry `kilocalorie (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `kcalᵢₜ` | — | MISSING | plain Julia numbers `kcalₜₕ=4184`, `kcalᵢₜ=4186.8`, `cal* = kcal*/1e3` (UnitSystems.jl:343-344) not defined | S | P2 |
| `kcalₜₕ` | — | MISSING | plain Julia numbers `kcalₜₕ=4184`, `kcalᵢₜ=4186.8`, `cal* = kcal*/1e3` (UnitSystems.jl:343-344) not defined | S | P2 |
| `ke` | value exists as `kₑ` (`moduleConstants`) | PARTIAL | ASCII alias of `kₑ` has no Lean name or registry key | S | P2 |
| `kelvin` | `UnitSystems.kelvin` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `kibi` | `moduleConstants` entry `kibi Num` (UnitSystems/Registry.lean); callable form `UnitSystems.kibiU` | DONE | constants.json (bit-exact) | — | — |
| `kilo` | `moduleConstants` entry `kilo Num` (UnitSystems/Registry.lean); callable form `UnitSystems.kiloU` | DONE | constants.json (bit-exact) | — | — |
| `kilocalorie` | `UnitSystems.kilocalorie` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `kilogram` | `UnitSystems.kilogram` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `kilograms` | `UnitSystems.kilograms` (UnitSystems/Derived.lean) | PARTIAL | implemented; spot-checked equal to Julia by this audit, but no oracle golden in Tests/UnitSystems | S | P2 |
| `kilopond` | `UnitSystems.kilopond` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `klitzing` | `UnitSystems.klitzing` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `kmh` | `UnitSystems.kmh` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `knot` | `UnitSystems.knot` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `kₑ` | `moduleConstants` entry `electrostatic (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `lA` | `moduleConstants` entry `Convert.length (Hartree Num) (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `lP` | value exists as `ℓP` (`moduleConstants`) | PARTIAL | ASCII alias of `ℓP` has no Lean name or registry key | S | P2 |
| `lQCD` | `moduleConstants` entry `Convert.length (QCD Num) (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `lS` | `moduleConstants` entry `Convert.length (Stoney Num) (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `lambert` | `UnitSystems.lambert` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `langley` | `UnitSystems.langley` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `lapserate` | `Conv.lapserate` / `Convert.lapserate` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `lb` | `moduleConstants` entry `ms Num .lb` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `lbm` | `moduleConstants` entry `ms Num .g₀ / ms Num .ft` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `lc` | `moduleConstants` entry `lc Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `lcq` | `moduleConstants` entry `lcq Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `length` | `Conv.length` / `Convert.length` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `lightspeed` | `UnitSystems.lightspeed` (UnitSystems/System.lean); two-system form `Convert.constRatio lightspeed` | DONE | scalars.json × 48; Coupling-aware variants in extras.json | — | — |
| `lightyear` | `UnitSystems.lightyear` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `linearchargedensity` | `Conv.linearchargedensity` / `Convert.linearchargedensity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `lineardensity` | `Conv.lineardensity` / `Convert.lineardensity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `liter` | `UnitSystems.liter` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `lorentz` | `UnitSystems.lorentz` (UnitSystems/System.lean); two-system form `Convert.constRatio lorentz` | DONE | scalars.json × 48; Coupling-aware variants in extras.json | — | — |
| `loschmidt` | `UnitSystems.loschmidt` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `lumen` | `UnitSystems.lumen` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `lumerg` | `UnitSystems.lumerg` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `luminance` | `Conv.luminance` / `Convert.luminance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `luminousefficacy` | `Conv.luminousefficacy` / `Convert.luminousefficacy` (UnitSystems/Convert.lean); one-arg accessor `UnitSystems.luminousefficacy` | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `luminousenergy` | `Conv.luminousenergy` / `Convert.luminousenergy` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `luminousexposure` | `Conv.luminousexposure` / `Convert.luminousexposure` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `luminousflux` | `Conv.luminousflux` / `Convert.luminousflux` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `luminousintensity` | `Conv.luminousintensity` / `Convert.luminousintensity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `lunardistance` | `UnitSystems.lunardistance` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `lunarmass` | `UnitSystems.lunarmass` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `lux` | `UnitSystems.lux` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `m0` | value exists as `μ₀` (`moduleConstants`) | PARTIAL | ASCII alias of `μ₀` has no Lean name or registry key | S | P2 |
| `mA` | `moduleConstants` entry `Convert.mass (Hartree Num) (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `mP` | `moduleConstants` entry `ms Num .mP` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `mQCD` | `moduleConstants` entry `Convert.mass (QCD Num) (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `mS` | `moduleConstants` entry `Convert.mass (Stoney Num) (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `magneticdipolemoment` | `Conv.magneticdipolemoment` / `Convert.magneticdipolemoment` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `magneticfield` | `Conv.magneticfield` / `Convert.magneticfield` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `magneticflux` | `Conv.magneticflux` / `Convert.magneticflux` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `magneticfluxdensity` | `Conv.magneticfluxdensity` / `Convert.magneticfluxdensity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `magneticfluxquantum` | `UnitSystems.magneticfluxquantum` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `magneticmoment` | `Conv.magneticmoment` / `Convert.magneticmoment` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `magneticpolarizability` | `Conv.magneticpolarizability` / `Convert.magneticpolarizability` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `magneticpotential` | `Conv.magneticpotential` / `Convert.magneticpotential` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `magneton` | `UnitSystems.magneton` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `magnetostatic` | `UnitSystems.magnetostatic` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `mass` | `Conv.mass` / `Convert.mass` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `massflow` | `Conv.massflow` / `Convert.massflow` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `maxwell` | `UnitSystems.maxwell` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `mc` | `moduleConstants` entry `mc Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `mcq` | `moduleConstants` entry `mcq Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `me` | value exists as `mₑ` (`moduleConstants`) | PARTIAL | ASCII alias of `mₑ` has no Lean name or registry key | S | P2 |
| `meancalorie` | `UnitSystems.meancalorie` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `mebi` | `moduleConstants` entry `mebi Num` (UnitSystems/Registry.lean); callable form `UnitSystems.mebiU` | DONE | constants.json (bit-exact) | — | — |
| `mechanicalheat` | `UnitSystems.mechanicalheat` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `mega` | `moduleConstants` entry `mega Num` (UnitSystems/Registry.lean); callable form `UnitSystems.megaU` | DONE | constants.json (bit-exact) | — | — |
| `meridianmile` | `UnitSystems.meridianmile` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `meter` | `UnitSystems.meter` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `meters` | `UnitSystems.meters` (UnitSystems/Derived.lean) | PARTIAL | implemented; spot-checked equal to Julia by this audit, but no oracle golden in Tests/UnitSystems | S | P2 |
| `meu` | value exists as `μₑᵤ` (`moduleConstants`) | PARTIAL | ASCII alias of `μₑᵤ` has no Lean name or registry key | S | P2 |
| `mi` | `moduleConstants` entry `mi Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `micro` | `moduleConstants` entry `micro Num` (UnitSystems/Registry.lean); callable form `UnitSystems.microU` | DONE | constants.json (bit-exact) | — | — |
| `mile` | `UnitSystems.mile` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `milli` | `moduleConstants` entry `milli Num` (UnitSystems/Registry.lean); callable form `UnitSystems.milliU` | DONE | constants.json (bit-exact) | — | — |
| `minute` | `UnitSystems.minute` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `mobility` | `Conv.mobility` / `Convert.mobility` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `molality` | `Conv.molality` / `Convert.molality` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `molaramount` | `Conv.molaramount` / `Convert.molaramount` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `molarconductivity` | `Conv.molarconductivity` / `Convert.molarconductivity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `molarenergy` | `Conv.molarenergy` / `Convert.molarenergy` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `molarentropy` | `Conv.molarentropy` / `Convert.molarentropy` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `molargas` | `UnitSystems.molargas` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `molarity` | `Conv.molarity` / `Convert.molarity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `molarmass` | `Conv.molarmass` / `Convert.molarmass` (UnitSystems/Convert.lean); one-arg accessor `UnitSystems.molarmass` | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `molarsusceptibility` | `Conv.molarsusceptibility` / `Convert.molarsusceptibility` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `molarvolume` | `Conv.molarvolume` / `Convert.molarvolume` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `mole` | `UnitSystems.mole` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `molecules` | `UnitSystems.molecules` (UnitSystems/Derived.lean) | PARTIAL | implemented; spot-checked equal to Julia by this audit, but no oracle golden in Tests/UnitSystems | S | P2 |
| `moles` | `UnitSystems.moles` (UnitSystems/Derived.lean) | PARTIAL | implemented; spot-checked equal to Julia by this audit, but no oracle golden in Tests/UnitSystems | S | P2 |
| `momentum` | `Conv.momentum` / `Convert.momentum` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `mp` | value exists as `mₚ` (`moduleConstants`) | PARTIAL | ASCII alias of `mₚ` has no Lean name or registry key | S | P2 |
| `mpe` | value exists as `μₚₑ` (`moduleConstants`) | PARTIAL | ASCII alias of `μₚₑ` has no Lean name or registry key | S | P2 |
| `mpge` | `UnitSystems.mpge` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `mph` | `UnitSystems.mph` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `mps` | `UnitSystems.mps` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `mpu` | value exists as `μₚᵤ` (`moduleConstants`) | PARTIAL | ASCII alias of `μₚᵤ` has no Lean name or registry key | S | P2 |
| `ms` | `UnitSystems.msU` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `mu` | value exists as `Da` (`moduleConstants`) | PARTIAL | ASCII alias of `Da` has no Lean name or registry key | S | P2 |
| `mᵤ` | value exists as `Da` (`moduleConstants`) | PARTIAL | ASCII alias of `Da` has no Lean name or registry key | S | P2 |
| `mₑ` | `moduleConstants` entry `mₑ Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `mₑ1990` | `moduleConstants` entry `electronmass (Conventional Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `mₑ2014` | `moduleConstants` entry `electronmass (CODATA Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `mₚ` | `moduleConstants` entry `protonmass (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `nano` | `moduleConstants` entry `nano Num` (UnitSystems/Registry.lean); callable form `UnitSystems.nanoU` | DONE | constants.json (bit-exact) | — | — |
| `nauticalmile` | `UnitSystems.nauticalmile` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `neper` | — | SKIP | exported but undefined in Julia (UndefVarError); nothing to port | — | — |
| `newton` | `UnitSystems.newton` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `nineteen` | `UnitSystems.nineteen U` accessor + `c19 α` constant (UnitSystems/System.lean) | DONE | callable constant: both forms exist (scalars/constants goldens) | — | — |
| `nit` | `UnitSystems.nit` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `nm` | `moduleConstants` entry `nm Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `numberdensity` | `Conv.numberdensity` / `Convert.numberdensity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `oersted` | `UnitSystems.oersted` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `ohm` | `UnitSystems.ohm` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `ounce` | `UnitSystems.ounce` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `parsec` | `UnitSystems.parsec` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `pascal` | `UnitSystems.pascal` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `pebi` | `moduleConstants` entry `pebi Num` (UnitSystems/Registry.lean); callable form `UnitSystems.pebiU` | DONE | constants.json (bit-exact) | — | — |
| `permeability` | `Conv.permeability` / `Convert.permeability` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `permeance` | `Conv.permeance` / `Convert.permeance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `permittivity` | `Conv.permittivity` / `Convert.permittivity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `peta` | `moduleConstants` entry `peta Num` (UnitSystems/Registry.lean); callable form `UnitSystems.petaU` | DONE | constants.json (bit-exact) | — | — |
| `phot` | `UnitSystems.phot` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `photonintensity` | `Conv.photonintensity` / `Convert.photonintensity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `photonirradiance` | `Conv.photonirradiance` / `Convert.photonirradiance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `photonradiance` | `Conv.photonradiance` / `Convert.photonradiance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `pico` | `moduleConstants` entry `pico Num` (UnitSystems/Registry.lean); callable form `UnitSystems.picoU` | DONE | constants.json (bit-exact) | — | — |
| `pint` | `UnitSystems.pint` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `planck` | `UnitSystems.planck` (UnitSystems/Physics.lean); two-system form `Convert.constRatio planck` | DONE | scalars.json × 48; Coupling-aware variants in extras.json | — | — |
| `planckmass` | `UnitSystems.planckmass` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `planckreduced` | `UnitSystems.planckreduced` (UnitSystems/System.lean); two-system form `Convert.constRatio planckreduced` | DONE | scalars.json × 48; Coupling-aware variants in extras.json | — | — |
| `poise` | `UnitSystems.poise` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `polestrength` | `Conv.polestrength` / `Convert.polestrength` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `pop` | `Conv.pop` / `Convert.pop` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `pound` | `UnitSystems.pound` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `poundal` | `UnitSystems.poundal` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `poundforce` | `UnitSystems.poundforce` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `poundmole` | `UnitSystems.poundmole` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `power` | `Conv.power` / `Convert.power` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `powerdensity` | `Conv.powerdensity` / `Convert.powerdensity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `pressure` | `Conv.pressure` / `Convert.pressure` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `protonelectron` | `UnitSystems.protonelectron`, `Coupling.protonelectron` (UnitSystems/System.lean) | DONE | scalars.json × 48 systems | — | — |
| `protonmass` | `UnitSystems.protonmass` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `protonunit` | `UnitSystems.protonunit`, `Coupling.protonunit` (UnitSystems/System.lean) | DONE | scalars.json × 48 systems | — | — |
| `psi` | `UnitSystems.psi` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `qA` | `moduleConstants` entry `Convert.charge (Hartree Num) (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `qS` | `moduleConstants` entry `Convert.charge (Stoney Num) (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `quart` | `UnitSystems.quart` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `radarmile` | `UnitSystems.radarmile` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `radian` | `UnitSystems.radian` (UnitSystems/System.lean); two-system form `Convert.constRatio radian` | DONE | scalars.json × 48; Coupling-aware variants in extras.json | — | — |
| `radiance` | `Conv.radiance` / `Convert.radiance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `radiantintensity` | `Conv.radiantintensity` / `Convert.radiantintensity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `radiationdensity` | `UnitSystems.radiationdensity` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `rankine` | `UnitSystems.rankine` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `rationalization` | `UnitSystems.rationalization` (UnitSystems/System.lean); two-system form `Convert.constRatio rationalization` | DONE | scalars.json × 48; Coupling-aware variants in extras.json | — | — |
| `rayl` | `UnitSystems.rayl` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `rayleigh` | `UnitSystems.rayleigh` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `re` | value exists as `rₑ` (`moduleConstants`) | PARTIAL | ASCII alias of `rₑ` has no Lean name or registry key | S | P2 |
| `reluctance` | `Conv.reluctance` / `Convert.reluctance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `rem` | `UnitSystems.remU` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `resistance` | `Conv.resistance` / `Convert.resistance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `resistivity` | `Conv.resistivity` / `Convert.resistivity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `reyn` | `UnitSystems.reyn` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `roentgen` | `UnitSystems.roentgen` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `rotationalinertia` | `Conv.rotationalinertia` / `Convert.rotationalinertia` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `rpm` | `UnitSystems.rpm` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `rydberg` | `UnitSystems.rydberg` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `rₑ` | `moduleConstants` entry `electronradius (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `sackurtetrode` | `UnitSystems.sackurtetrode` (UnitSystems/Registry.lean) | DONE | scalars.json × 48 (Num scalar only) | — | — |
| `sealevel` | `UnitSystems.sealevel` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `second` | `UnitSystems.second` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `seven` | `UnitSystems.seven U` accessor + `c7 α` constant (UnitSystems/System.lean) | DONE | callable constant: both forms exist (scalars/constants goldens) | — | — |
| `siderealmonth` | `UnitSystems.siderealmonth` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `siderealyear` | `UnitSystems.siderealyear` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `siemens` | `UnitSystems.siemens` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `similitude` | — | SKIP | `ENV["SIMILITUDE"]` build toggle; Lean selects the scalar type statically | — | — |
| `sixty` | `moduleConstants` entry `sixty Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `slinch` | `UnitSystems.slinch` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `slinchmole` | `UnitSystems.slinchmole` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `slug` | `UnitSystems.slugU` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `slugmole` | `UnitSystems.slugmole` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `slugs` | `UnitSystems.slugs` (UnitSystems/Derived.lean) | PARTIAL | implemented; spot-checked equal to Julia by this audit, but no oracle golden in Tests/UnitSystems | S | P2 |
| `snap` | `Conv.snap` / `Convert.snap` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `solarflux` | `UnitSystems.solarflux` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `solarmass` | `UnitSystems.solarmass` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `solidangle` | `Conv.solidangle` / `Convert.solidangle` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `soundexposure` | `Conv.soundexposure` / `Convert.soundexposure` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `spat` | `UnitSystems.spat` (UnitSystems/System.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `spatian` | `UnitSystems.spatian` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `specificenergy` | `Conv.specificenergy` / `Convert.specificenergy` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `specificentropy` | `Conv.specificentropy` / `Convert.specificentropy` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `specificforce` | `Conv.specificforce` / `Convert.specificforce` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `specificimpedance` | `Conv.specificimpedance` / `Convert.specificimpedance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `specificity` | `Conv.specificity` / `Convert.specificity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `specificmagnetization` | `Conv.specificmagnetization` / `Convert.specificmagnetization` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `specificsusceptibility` | `Conv.specificsusceptibility` / `Convert.specificsusceptibility` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `specificvolume` | `Conv.specificvolume` / `Convert.specificvolume` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `specificweight` | `Conv.specificweight` / `Convert.specificweight` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `spectralexposure` | `Conv.spectralexposure` / `Convert.spectralexposure` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `spectralflux` | `Conv.spectralflux` / `Convert.spectralflux` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `speed` | `Conv.speed` / `Convert.speed` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `squaredegree` | `UnitSystems.squaredegree` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `stagnance` | `Conv.stagnance` / `Convert.stagnance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `statampere` | `UnitSystems.statampere` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `statcoulomb` | `UnitSystems.statcoulomb` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `statfarad` | `UnitSystems.statfarad` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `stathenry` | `UnitSystems.stathenry` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `statmho` | `UnitSystems.statmho` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `statohm` | `UnitSystems.statohm` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `stattesla` | `UnitSystems.stattesla` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `statutemile` | `UnitSystems.statutemile` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `statvolt` | `UnitSystems.statvolt` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `statweber` | `UnitSystems.statweber` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `stefan` | `UnitSystems.stefan` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `steradian` | `UnitSystems.steradian` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `stilb` | `UnitSystems.stilb` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `stokes` | `UnitSystems.stokes` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `surveyacre` | `UnitSystems.surveyacre` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `surveyfoot` | `UnitSystems.surveyfoot` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `susceptibility` | `Conv.susceptibility` / `Convert.susceptibility` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `synodicmonth` | `UnitSystems.synodicmonth` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `tA` | `moduleConstants` entry `Convert.time (Hartree Num) (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `tP` | `moduleConstants` entry `Convert.time (PlanckGauss Num) (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `tQCD` | `moduleConstants` entry `Convert.time (QCD Num) (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `tS` | `moduleConstants` entry `Convert.time (Stoney Num) (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `tablespoon` | `UnitSystems.tablespoon` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `talbot` | `UnitSystems.talbot` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `tau` | `UnitSystems.tau U`, `UnitAlg.tau` (UnitSystems/System.lean, Alg.lean) | DONE | module constant `τ` golden | — | — |
| `tcq` | `moduleConstants` entry `tcq Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `teaspoon` | `UnitSystems.teaspoon` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `tebi` | `moduleConstants` entry `tebi Num` (UnitSystems/Registry.lean); callable form `UnitSystems.tebiU` | DONE | constants.json (bit-exact) | — | — |
| `technicalatmosphere` | `UnitSystems.technicalatmosphere` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `temp` | `temperature` exists | PARTIAL | alias `temp = temperature` not defined | S | P2 |
| `temperature` | `Conv.temperature` / `Convert.temperature` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `tera` | `moduleConstants` entry `tera Num` (UnitSystems/Registry.lean); callable form `UnitSystems.teraU` | DONE | constants.json (bit-exact) | — | — |
| `tesla` | `UnitSystems.tesla` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `th` | `moduleConstants` entry `th Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `thermalconductance` | `Conv.thermalconductance` / `Convert.thermalconductance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `thermalconductivity` | `Conv.thermalconductivity` / `Convert.thermalconductivity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `thermalexpansion` | `Conv.thermalexpansion` / `Convert.thermalexpansion` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `thermalresistance` | `Conv.thermalresistance` / `Convert.thermalresistance` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `thermalresistivity` | `Conv.thermalresistivity` / `Convert.thermalresistivity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `thermalunit` | `UnitSystems.thermalunit` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `three` | `UnitSystems.three U` accessor + `c3 α` constant (UnitSystems/System.lean) | DONE | callable constant: both forms exist (scalars/constants goldens) | — | — |
| `time` | `Conv.time` / `Convert.time` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `ton` | `UnitSystems.ton` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `tonne` | `UnitSystems.tonne` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `tonsrefrigeration` | `UnitSystems.tonsrefrigeration` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `tontnt` | `UnitSystems.tontnt` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `torr` | `UnitSystems.torr` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `turn` | `UnitSystems.turn` (UnitSystems/System.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `two` | `UnitSystems.two U` accessor + `c2 α` constant (UnitSystems/System.lean) | DONE | callable constant: both forms exist (scalars/constants goldens) | — | — |
| `units` | `UnitSystems.UnitSystem` | PARTIAL | type alias `US`/`units` not defined | S | P2 |
| `universal` | `molargas` exists | PARTIAL | alias `universal = molargas` not defined | S | P2 |
| `universe` | `UnitSystems.universeOf` (UnitSystems/System.lean) | DONE | renamed (`universe` is a Lean keyword) | — | — |
| `vacuumimpedance` | `UnitSystems.vacuumimpedance` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `vacuumpermeability` | `UnitSystems.vacuumpermeability` (UnitSystems/System.lean); two-system form `Convert.constRatio vacuumpermeability` | DONE | scalars.json × 48; Coupling-aware variants in extras.json | — | — |
| `vacuumpermittivity` | `UnitSystems.vacuumpermittivity` (UnitSystems/Physics.lean) | DONE | scalars.json × 48 + perturbed-Coupling goldens (extras.json) | — | — |
| `vectorpotential` | `Conv.vectorpotential` / `Convert.vectorpotential` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `viscosity` | `Conv.viscosity` / `Convert.viscosity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `volt` | `UnitSystems.volt` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `volume` | `Conv.volume` / `Convert.volume` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `volumeflow` | `Conv.volumeflow` / `Convert.volumeflow` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `volumeheatcapacity` | `Conv.volumeheatcapacity` / `Convert.volumeheatcapacity` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `watt` | `UnitSystems.watt` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `wavenumber` | `Conv.wavenumber` / `Convert.wavenumber` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `weber` | `UnitSystems.weber` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `wienfrequency` | `UnitSystems.wienfrequency` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `wienwavelength` | `UnitSystems.wienwavelength` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `yank` | `Conv.yank` / `Convert.yank` (UnitSystems/Convert.lean) | DONE | `q(U,S)`, `q(U)`, `q(v,U,S)`, `q(v,U)` vs conversions.json (31k factors, 131×48 one-arg, 3000 values); dims proved in DimProofs | — | — |
| `yard` | `UnitSystems.yard` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `year` | `UnitSystems.year` (UnitSystems/Derived.lean) | DONE | scalars.json × 48 systems | — | — |
| `yobi` | `moduleConstants` entry `yobi Num` (UnitSystems/Registry.lean); callable form `UnitSystems.yobiU` | DONE | constants.json (bit-exact) | — | — |
| `yocto` | `moduleConstants` entry `ms Num .yocto` (UnitSystems/Registry.lean); callable form `UnitSystems.yoctoU` | DONE | constants.json (bit-exact) | — | — |
| `yotta` | `moduleConstants` entry `ms Num .yotta` (UnitSystems/Registry.lean); callable form `UnitSystems.yottaU` | DONE | constants.json (bit-exact) | — | — |
| `zebi` | `moduleConstants` entry `zebi Num` (UnitSystems/Registry.lean); callable form `UnitSystems.zebiU` | DONE | constants.json (bit-exact) | — | — |
| `zepto` | `moduleConstants` entry `ms Num .zepto` (UnitSystems/Registry.lean); callable form `UnitSystems.zeptoU` | DONE | constants.json (bit-exact) | — | — |
| `zetta` | `moduleConstants` entry `ms Num .zetta` (UnitSystems/Registry.lean); callable form `UnitSystems.zettaU` | DONE | constants.json (bit-exact) | — | — |
| `°R` | `moduleConstants` entry `degR Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `ħ` | `moduleConstants` entry `ħ Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `ΔνCs` | `moduleConstants` entry `ms Num .ΔνCs` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `Θ` | `USQ.Θ` (UnitSystems/Dim.lean) | DONE | Julia binds these to `Constant{1}` in UnitSystems (doc markers); Lean gives them their Similitude meaning as type-level dimensions | — | — |
| `Λ` | — | SKIP | exported but undefined in Julia (UndefVarError); nothing to port | — | — |
| `Φ₀` | `moduleConstants` entry `magneticfluxquantum (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `Ωᵢₜ` | `moduleConstants` entry `ms Num .Ωᵢₜ` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `αG` | `moduleConstants` entry `αG Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `αL` | `moduleConstants` entry `αL Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `αinv` | `moduleConstants` entry `ms Num .αinv` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `δμ₀` | `moduleConstants` entry `μ₀ Num - .p (.float (4.0 * 3.141592653589793 * 1e-7))` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `ε₀` | `moduleConstants` entry `vacuumpermittivity (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `κ` | `moduleConstants` entry `einstein (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `μB` | `moduleConstants` entry `magneton (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `μ₀` | `moduleConstants` entry `μ₀ Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `μₑᵤ` | `moduleConstants` entry `ms Num .μₑᵤ` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `μₑₚ` | `moduleConstants` entry `μₑₚ Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `μₚᵤ` | `moduleConstants` entry `ms Num .μₚᵤ` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `μₚₑ` | `moduleConstants` entry `μₚₑ Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `ς` | `moduleConstants` entry `ς Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `σ` | `moduleConstants` entry `stefan (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `τ` | `moduleConstants` entry `UnitAlg.tau` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `φ` | Similitude generators `Consts.gen 33/34` only | MISSING | re-exported `Base.MathConstants` irrationals have no UnitSystems-level value | S | P2 |
| `ϵ₀` | value exists as `ε₀` (`moduleConstants`) | PARTIAL | ASCII alias of `ε₀` has no Lean name or registry key | S | P2 |
| `ℓP` | `moduleConstants` entry `Convert.length (PlanckGauss Num) (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `𝔉` | `moduleConstants` entry `faraday (SI2019 Num)` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `𝘤` | `moduleConstants` entry `ms Num .cc` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `𝘦` | `moduleConstants` entry `ms Num .ee` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `𝘦ᵣ` | `moduleConstants` entry `eᵣ Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `𝘦ₙ` | `moduleConstants` entry `eₙ Num` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `𝘩` | `moduleConstants` entry `ms Num .hh` (UnitSystems/Registry.lean) | DONE | constants.json (bit-exact) | — | — |
| `𝟏` | `UnitAlg.one` (UnitSystems/System.lean) | DONE | exact integer Constant | — | — |
| `𝟏𝟎` | `deka` (UnitSystems/System.lean) | DONE | exact integer Constant | — | — |
| `𝟏𝟏` | `c11` (UnitSystems/System.lean) | DONE | exact integer Constant | — | — |
| `𝟏𝟗` | `c19` (UnitSystems/System.lean) | DONE | exact integer Constant | — | — |
| `𝟐` | `c2` (UnitSystems/System.lean) | DONE | exact integer Constant | — | — |
| `𝟑` | `c3` (UnitSystems/System.lean) | DONE | exact integer Constant | — | — |
| `𝟒𝟑` | `c43` (UnitSystems/System.lean) | DONE | exact integer Constant | — | — |
| `𝟓` | `c5` (UnitSystems/System.lean) | DONE | exact integer Constant | — | — |
| `𝟔𝟎` | `sixty` (UnitSystems/System.lean) | DONE | exact integer Constant | — | — |
| `𝟕` | `c7` (UnitSystems/System.lean) | DONE | exact integer Constant | — | — |
| `𝟙` | `UnitAlg.one` (UnitSystems/System.lean) | DONE | exact integer Constant | — | — |
| `(U::UnitSystem)(JK,Js,ms,Hm,kg)` | — | MISSING | callable rescale constructor (UnitSystems.jl:205-221; `Metric(1.0,1.0,1.0,1.0,1.0)` is documented) not ported | S | P2 |
| `show/unitname(::UnitSystem) → "Unknown"` | `Sys.name` (named systems only) | PARTIAL | no way to print/identify an arbitrary `UnitSystem Num` (Julia prints its name if `===` a named system, else `Unknown`) | S | P2 |
| `display(::UnitSystem)` | `UnitSystem.display`, `Sys.display` (UnitSystems/Show.lean) | DONE | systems.json display strings | — | — |
| `normal(U), UnitSystems.constant(U)` | `UnitSystem.map` (UnitSystems/System.lean) | DONE | hooks are identity in UnitSystems | — | — |
| `isquantity, evaldim, Quantity(D,U,x), (U)(x,D)` | — | SKIP | dispatch hooks for Similitude; Lean instantiates the generic scalar instead | — | — |
| `UnitSystems.derived(U)` | — | SKIP | throws `UndefVarError: neper` in Julia | — | — |
| `textconstants/textderived/textquantities (text.jl)` | — | MISSING | unexported name tables used by docs/appendix generation | M | P2 |
| `docstring example corpus (1658 `julia>` examples)` | values covered by scalars/conversions goldens | PARTIAL | the corpus itself (port notes §6.3 `doc_goldens.json`) is not replayed as a test | M | P2 |
| `PERF: `q(v,U,S)` value conversion` | `Conv.convert` (UnitSystems/Convert.lean) | PARTIAL | measured 7286 ns/call (compiled, literal systems) vs Julia 0.58 ns (`energy(v,English,Metric)` constant-folds); chain + `ident` recomputed every call | S | P0 |
| `PERF: `q(U,S)` with runtime-chosen U` | `Conv.factor` | PARTIAL | measured 6057 ns/call vs Julia 74 ns (dynamic dispatch) | M | P1 |

## Similitude.jl (v0.3.3): 476 exports

| Julia symbol | Lean name(s) + file | status | gap / evidence | effort | prio |
|---|---|---|---|---|---|
| `@unitdim` | static `unitTextData`/`dimTextTable` (Similitude/UnitNames.lean), `Sys.hom` | MISSING | registries and homomorphisms are generated constants; users cannot register unit names or a homomorphism for a new system | M | P2 |
| `@unitgroup` | static `unitTextData`/`dimTextTable` (Similitude/UnitNames.lean), `Sys.hom` | MISSING | registries and homomorphisms are generated constants; users cannot register unit names or a homomorphism for a new system | M | P2 |
| `A` | `USQ.A` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `AE` | `Sys.ofName? "AE"` → `Sys.FPS` | PARTIAL | alias not a Lean identifier | S | P2 |
| `AbelianGroup` | — | SKIP | abstract supertype | — | — |
| `AbsoluteEnglish` | `Sys.ofName? "AbsoluteEnglish"` → `Sys.FPS` | PARTIAL | alias not a Lean identifier | S | P2 |
| `AstronomicalSystem` | `UnitSystems.AstronomicalSystem` instantiated at `Scalar` | DONE | generic over `UnitAlg` | — | — |
| `BG` | `Sys.ofName? "BG"` → `Sys.British` | PARTIAL | alias not a Lean identifier | S | P2 |
| `British` | `Sys.British.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.British Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `BritishGravitational` | `Sys.ofName? "BritishGravitational"` → `Sys.British` | PARTIAL | alias not a Lean identifier | S | P2 |
| `C` | `USQ.C` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `CGS` | `Sys.ofName? "CGS"` → `Sys.Gauss` | PARTIAL | alias not a Lean identifier | S | P2 |
| `CGS2019` | — | SKIP | exported but undefined in Julia Similitude | — | — |
| `CGSe` | `Sys.ofName? "CGSe"` → `Sys.ESU` | PARTIAL | alias not a Lean identifier | S | P2 |
| `CGSm` | `Sys.ofName? "CGSm"` → `Sys.EMU` | PARTIAL | alias not a Lean identifier | S | P2 |
| `CODATA` | `Sys.CODATA.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.CODATA Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `Conventional` | `Sys.Conventional.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Conventional Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `ConventionalSystem` | `UnitSystems.ConventionalSystem` instantiated at `Scalar` | DONE | generic over `UnitAlg` | — | — |
| `Cosmological` | `Sys.Cosmological.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Cosmological Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `CosmologicalQuantum` | `Sys.CosmologicalQuantum.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.CosmologicalQuantum Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `Dimension` | type index `d` / `Dim.toGroup` | MISSING | no value-level accessor `Quantity.dimensions : USQGroup` / `ConvertUnit.dimensions` (trivial) | S | P1 |
| `EE` | `Sys.ofName? "EE"` → `Sys.English` | PARTIAL | alias not a Lean identifier | S | P2 |
| `EE2019` | — | SKIP | exported but undefined in Julia Similitude | — | — |
| `EMU` | `Sys.EMU.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.EMU Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `ESU` | `Sys.ESU.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.ESU Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `ElectricSystem` | `UnitSystems.ElectricSystem` instantiated at `Scalar` | DONE | generic over `UnitAlg` | — | — |
| `Electronic` | `Sys.Electronic.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Electronic Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `Engineering` | `Sys.Engineering.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Engineering Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `English` | `Sys.English.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.English Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `EnglishEngineering` | `Sys.ofName? "EnglishEngineering"` → `Sys.English` | PARTIAL | alias not a Lean identifier | S | P2 |
| `EnglishUS` | `Sys.ofName? "EnglishUS"` → `Sys.Survey` | PARTIAL | alias not a Lean identifier | S | P2 |
| `EntropySystem` | `UnitSystems.EntropySystem` instantiated at `Scalar` | DONE | generic over `UnitAlg` | — | — |
| `ExpGroup` | `FieldAlgebra.ExpGroup` (re-export) | DONE | see FieldAlgebra | — | — |
| `F` | `USQ.F` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `FFF` | `Sys.FFF.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.FFF Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `FPS` | `Sys.FPS.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.FPS Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `GM` | `Sys.ofName? "GM"` → `Sys.Gravitational` | PARTIAL | alias not a Lean identifier | S | P2 |
| `Gauss` | `Sys.Gauss.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Gauss Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `GaussSystem` | `UnitSystems.GaussSystem` instantiated at `Scalar` | DONE | generic over `UnitAlg` | — | — |
| `Gravitational` | `Sys.Gravitational.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Gravitational Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `Group` | `FieldAlgebra.Group` (re-export) | DONE | see FieldAlgebra | — | — |
| `HLU` | `Sys.ofName? "HLU"` → `Sys.LorentzHeaviside` | PARTIAL | alias not a Lean identifier | S | P2 |
| `Hartree` | `Sys.Hartree.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Hartree Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `Hubble` | `Sys.Hubble.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Hubble Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `IAU` | `Sys.IAU.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.IAU Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `IAUE` | `Sys.IAUE.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.IAUE Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `IAUJ` | `Sys.IAUJ.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.IAUJ Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `IAU☉` | `Sys.IAU.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.IAU Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `IPS` | `Sys.IPS.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.IPS Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `International` | `Sys.International.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.International Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `InternationalMean` | `Sys.InternationalMean.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.InternationalMean Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `J` | `USQ.J` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `KKH` | `Sys.KKH.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.KKH Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `L` | `USQ.L` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `LogGroup` | `FieldAlgebra.LogGroup` (re-export) | DONE | see FieldAlgebra | — | — |
| `LorentzHeaviside` | `Sys.LorentzHeaviside.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.LorentzHeaviside Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `M` | `USQ.M` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `ME` | `Sys.ofName? "ME"` → `Sys.Engineering` | PARTIAL | alias not a Lean identifier | S | P2 |
| `MKS` | `Sys.ofName? "MKS"` → `Sys.Metric` | PARTIAL | alias not a Lean identifier | S | P2 |
| `MPH` | `Sys.MPH.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.MPH Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `MTS` | `Sys.MTS.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.MTS Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `Meridian` | `Sys.Meridian.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Meridian Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `Metric` | `Sys.Metric.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Metric Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `MetricArcminute` | `Sys.MetricArcminute.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.MetricArcminute Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `MetricArcsecond` | `Sys.MetricArcsecond.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.MetricArcsecond Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `MetricDegree` | `Sys.MetricDegree.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.MetricDegree Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `MetricGradian` | `Sys.MetricGradian.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.MetricGradian Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `MetricSpatian` | `Sys.MetricSpatian.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.MetricSpatian Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `MetricSystem` | `UnitSystems.MetricSystem` instantiated at `Scalar` | DONE | generic over `UnitAlg` | — | — |
| `MetricTurn` | `Sys.MetricTurn.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.MetricTurn Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `N` | `USQ.N` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `Natural` | `Sys.Natural.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Natural Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `NaturalGauss` | `Sys.NaturalGauss.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.NaturalGauss Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `Nautical` | `Sys.Nautical.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Nautical Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `Planck` | `Sys.Planck.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Planck Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `PlanckGauss` | `Sys.PlanckGauss.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.PlanckGauss Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `Q` | `USQ.Q` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `QCD` | `Sys.QCD.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.QCD Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `QCDGauss` | `Sys.QCDGauss.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.QCDGauss Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `QCDoriginal` | `Sys.QCDoriginal.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.QCDoriginal Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `Quantities` | — | MISSING | vector of values sharing a dimension (largely broken in Julia); natural Lean form `Quantity U d (Values n Float)` needs a `QScalar` instance | S | P2 |
| `Quantity` | `Similitude.Quantity U d α`, `Q U d` (Similitude/Quantity.lean) | PARTIAL | typed * / inv npow sqrt cbrt `.to` `.recast` display tested (quantity_arith.json). Gaps: U ranges over the 48 named `Sys` only (no user-built UnitSystem); no negative/`Rational` power (`q^-2`, `q^(3//2)`); no `log/exp/Number^q`; no `Quantity{A}/Quantity{B}` → ConvertUnit; no dimensionless `q ± Number`; no `Quantity * ConvertUnit` (right) | M | P1 |
| `R` | `USQ.R` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `RankineSystem` | `UnitSystems.RankineSystem` instantiated at `Scalar` | DONE | generic over `UnitAlg` | — | — |
| `Ratio` | `Similitude.ratio` / `ratio?` (Similitude/Ratio.lean) | DONE | ratios.json (exact show + bits) + cocycle property tests | — | — |
| `Rydberg` | `Sys.Rydberg.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Rydberg Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `SI` | `Sys.ofName? "SI"` → `Sys.SI2019` | PARTIAL | alias not a Lean identifier | S | P2 |
| `SI1976` | `Sys.SI1976.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.SI1976 Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `SI2019` | `Sys.SI2019.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.SI2019 Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `Schrodinger` | `Sys.Schrodinger.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Schrodinger Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `Similitude` | `Similitude` (lib) | SKIP | module name | — | — |
| `Stoney` | `Sys.Stoney.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Stoney Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `Survey` | `Sys.Survey.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Survey Scalar` | DONE | exercised by ratios/system_constants/homs goldens | — | — |
| `T` | `USQ.T` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `Unified` | `usqMap`, `showDimUnified` (Similitude/Hom.lean, Registry.lean) | PARTIAL | isomorphism and display tested (unified.json); `Unified` is not a `Sys`, so `Quantity .Unified d` / conversions to Unified are impossible | S | P2 |
| `UnitSystems` | `UnitSystems` (lib) | SKIP | module name | — | — |
| `Universe` | `UnitSystems.Universe Scalar` (exact `Coupling`, UnitSystems/System.lean) | DONE | exact coupling groups (constants.json named `αG`) | — | — |
| `abampere` | `Similitude.Units.abampere` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `abcoulomb` | `Similitude.Units.abcoulomb` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `abfarad` | `Similitude.Units.abfarad` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `abhenry` | `Similitude.Units.abhenry` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `abmho` | `Similitude.Units.abmho` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `abohm` | `Similitude.Units.abohm` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `abvolt` | `Similitude.Units.abvolt` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `acceleration` | `Dim.acceleration` (UnitSystems/Dim.lean), `Conv.acceleration.dim`; `d(U,S)` = `Dim.acceleration.conv U S`, `d(U)` = `naturalUnit U Dim.acceleration` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `acre` | `Similitude.Units.acre` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `action` | `Dim.action` (UnitSystems/Dim.lean), `Conv.action.dim`; `d(U,S)` = `Dim.action.conv U S`, `d(U)` = `naturalUnit U Dim.action` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `admiraltymile` | `Similitude.Units.admiraltymile` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `admittance` | `Dim.admittance` (UnitSystems/Dim.lean), `Conv.admittance.dim`; `d(U,S)` = `Dim.admittance.conv U S`, `d(U)` = `naturalUnit U Dim.admittance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `amagat` | `Similitude.Units.amagat` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `ampere` | `Similitude.Units.ampere` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `angstrom` | `Similitude.Units.angstrom` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `angulararea` | `Dim.angulararea` (UnitSystems/Dim.lean), `Conv.angulararea.dim`; `d(U,S)` = `Dim.angulararea.conv U S`, `d(U)` = `naturalUnit U Dim.angulararea` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `angularfrequency` | `Dim.angularfrequency` (UnitSystems/Dim.lean), `Conv.angularfrequency.dim`; `d(U,S)` = `Dim.angularfrequency.conv U S`, `d(U)` = `naturalUnit U Dim.angularfrequency` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `angularlength` | `Dim.angularlength` (UnitSystems/Dim.lean), `Conv.angularlength.dim`; `d(U,S)` = `Dim.angularlength.conv U S`, `d(U)` = `naturalUnit U Dim.angularlength` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `angularmomentum` | `Dim.angularmomentum` (UnitSystems/Dim.lean), `Conv.angularmomentum.dim`; `d(U,S)` = `Dim.angularmomentum.conv U S`, `d(U)` = `naturalUnit U Dim.angularmomentum` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `angulartime` | `Dim.angulartime` (UnitSystems/Dim.lean), `Conv.angulartime.dim`; `d(U,S)` = `Dim.angulartime.conv U S`, `d(U)` = `naturalUnit U Dim.angulartime` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `angularwavenumber` | `Dim.angularwavenumber` (UnitSystems/Dim.lean), `Conv.angularwavenumber.dim`; `d(U,S)` = `Dim.angularwavenumber.conv U S`, `d(U)` = `naturalUnit U Dim.angularwavenumber` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `apm` | `Similitude.Units.apm` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `apostilb` | `Similitude.Units.apostilb` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `arcminute` | `Similitude.Units.arcminute` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `arcsecond` | `Similitude.Units.arcsecond` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `area` | `Dim.area` (UnitSystems/Dim.lean), `Conv.area.dim`; `d(U,S)` = `Dim.area.conv U S`, `d(U)` = `naturalUnit U Dim.area` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `areadensity` | `Dim.areadensity` (UnitSystems/Dim.lean), `Conv.areadensity.dim`; `d(U,S)` = `Dim.areadensity.conv U S`, `d(U)` = `naturalUnit U Dim.areadensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `astronomicalunit` | `Similitude.Units.astronomicalunit` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `atmosphere` | `Similitude.Units.atmosphere` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `avogadro` | `Similitude.avogadro (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `bar` | `Similitude.Units.bar` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `barn` | `Similitude.Units.barn` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `barye` | `Similitude.Units.barye` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `bel` | — | MISSING | `U(𝟏, log(𝟙))`, `U(𝟏, log10(𝟙))`, `U(𝟏, dB(𝟙))`: typed `Dim` has no LogGroup dimensions, so log-valued quantities cannot be formed (README lists these units) | M | P1 |
| `biotsavart` | `Similitude.biotsavart (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `bohr` | `Similitude.bohr (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `boilerhorsepower` | `Similitude.Units.boilerhorsepower` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `boiling` | `Similitude.Units.boiling` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `boltzmann` | `Similitude.boltzmann (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `bradian` | `Similitude.Units.bradian` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `bril` | `Similitude.Units.bril` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `bubnoff` | `Similitude.Units.bubnoff` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `calorie` | `Similitude.Units.calorie` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `candela` | `Similitude.Units.candela` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `capacitance` | `Dim.capacitance` (UnitSystems/Dim.lean), `Conv.capacitance.dim`; `d(U,S)` = `Dim.capacitance.conv U S`, `d(U)` = `naturalUnit U Dim.capacitance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `catalysis` | `Dim.catalysis` (UnitSystems/Dim.lean), `Conv.catalysis.dim`; `d(U,S)` = `Dim.catalysis.conv U S`, `d(U)` = `naturalUnit U Dim.catalysis` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `celsius` | `Similitude.Units.celsius` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `charge` | `Dim.charge` (UnitSystems/Dim.lean), `Conv.charge.dim`; `d(U,S)` = `Dim.charge.conv U S`, `d(U)` = `naturalUnit U Dim.charge` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `chargedensity` | `Dim.chargedensity` (UnitSystems/Dim.lean), `Conv.chargedensity.dim`; `d(U,S)` = `Dim.chargedensity.conv U S`, `d(U)` = `naturalUnit U Dim.chargedensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `compliance` | `Dim.compliance` (UnitSystems/Dim.lean), `Conv.compliance.dim`; `d(U,S)` = `Dim.compliance.conv U S`, `d(U)` = `naturalUnit U Dim.compliance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `compressibility` | `Dim.compressibility` (UnitSystems/Dim.lean), `Conv.compressibility.dim`; `d(U,S)` = `Dim.compressibility.conv U S`, `d(U)` = `naturalUnit U Dim.compressibility` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `conductance` | `Dim.conductance` (UnitSystems/Dim.lean), `Conv.conductance.dim`; `d(U,S)` = `Dim.conductance.conv U S`, `d(U)` = `naturalUnit U Dim.conductance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `conductancequantum` | `Similitude.conductancequantum (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `conductivity` | `Dim.conductivity` (UnitSystems/Dim.lean), `Conv.conductivity.dim`; `d(U,S)` = `Dim.conductivity.conv U S`, `d(U)` = `naturalUnit U Dim.conductivity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `cosmological` | `Similitude.Units.cosmological` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `coulomb` | `Similitude.Units.coulomb` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `coupling` | `UnitSystems.coupling (Sys.consts U)` (exact group) | DONE | generic formula; Scalar instantiation tested through system constants | — | — |
| `crackle` | `Dim.crackle` (UnitSystems/Dim.lean), `Conv.crackle.dim`; `d(U,S)` = `Dim.crackle.conv U S`, `d(U)` = `naturalUnit U Dim.crackle` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `cup` | `Similitude.Units.cup` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `curie` | `Similitude.Units.curie` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `current` | `Dim.current` (UnitSystems/Dim.lean), `Conv.current.dim`; `d(U,S)` = `Dim.current.conv U S`, `d(U)` = `naturalUnit U Dim.current` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `currentdensity` | `Dim.currentdensity` (UnitSystems/Dim.lean), `Conv.currentdensity.dim`; `d(U,S)` = `Dim.currentdensity.conv U S`, `d(U)` = `naturalUnit U Dim.currentdensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `dB` | `FieldConstants.logdb/expdb/dB` (numbers), `Group.logdb` (groups) | PARTIAL | `logdb(::Quantity)` (value and LogGroup dimension) missing, same root cause as neper/bel/decibel | M | P2 |
| `dalton` | `Similitude.dalton (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `darcy` | `Similitude.Units.darcy` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `darkenergydensity` | `UnitSystems.darkenergydensity (Sys.consts U)` (exact group) | DONE | generic formula; Scalar instantiation tested through system constants | — | — |
| `day` | `Similitude.Units.day` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `decibel` | — | MISSING | `U(𝟏, log(𝟙))`, `U(𝟏, log10(𝟙))`, `U(𝟏, dB(𝟙))`: typed `Dim` has no LogGroup dimensions, so log-valued quantities cannot be formed (README lists these units) | M | P1 |
| `degree` | `Similitude.Units.degree` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `demagnetizingfactor` | `Dim.demagnetizingfactor` (UnitSystems/Dim.lean), `Conv.demagnetizingfactor.dim`; `d(U,S)` = `Dim.demagnetizingfactor.conv U S`, `d(U)` = `naturalUnit U Dim.demagnetizingfactor` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `density` | `Dim.density` (UnitSystems/Dim.lean), `Conv.density.dim`; `d(U,S)` = `Dim.density.conv U S`, `d(U)` = `naturalUnit U Dim.density` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `diffusionflux` | `Dim.diffusionflux` (UnitSystems/Dim.lean), `Conv.diffusionflux.dim`; `d(U,S)` = `Dim.diffusionflux.conv U S`, `d(U)` = `naturalUnit U Dim.diffusionflux` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `diffusivity` | `Dim.diffusivity` (UnitSystems/Dim.lean), `Conv.diffusivity.dim`; `d(U,S)` = `Dim.diffusivity.conv U S`, `d(U)` = `naturalUnit U Dim.diffusivity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `dimensionless` | `Dim.dimensionless` (UnitSystems/Dim.lean), `Conv.dimensionless.dim`; `d(U,S)` = `Dim.dimensionless.conv U S`, `d(U)` = `naturalUnit U Dim.dimensionless` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `dimensions` | type index `d` / `Dim.toGroup` | MISSING | no value-level accessor `Quantity.dimensions : USQGroup` / `ConvertUnit.dimensions` (trivial) | S | P1 |
| `diopter` | `Similitude.Units.diopter` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `dyne` | `Similitude.Units.dyne` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `earthcalorie` | `Similitude.Units.earthcalorie` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `earthcoulomb` | `Similitude.Units.earthcoulomb` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `earthgram` | `Similitude.Units.earthgram` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `earthmass` | `Similitude.Units.earthmass` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `earthmeter` | `Similitude.Units.earthmeter` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `earthmole` | `Similitude.Units.earthmole` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `earthradius` | `Similitude.Units.earthradius` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `eddington` | `Similitude.Units.eddington` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `einstein` | `Similitude.einstein (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `electricalhorsepower` | `Similitude.Units.electricalhorsepower` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `electricdipolemoment` | `Dim.electricdipolemoment` (UnitSystems/Dim.lean), `Conv.electricdipolemoment.dim`; `d(U,S)` = `Dim.electricdipolemoment.conv U S`, `d(U)` = `naturalUnit U Dim.electricdipolemoment` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `electricdisplacement` | `Dim.electricdisplacement` (UnitSystems/Dim.lean), `Conv.electricdisplacement.dim`; `d(U,S)` = `Dim.electricdisplacement.conv U S`, `d(U)` = `naturalUnit U Dim.electricdisplacement` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `electricfield` | `Dim.electricfield` (UnitSystems/Dim.lean), `Conv.electricfield.dim`; `d(U,S)` = `Dim.electricfield.conv U S`, `d(U)` = `naturalUnit U Dim.electricfield` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `electricflux` | `Dim.electricflux` (UnitSystems/Dim.lean), `Conv.electricflux.dim`; `d(U,S)` = `Dim.electricflux.conv U S`, `d(U)` = `naturalUnit U Dim.electricflux` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `electricpolarizability` | `Dim.electricpolarizability` (UnitSystems/Dim.lean), `Conv.electricpolarizability.dim`; `d(U,S)` = `Dim.electricpolarizability.conv U S`, `d(U)` = `naturalUnit U Dim.electricpolarizability` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `electricpotential` | `Dim.electricpotential` (UnitSystems/Dim.lean), `Conv.electricpotential.dim`; `d(U,S)` = `Dim.electricpotential.conv U S`, `d(U)` = `naturalUnit U Dim.electricpotential` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `electronmass` | `Similitude.electronmass (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `electronradius` | `Similitude.electronradius (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `electronunit` | `UnitSystems.electronunit (Sys.consts U)` (exact group) | DONE | generic formula; Scalar instantiation tested through system constants | — | — |
| `electronvolt` | `Similitude.Units.electronvolt` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `electrostatic` | `Similitude.electrostatic (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `elementarycharge` | `Similitude.elementarycharge (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `energy` | `Dim.energy` (UnitSystems/Dim.lean), `Conv.energy.dim`; `d(U,S)` = `Dim.energy.conv U S`, `d(U)` = `naturalUnit U Dim.energy` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `entropy` | `Dim.entropy` (UnitSystems/Dim.lean), `Conv.entropy.dim`; `d(U,S)` = `Dim.entropy.conv U S`, `d(U)` = `naturalUnit U Dim.entropy` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `eotvos` | `Similitude.Units.eotvos` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `erg` | `Similitude.Units.erg` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `etendue` | `Dim.etendue` (UnitSystems/Dim.lean), `Conv.etendue.dim`; `d(U,S)` = `Dim.etendue.conv U S`, `d(U)` = `naturalUnit U Dim.etendue` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `expdb` | `FieldConstants.logdb/expdb/dB` (numbers), `Group.logdb` (groups) | PARTIAL | `logdb(::Quantity)` (value and LogGroup dimension) missing, same root cause as neper/bel/decibel | M | P2 |
| `exposure` | `Dim.exposure` (UnitSystems/Dim.lean), `Conv.exposure.dim`; `d(U,S)` = `Dim.exposure.conv U S`, `d(U)` = `naturalUnit U Dim.exposure` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `factorize` | `Consts.factorize`, `Consts.factorizeF` (Similitude/Constants.lean) | DONE | constants.json factorize_int/float | — | — |
| `fahrenheit` | `Similitude.Units.fahrenheit` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `farad` | `Similitude.Units.farad` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `faraday` | `Similitude.faraday (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `finestructure` | `UnitSystems.finestructure (Sys.consts U)` (exact group) | DONE | generic formula; Scalar instantiation tested through system constants | — | — |
| `flick` | `Similitude.Units.flick` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `fluence` | `Dim.fluence` (UnitSystems/Dim.lean), `Conv.fluence.dim`; `d(U,S)` = `Dim.fluence.conv U S`, `d(U)` = `naturalUnit U Dim.fluence` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `fluidounce` | `Similitude.Units.fluidounce` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `foot` | `Similitude.Units.foot` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `footcandle` | `Similitude.Units.footcandle` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `footlambert` | `Similitude.Units.footlambert` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `footpound` | `Similitude.Units.footpound` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `force` | `Dim.force` (UnitSystems/Dim.lean), `Conv.force.dim`; `d(U,S)` = `Dim.force.conv U S`, `d(U)` = `naturalUnit U Dim.force` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `fpm` | `Similitude.Units.fpm` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `fps` | `Similitude.Units.fps` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `frequency` | `Dim.frequency` (UnitSystems/Dim.lean), `Conv.frequency.dim`; `d(U,S)` = `Dim.frequency.conv U S`, `d(U)` = `naturalUnit U Dim.frequency` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `frequencydrift` | `Dim.frequencydrift` (UnitSystems/Dim.lean), `Conv.frequencydrift.dim`; `d(U,S)` = `Dim.frequencydrift.conv U S`, `d(U)` = `naturalUnit U Dim.frequencydrift` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `fuelefficiency` | `Dim.fuelefficiency` (UnitSystems/Dim.lean), `Conv.fuelefficiency.dim`; `d(U,S)` = `Dim.fuelefficiency.conv U S`, `d(U)` = `naturalUnit U Dim.fuelefficiency` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `galileo` | `Similitude.Units.galileo` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `gallon` | `Similitude.Units.gallon` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `gasgallon` | `Similitude.Units.gasgallon` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `gauss` | `Similitude.Units.gauss` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `gaussgravitation` | `Similitude.Units.gaussgravitation` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `gaussianmonth` | `Similitude.Units.gaussianmonth` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `gaussianyear` | `Similitude.Units.gaussianyear` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `gforce` | `Similitude.Units.gforce` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `gilbert` | `Similitude.Units.gilbert` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `gradian` | `Similitude.Units.gradian` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `grain` | `Similitude.Units.grain` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `gram` | `Similitude.Units.gram` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `gravitation` | `Similitude.gravitation (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `gravity` | `Similitude.gravity (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `gravityforce` | `Dim.gravityforce` (UnitSystems/Dim.lean), `Conv.gravityforce.dim`; `d(U,S)` = `Dim.gravityforce.conv U S`, `d(U)` = `naturalUnit U Dim.gravityforce` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `gray` | `Similitude.Units.gray` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `greatcircle` | `Similitude.Units.greatcircle` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `hartree` | `Similitude.hartree (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `hectare` | `Similitude.Units.hectare` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `henry` | `Similitude.Units.henry` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `hertz` | `Similitude.Units.hertz` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `horsepower` | `Similitude.Units.horsepower` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `horsepowermetric` | `Similitude.Units.horsepowermetric` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `horsepowerwatt` | `Similitude.Units.horsepowerwatt` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `hour` | `Similitude.Units.hour` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `hubble` | `Similitude.Units.hubble` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `hyl` | `Similitude.Units.hyl` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `hyperfine` | `Similitude.Units.hyperfine` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `illuminance` | `Dim.illuminance` (UnitSystems/Dim.lean), `Conv.illuminance.dim`; `d(U,S)` = `Dim.illuminance.conv U S`, `d(U)` = `naturalUnit U Dim.illuminance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `impedance` | `Dim.impedance` (UnitSystems/Dim.lean), `Conv.impedance.dim`; `d(U,S)` = `Dim.impedance.conv U S`, `d(U)` = `naturalUnit U Dim.impedance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `impulse` | `Dim.impulse` (UnitSystems/Dim.lean), `Conv.impulse.dim`; `d(U,S)` = `Dim.impulse.conv U S`, `d(U)` = `naturalUnit U Dim.impulse` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `inch` | `Similitude.Units.inch` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `inchmercury` | `Similitude.Units.inchmercury` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `inductance` | `Dim.inductance` (UnitSystems/Dim.lean), `Conv.inductance.dim`; `d(U,S)` = `Dim.inductance.conv U S`, `d(U)` = `naturalUnit U Dim.inductance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `inertance` | `Dim.inertance` (UnitSystems/Dim.lean), `Conv.inertance.dim`; `d(U,S)` = `Dim.inertance.conv U S`, `d(U)` = `naturalUnit U Dim.inertance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `inertia` | `Dim.inertia` (UnitSystems/Dim.lean), `Conv.inertia.dim`; `d(U,S)` = `Dim.inertia.conv U S`, `d(U)` = `naturalUnit U Dim.inertia` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `ips` | `Similitude.Units.ips` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `irradiance` | `Dim.irradiance` (UnitSystems/Dim.lean), `Conv.irradiance.dim`; `d(U,S)` = `Dim.irradiance.conv U S`, `d(U)` = `naturalUnit U Dim.irradiance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `jansky` | `Similitude.Units.jansky` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `jerk` | `Dim.jerk` (UnitSystems/Dim.lean), `Conv.jerk.dim`; `d(U,S)` = `Dim.jerk.conv U S`, `d(U)` = `naturalUnit U Dim.jerk` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `josephson` | `Similitude.josephson (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `joule` | `Similitude.Units.joule` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `jovianyear` | `Similitude.Units.jovianyear` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `jupiterdistance` | `Similitude.Units.jupiterdistance` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `jupitermass` | `Similitude.Units.jupitermass` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `katal` | `Similitude.Units.katal` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `kayser` | `Similitude.Units.kayser` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `kelvin` | `Similitude.Units.kelvin` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `kilocalorie` | `Similitude.Units.kilocalorie` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `kilogram` | `Similitude.Units.kilogram` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `kilopond` | `Similitude.Units.kilopond` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `klitzing` | `Similitude.klitzing (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `kmh` | `Similitude.Units.kmh` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `knot` | `Similitude.Units.knot` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `lambert` | `Similitude.Units.lambert` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `langley` | `Similitude.Units.langley` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `lapserate` | `Dim.lapserate` (UnitSystems/Dim.lean), `Conv.lapserate.dim`; `d(U,S)` = `Dim.lapserate.conv U S`, `d(U)` = `naturalUnit U Dim.lapserate` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `lightspeed` | `Similitude.lightspeed (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `lightyear` | `Similitude.Units.lightyear` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `linearchargedensity` | `Dim.linearchargedensity` (UnitSystems/Dim.lean), `Conv.linearchargedensity.dim`; `d(U,S)` = `Dim.linearchargedensity.conv U S`, `d(U)` = `naturalUnit U Dim.linearchargedensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `lineardensity` | `Dim.lineardensity` (UnitSystems/Dim.lean), `Conv.lineardensity.dim`; `d(U,S)` = `Dim.lineardensity.conv U S`, `d(U)` = `naturalUnit U Dim.lineardensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `liter` | `Similitude.Units.liter` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `logdb` | `FieldConstants.logdb/expdb/dB` (numbers), `Group.logdb` (groups) | PARTIAL | `logdb(::Quantity)` (value and LogGroup dimension) missing, same root cause as neper/bel/decibel | M | P2 |
| `lorentz` | `Similitude.lorentz (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `loschmidt` | `Similitude.Units.loschmidt` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `lumen` | `Similitude.Units.lumen` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `lumerg` | `Similitude.Units.lumerg` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `luminance` | `Dim.luminance` (UnitSystems/Dim.lean), `Conv.luminance.dim`; `d(U,S)` = `Dim.luminance.conv U S`, `d(U)` = `naturalUnit U Dim.luminance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `luminousefficacy` | `Similitude.luminousefficacy (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `luminousenergy` | `Dim.luminousenergy` (UnitSystems/Dim.lean), `Conv.luminousenergy.dim`; `d(U,S)` = `Dim.luminousenergy.conv U S`, `d(U)` = `naturalUnit U Dim.luminousenergy` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `luminousexposure` | `Dim.luminousexposure` (UnitSystems/Dim.lean), `Conv.luminousexposure.dim`; `d(U,S)` = `Dim.luminousexposure.conv U S`, `d(U)` = `naturalUnit U Dim.luminousexposure` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `luminousflux` | `Dim.luminousflux` (UnitSystems/Dim.lean), `Conv.luminousflux.dim`; `d(U,S)` = `Dim.luminousflux.conv U S`, `d(U)` = `naturalUnit U Dim.luminousflux` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `luminousintensity` | `Dim.luminousintensity` (UnitSystems/Dim.lean), `Conv.luminousintensity.dim`; `d(U,S)` = `Dim.luminousintensity.conv U S`, `d(U)` = `naturalUnit U Dim.luminousintensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `lunardistance` | `Similitude.Units.lunardistance` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `lunarmass` | `Similitude.Units.lunarmass` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `lux` | `Similitude.Units.lux` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `magneticdipolemoment` | `Dim.magneticdipolemoment` (UnitSystems/Dim.lean), `Conv.magneticdipolemoment.dim`; `d(U,S)` = `Dim.magneticdipolemoment.conv U S`, `d(U)` = `naturalUnit U Dim.magneticdipolemoment` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `magneticfield` | `Dim.magneticfield` (UnitSystems/Dim.lean), `Conv.magneticfield.dim`; `d(U,S)` = `Dim.magneticfield.conv U S`, `d(U)` = `naturalUnit U Dim.magneticfield` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `magneticflux` | `Dim.magneticflux` (UnitSystems/Dim.lean), `Conv.magneticflux.dim`; `d(U,S)` = `Dim.magneticflux.conv U S`, `d(U)` = `naturalUnit U Dim.magneticflux` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `magneticfluxdensity` | `Dim.magneticfluxdensity` (UnitSystems/Dim.lean), `Conv.magneticfluxdensity.dim`; `d(U,S)` = `Dim.magneticfluxdensity.conv U S`, `d(U)` = `naturalUnit U Dim.magneticfluxdensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `magneticfluxquantum` | `Similitude.magneticfluxquantum (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `magneticmoment` | `Dim.magneticmoment` (UnitSystems/Dim.lean), `Conv.magneticmoment.dim`; `d(U,S)` = `Dim.magneticmoment.conv U S`, `d(U)` = `naturalUnit U Dim.magneticmoment` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `magneticpolarizability` | `Dim.magneticpolarizability` (UnitSystems/Dim.lean), `Conv.magneticpolarizability.dim`; `d(U,S)` = `Dim.magneticpolarizability.conv U S`, `d(U)` = `naturalUnit U Dim.magneticpolarizability` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `magneticpotential` | `Dim.magneticpotential` (UnitSystems/Dim.lean), `Conv.magneticpotential.dim`; `d(U,S)` = `Dim.magneticpotential.conv U S`, `d(U)` = `naturalUnit U Dim.magneticpotential` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `magneton` | `Similitude.magneton (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `magnetostatic` | `Similitude.magnetostatic (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `mass` | `Dim.mass` (UnitSystems/Dim.lean), `Conv.mass.dim`; `d(U,S)` = `Dim.mass.conv U S`, `d(U)` = `naturalUnit U Dim.mass` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `massflow` | `Dim.massflow` (UnitSystems/Dim.lean), `Conv.massflow.dim`; `d(U,S)` = `Dim.massflow.conv U S`, `d(U)` = `naturalUnit U Dim.massflow` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `maxwell` | `Similitude.Units.maxwell` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `meancalorie` | `Similitude.Units.meancalorie` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `mechanicalheat` | `Similitude.Units.mechanicalheat` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `meridianmile` | `Similitude.Units.meridianmile` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `meter` | `Similitude.Units.meter` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `mile` | `Similitude.Units.mile` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `minute` | `Similitude.Units.minute` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `mobility` | `Dim.mobility` (UnitSystems/Dim.lean), `Conv.mobility.dim`; `d(U,S)` = `Dim.mobility.conv U S`, `d(U)` = `naturalUnit U Dim.mobility` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `molality` | `Dim.molality` (UnitSystems/Dim.lean), `Conv.molality.dim`; `d(U,S)` = `Dim.molality.conv U S`, `d(U)` = `naturalUnit U Dim.molality` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `molaramount` | `Dim.molaramount` (UnitSystems/Dim.lean), `Conv.molaramount.dim`; `d(U,S)` = `Dim.molaramount.conv U S`, `d(U)` = `naturalUnit U Dim.molaramount` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `molarconductivity` | `Dim.molarconductivity` (UnitSystems/Dim.lean), `Conv.molarconductivity.dim`; `d(U,S)` = `Dim.molarconductivity.conv U S`, `d(U)` = `naturalUnit U Dim.molarconductivity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `molarenergy` | `Dim.molarenergy` (UnitSystems/Dim.lean), `Conv.molarenergy.dim`; `d(U,S)` = `Dim.molarenergy.conv U S`, `d(U)` = `naturalUnit U Dim.molarenergy` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `molarentropy` | `Dim.molarentropy` (UnitSystems/Dim.lean), `Conv.molarentropy.dim`; `d(U,S)` = `Dim.molarentropy.conv U S`, `d(U)` = `naturalUnit U Dim.molarentropy` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `molargas` | `Similitude.molargas (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `molarity` | `Dim.molarity` (UnitSystems/Dim.lean), `Conv.molarity.dim`; `d(U,S)` = `Dim.molarity.conv U S`, `d(U)` = `naturalUnit U Dim.molarity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `molarmass` | `Similitude.molarmass (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `molarsusceptibility` | `Dim.molarsusceptibility` (UnitSystems/Dim.lean), `Conv.molarsusceptibility.dim`; `d(U,S)` = `Dim.molarsusceptibility.conv U S`, `d(U)` = `naturalUnit U Dim.molarsusceptibility` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `molarvolume` | `Dim.molarvolume` (UnitSystems/Dim.lean), `Conv.molarvolume.dim`; `d(U,S)` = `Dim.molarvolume.conv U S`, `d(U)` = `naturalUnit U Dim.molarvolume` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `mole` | `Similitude.Units.mole` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `momentum` | `Dim.momentum` (UnitSystems/Dim.lean), `Conv.momentum.dim`; `d(U,S)` = `Dim.momentum.conv U S`, `d(U)` = `naturalUnit U Dim.momentum` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `mpge` | `Similitude.Units.mpge` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `mph` | `Similitude.Units.mph` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `mps` | `Similitude.Units.mps` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `ms` | `Similitude.Units.ms` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `nauticalmile` | `Similitude.Units.nauticalmile` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `neper` | — | MISSING | `U(𝟏, log(𝟙))`, `U(𝟏, log10(𝟙))`, `U(𝟏, dB(𝟙))`: typed `Dim` has no LogGroup dimensions, so log-valued quantities cannot be formed (README lists these units) | M | P1 |
| `newton` | `Similitude.Units.newton` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `nit` | `Similitude.Units.nit` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `normal` | `Quantity.normal` | DONE | value projection | — | — |
| `numberdensity` | `Dim.numberdensity` (UnitSystems/Dim.lean), `Conv.numberdensity.dim`; `d(U,S)` = `Dim.numberdensity.conv U S`, `d(U)` = `naturalUnit U Dim.numberdensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `oersted` | `Similitude.Units.oersted` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `ohm` | `Similitude.Units.ohm` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `ounce` | `Similitude.Units.ounce` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `parsec` | `Similitude.Units.parsec` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `pascal` | `Similitude.Units.pascal` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `permeability` | `Dim.permeability` (UnitSystems/Dim.lean), `Conv.permeability.dim`; `d(U,S)` = `Dim.permeability.conv U S`, `d(U)` = `naturalUnit U Dim.permeability` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `permeance` | `Dim.permeance` (UnitSystems/Dim.lean), `Conv.permeance.dim`; `d(U,S)` = `Dim.permeance.conv U S`, `d(U)` = `naturalUnit U Dim.permeance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `permittivity` | `Dim.permittivity` (UnitSystems/Dim.lean), `Conv.permittivity.dim`; `d(U,S)` = `Dim.permittivity.conv U S`, `d(U)` = `naturalUnit U Dim.permittivity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `phot` | `Similitude.Units.phot` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `photonintensity` | `Dim.photonintensity` (UnitSystems/Dim.lean), `Conv.photonintensity.dim`; `d(U,S)` = `Dim.photonintensity.conv U S`, `d(U)` = `naturalUnit U Dim.photonintensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `photonirradiance` | `Dim.photonirradiance` (UnitSystems/Dim.lean), `Conv.photonirradiance.dim`; `d(U,S)` = `Dim.photonirradiance.conv U S`, `d(U)` = `naturalUnit U Dim.photonirradiance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `photonradiance` | `Dim.photonradiance` (UnitSystems/Dim.lean), `Conv.photonradiance.dim`; `d(U,S)` = `Dim.photonradiance.conv U S`, `d(U)` = `naturalUnit U Dim.photonradiance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `pint` | `Similitude.Units.pint` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `planck` | `Similitude.planck (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `planckmass` | `Similitude.planckmass (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `planckreduced` | `Similitude.planckreduced (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `poise` | `Similitude.Units.poise` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `polestrength` | `Dim.polestrength` (UnitSystems/Dim.lean), `Conv.polestrength.dim`; `d(U,S)` = `Dim.polestrength.conv U S`, `d(U)` = `naturalUnit U Dim.polestrength` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `pop` | `Dim.pop` (UnitSystems/Dim.lean), `Conv.pop.dim`; `d(U,S)` = `Dim.pop.conv U S`, `d(U)` = `naturalUnit U Dim.pop` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `pound` | `Similitude.Units.pound` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `poundal` | `Similitude.Units.poundal` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `poundforce` | `Similitude.Units.poundforce` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `poundmole` | `Similitude.Units.poundmole` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `power` | `Dim.power` (UnitSystems/Dim.lean), `Conv.power.dim`; `d(U,S)` = `Dim.power.conv U S`, `d(U)` = `naturalUnit U Dim.power` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `powerdensity` | `Dim.powerdensity` (UnitSystems/Dim.lean), `Conv.powerdensity.dim`; `d(U,S)` = `Dim.powerdensity.conv U S`, `d(U)` = `naturalUnit U Dim.powerdensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `pressure` | `Dim.pressure` (UnitSystems/Dim.lean), `Conv.pressure.dim`; `d(U,S)` = `Dim.pressure.conv U S`, `d(U)` = `naturalUnit U Dim.pressure` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `protonelectron` | `UnitSystems.protonelectron (Sys.consts U)` (exact group) | DONE | generic formula; Scalar instantiation tested through system constants | — | — |
| `protonmass` | `Similitude.protonmass (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `protonunit` | `UnitSystems.protonunit (Sys.consts U)` (exact group) | DONE | generic formula; Scalar instantiation tested through system constants | — | — |
| `psi` | `Similitude.Units.psi` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `quart` | `Similitude.Units.quart` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `quotient` | `Similitude.quotient`, `printQuotient` (Similitude/Quotient.lean) | DONE | quotients.json (48 systems) | — | — |
| `radarmile` | `Similitude.Units.radarmile` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `radian` | `Similitude.radian (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `radiance` | `Dim.radiance` (UnitSystems/Dim.lean), `Conv.radiance.dim`; `d(U,S)` = `Dim.radiance.conv U S`, `d(U)` = `naturalUnit U Dim.radiance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `radiantintensity` | `Dim.radiantintensity` (UnitSystems/Dim.lean), `Conv.radiantintensity.dim`; `d(U,S)` = `Dim.radiantintensity.conv U S`, `d(U)` = `naturalUnit U Dim.radiantintensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `radiationdensity` | `Similitude.radiationdensity (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `rankine` | `Similitude.Units.rankine` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `rationalization` | `Similitude.rationalization (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `rayl` | `Similitude.Units.rayl` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `rayleigh` | `Similitude.Units.rayleigh` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `reluctance` | `Dim.reluctance` (UnitSystems/Dim.lean), `Conv.reluctance.dim`; `d(U,S)` = `Dim.reluctance.conv U S`, `d(U)` = `naturalUnit U Dim.reluctance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `rem` | — | SKIP | `Base.rem` in Julia (calling it on a system errors) | — | — |
| `resistance` | `Dim.resistance` (UnitSystems/Dim.lean), `Conv.resistance.dim`; `d(U,S)` = `Dim.resistance.conv U S`, `d(U)` = `naturalUnit U Dim.resistance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `resistivity` | `Dim.resistivity` (UnitSystems/Dim.lean), `Conv.resistivity.dim`; `d(U,S)` = `Dim.resistivity.conv U S`, `d(U)` = `naturalUnit U Dim.resistivity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `reyn` | `Similitude.Units.reyn` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `roentgen` | `Similitude.Units.roentgen` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `rotationalinertia` | `Dim.rotationalinertia` (UnitSystems/Dim.lean), `Conv.rotationalinertia.dim`; `d(U,S)` = `Dim.rotationalinertia.conv U S`, `d(U)` = `naturalUnit U Dim.rotationalinertia` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `rpm` | `Similitude.Units.rpm` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `rydberg` | `Similitude.rydberg (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `sealevel` | `Similitude.Units.sealevel` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `second` | `Similitude.Units.second` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `siderealmonth` | `Similitude.Units.siderealmonth` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `siderealyear` | `Similitude.Units.siderealyear` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `siemens` | `Similitude.Units.siemens` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `slinch` | `Similitude.Units.slinch` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `slinchmole` | `Similitude.Units.slinchmole` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `slug` | `Similitude.Units.slug` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `slugmole` | `Similitude.Units.slugmole` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `snap` | `Dim.snap` (UnitSystems/Dim.lean), `Conv.snap.dim`; `d(U,S)` = `Dim.snap.conv U S`, `d(U)` = `naturalUnit U Dim.snap` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `solarflux` | `Similitude.Units.solarflux` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `solarmass` | `Similitude.Units.solarmass` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `solidangle` | `Dim.solidangle` (UnitSystems/Dim.lean), `Conv.solidangle.dim`; `d(U,S)` = `Dim.solidangle.conv U S`, `d(U)` = `naturalUnit U Dim.solidangle` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `soundexposure` | `Dim.soundexposure` (UnitSystems/Dim.lean), `Conv.soundexposure.dim`; `d(U,S)` = `Dim.soundexposure.conv U S`, `d(U)` = `naturalUnit U Dim.soundexposure` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `spat` | `Similitude.spat (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `spatian` | `Similitude.Units.spatian` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `specificenergy` | `Dim.specificenergy` (UnitSystems/Dim.lean), `Conv.specificenergy.dim`; `d(U,S)` = `Dim.specificenergy.conv U S`, `d(U)` = `naturalUnit U Dim.specificenergy` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `specificentropy` | `Dim.specificentropy` (UnitSystems/Dim.lean), `Conv.specificentropy.dim`; `d(U,S)` = `Dim.specificentropy.conv U S`, `d(U)` = `naturalUnit U Dim.specificentropy` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `specificforce` | `Dim.specificforce` (UnitSystems/Dim.lean), `Conv.specificforce.dim`; `d(U,S)` = `Dim.specificforce.conv U S`, `d(U)` = `naturalUnit U Dim.specificforce` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `specificimpedance` | `Dim.specificimpedance` (UnitSystems/Dim.lean), `Conv.specificimpedance.dim`; `d(U,S)` = `Dim.specificimpedance.conv U S`, `d(U)` = `naturalUnit U Dim.specificimpedance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `specificity` | `Dim.specificity` (UnitSystems/Dim.lean), `Conv.specificity.dim`; `d(U,S)` = `Dim.specificity.conv U S`, `d(U)` = `naturalUnit U Dim.specificity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `specificmagnetization` | `Dim.specificmagnetization` (UnitSystems/Dim.lean), `Conv.specificmagnetization.dim`; `d(U,S)` = `Dim.specificmagnetization.conv U S`, `d(U)` = `naturalUnit U Dim.specificmagnetization` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `specificsusceptibility` | `Dim.specificsusceptibility` (UnitSystems/Dim.lean), `Conv.specificsusceptibility.dim`; `d(U,S)` = `Dim.specificsusceptibility.conv U S`, `d(U)` = `naturalUnit U Dim.specificsusceptibility` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `specificvolume` | `Dim.specificvolume` (UnitSystems/Dim.lean), `Conv.specificvolume.dim`; `d(U,S)` = `Dim.specificvolume.conv U S`, `d(U)` = `naturalUnit U Dim.specificvolume` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `specificweight` | `Dim.specificweight` (UnitSystems/Dim.lean), `Conv.specificweight.dim`; `d(U,S)` = `Dim.specificweight.conv U S`, `d(U)` = `naturalUnit U Dim.specificweight` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `spectralexposure` | `Dim.spectralexposure` (UnitSystems/Dim.lean), `Conv.spectralexposure.dim`; `d(U,S)` = `Dim.spectralexposure.conv U S`, `d(U)` = `naturalUnit U Dim.spectralexposure` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `spectralflux` | `Dim.spectralflux` (UnitSystems/Dim.lean), `Conv.spectralflux.dim`; `d(U,S)` = `Dim.spectralflux.conv U S`, `d(U)` = `naturalUnit U Dim.spectralflux` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `speed` | `Dim.speed` (UnitSystems/Dim.lean), `Conv.speed.dim`; `d(U,S)` = `Dim.speed.conv U S`, `d(U)` = `naturalUnit U Dim.speed` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `squaredegree` | `Similitude.Units.squaredegree` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `stagnance` | `Dim.stagnance` (UnitSystems/Dim.lean), `Conv.stagnance.dim`; `d(U,S)` = `Dim.stagnance.conv U S`, `d(U)` = `naturalUnit U Dim.stagnance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `statampere` | `Similitude.Units.statampere` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `statcoulomb` | `Similitude.Units.statcoulomb` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `statfarad` | `Similitude.Units.statfarad` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `stathenry` | `Similitude.Units.stathenry` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `statmho` | `Similitude.Units.statmho` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `statohm` | `Similitude.Units.statohm` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `stattesla` | `Similitude.Units.stattesla` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `statutemile` | `Similitude.Units.statutemile` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `statvolt` | `Similitude.Units.statvolt` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `statweber` | `Similitude.Units.statweber` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `stefan` | `Similitude.stefan (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `steradian` | `Similitude.Units.steradian` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `stilb` | `Similitude.Units.stilb` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `stokes` | `Similitude.Units.stokes` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `surveyacre` | `Similitude.Units.surveyacre` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `surveyfoot` | `Similitude.Units.surveyfoot` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `susceptibility` | `Dim.susceptibility` (UnitSystems/Dim.lean), `Conv.susceptibility.dim`; `d(U,S)` = `Dim.susceptibility.conv U S`, `d(U)` = `naturalUnit U Dim.susceptibility` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `synodicmonth` | `Similitude.Units.synodicmonth` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `tablespoon` | `Similitude.Units.tablespoon` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `talbot` | `Similitude.Units.talbot` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `teaspoon` | `Similitude.Units.teaspoon` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `technicalatmosphere` | `Similitude.Units.technicalatmosphere` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `temperature` | `Dim.temperature` (UnitSystems/Dim.lean), `Conv.temperature.dim`; `d(U,S)` = `Dim.temperature.conv U S`, `d(U)` = `naturalUnit U Dim.temperature` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `tesla` | `Similitude.Units.tesla` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `thermalconductance` | `Dim.thermalconductance` (UnitSystems/Dim.lean), `Conv.thermalconductance.dim`; `d(U,S)` = `Dim.thermalconductance.conv U S`, `d(U)` = `naturalUnit U Dim.thermalconductance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `thermalconductivity` | `Dim.thermalconductivity` (UnitSystems/Dim.lean), `Conv.thermalconductivity.dim`; `d(U,S)` = `Dim.thermalconductivity.conv U S`, `d(U)` = `naturalUnit U Dim.thermalconductivity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `thermalexpansion` | `Dim.thermalexpansion` (UnitSystems/Dim.lean), `Conv.thermalexpansion.dim`; `d(U,S)` = `Dim.thermalexpansion.conv U S`, `d(U)` = `naturalUnit U Dim.thermalexpansion` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `thermalresistance` | `Dim.thermalresistance` (UnitSystems/Dim.lean), `Conv.thermalresistance.dim`; `d(U,S)` = `Dim.thermalresistance.conv U S`, `d(U)` = `naturalUnit U Dim.thermalresistance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `thermalresistivity` | `Dim.thermalresistivity` (UnitSystems/Dim.lean), `Conv.thermalresistivity.dim`; `d(U,S)` = `Dim.thermalresistivity.conv U S`, `d(U)` = `naturalUnit U Dim.thermalresistivity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `thermalunit` | `Similitude.Units.thermalunit` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `ton` | `Similitude.Units.ton` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `tonne` | `Similitude.Units.tonne` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `tonsrefrigeration` | `Similitude.Units.tonsrefrigeration` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `tontnt` | `Similitude.Units.tontnt` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `torr` | `Similitude.Units.torr` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `turn` | `Similitude.turn (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `unitname` | `Sys.name` | DONE | homs.json unitname | — | — |
| `universe` | `UnitSystems.universeOf` | DONE | renamed | — | — |
| `vacuumimpedance` | `Similitude.vacuumimpedance (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `vacuumpermeability` | `Similitude.vacuumpermeability (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `vacuumpermittivity` | `Similitude.vacuumpermittivity (U : Sys) : Q U d` (Similitude/Physics.lean) | DONE | system_constants.json (every system); dimension proved by `decide` | — | — |
| `vectorpotential` | `Dim.vectorpotential` (UnitSystems/Dim.lean), `Conv.vectorpotential.dim`; `d(U,S)` = `Dim.vectorpotential.conv U S`, `d(U)` = `naturalUnit U Dim.vectorpotential` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `viscosity` | `Dim.viscosity` (UnitSystems/Dim.lean), `Conv.viscosity.dim`; `d(U,S)` = `Dim.viscosity.conv U S`, `d(U)` = `naturalUnit U Dim.viscosity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `volt` | `Similitude.Units.volt` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `volume` | `Dim.volume` (UnitSystems/Dim.lean), `Conv.volume.dim`; `d(U,S)` = `Dim.volume.conv U S`, `d(U)` = `naturalUnit U Dim.volume` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `volumeflow` | `Dim.volumeflow` (UnitSystems/Dim.lean), `Conv.volumeflow.dim`; `d(U,S)` = `Dim.volumeflow.conv U S`, `d(U)` = `naturalUnit U Dim.volumeflow` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `volumeheatcapacity` | `Dim.volumeheatcapacity` (UnitSystems/Dim.lean), `Conv.volumeheatcapacity.dim`; `d(U,S)` = `Dim.volumeheatcapacity.conv U S`, `d(U)` = `naturalUnit U Dim.volumeheatcapacity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `watt` | `Similitude.Units.watt` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `wavenumber` | `Dim.wavenumber` (UnitSystems/Dim.lean), `Conv.wavenumber.dim`; `d(U,S)` = `Dim.wavenumber.conv U S`, `d(U)` = `naturalUnit U Dim.wavenumber` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `weber` | `Similitude.Units.weber` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `wienfrequency` | `Similitude.Units.wienfrequency` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `wienwavelength` | `Similitude.Units.wienwavelength` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `yank` | `Dim.yank` (UnitSystems/Dim.lean), `Conv.yank.dim`; `d(U,S)` = `Dim.yank.conv U S`, `d(U)` = `naturalUnit U Dim.yank` | DONE | homs.json (48×131 images/display), unified.json, ratios.json | — | — |
| `yard` | `Similitude.Units.yard` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `year` | `Similitude.Units.year` (Similitude/Derived.lean) | DONE | derived.json (value, system, dims, Metric bits) | — | — |
| `Θ` | `USQ.Θ` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `𝟙` | `USQ.one` | DONE | dimensionless | — | — |
| `(U::UnitSystem)(v, d) / Quantity{U}(v,d)` | `Sys.qty U d v` | DONE | quantity_arith.json | — | — |
| `(S::UnitSystem)(q::Quantity), q(S)` | `Quantity.to S` | DONE | quantity_arith.json (Metric, English targets) | — | — |
| `ConvertUnit (d(U,S))` | `ConvertUnit U S d`, `Dim.conv`, `showConvert` (Similitude/Ratio.lean) | PARTIAL | ratio/show/`inv` (Julia bug fixed) tested; missing `ConvertUnit * ConvertUnit`, `/`, `log/exp`, `Quantity(c::ConvertUnit)` | S | P2 |
| `d(v::Real, U, S=Metric)` | `Conv.convert` over `Scalar` (131 named dims) or `v / ratio d U S` | PARTIAL | no direct API for an arbitrary `Dim`/`USQGroup` | S | P2 |
| `naturalunits(U)` | `naturalUnit U d` (Similitude/Quantity.lean) | DONE | extras.json (48 × 11 bases) | — | — |
| `dimlist(U), printquotient(U)` | `dimlist`, `printQuotient` (Similitude/Quotient.lean) | DONE | extras.json / quotients.json | — | — |
| `latexquotient, latexquantity, latexdimensions, isodim, unitdim(U,D), dimlistlatex, convertext, unitext, systext, unitsym, unitdict` | `Sys.latexDim` only | MISSING | LaTeX/markdown table helpers (Similitude.jl:270-362, derived.jl:442-501) not ported | M | P2 |
| `morphism(U)` | `Sys.hom` (`LinMap`) | MISSING | 11×11 matrix accessor missing (broken in Julia when CONSTDIM=false) | S | P2 |
| `evaldim` | `UnitSystems.dimOf` (DimModel.lean) + proofs | DONE | dims recovered and proved | — | — |
| `convertdim` | `convertDim` (Similitude/Ratio.lean) | DONE | ConvertUnit display goldens | — | — |
| `display(::UnitSystem) with Quantity slots` | — | MISSING | Similitude/MeasureSystems print each slot as a dimensioned quantity (`kB = 1.380649e-23 [J⋅K⁻¹] SI2019, …`); no Lean printer for `UnitSystem Scalar` | S | P2 |
| `PERF: runtime `ratio(D,U,S)`` | `Similitude.ratio` | PARTIAL | measured 269,784 ns/call (compiled) vs Julia 2,617 ns: exact `Vector Rat 44` group arithmetic per call; `Quantity.to` with literal U,S,d is hoisted (1.24 ns vs Julia 3,041 ns) | M | P1 |

## MeasureSystems.jl (v0.2.2): 680 exports

| Julia symbol | Lean name(s) + file | status | gap / evidence | effort | prio |
|---|---|---|---|---|---|
| `@unitdim` | static `unitTextData`/`dimTextTable` (Similitude/UnitNames.lean), `Sys.hom` | MISSING | registries and homomorphisms are generated constants; users cannot register unit names or a homomorphism for a new system | M | P2 |
| `@unitgroup` | static `unitTextData`/`dimTextTable` (Similitude/UnitNames.lean), `Sys.hom` | MISSING | registries and homomorphisms are generated constants; users cannot register unit names or a homomorphism for a new system | M | P2 |
| `A` | `USQ.A` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `AE` | `Sys.ofName? "AE"` → `Sys.FPS` | PARTIAL | alias not a Lean identifier | S | P2 |
| `AbelianGroup` | — | SKIP | abstract supertype | — | — |
| `AbsoluteEnglish` | `Sys.ofName? "AbsoluteEnglish"` → `Sys.FPS` | PARTIAL | alias not a Lean identifier | S | P2 |
| `AstronomicalSystem` | `UnitSystems.AstronomicalSystem` instantiated at `Scalar` | DONE | generic over `UnitAlg` | — | — |
| `BG` | `Sys.ofName? "BG"` → `Sys.British` | PARTIAL | alias not a Lean identifier | S | P2 |
| `BTUJ` | `measured (Similitude.Units.thermalunit.to .SI2019)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `BTUftlb` | `measured (Similitude.Units.thermalunit.to .British)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `British` | `Sys.British.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.British Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `BritishGravitational` | `Sys.ofName? "BritishGravitational"` → `Sys.British` | PARTIAL | alias not a Lean identifier | S | P2 |
| `C` | `USQ.C` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `CGS` | `Sys.ofName? "CGS"` → `Sys.Gauss` | PARTIAL | alias not a Lean identifier | S | P2 |
| `CGS2019` | — | SKIP | exported but undefined in Julia MeasureSystems | — | — |
| `CGSe` | `Sys.ofName? "CGSe"` → `Sys.ESU` | PARTIAL | alias not a Lean identifier | S | P2 |
| `CGSm` | `Sys.ofName? "CGSm"` → `Sys.EMU` | PARTIAL | alias not a Lean identifier | S | P2 |
| `CODATA` | `Sys.CODATA.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.CODATA Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `Constant` | `FieldConstants.Constant` | PARTIAL | see FieldConstants | S | P2 |
| `Conventional` | `Sys.Conventional.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Conventional Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `ConventionalSystem` | `UnitSystems.ConventionalSystem` instantiated at `Scalar` | DONE | generic over `UnitAlg` | — | — |
| `Cosmological` | `Sys.Cosmological.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Cosmological Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `CosmologicalQuantum` | `Sys.CosmologicalQuantum.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.CosmologicalQuantum Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `DAY` | exact group `DAY Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `Da` | `measured (Similitude.dalton .SI2019)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `Dimension` | type index `d` / `Dim.toGroup` | MISSING | no value-level accessor `Quantity.dimensions : USQGroup` / `ConvertUnit.dimensions` (trivial) | S | P1 |
| `EE` | `Sys.ofName? "EE"` → `Sys.English` | PARTIAL | alias not a Lean identifier | S | P2 |
| `EE2019` | — | SKIP | exported but undefined in Julia MeasureSystems | — | — |
| `EMU` | `Sys.EMU.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.EMU Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `ESU` | `Sys.ESU.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.ESU Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `Eh` | value exists as `Eₕ` | PARTIAL | ASCII alias not defined | S | P2 |
| `ElectricSystem` | `UnitSystems.ElectricSystem` instantiated at `Scalar` | DONE | generic over `UnitAlg` | — | — |
| `Electronic` | `Sys.Electronic.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Electronic Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `Engineering` | `Sys.Engineering.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Engineering Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `English` | `Sys.English.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.English Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `EnglishEngineering` | `Sys.ofName? "EnglishEngineering"` → `Sys.English` | PARTIAL | alias not a Lean identifier | S | P2 |
| `EnglishUS` | `Sys.ofName? "EnglishUS"` → `Sys.Survey` | PARTIAL | alias not a Lean identifier | S | P2 |
| `EntropySystem` | `UnitSystems.EntropySystem` instantiated at `Scalar` | DONE | generic over `UnitAlg` | — | — |
| `ExpGroup` | `FieldAlgebra.ExpGroup` (re-export) | DONE | see FieldAlgebra | — | — |
| `Eₕ` | `measured (Similitude.hartree .SI2019)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `F` | `USQ.F` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `FF` | value exists as `𝔉` | PARTIAL | ASCII alias not defined | S | P2 |
| `FFF` | `Sys.FFF.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.FFF Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `FPS` | `Sys.FPS.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.FPS Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `G` | exact group `G Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `G0` | value exists as `G₀` | PARTIAL | ASCII alias not defined | S | P2 |
| `GG` | — | SKIP | exported but undefined in Julia MeasureSystems | — | — |
| `GM` | `Sys.ofName? "GM"` → `Sys.Gravitational` | PARTIAL | alias not a Lean identifier | S | P2 |
| `GME` | exact group `ms Scalar .GME` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `GMJ` | exact group `ms Scalar .GMJ` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `GM☉` | exact group `GMsun Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `Gauss` | `Sys.Gauss.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Gauss Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `GaussSystem` | `UnitSystems.GaussSystem` instantiated at `Scalar` | DONE | generic over `UnitAlg` | — | — |
| `Gravitational` | `Sys.Gravitational.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Gravitational Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `Group` | `FieldAlgebra.Group` (re-export) | DONE | see FieldAlgebra | — | — |
| `G₀` | `measured (Similitude.conductancequantum .SI2019)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `HLU` | `Sys.ofName? "HLU"` → `Sys.LorentzHeaviside` | PARTIAL | alias not a Lean identifier | S | P2 |
| `HOUR` | exact group `HOUR Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `Hartree` | `Sys.Hartree.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Hartree Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `Hubble` | `Sys.Hubble.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Hubble Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `IAU` | `Sys.IAU.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.IAU Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `IAUE` | `Sys.IAUE.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.IAUE Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `IAUJ` | `Sys.IAUJ.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.IAUJ Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `IAU☉` | `Sys.IAU.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.IAU Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `IPS` | `Sys.IPS.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.IPS Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `International` | `Sys.International.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.International Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `InternationalMean` | `Sys.InternationalMean.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.InternationalMean Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `J` | `USQ.J` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `JD` | exact group `ms Scalar .JD` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `KJ` | exact group `josephson (SI2019 Scalar)` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `KJ1990` | exact group `ms Scalar .KJ1990` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `KJ2014` | exact group `ms Scalar .KJ2014` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `KKH` | `Sys.KKH.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.KKH Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `Kcd` | exact group `ms Scalar .Kcd` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `L` | `USQ.L` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `LD` | exact group `ms Scalar .LD` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `LogGroup` | `FieldAlgebra.LogGroup` (re-export) | DONE | see FieldAlgebra | — | — |
| `LorentzHeaviside` | `Sys.LorentzHeaviside.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.LorentzHeaviside Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `M` | `USQ.M` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `ME` | `Sys.ofName? "ME"` → `Sys.Engineering` | PARTIAL | alias not a Lean identifier | S | P2 |
| `MKS` | `Sys.ofName? "MKS"` → `Sys.Metric` | PARTIAL | alias not a Lean identifier | S | P2 |
| `MPH` | `Sys.MPH.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.MPH Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `MTS` | `Sys.MTS.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.MTS Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `Measure` | `MValue` / `Measurement` (MeasureSystems/Measures.lean) | SKIP | `Measure{N}` is a type-parameter interning cache; Lean stores `Measurement` values directly (`MValue.toMeas` = `measure`) | — | — |
| `MeasureSystems` | `MeasureSystems` (lib) | SKIP | module name | — | — |
| `Meridian` | `Sys.Meridian.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Meridian Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `Metric` | `Sys.Metric.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Metric Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `MetricArcminute` | `Sys.MetricArcminute.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.MetricArcminute Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `MetricArcsecond` | `Sys.MetricArcsecond.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.MetricArcsecond Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `MetricDegree` | `Sys.MetricDegree.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.MetricDegree Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `MetricGradian` | `Sys.MetricGradian.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.MetricGradian Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `MetricSpatian` | `Sys.MetricSpatian.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.MetricSpatian Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `MetricSystem` | `UnitSystems.MetricSystem` instantiated at `Scalar` | DONE | generic over `UnitAlg` | — | — |
| `MetricTurn` | `Sys.MetricTurn.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.MetricTurn Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `Mu` | value exists as `Mᵤ` | PARTIAL | ASCII alias not defined | S | P2 |
| `Mᵤ` | exact group `Mᵤ Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `N` | `USQ.N` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `NA` | exact group `ms Scalar .NA` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `Natural` | `Sys.Natural.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Natural Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `NaturalGauss` | `Sys.NaturalGauss.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.NaturalGauss Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `Nautical` | `Sys.Nautical.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Nautical Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `Planck` | `Sys.Planck.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Planck Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `PlanckGauss` | `Sys.PlanckGauss.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.PlanckGauss Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `Q` | `USQ.Q` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `QCD` | `Sys.QCD.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.QCD Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `QCDGauss` | `Sys.QCDGauss.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.QCDGauss Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `QCDoriginal` | `Sys.QCDoriginal.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.QCDoriginal Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `Quantities` | — | MISSING | vector of values sharing a dimension (largely broken in Julia); natural Lean form `Quantity U d (Values n Float)` needs a `QScalar` instance | S | P2 |
| `Quantity` | `Similitude.Quantity U d α`, `Q U d` (Similitude/Quantity.lean), `α := MValue` | PARTIAL | typed * / inv npow sqrt cbrt `.to` `.recast` display tested (quantity_arith.json). Gaps: U ranges over the 48 named `Sys` only (no user-built UnitSystem); no negative/`Rational` power (`q^-2`, `q^(3//2)`); no `log/exp/Number^q`; no `Quantity{A}/Quantity{B}` → ConvertUnit; no dimensionless `q ± Number`; no `Quantity * ConvertUnit` (right) | M | P1 |
| `R` | `USQ.R` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `RH` | `ms Scalar .Rinf * …` (UnitSystems registry `RH` over Num only) | PARTIAL | measured `RH` carries a Measure coefficient in Julia (`…⋅5.9753831112(19)e26`); Lean has no exact/measured RH quantity | M | P2 |
| `RK` | exact group `klitzing (SI2019 Scalar)` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `RK1990` | exact group `ms Scalar .RK1990` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `RK2014` | exact group `ms Scalar .RK2014` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `RankineSystem` | `UnitSystems.RankineSystem` instantiated at `Scalar` | DONE | generic over `UnitAlg` | — | — |
| `Ru` | value exists as `Rᵤ` | PARTIAL | ASCII alias not defined | S | P2 |
| `Ry` | `𝘩*𝘤*R∞` over `Scalar` (UnitSystems registry `Ry` over Num) | PARTIAL | no named exact/measured constant | S | P2 |
| `Rydberg` | `Sys.Rydberg.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Rydberg Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `Rᵤ` | exact group `Rᵤ Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `Rᵤ2014` | exact group `ms Scalar .Rᵤ2014` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `R∞` | exact group `ms Scalar .Rinf` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `SB` | value exists as `σ` | PARTIAL | ASCII alias not defined | S | P2 |
| `SI` | `Sys.ofName? "SI"` → `Sys.SI2019` | PARTIAL | alias not a Lean identifier | S | P2 |
| `SI1976` | `Sys.SI1976.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.SI1976 Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `SI2019` | `Sys.SI2019.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.SI2019 Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `Schrodinger` | `Sys.Schrodinger.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Schrodinger Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `Similitude` | `Similitude` (lib) | SKIP | module name | — | — |
| `Stoney` | `Sys.Stoney.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Stoney Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `Survey` | `Sys.Survey.consts` (exact constants, Similitude/Ratio.lean) = `UnitSystems.Survey Scalar` | DONE | exercised by ratios/system_constants/homs goldens; measured via `MValue` | — | — |
| `T` | `USQ.T` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `TP` | `Dim.temperature.conv .PlanckGauss .SI2019` (+ `showConvertM`) | DONE | measured ratios | — | — |
| `T₀` | exact group `ms Scalar .T₀` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `US` | `UnitSystems.UnitSystem` | PARTIAL | alias `US` missing | S | P2 |
| `Unified` | `usqMap`, `showDimUnified` (Similitude/Hom.lean, Registry.lean) | PARTIAL | isomorphism and display tested (unified.json); `Unified` is not a `Sys`, so `Quantity .Unified d` / conversions to Unified are impossible | S | P2 |
| `UnitSystem` | `UnitSystems.UnitSystem` | DONE | — | — | — |
| `UnitSystems` | `UnitSystems` (lib) | SKIP | module name | — | — |
| `Universe` | `UnitSystems.Universe Scalar` (exact `Coupling`, UnitSystems/System.lean) | DONE | exact coupling groups (constants.json named `αG`); Julia MeasureSystems also keeps it uncertainty-free | — | — |
| `Vᵢₜ` | exact group `ms Scalar .Vᵢₜ` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `Z0` | value exists as `Z₀` | PARTIAL | ASCII alias not defined | S | P2 |
| `Z₀` | `measured (Similitude.vacuumimpedance .SI2019)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `a0` | value exists as `a₀` | PARTIAL | ASCII alias not defined | S | P2 |
| `aG` | value exists as `αG` | PARTIAL | ASCII alias not defined | S | P2 |
| `aL` | value exists as `αL` | PARTIAL | ASCII alias not defined | S | P2 |
| `abampere` | `MeasureSystems.measured Similitude.Units.abampere` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `abcoulomb` | `MeasureSystems.measured Similitude.Units.abcoulomb` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `abfarad` | `MeasureSystems.measured Similitude.Units.abfarad` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `abhenry` | `MeasureSystems.measured Similitude.Units.abhenry` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `abmho` | `MeasureSystems.measured Similitude.Units.abmho` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `abohm` | `MeasureSystems.measured Similitude.Units.abohm` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `abvolt` | `MeasureSystems.measured Similitude.Units.abvolt` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `acceleration` | `Dim.acceleration` (UnitSystems/Dim.lean), `Conv.acceleration.dim`; `d(U,S)` = `Dim.acceleration.conv U S`, `d(U)` = `naturalUnit U Dim.acceleration` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `acre` | `MeasureSystems.measured Similitude.Units.acre` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `action` | `Dim.action` (UnitSystems/Dim.lean), `Conv.action.dim`; `d(U,S)` = `Dim.action.conv U S`, `d(U)` = `naturalUnit U Dim.action` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `admiraltymile` | `MeasureSystems.measured Similitude.Units.admiraltymile` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `admittance` | `Dim.admittance` (UnitSystems/Dim.lean), `Conv.admittance.dim`; `d(U,S)` = `Dim.admittance.conv U S`, `d(U)` = `naturalUnit U Dim.admittance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `ainv` | value exists as `αinv` | PARTIAL | ASCII alias not defined | S | P2 |
| `amagat` | `MeasureSystems.measured Similitude.Units.amagat` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `ampere` | `MeasureSystems.measured Similitude.Units.ampere` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `angle` | `Dim.angle` (UnitSystems/Dim.lean), `Conv.angle.dim`; `d(U,S)` = `Dim.angle.conv U S`, `d(U)` = `naturalUnit U Dim.angle` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `angstrom` | `MeasureSystems.measured Similitude.Units.angstrom` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `angulararea` | `Dim.angulararea` (UnitSystems/Dim.lean), `Conv.angulararea.dim`; `d(U,S)` = `Dim.angulararea.conv U S`, `d(U)` = `naturalUnit U Dim.angulararea` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `angularfrequency` | `Dim.angularfrequency` (UnitSystems/Dim.lean), `Conv.angularfrequency.dim`; `d(U,S)` = `Dim.angularfrequency.conv U S`, `d(U)` = `naturalUnit U Dim.angularfrequency` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `angularlength` | `Dim.angularlength` (UnitSystems/Dim.lean), `Conv.angularlength.dim`; `d(U,S)` = `Dim.angularlength.conv U S`, `d(U)` = `naturalUnit U Dim.angularlength` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `angularmomentum` | `Dim.angularmomentum` (UnitSystems/Dim.lean), `Conv.angularmomentum.dim`; `d(U,S)` = `Dim.angularmomentum.conv U S`, `d(U)` = `naturalUnit U Dim.angularmomentum` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `angulartime` | `Dim.angulartime` (UnitSystems/Dim.lean), `Conv.angulartime.dim`; `d(U,S)` = `Dim.angulartime.conv U S`, `d(U)` = `naturalUnit U Dim.angulartime` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `angularwavenumber` | `Dim.angularwavenumber` (UnitSystems/Dim.lean), `Conv.angularwavenumber.dim`; `d(U,S)` = `Dim.angularwavenumber.conv U S`, `d(U)` = `naturalUnit U Dim.angularwavenumber` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `apm` | `MeasureSystems.measured Similitude.Units.apm` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `apostilb` | `MeasureSystems.measured Similitude.Units.apostilb` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `arcminute` | `MeasureSystems.measured Similitude.Units.arcminute` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `arcsecond` | `MeasureSystems.measured Similitude.Units.arcsecond` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `area` | `Dim.area` (UnitSystems/Dim.lean), `Conv.area.dim`; `d(U,S)` = `Dim.area.conv U S`, `d(U)` = `naturalUnit U Dim.area` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `areadensity` | `Dim.areadensity` (UnitSystems/Dim.lean), `Conv.areadensity.dim`; `d(U,S)` = `Dim.areadensity.conv U S`, `d(U)` = `naturalUnit U Dim.areadensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `astronomicalunit` | `MeasureSystems.measured Similitude.Units.astronomicalunit` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `atm` | exact group `ms Scalar .atm` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `atmosphere` | `MeasureSystems.measured Similitude.Units.atmosphere` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `atomicmass` | `dalton` exists | PARTIAL | alias `atomicmass` not defined | S | P2 |
| `atto` | exact group `atto Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `au` | exact group `ms Scalar .au` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `avogadro` | `Similitude.avogadro (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `a₀` | `measured (Similitude.bohr .SI2019)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `bar` | `MeasureSystems.measured Similitude.Units.bar` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `barn` | `MeasureSystems.measured Similitude.Units.barn` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `barye` | `MeasureSystems.measured Similitude.Units.barye` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `bel` | — | MISSING | `U(𝟏, log(𝟙))`, `U(𝟏, log10(𝟙))`, `U(𝟏, dB(𝟙))`: typed `Dim` has no LogGroup dimensions, so log-valued quantities cannot be formed (README lists these units) | M | P1 |
| `biotsavart` | `Similitude.biotsavart (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `bohr` | `Similitude.bohr (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `boilerhorsepower` | `MeasureSystems.measured Similitude.Units.boilerhorsepower` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `boiling` | `MeasureSystems.measured Similitude.Units.boiling` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `boltzmann` | `Similitude.boltzmann (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `bradian` | `MeasureSystems.measured Similitude.Units.bradian` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `bril` | `MeasureSystems.measured Similitude.Units.bril` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `bubnoff` | `MeasureSystems.measured Similitude.Units.bubnoff` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `byte` | exact group `byte Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `cache` | `MValue` / `Measurement` (MeasureSystems/Measures.lean) | SKIP | `Measure{N}` is a type-parameter interning cache; Lean stores `Measurement` values directly (`MValue.toMeas` = `measure`) | — | — |
| `cal` | `measured (Similitude.Units.calorie.to .SI2019)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `calorie` | `MeasureSystems.measured Similitude.Units.calorie` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `calᵢₜ` | — | MISSING | `SI(UnitSystems.cal…, energy)` quantities not defined | S | P2 |
| `calₜₕ` | — | MISSING | `SI(UnitSystems.cal…, energy)` quantities not defined | S | P2 |
| `candela` | `MeasureSystems.measured Similitude.Units.candela` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `capacitance` | `Dim.capacitance` (UnitSystems/Dim.lean), `Conv.capacitance.dim`; `d(U,S)` = `Dim.capacitance.conv U S`, `d(U)` = `naturalUnit U Dim.capacitance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `catalysis` | `Dim.catalysis` (UnitSystems/Dim.lean), `Conv.catalysis.dim`; `d(U,S)` = `Dim.catalysis.conv U S`, `d(U)` = `naturalUnit U Dim.catalysis` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `cc` | value exists as `𝘤` | PARTIAL | ASCII alias not defined | S | P2 |
| `celsius` | `MeasureSystems.measured Similitude.Units.celsius` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `centi` | exact group `centi Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `charge` | `Dim.charge` (UnitSystems/Dim.lean), `Conv.charge.dim`; `d(U,S)` = `Dim.charge.conv U S`, `d(U)` = `naturalUnit U Dim.charge` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `chargedensity` | `Dim.chargedensity` (UnitSystems/Dim.lean), `Conv.chargedensity.dim`; `d(U,S)` = `Dim.chargedensity.conv U S`, `d(U)` = `naturalUnit U Dim.chargedensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `compliance` | `Dim.compliance` (UnitSystems/Dim.lean), `Conv.compliance.dim`; `d(U,S)` = `Dim.compliance.conv U S`, `d(U)` = `naturalUnit U Dim.compliance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `compressibility` | `Dim.compressibility` (UnitSystems/Dim.lean), `Conv.compressibility.dim`; `d(U,S)` = `Dim.compressibility.conv U S`, `d(U)` = `naturalUnit U Dim.compressibility` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `conductance` | `Dim.conductance` (UnitSystems/Dim.lean), `Conv.conductance.dim`; `d(U,S)` = `Dim.conductance.conv U S`, `d(U)` = `naturalUnit U Dim.conductance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `conductancequantum` | `Similitude.conductancequantum (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `conductivity` | `Dim.conductivity` (UnitSystems/Dim.lean), `Conv.conductivity.dim`; `d(U,S)` = `Dim.conductivity.conv U S`, `d(U)` = `naturalUnit U Dim.conductivity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `cosmological` | `MeasureSystems.measured Similitude.Units.cosmological` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `coulomb` | `MeasureSystems.measured Similitude.Units.coulomb` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `coupling` | `UnitSystems.coupling (Sys.consts U)` (exact group) | DONE | generic formula; Scalar instantiation tested through system constants | — | — |
| `crackle` | `Dim.crackle` (UnitSystems/Dim.lean), `Conv.crackle.dim`; `d(U,S)` = `Dim.crackle.conv U S`, `d(U)` = `naturalUnit U Dim.crackle` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `cup` | `MeasureSystems.measured Similitude.Units.cup` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `curie` | `MeasureSystems.measured Similitude.Units.curie` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `current` | `Dim.current` (UnitSystems/Dim.lean), `Conv.current.dim`; `d(U,S)` = `Dim.current.conv U S`, `d(U)` = `naturalUnit U Dim.current` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `currentdensity` | `Dim.currentdensity` (UnitSystems/Dim.lean), `Conv.currentdensity.dim`; `d(U,S)` = `Dim.currentdensity.conv U S`, `d(U)` = `naturalUnit U Dim.currentdensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `dB` | `FieldConstants.logdb/expdb/dB` (numbers), `Group.logdb` (groups) | PARTIAL | `logdb(::Quantity)` (value and LogGroup dimension) missing, same root cause as neper/bel/decibel | M | P2 |
| `dalton` | `Similitude.dalton (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `darcy` | `MeasureSystems.measured Similitude.Units.darcy` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `darkenergydensity` | `UnitSystems.darkenergydensity (Sys.consts U)` (exact group) | DONE | generic formula; Scalar instantiation tested through system constants | — | — |
| `day` | `MeasureSystems.measured Similitude.Units.day` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `deci` | exact group `deci Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `decibel` | — | MISSING | `U(𝟏, log(𝟙))`, `U(𝟏, log10(𝟙))`, `U(𝟏, dB(𝟙))`: typed `Dim` has no LogGroup dimensions, so log-valued quantities cannot be formed (README lists these units) | M | P1 |
| `degree` | `MeasureSystems.measured Similitude.Units.degree` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `deka` | exact group `deka Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `demagnetizingfactor` | `Dim.demagnetizingfactor` (UnitSystems/Dim.lean), `Conv.demagnetizingfactor.dim`; `d(U,S)` = `Dim.demagnetizingfactor.conv U S`, `d(U)` = `naturalUnit U Dim.demagnetizingfactor` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `density` | `Dim.density` (UnitSystems/Dim.lean), `Conv.density.dim`; `d(U,S)` = `Dim.density.conv U S`, `d(U)` = `naturalUnit U Dim.density` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `diffusionflux` | `Dim.diffusionflux` (UnitSystems/Dim.lean), `Conv.diffusionflux.dim`; `d(U,S)` = `Dim.diffusionflux.conv U S`, `d(U)` = `naturalUnit U Dim.diffusionflux` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `diffusivity` | `Dim.diffusivity` (UnitSystems/Dim.lean), `Conv.diffusivity.dim`; `d(U,S)` = `Dim.diffusivity.conv U S`, `d(U)` = `naturalUnit U Dim.diffusivity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `dimensionless` | `Dim.dimensionless` (UnitSystems/Dim.lean), `Conv.dimensionless.dim`; `d(U,S)` = `Dim.dimensionless.conv U S`, `d(U)` = `naturalUnit U Dim.dimensionless` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `dimensions` | type index `d` / `Dim.toGroup` | MISSING | no value-level accessor `Quantity.dimensions : USQGroup` / `ConvertUnit.dimensions` (trivial) | S | P1 |
| `diopter` | `MeasureSystems.measured Similitude.Units.diopter` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `dyne` | `MeasureSystems.measured Similitude.Units.dyne` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `e0` | value exists as `ε₀` | PARTIAL | ASCII alias not defined | S | P2 |
| `eV` | `measured (Similitude.Units.electronvolt)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `earthcalorie` | `MeasureSystems.measured Similitude.Units.earthcalorie` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `earthcoulomb` | `MeasureSystems.measured Similitude.Units.earthcoulomb` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `earthgram` | `MeasureSystems.measured Similitude.Units.earthgram` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `earthmass` | `MeasureSystems.measured Similitude.Units.earthmass` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `earthmeter` | `MeasureSystems.measured Similitude.Units.earthmeter` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `earthmole` | `MeasureSystems.measured Similitude.Units.earthmole` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `earthradius` | `MeasureSystems.measured Similitude.Units.earthradius` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `eddington` | `MeasureSystems.measured Similitude.Units.eddington` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `ee` | value exists as `𝘦` | PARTIAL | ASCII alias not defined | S | P2 |
| `einstein` | `Similitude.einstein (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `electricalhorsepower` | `MeasureSystems.measured Similitude.Units.electricalhorsepower` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `electricdipolemoment` | `Dim.electricdipolemoment` (UnitSystems/Dim.lean), `Conv.electricdipolemoment.dim`; `d(U,S)` = `Dim.electricdipolemoment.conv U S`, `d(U)` = `naturalUnit U Dim.electricdipolemoment` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `electricdisplacement` | `Dim.electricdisplacement` (UnitSystems/Dim.lean), `Conv.electricdisplacement.dim`; `d(U,S)` = `Dim.electricdisplacement.conv U S`, `d(U)` = `naturalUnit U Dim.electricdisplacement` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `electricfield` | `Dim.electricfield` (UnitSystems/Dim.lean), `Conv.electricfield.dim`; `d(U,S)` = `Dim.electricfield.conv U S`, `d(U)` = `naturalUnit U Dim.electricfield` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `electricflux` | `Dim.electricflux` (UnitSystems/Dim.lean), `Conv.electricflux.dim`; `d(U,S)` = `Dim.electricflux.conv U S`, `d(U)` = `naturalUnit U Dim.electricflux` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `electricpolarizability` | `Dim.electricpolarizability` (UnitSystems/Dim.lean), `Conv.electricpolarizability.dim`; `d(U,S)` = `Dim.electricpolarizability.conv U S`, `d(U)` = `naturalUnit U Dim.electricpolarizability` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `electricpotential` | `Dim.electricpotential` (UnitSystems/Dim.lean), `Conv.electricpotential.dim`; `d(U,S)` = `Dim.electricpotential.conv U S`, `d(U)` = `naturalUnit U Dim.electricpotential` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `electronmass` | `Similitude.electronmass (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `electronradius` | `Similitude.electronradius (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `electronunit` | `UnitSystems.electronunit (Sys.consts U)` (exact group) | DONE | generic formula; Scalar instantiation tested through system constants | — | — |
| `electronvolt` | `MeasureSystems.measured Similitude.Units.electronvolt` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `electrostatic` | `Similitude.electrostatic (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `elementarycharge` | `Similitude.elementarycharge (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `eleven` | exact group `eleven` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `em` | exact group `em Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `energy` | `Dim.energy` (UnitSystems/Dim.lean), `Conv.energy.dim`; `d(U,S)` = `Dim.energy.conv U S`, `d(U)` = `naturalUnit U Dim.energy` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `entropy` | `Dim.entropy` (UnitSystems/Dim.lean), `Conv.entropy.dim`; `d(U,S)` = `Dim.entropy.conv U S`, `d(U)` = `naturalUnit U Dim.entropy` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `eotvos` | `MeasureSystems.measured Similitude.Units.eotvos` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `erg` | `MeasureSystems.measured Similitude.Units.erg` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `etendue` | `Dim.etendue` (UnitSystems/Dim.lean), `Conv.etendue.dim`; `d(U,S)` = `Dim.etendue.conv U S`, `d(U)` = `naturalUnit U Dim.etendue` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `eulergamma` | exact group `Consts.gen 34` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `exa` | exact group `exa Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `exbi` | exact group `exbi Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `expdb` | `FieldConstants.logdb/expdb/dB` (numbers), `Group.logdb` (groups) | PARTIAL | `logdb(::Quantity)` (value and LogGroup dimension) missing, same root cause as neper/bel/decibel | M | P2 |
| `exposure` | `Dim.exposure` (UnitSystems/Dim.lean), `Conv.exposure.dim`; `d(U,S)` = `Dim.exposure.conv U S`, `d(U)` = `naturalUnit U Dim.exposure` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `factorize` | `Consts.factorize`, `Consts.factorizeF` (Similitude/Constants.lean) | DONE | constants.json factorize_int/float | — | — |
| `fahrenheit` | `MeasureSystems.measured Similitude.Units.fahrenheit` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `farad` | `MeasureSystems.measured Similitude.Units.farad` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `faraday` | `Similitude.faraday (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `feet` | — | SKIP | exported but undefined in Julia MeasureSystems | — | — |
| `femto` | exact group `femto Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `finestructure` | `UnitSystems.finestructure (Sys.consts U)` (exact group) | DONE | generic formula; Scalar instantiation tested through system constants | — | — |
| `five` | exact group `five` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `flick` | `MeasureSystems.measured Similitude.Units.flick` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `fluence` | `Dim.fluence` (UnitSystems/Dim.lean), `Conv.fluence.dim`; `d(U,S)` = `Dim.fluence.conv U S`, `d(U)` = `naturalUnit U Dim.fluence` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `fluidounce` | `MeasureSystems.measured Similitude.Units.fluidounce` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `foot` | `MeasureSystems.measured Similitude.Units.foot` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `footcandle` | `MeasureSystems.measured Similitude.Units.footcandle` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `footlambert` | `MeasureSystems.measured Similitude.Units.footlambert` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `footpound` | `MeasureSystems.measured Similitude.Units.footpound` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `force` | `Dim.force` (UnitSystems/Dim.lean), `Conv.force.dim`; `d(U,S)` = `Dim.force.conv U S`, `d(U)` = `naturalUnit U Dim.force` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `fourtythree` | exact group `fourtythree` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `fpm` | `MeasureSystems.measured Similitude.Units.fpm` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `fps` | `MeasureSystems.measured Similitude.Units.fps` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `frequency` | `Dim.frequency` (UnitSystems/Dim.lean), `Conv.frequency.dim`; `d(U,S)` = `Dim.frequency.conv U S`, `d(U)` = `naturalUnit U Dim.frequency` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `frequencydrift` | `Dim.frequencydrift` (UnitSystems/Dim.lean), `Conv.frequencydrift.dim`; `d(U,S)` = `Dim.frequencydrift.conv U S`, `d(U)` = `naturalUnit U Dim.frequencydrift` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `ft` | exact group `ms Scalar .ft` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `ftUS` | exact group `ms Scalar .ftUS` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `fuelefficiency` | `Dim.fuelefficiency` (UnitSystems/Dim.lean), `Conv.fuelefficiency.dim`; `d(U,S)` = `Dim.fuelefficiency.conv U S`, `d(U)` = `naturalUnit U Dim.fuelefficiency` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `fur` | exact group `fur Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `g0` | value exists as `g₀` | PARTIAL | ASCII alias not defined | S | P2 |
| `galileo` | `MeasureSystems.measured Similitude.Units.galileo` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `gallon` | `MeasureSystems.measured Similitude.Units.gallon` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `gasgallon` | `MeasureSystems.measured Similitude.Units.gasgallon` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `gauss` | `MeasureSystems.measured Similitude.Units.gauss` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `gaussgravitation` | `MeasureSystems.measured Similitude.Units.gaussgravitation` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `gaussianmonth` | `MeasureSystems.measured Similitude.Units.gaussianmonth` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `gaussianyear` | `MeasureSystems.measured Similitude.Units.gaussianyear` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `gforce` | `MeasureSystems.measured Similitude.Units.gforce` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `gibi` | exact group `gibi Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `giga` | exact group `giga Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `gilbert` | `MeasureSystems.measured Similitude.Units.gilbert` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `golden` | exact group `Consts.gen 33` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `gradian` | `MeasureSystems.measured Similitude.Units.gradian` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `grain` | `MeasureSystems.measured Similitude.Units.grain` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `gram` | `MeasureSystems.measured Similitude.Units.gram` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `gravitation` | `Similitude.gravitation (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `gravity` | `Similitude.gravity (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `gravityforce` | `Dim.gravityforce` (UnitSystems/Dim.lean), `Conv.gravityforce.dim`; `d(U,S)` = `Dim.gravityforce.conv U S`, `d(U)` = `naturalUnit U Dim.gravityforce` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `gray` | `MeasureSystems.measured Similitude.Units.gray` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `greatcircle` | `MeasureSystems.measured Similitude.Units.greatcircle` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `g₀` | exact group `ms Scalar .g₀` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `hartree` | `Similitude.hartree (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `hectare` | `MeasureSystems.measured Similitude.Units.hectare` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `hecto` | exact group `hecto Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `henry` | `MeasureSystems.measured Similitude.Units.henry` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `hertz` | `MeasureSystems.measured Similitude.Units.hertz` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `hh` | value exists as `𝘩` | PARTIAL | ASCII alias not defined | S | P2 |
| `horsepower` | `MeasureSystems.measured Similitude.Units.horsepower` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `horsepowermetric` | `MeasureSystems.measured Similitude.Units.horsepowermetric` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `horsepowerwatt` | `MeasureSystems.measured Similitude.Units.horsepowerwatt` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `hour` | `MeasureSystems.measured Similitude.Units.hour` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `hubble` | `MeasureSystems.measured Similitude.Units.hubble` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `hyl` | `MeasureSystems.measured Similitude.Units.hyl` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `hyperfine` | `MeasureSystems.measured Similitude.Units.hyperfine` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `illuminance` | `Dim.illuminance` (UnitSystems/Dim.lean), `Conv.illuminance.dim`; `d(U,S)` = `Dim.illuminance.conv U S`, `d(U)` = `naturalUnit U Dim.illuminance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `impedance` | `Dim.impedance` (UnitSystems/Dim.lean), `Conv.impedance.dim`; `d(U,S)` = `Dim.impedance.conv U S`, `d(U)` = `naturalUnit U Dim.impedance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `impulse` | `Dim.impulse` (UnitSystems/Dim.lean), `Conv.impulse.dim`; `d(U,S)` = `Dim.impulse.conv U S`, `d(U)` = `naturalUnit U Dim.impulse` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `inch` | `MeasureSystems.measured Similitude.Units.inch` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `inchmercury` | `MeasureSystems.measured Similitude.Units.inchmercury` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `inductance` | `Dim.inductance` (UnitSystems/Dim.lean), `Conv.inductance.dim`; `d(U,S)` = `Dim.inductance.conv U S`, `d(U)` = `naturalUnit U Dim.inductance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `inertance` | `Dim.inertance` (UnitSystems/Dim.lean), `Conv.inertance.dim`; `d(U,S)` = `Dim.inertance.conv U S`, `d(U)` = `naturalUnit U Dim.inertance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `inertia` | `Dim.inertia` (UnitSystems/Dim.lean), `Conv.inertia.dim`; `d(U,S)` = `Dim.inertia.conv U S`, `d(U)` = `naturalUnit U Dim.inertia` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `intensity` | `irradiance` exists | PARTIAL | alias `intensity` not defined | S | P2 |
| `ips` | `MeasureSystems.measured Similitude.Units.ips` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `irradiance` | `Dim.irradiance` (UnitSystems/Dim.lean), `Conv.irradiance.dim`; `d(U,S)` = `Dim.irradiance.conv U S`, `d(U)` = `naturalUnit U Dim.irradiance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `jansky` | `MeasureSystems.measured Similitude.Units.jansky` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `jerk` | `Dim.jerk` (UnitSystems/Dim.lean), `Conv.jerk.dim`; `d(U,S)` = `Dim.jerk.conv U S`, `d(U)` = `naturalUnit U Dim.jerk` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `josephson` | `Similitude.josephson (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `joule` | `MeasureSystems.measured Similitude.Units.joule` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `jovianyear` | `MeasureSystems.measured Similitude.Units.jovianyear` | PARTIAL | uncertainty of `μE☾ = 81.300568(3)` (a measured non-generator coefficient) is dropped: e.g. lunarmass `3.6943034122(74)e-8` vs Julia `3.69430341(14)e-8`, synodicmonth prints no ± at all | M | P1 |
| `jupiterdistance` | `MeasureSystems.measured Similitude.Units.jupiterdistance` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `jupitermass` | `MeasureSystems.measured Similitude.Units.jupitermass` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `kB` | exact group `ms Scalar .kB` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `katal` | `MeasureSystems.measured Similitude.Units.katal` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `kayser` | `MeasureSystems.measured Similitude.Units.kayser` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `kcal` | `measured (Similitude.Units.kilocalorie.to .SI2019)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `kcalᵢₜ` | — | MISSING | `SI(UnitSystems.cal…, energy)` quantities not defined | S | P2 |
| `kcalₜₕ` | — | MISSING | `SI(UnitSystems.cal…, energy)` quantities not defined | S | P2 |
| `ke` | value exists as `kₑ` | PARTIAL | ASCII alias not defined | S | P2 |
| `kelvin` | `MeasureSystems.measured Similitude.Units.kelvin` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `kibi` | exact group `kibi Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `kilo` | exact group `kilo Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `kilocalorie` | `MeasureSystems.measured Similitude.Units.kilocalorie` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `kilogram` | `MeasureSystems.measured Similitude.Units.kilogram` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `kilograms` | — | SKIP | exported but undefined in Julia MeasureSystems | — | — |
| `kilopond` | `MeasureSystems.measured Similitude.Units.kilopond` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `klitzing` | `Similitude.klitzing (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `kmh` | `MeasureSystems.measured Similitude.Units.kmh` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `knot` | `MeasureSystems.measured Similitude.Units.knot` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `kₑ` | `measured (Similitude.electrostatic .SI2019)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `lA` | `Dim.length.conv .Hartree .SI2019` (+ `showConvertM`) | DONE | measured ratios | — | — |
| `lP` | `Dim.length.conv .PlanckGauss .SI2019` (+ `showConvertM`) | PARTIAL | ASCII alias of ℓP missing | S | P2 |
| `lQCD` | `Dim.length.conv .QCD .SI2019` (+ `showConvertM`) | DONE | measured ratios | — | — |
| `lS` | `Dim.length.conv .Stoney .SI2019` (+ `showConvertM`) | DONE | measured ratios | — | — |
| `lambert` | `MeasureSystems.measured Similitude.Units.lambert` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `langley` | `MeasureSystems.measured Similitude.Units.langley` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `lapserate` | `Dim.lapserate` (UnitSystems/Dim.lean), `Conv.lapserate.dim`; `d(U,S)` = `Dim.lapserate.conv U S`, `d(U)` = `naturalUnit U Dim.lapserate` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `lb` | exact group `ms Scalar .lb` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `lbm` | — | SKIP | exported but undefined in Julia MeasureSystems | — | — |
| `lc` | exact group `lc Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `lcq` | exact group `lcq Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `lightspeed` | `Similitude.lightspeed (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `lightyear` | `MeasureSystems.measured Similitude.Units.lightyear` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `linearchargedensity` | `Dim.linearchargedensity` (UnitSystems/Dim.lean), `Conv.linearchargedensity.dim`; `d(U,S)` = `Dim.linearchargedensity.conv U S`, `d(U)` = `naturalUnit U Dim.linearchargedensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `lineardensity` | `Dim.lineardensity` (UnitSystems/Dim.lean), `Conv.lineardensity.dim`; `d(U,S)` = `Dim.lineardensity.conv U S`, `d(U)` = `naturalUnit U Dim.lineardensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `liter` | `MeasureSystems.measured Similitude.Units.liter` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `logdb` | `FieldConstants.logdb/expdb/dB` (numbers), `Group.logdb` (groups) | PARTIAL | `logdb(::Quantity)` (value and LogGroup dimension) missing, same root cause as neper/bel/decibel | M | P2 |
| `lorentz` | `Similitude.lorentz (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `loschmidt` | `MeasureSystems.measured Similitude.Units.loschmidt` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `lumen` | `MeasureSystems.measured Similitude.Units.lumen` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `lumerg` | `MeasureSystems.measured Similitude.Units.lumerg` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `luminance` | `Dim.luminance` (UnitSystems/Dim.lean), `Conv.luminance.dim`; `d(U,S)` = `Dim.luminance.conv U S`, `d(U)` = `naturalUnit U Dim.luminance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `luminousefficacy` | `Similitude.luminousefficacy (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `luminousenergy` | `Dim.luminousenergy` (UnitSystems/Dim.lean), `Conv.luminousenergy.dim`; `d(U,S)` = `Dim.luminousenergy.conv U S`, `d(U)` = `naturalUnit U Dim.luminousenergy` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `luminousexposure` | `Dim.luminousexposure` (UnitSystems/Dim.lean), `Conv.luminousexposure.dim`; `d(U,S)` = `Dim.luminousexposure.conv U S`, `d(U)` = `naturalUnit U Dim.luminousexposure` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `luminousflux` | `Dim.luminousflux` (UnitSystems/Dim.lean), `Conv.luminousflux.dim`; `d(U,S)` = `Dim.luminousflux.conv U S`, `d(U)` = `naturalUnit U Dim.luminousflux` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `luminousintensity` | `Dim.luminousintensity` (UnitSystems/Dim.lean), `Conv.luminousintensity.dim`; `d(U,S)` = `Dim.luminousintensity.conv U S`, `d(U)` = `naturalUnit U Dim.luminousintensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `lunardistance` | `MeasureSystems.measured Similitude.Units.lunardistance` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `lunarmass` | `MeasureSystems.measured Similitude.Units.lunarmass` | PARTIAL | uncertainty of `μE☾ = 81.300568(3)` (a measured non-generator coefficient) is dropped: e.g. lunarmass `3.6943034122(74)e-8` vs Julia `3.69430341(14)e-8`, synodicmonth prints no ± at all | M | P1 |
| `lux` | `MeasureSystems.measured Similitude.Units.lux` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `m0` | value exists as `μ₀` | PARTIAL | ASCII alias not defined | S | P2 |
| `mA` | `Dim.mass.conv .Hartree .SI2019` (+ `showConvertM`) | DONE | measured ratios | — | — |
| `mP` | exact group `ms Scalar .mP` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `mQCD` | `Dim.mass.conv .QCD .SI2019` (+ `showConvertM`) | DONE | measured ratios | — | — |
| `mS` | `Dim.mass.conv .Stoney .SI2019` (+ `showConvertM`) | DONE | measured ratios | — | — |
| `magneticdipolemoment` | `Dim.magneticdipolemoment` (UnitSystems/Dim.lean), `Conv.magneticdipolemoment.dim`; `d(U,S)` = `Dim.magneticdipolemoment.conv U S`, `d(U)` = `naturalUnit U Dim.magneticdipolemoment` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `magneticfield` | `Dim.magneticfield` (UnitSystems/Dim.lean), `Conv.magneticfield.dim`; `d(U,S)` = `Dim.magneticfield.conv U S`, `d(U)` = `naturalUnit U Dim.magneticfield` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `magneticflux` | `Dim.magneticflux` (UnitSystems/Dim.lean), `Conv.magneticflux.dim`; `d(U,S)` = `Dim.magneticflux.conv U S`, `d(U)` = `naturalUnit U Dim.magneticflux` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `magneticfluxdensity` | `Dim.magneticfluxdensity` (UnitSystems/Dim.lean), `Conv.magneticfluxdensity.dim`; `d(U,S)` = `Dim.magneticfluxdensity.conv U S`, `d(U)` = `naturalUnit U Dim.magneticfluxdensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `magneticfluxquantum` | `Similitude.magneticfluxquantum (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `magneticmoment` | `Dim.magneticmoment` (UnitSystems/Dim.lean), `Conv.magneticmoment.dim`; `d(U,S)` = `Dim.magneticmoment.conv U S`, `d(U)` = `naturalUnit U Dim.magneticmoment` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `magneticpolarizability` | `Dim.magneticpolarizability` (UnitSystems/Dim.lean), `Conv.magneticpolarizability.dim`; `d(U,S)` = `Dim.magneticpolarizability.conv U S`, `d(U)` = `naturalUnit U Dim.magneticpolarizability` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `magneticpotential` | `Dim.magneticpotential` (UnitSystems/Dim.lean), `Conv.magneticpotential.dim`; `d(U,S)` = `Dim.magneticpotential.conv U S`, `d(U)` = `naturalUnit U Dim.magneticpotential` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `magneton` | `Similitude.magneton (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `magnetostatic` | `Similitude.magnetostatic (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `mass` | `Dim.mass` (UnitSystems/Dim.lean), `Conv.mass.dim`; `d(U,S)` = `Dim.mass.conv U S`, `d(U)` = `naturalUnit U Dim.mass` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `massflow` | `Dim.massflow` (UnitSystems/Dim.lean), `Conv.massflow.dim`; `d(U,S)` = `Dim.massflow.conv U S`, `d(U)` = `naturalUnit U Dim.massflow` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `maxwell` | `MeasureSystems.measured Similitude.Units.maxwell` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `mc` | exact group `mc Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `mcq` | exact group `mcq Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `me` | value exists as `mₑ` | PARTIAL | ASCII alias not defined | S | P2 |
| `meancalorie` | `MeasureSystems.measured Similitude.Units.meancalorie` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `measure` | `MValue` / `Measurement` (MeasureSystems/Measures.lean) | SKIP | `Measure{N}` is a type-parameter interning cache; Lean stores `Measurement` values directly (`MValue.toMeas` = `measure`) | — | — |
| `mebi` | exact group `mebi Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `mechanicalheat` | `MeasureSystems.measured Similitude.Units.mechanicalheat` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `mega` | exact group `mega Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `meridianmile` | `MeasureSystems.measured Similitude.Units.meridianmile` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `meter` | `MeasureSystems.measured Similitude.Units.meter` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `meters` | — | SKIP | exported but undefined in Julia MeasureSystems | — | — |
| `meu` | value exists as `μₑᵤ` | PARTIAL | ASCII alias not defined | S | P2 |
| `mi` | exact group `mi Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `micro` | exact group `micro Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `mile` | `MeasureSystems.measured Similitude.Units.mile` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `milli` | exact group `milli Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `minute` | `MeasureSystems.measured Similitude.Units.minute` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `mobility` | `Dim.mobility` (UnitSystems/Dim.lean), `Conv.mobility.dim`; `d(U,S)` = `Dim.mobility.conv U S`, `d(U)` = `naturalUnit U Dim.mobility` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `molality` | `Dim.molality` (UnitSystems/Dim.lean), `Conv.molality.dim`; `d(U,S)` = `Dim.molality.conv U S`, `d(U)` = `naturalUnit U Dim.molality` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `molaramount` | `Dim.molaramount` (UnitSystems/Dim.lean), `Conv.molaramount.dim`; `d(U,S)` = `Dim.molaramount.conv U S`, `d(U)` = `naturalUnit U Dim.molaramount` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `molarconductivity` | `Dim.molarconductivity` (UnitSystems/Dim.lean), `Conv.molarconductivity.dim`; `d(U,S)` = `Dim.molarconductivity.conv U S`, `d(U)` = `naturalUnit U Dim.molarconductivity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `molarenergy` | `Dim.molarenergy` (UnitSystems/Dim.lean), `Conv.molarenergy.dim`; `d(U,S)` = `Dim.molarenergy.conv U S`, `d(U)` = `naturalUnit U Dim.molarenergy` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `molarentropy` | `Dim.molarentropy` (UnitSystems/Dim.lean), `Conv.molarentropy.dim`; `d(U,S)` = `Dim.molarentropy.conv U S`, `d(U)` = `naturalUnit U Dim.molarentropy` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `molargas` | `Similitude.molargas (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `molarity` | `Dim.molarity` (UnitSystems/Dim.lean), `Conv.molarity.dim`; `d(U,S)` = `Dim.molarity.conv U S`, `d(U)` = `naturalUnit U Dim.molarity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `molarmass` | `Similitude.molarmass (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `molarsusceptibility` | `Dim.molarsusceptibility` (UnitSystems/Dim.lean), `Conv.molarsusceptibility.dim`; `d(U,S)` = `Dim.molarsusceptibility.conv U S`, `d(U)` = `naturalUnit U Dim.molarsusceptibility` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `molarvolume` | `Dim.molarvolume` (UnitSystems/Dim.lean), `Conv.molarvolume.dim`; `d(U,S)` = `Dim.molarvolume.conv U S`, `d(U)` = `naturalUnit U Dim.molarvolume` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `mole` | `MeasureSystems.measured Similitude.Units.mole` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `molecules` | — | SKIP | exported but undefined in Julia MeasureSystems | — | — |
| `moles` | — | SKIP | exported but undefined in Julia MeasureSystems | — | — |
| `momentum` | `Dim.momentum` (UnitSystems/Dim.lean), `Conv.momentum.dim`; `d(U,S)` = `Dim.momentum.conv U S`, `d(U)` = `naturalUnit U Dim.momentum` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `mp` | value exists as `mₚ` | PARTIAL | ASCII alias not defined | S | P2 |
| `mpe` | value exists as `μₚₑ` | PARTIAL | ASCII alias not defined | S | P2 |
| `mpge` | `MeasureSystems.measured Similitude.Units.mpge` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `mph` | `MeasureSystems.measured Similitude.Units.mph` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `mps` | `MeasureSystems.measured Similitude.Units.mps` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `mpu` | value exists as `μₚᵤ` | PARTIAL | ASCII alias not defined | S | P2 |
| `ms` | `MeasureSystems.measured Similitude.Units.ms` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `mu` | value exists as `Da` | PARTIAL | ASCII alias not defined | S | P2 |
| `mᵤ` | value exists as `Da` | PARTIAL | ASCII alias not defined | S | P2 |
| `mₑ` | exact group `mₑ Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `mₑ1990` | — | SKIP | exported but undefined in Julia MeasureSystems | — | — |
| `mₑ2014` | — | SKIP | exported but undefined in Julia MeasureSystems | — | — |
| `mₚ` | `measured (Similitude.protonmass .SI2019)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `nano` | exact group `nano Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `nauticalmile` | `MeasureSystems.measured Similitude.Units.nauticalmile` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `neper` | — | MISSING | `U(𝟏, log(𝟙))`, `U(𝟏, log10(𝟙))`, `U(𝟏, dB(𝟙))`: typed `Dim` has no LogGroup dimensions, so log-valued quantities cannot be formed (README lists these units) | M | P1 |
| `newton` | `MeasureSystems.measured Similitude.Units.newton` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `nineteen` | exact group `nineteen` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `nit` | `MeasureSystems.measured Similitude.Units.nit` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `nm` | exact group `nm Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `normal` | `Quantity.normal` | DONE | value projection | — | — |
| `numberdensity` | `Dim.numberdensity` (UnitSystems/Dim.lean), `Conv.numberdensity.dim`; `d(U,S)` = `Dim.numberdensity.conv U S`, `d(U)` = `naturalUnit U Dim.numberdensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `oersted` | `MeasureSystems.measured Similitude.Units.oersted` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `ohm` | `MeasureSystems.measured Similitude.Units.ohm` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `ounce` | `MeasureSystems.measured Similitude.Units.ounce` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `parsec` | `MeasureSystems.measured Similitude.Units.parsec` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `pascal` | `MeasureSystems.measured Similitude.Units.pascal` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `pebi` | exact group `pebi Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `permeability` | `Dim.permeability` (UnitSystems/Dim.lean), `Conv.permeability.dim`; `d(U,S)` = `Dim.permeability.conv U S`, `d(U)` = `naturalUnit U Dim.permeability` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `permeance` | `Dim.permeance` (UnitSystems/Dim.lean), `Conv.permeance.dim`; `d(U,S)` = `Dim.permeance.conv U S`, `d(U)` = `naturalUnit U Dim.permeance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `permittivity` | `Dim.permittivity` (UnitSystems/Dim.lean), `Conv.permittivity.dim`; `d(U,S)` = `Dim.permittivity.conv U S`, `d(U)` = `naturalUnit U Dim.permittivity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `peta` | exact group `peta Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `phot` | `MeasureSystems.measured Similitude.Units.phot` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `photonintensity` | `Dim.photonintensity` (UnitSystems/Dim.lean), `Conv.photonintensity.dim`; `d(U,S)` = `Dim.photonintensity.conv U S`, `d(U)` = `naturalUnit U Dim.photonintensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `photonirradiance` | `Dim.photonirradiance` (UnitSystems/Dim.lean), `Conv.photonirradiance.dim`; `d(U,S)` = `Dim.photonirradiance.conv U S`, `d(U)` = `naturalUnit U Dim.photonirradiance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `photonradiance` | `Dim.photonradiance` (UnitSystems/Dim.lean), `Conv.photonradiance.dim`; `d(U,S)` = `Dim.photonradiance.conv U S`, `d(U)` = `naturalUnit U Dim.photonradiance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `pico` | exact group `pico Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `pint` | `MeasureSystems.measured Similitude.Units.pint` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `planck` | `Similitude.planck (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `planckmass` | `Similitude.planckmass (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `planckreduced` | `Similitude.planckreduced (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `poise` | `MeasureSystems.measured Similitude.Units.poise` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `polestrength` | `Dim.polestrength` (UnitSystems/Dim.lean), `Conv.polestrength.dim`; `d(U,S)` = `Dim.polestrength.conv U S`, `d(U)` = `naturalUnit U Dim.polestrength` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `pop` | `Dim.pop` (UnitSystems/Dim.lean), `Conv.pop.dim`; `d(U,S)` = `Dim.pop.conv U S`, `d(U)` = `naturalUnit U Dim.pop` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `pound` | `MeasureSystems.measured Similitude.Units.pound` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `poundal` | `MeasureSystems.measured Similitude.Units.poundal` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `poundforce` | `MeasureSystems.measured Similitude.Units.poundforce` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `poundmole` | `MeasureSystems.measured Similitude.Units.poundmole` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `power` | `Dim.power` (UnitSystems/Dim.lean), `Conv.power.dim`; `d(U,S)` = `Dim.power.conv U S`, `d(U)` = `naturalUnit U Dim.power` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `powerdensity` | `Dim.powerdensity` (UnitSystems/Dim.lean), `Conv.powerdensity.dim`; `d(U,S)` = `Dim.powerdensity.conv U S`, `d(U)` = `naturalUnit U Dim.powerdensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `pressure` | `Dim.pressure` (UnitSystems/Dim.lean), `Conv.pressure.dim`; `d(U,S)` = `Dim.pressure.conv U S`, `d(U)` = `naturalUnit U Dim.pressure` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `protonelectron` | `UnitSystems.protonelectron (Sys.consts U)` (exact group) | DONE | generic formula; Scalar instantiation tested through system constants | — | — |
| `protonmass` | `Similitude.protonmass (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `protonunit` | `UnitSystems.protonunit (Sys.consts U)` (exact group) | DONE | generic formula; Scalar instantiation tested through system constants | — | — |
| `psi` | `MeasureSystems.measured Similitude.Units.psi` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `qA` | `Dim.charge.conv .Hartree .SI2019` (+ `showConvertM`) | DONE | measured ratios | — | — |
| `qS` | `Dim.charge.conv .Stoney .SI2019` (+ `showConvertM`) | DONE | measured ratios | — | — |
| `quart` | `MeasureSystems.measured Similitude.Units.quart` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `quotient` | `Similitude.quotient`, `printQuotient` (Similitude/Quotient.lean) | DONE | quotients.json (48 systems) | — | — |
| `radarmile` | `MeasureSystems.measured Similitude.Units.radarmile` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `radian` | `Similitude.radian (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `radiance` | `Dim.radiance` (UnitSystems/Dim.lean), `Conv.radiance.dim`; `d(U,S)` = `Dim.radiance.conv U S`, `d(U)` = `naturalUnit U Dim.radiance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `radiantintensity` | `Dim.radiantintensity` (UnitSystems/Dim.lean), `Conv.radiantintensity.dim`; `d(U,S)` = `Dim.radiantintensity.conv U S`, `d(U)` = `naturalUnit U Dim.radiantintensity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `radiationdensity` | `Similitude.radiationdensity (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `rankine` | `MeasureSystems.measured Similitude.Units.rankine` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `rationalization` | `Similitude.rationalization (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `rayl` | `MeasureSystems.measured Similitude.Units.rayl` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `rayleigh` | `MeasureSystems.measured Similitude.Units.rayleigh` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `re` | value exists as `rₑ` | PARTIAL | ASCII alias not defined | S | P2 |
| `reluctance` | `Dim.reluctance` (UnitSystems/Dim.lean), `Conv.reluctance.dim`; `d(U,S)` = `Dim.reluctance.conv U S`, `d(U)` = `naturalUnit U Dim.reluctance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `rem` | — | SKIP | `Base.rem` in Julia (calling it on a system errors) | — | — |
| `resistance` | `Dim.resistance` (UnitSystems/Dim.lean), `Conv.resistance.dim`; `d(U,S)` = `Dim.resistance.conv U S`, `d(U)` = `naturalUnit U Dim.resistance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `resistivity` | `Dim.resistivity` (UnitSystems/Dim.lean), `Conv.resistivity.dim`; `d(U,S)` = `Dim.resistivity.conv U S`, `d(U)` = `naturalUnit U Dim.resistivity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `reyn` | `MeasureSystems.measured Similitude.Units.reyn` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `roentgen` | `MeasureSystems.measured Similitude.Units.roentgen` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `rotationalinertia` | `Dim.rotationalinertia` (UnitSystems/Dim.lean), `Conv.rotationalinertia.dim`; `d(U,S)` = `Dim.rotationalinertia.conv U S`, `d(U)` = `naturalUnit U Dim.rotationalinertia` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `rpm` | `MeasureSystems.measured Similitude.Units.rpm` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `rydberg` | `Similitude.rydberg (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `rₑ` | `measured (Similitude.electronradius .SI2019)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `sackurtetrode` | `UnitSystems.sackurtetrode` (Num only) | PARTIAL | no exact/measured version (Julia MeasureSystems returns a Measurement) | S | P2 |
| `sealevel` | `MeasureSystems.measured Similitude.Units.sealevel` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `second` | `MeasureSystems.measured Similitude.Units.second` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `seven` | exact group `seven` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `siderealmonth` | `MeasureSystems.measured Similitude.Units.siderealmonth` | PARTIAL | uncertainty of `μE☾ = 81.300568(3)` (a measured non-generator coefficient) is dropped: e.g. lunarmass `3.6943034122(74)e-8` vs Julia `3.69430341(14)e-8`, synodicmonth prints no ± at all | M | P1 |
| `siderealyear` | `MeasureSystems.measured Similitude.Units.siderealyear` | PARTIAL | uncertainty of `μE☾ = 81.300568(3)` (a measured non-generator coefficient) is dropped: e.g. lunarmass `3.6943034122(74)e-8` vs Julia `3.69430341(14)e-8`, synodicmonth prints no ± at all | M | P1 |
| `siemens` | `MeasureSystems.measured Similitude.Units.siemens` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `similitude` | — | SKIP | exported but undefined in Julia MeasureSystems | — | — |
| `sixty` | exact group `sixty Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `slinch` | `MeasureSystems.measured Similitude.Units.slinch` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `slinchmole` | `MeasureSystems.measured Similitude.Units.slinchmole` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `slug` | `MeasureSystems.measured Similitude.Units.slug` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `slugmole` | `MeasureSystems.measured Similitude.Units.slugmole` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `slugs` | — | SKIP | exported but undefined in Julia MeasureSystems | — | — |
| `snap` | `Dim.snap` (UnitSystems/Dim.lean), `Conv.snap.dim`; `d(U,S)` = `Dim.snap.conv U S`, `d(U)` = `naturalUnit U Dim.snap` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `solarflux` | `MeasureSystems.measured Similitude.Units.solarflux` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `solarmass` | `MeasureSystems.measured Similitude.Units.solarmass` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `solidangle` | `Dim.solidangle` (UnitSystems/Dim.lean), `Conv.solidangle.dim`; `d(U,S)` = `Dim.solidangle.conv U S`, `d(U)` = `naturalUnit U Dim.solidangle` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `soundexposure` | `Dim.soundexposure` (UnitSystems/Dim.lean), `Conv.soundexposure.dim`; `d(U,S)` = `Dim.soundexposure.conv U S`, `d(U)` = `naturalUnit U Dim.soundexposure` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `spat` | `Similitude.spat (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `spatian` | `MeasureSystems.measured Similitude.Units.spatian` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `specificenergy` | `Dim.specificenergy` (UnitSystems/Dim.lean), `Conv.specificenergy.dim`; `d(U,S)` = `Dim.specificenergy.conv U S`, `d(U)` = `naturalUnit U Dim.specificenergy` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `specificentropy` | `Dim.specificentropy` (UnitSystems/Dim.lean), `Conv.specificentropy.dim`; `d(U,S)` = `Dim.specificentropy.conv U S`, `d(U)` = `naturalUnit U Dim.specificentropy` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `specificforce` | `Dim.specificforce` (UnitSystems/Dim.lean), `Conv.specificforce.dim`; `d(U,S)` = `Dim.specificforce.conv U S`, `d(U)` = `naturalUnit U Dim.specificforce` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `specificimpedance` | `Dim.specificimpedance` (UnitSystems/Dim.lean), `Conv.specificimpedance.dim`; `d(U,S)` = `Dim.specificimpedance.conv U S`, `d(U)` = `naturalUnit U Dim.specificimpedance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `specificity` | `Dim.specificity` (UnitSystems/Dim.lean), `Conv.specificity.dim`; `d(U,S)` = `Dim.specificity.conv U S`, `d(U)` = `naturalUnit U Dim.specificity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `specificmagnetization` | `Dim.specificmagnetization` (UnitSystems/Dim.lean), `Conv.specificmagnetization.dim`; `d(U,S)` = `Dim.specificmagnetization.conv U S`, `d(U)` = `naturalUnit U Dim.specificmagnetization` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `specificsusceptibility` | `Dim.specificsusceptibility` (UnitSystems/Dim.lean), `Conv.specificsusceptibility.dim`; `d(U,S)` = `Dim.specificsusceptibility.conv U S`, `d(U)` = `naturalUnit U Dim.specificsusceptibility` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `specificvolume` | `Dim.specificvolume` (UnitSystems/Dim.lean), `Conv.specificvolume.dim`; `d(U,S)` = `Dim.specificvolume.conv U S`, `d(U)` = `naturalUnit U Dim.specificvolume` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `specificweight` | `Dim.specificweight` (UnitSystems/Dim.lean), `Conv.specificweight.dim`; `d(U,S)` = `Dim.specificweight.conv U S`, `d(U)` = `naturalUnit U Dim.specificweight` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `spectralexposure` | `Dim.spectralexposure` (UnitSystems/Dim.lean), `Conv.spectralexposure.dim`; `d(U,S)` = `Dim.spectralexposure.conv U S`, `d(U)` = `naturalUnit U Dim.spectralexposure` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `spectralflux` | `Dim.spectralflux` (UnitSystems/Dim.lean), `Conv.spectralflux.dim`; `d(U,S)` = `Dim.spectralflux.conv U S`, `d(U)` = `naturalUnit U Dim.spectralflux` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `speed` | `Dim.speed` (UnitSystems/Dim.lean), `Conv.speed.dim`; `d(U,S)` = `Dim.speed.conv U S`, `d(U)` = `naturalUnit U Dim.speed` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `squaredegree` | `MeasureSystems.measured Similitude.Units.squaredegree` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `stagnance` | `Dim.stagnance` (UnitSystems/Dim.lean), `Conv.stagnance.dim`; `d(U,S)` = `Dim.stagnance.conv U S`, `d(U)` = `naturalUnit U Dim.stagnance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `statampere` | `MeasureSystems.measured Similitude.Units.statampere` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `statcoulomb` | `MeasureSystems.measured Similitude.Units.statcoulomb` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `statfarad` | `MeasureSystems.measured Similitude.Units.statfarad` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `stathenry` | `MeasureSystems.measured Similitude.Units.stathenry` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `statmho` | `MeasureSystems.measured Similitude.Units.statmho` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `statohm` | `MeasureSystems.measured Similitude.Units.statohm` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `stattesla` | `MeasureSystems.measured Similitude.Units.stattesla` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `statutemile` | `MeasureSystems.measured Similitude.Units.statutemile` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `statvolt` | `MeasureSystems.measured Similitude.Units.statvolt` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `statweber` | `MeasureSystems.measured Similitude.Units.statweber` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `stefan` | `Similitude.stefan (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `steradian` | `MeasureSystems.measured Similitude.Units.steradian` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `stilb` | `MeasureSystems.measured Similitude.Units.stilb` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `stokes` | `MeasureSystems.measured Similitude.Units.stokes` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `surveyacre` | `MeasureSystems.measured Similitude.Units.surveyacre` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `surveyfoot` | `MeasureSystems.measured Similitude.Units.surveyfoot` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `susceptibility` | `Dim.susceptibility` (UnitSystems/Dim.lean), `Conv.susceptibility.dim`; `d(U,S)` = `Dim.susceptibility.conv U S`, `d(U)` = `naturalUnit U Dim.susceptibility` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `synodicmonth` | `MeasureSystems.measured Similitude.Units.synodicmonth` | PARTIAL | uncertainty of `μE☾ = 81.300568(3)` (a measured non-generator coefficient) is dropped: e.g. lunarmass `3.6943034122(74)e-8` vs Julia `3.69430341(14)e-8`, synodicmonth prints no ± at all | M | P1 |
| `tA` | `Dim.time.conv .Hartree .SI2019` (+ `showConvertM`) | DONE | measured ratios | — | — |
| `tP` | `Dim.time.conv .PlanckGauss .SI2019` (+ `showConvertM`) | DONE | measured ratios | — | — |
| `tQCD` | `Dim.time.conv .QCD .SI2019` (+ `showConvertM`) | DONE | measured ratios | — | — |
| `tS` | `Dim.time.conv .Stoney .SI2019` (+ `showConvertM`) | DONE | measured ratios | — | — |
| `tablespoon` | `MeasureSystems.measured Similitude.Units.tablespoon` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `talbot` | `MeasureSystems.measured Similitude.Units.talbot` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `tau` | exact group `tau` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `tcq` | exact group `tcq Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `teaspoon` | `MeasureSystems.measured Similitude.Units.teaspoon` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `tebi` | exact group `tebi Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `technicalatmosphere` | `MeasureSystems.measured Similitude.Units.technicalatmosphere` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `temp` | — | SKIP | exported but undefined in Julia MeasureSystems | — | — |
| `temperature` | `Dim.temperature` (UnitSystems/Dim.lean), `Conv.temperature.dim`; `d(U,S)` = `Dim.temperature.conv U S`, `d(U)` = `naturalUnit U Dim.temperature` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `tera` | exact group `tera Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `tesla` | `MeasureSystems.measured Similitude.Units.tesla` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `th` | exact group `th Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `thermalconductance` | `Dim.thermalconductance` (UnitSystems/Dim.lean), `Conv.thermalconductance.dim`; `d(U,S)` = `Dim.thermalconductance.conv U S`, `d(U)` = `naturalUnit U Dim.thermalconductance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `thermalconductivity` | `Dim.thermalconductivity` (UnitSystems/Dim.lean), `Conv.thermalconductivity.dim`; `d(U,S)` = `Dim.thermalconductivity.conv U S`, `d(U)` = `naturalUnit U Dim.thermalconductivity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `thermalexpansion` | `Dim.thermalexpansion` (UnitSystems/Dim.lean), `Conv.thermalexpansion.dim`; `d(U,S)` = `Dim.thermalexpansion.conv U S`, `d(U)` = `naturalUnit U Dim.thermalexpansion` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `thermalresistance` | `Dim.thermalresistance` (UnitSystems/Dim.lean), `Conv.thermalresistance.dim`; `d(U,S)` = `Dim.thermalresistance.conv U S`, `d(U)` = `naturalUnit U Dim.thermalresistance` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `thermalresistivity` | `Dim.thermalresistivity` (UnitSystems/Dim.lean), `Conv.thermalresistivity.dim`; `d(U,S)` = `Dim.thermalresistivity.conv U S`, `d(U)` = `naturalUnit U Dim.thermalresistivity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `thermalunit` | `MeasureSystems.measured Similitude.Units.thermalunit` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `three` | exact group `three` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `ton` | `MeasureSystems.measured Similitude.Units.ton` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `tonne` | `MeasureSystems.measured Similitude.Units.tonne` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `tonsrefrigeration` | `MeasureSystems.measured Similitude.Units.tonsrefrigeration` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `tontnt` | `MeasureSystems.measured Similitude.Units.tontnt` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `torr` | `MeasureSystems.measured Similitude.Units.torr` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `turn` | `Similitude.turn (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `two` | exact group `two` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `unitname` | `Sys.name` | DONE | homs.json unitname | — | — |
| `units` | — | SKIP | exported but undefined in Julia MeasureSystems | — | — |
| `universal` | `molargas` exists | PARTIAL | alias `universal` not defined | S | P2 |
| `universe` | `UnitSystems.universeOf` | DONE | renamed | — | — |
| `vacuumimpedance` | `Similitude.vacuumimpedance (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `vacuumpermeability` | `Similitude.vacuumpermeability (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `vacuumpermittivity` | `Similitude.vacuumpermittivity (U : Sys) : Q U d` (Similitude/Physics.lean) + `MeasureSystems.measured` | DONE | system_constants.json (every system); measured system_constants.json (28 systems); dimension proved by `decide` | — | — |
| `vectorpotential` | `Dim.vectorpotential` (UnitSystems/Dim.lean), `Conv.vectorpotential.dim`; `d(U,S)` = `Dim.vectorpotential.conv U S`, `d(U)` = `naturalUnit U Dim.vectorpotential` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `viscosity` | `Dim.viscosity` (UnitSystems/Dim.lean), `Conv.viscosity.dim`; `d(U,S)` = `Dim.viscosity.conv U S`, `d(U)` = `naturalUnit U Dim.viscosity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `volt` | `MeasureSystems.measured Similitude.Units.volt` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `volume` | `Dim.volume` (UnitSystems/Dim.lean), `Conv.volume.dim`; `d(U,S)` = `Dim.volume.conv U S`, `d(U)` = `naturalUnit U Dim.volume` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `volumeflow` | `Dim.volumeflow` (UnitSystems/Dim.lean), `Conv.volumeflow.dim`; `d(U,S)` = `Dim.volumeflow.conv U S`, `d(U)` = `naturalUnit U Dim.volumeflow` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `volumeheatcapacity` | `Dim.volumeheatcapacity` (UnitSystems/Dim.lean), `Conv.volumeheatcapacity.dim`; `d(U,S)` = `Dim.volumeheatcapacity.conv U S`, `d(U)` = `naturalUnit U Dim.volumeheatcapacity` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `watt` | `MeasureSystems.measured Similitude.Units.watt` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `wavenumber` | `Dim.wavenumber` (UnitSystems/Dim.lean), `Conv.wavenumber.dim`; `d(U,S)` = `Dim.wavenumber.conv U S`, `d(U)` = `naturalUnit U Dim.wavenumber` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `weber` | `MeasureSystems.measured Similitude.Units.weber` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `wienfrequency` | `MeasureSystems.measured Similitude.Units.wienfrequency` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `wienwavelength` | `MeasureSystems.measured Similitude.Units.wienwavelength` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `yank` | `Dim.yank` (UnitSystems/Dim.lean), `Conv.yank.dim`; `d(U,S)` = `Dim.yank.conv U S`, `d(U)` = `naturalUnit U Dim.yank` | DONE | homs.json (48×131 images/display), unified.json, ratios.json, measured ratios.json | — | — |
| `yard` | `MeasureSystems.measured Similitude.Units.yard` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `year` | `MeasureSystems.measured Similitude.Units.year` | DONE | display in own system and in Metric identical to Julia (this audit's probe, 194/199); no repo golden yet | — | — |
| `yobi` | exact group `yobi Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `yocto` | exact group `ms Scalar .yocto` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `yotta` | exact group `ms Scalar .yotta` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `zebi` | exact group `zebi Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `zepto` | exact group `ms Scalar .zepto` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `zetta` | exact group `ms Scalar .zetta` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `°R` | exact group `degR Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `ħ` | exact group `ħ Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `ΔνCs` | exact group `ms Scalar .ΔνCs` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `Θ` | `USQ.Θ` (UnitSystems/Dim.lean) | DONE | type-level USQ generator; homs/unified goldens | — | — |
| `Λ` | — | SKIP | exported but undefined in Julia MeasureSystems | — | — |
| `Φ₀` | `measured (Similitude.magneticfluxquantum .SI2019)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `Ωᵢₜ` | exact group `ms Scalar .Ωᵢₜ` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `αG` | exact group `αG Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `αL` | exact group `αL Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `αinv` | exact group `ms Scalar .αinv` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `δμ₀` | — | MISSING | `μ₀ - 4π*1e-7 = 6.9e-16 ± 1.9e-16` measured constant | S | P2 |
| `ε₀` | `measured (Similitude.vacuumpermittivity .SI2019)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `κ` | `measured (Similitude.einstein .SI2019)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `μB` | `measured (Similitude.magneton .SI2019)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `μ₀` | exact group `μ₀ Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `μₑᵤ` | exact group `ms Scalar .μₑᵤ` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `μₑₚ` | exact group `μₑₚ Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `μₚᵤ` | exact group `ms Scalar .μₚᵤ` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `μₚₑ` | exact group `μₚₑ Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `ς` | exact group `ς Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `σ` | `measured (Similitude.stefan .SI2019)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `τ` | exact group `UnitAlg.tau` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `φ` | exact group `Consts.gen 33` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `ϵ₀` | value exists as `ε₀` | PARTIAL | ASCII alias not defined | S | P2 |
| `ℓP` | `Dim.length.conv .PlanckGauss .SI2019` (+ `showConvertM`) | DONE | measured ratios | — | — |
| `𝔉` | `measured (Similitude.faraday .SI2019)` | PARTIAL | reachable, but no named constant under the Julia symbol | S | P2 |
| `𝘤` | exact group `ms Scalar .cc` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `𝘦` | exact group `ms Scalar .ee` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `𝘦ᵣ` | exact group `eᵣ Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `𝘦ₙ` | exact group `eₙ Scalar` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `𝘩` | exact group `ms Scalar .hh` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `𝟏` | exact group `𝟏` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `𝟏𝟎` | exact group `𝟏𝟎` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `𝟏𝟏` | exact group `𝟏𝟏` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `𝟏𝟗` | exact group `𝟏𝟗` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `𝟐` | exact group `𝟐` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `𝟑` | exact group `𝟑` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `𝟒𝟑` | exact group `𝟒𝟑` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `𝟓` | exact group `𝟓` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `𝟔𝟎` | exact group `𝟔𝟎` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `𝟕` | exact group `𝟕` + `productM`/`showMeasures` (MeasureSystems/Measures.lean) | DONE | measures.json basis (44) + 24 named constants (value/uncertainty bit-exact); remaining constants are the same exact Similitude groups | — | — |
| `𝟙` | `USQ.one` | DONE | dimensionless | — | — |
| `(U::UnitSystem)(v, d) / Quantity{U}(v,d)` | `Sys.qty U d v` | DONE | quantity_arith.json | — | — |
| `(S::UnitSystem)(q::Quantity), q(S)` | `Quantity.to S` | DONE | quantity_arith.json (Metric, English targets) | — | — |
| `ConvertUnit (d(U,S))` | `ConvertUnit U S d`, `Dim.conv`, `showConvert` (Similitude/Ratio.lean) | PARTIAL | ratio/show/`inv` (Julia bug fixed) tested; missing `ConvertUnit * ConvertUnit`, `/`, `log/exp`, `Quantity(c::ConvertUnit)` | S | P2 |
| `d(v::Real, U, S=Metric)` | `Conv.convert` over `Scalar` (131 named dims) or `v / ratio d U S` | PARTIAL | no direct API for an arbitrary `Dim`/`USQGroup` | S | P2 |
| `naturalunits(U)` | `naturalUnit U d` (Similitude/Quantity.lean) | DONE | extras.json (48 × 11 bases) | — | — |
| `dimlist(U), printquotient(U)` | `dimlist`, `printQuotient` (Similitude/Quotient.lean) | DONE | extras.json / quotients.json | — | — |
| `latexquotient, latexquantity, latexdimensions, isodim, unitdim(U,D), dimlistlatex, convertext, unitext, systext, unitsym, unitdict` | `Sys.latexDim` only | MISSING | LaTeX/markdown table helpers (Similitude.jl:270-362, derived.jl:442-501) not ported | M | P2 |
| `morphism(U)` | `Sys.hom` (`LinMap`) | MISSING | 11×11 matrix accessor missing (broken in Julia when CONSTDIM=false) | S | P2 |
| `evaldim` | `UnitSystems.dimOf` (DimModel.lean) + proofs | DONE | dims recovered and proved | — | — |
| `convertdim` | `convertDim` (Similitude/Ratio.lean) | DONE | ConvertUnit display goldens | — | — |
| `display(::UnitSystem) with Quantity slots` | — | MISSING | Similitude/MeasureSystems print each slot as a dimensioned quantity (`kB = 1.380649e-23 [J⋅K⁻¹] SI2019, …`); no Lean printer for `UnitSystem Scalar` | S | P2 |
| `PERF: runtime `ratio(D,U,S)`` | `Similitude.ratio` | PARTIAL | measured 269,784 ns/call (compiled) vs Julia 2,617 ns: exact `Vector Rat 44` group arithmetic per call; `Quantity.to` with literal U,S,d is hoisted (1.24 ns vs Julia 3,041 ns) | M | P1 |
| `measurement("v(e)"), show, print_special, special_print` | `Measurement.parse?`, `display`, `printSpecial`, `specialPrint` (MeasureSystems/Measurement.lean) | DONE | measurements.json | — | — |
| `Measurements arithmetic (+ - * / ^ sqrt cbrt inv)` | `Measurement.*` (linear propagation with tags) | DONE | measurements.json arith; `exp/log` of a Measurement not provided | — | — |
| `measured derived-unit goldens` | Tests/MeasureSystems/Goldens.lean | PARTIAL | no golden for MeasureSystems' ~190 derived units (this audit's probe: 194/199 identical) | S | P2 |

## Geophysics.jl (v0.3.8): 182 exports

| Julia symbol | Lean name(s) + file | status | gap / evidence | effort | prio |
|---|---|---|---|---|---|
| `ARDC` | `Geophysics.ARDC : Atmosphere n` (Geophysics/Data.lean) | DONE | weather_*.json layer tables | — | — |
| `ARDCE` | `Geophysics.ARDCE : Atmosphere n` (Geophysics/Data.lean) | DONE | weather_*.json layer tables | — | — |
| `AbstractMole` | `Geophysics.Mole` (sum of `MoleGas` and `Mixture`) | SKIP | abstract supertype; Lean uses a closed sum type | — | — |
| `Air` | `Geophysics.Air` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `AirEnglish` | — | SKIP | exported but undefined in Julia | — | — |
| `AirMix` | `Geophysics.AirMix` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `Ar` | `Geophysics.Ar` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `Argon` | `Geophysics.Argon` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `Atmosphere` | `Geophysics.Atmosphere` (Geophysics/Atmosphere.lean) | DONE | weather_custom.json / fluidstate.json / planets.json; `Weather.integrate`, `Atmosphere.weather`, `W.state h`, `toUnits` cover the callable forms | — | — |
| `AtomicGas` | `Geophysics.AtomicGas` constructor (Geophysics/Gas.lean) | DONE | gases.json (constructed data + all properties) | — | — |
| `British` | `Sys.British` | DONE | re-exported UnitSystem | — | — |
| `CH4` | `Geophysics.CH4` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `CH₄` | `Geophysics.CH4` | PARTIAL | Unicode-subscript alias not defined (ASCII only) | S | P2 |
| `CO2` | `Geophysics.CO2` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `CO₂` | `Geophysics.CO2` | PARTIAL | Unicode-subscript alias not defined (ASCII only) | S | P2 |
| `CarbonDioxide` | `Geophysics.CarbonDioxide` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `Ceres` | `Geophysics.Ceres : Planet` (Geophysics/Data.lean) | DONE | planets.json | — | — |
| `DiatomicGas` | `Geophysics.DiatomicGas` constructor (Geophysics/Gas.lean) | DONE | gases.json (constructed data + all properties) | — | — |
| `Earth` | `Geophysics.Earth : Planet` (Geophysics/Data.lean) | DONE | planets.json | — | — |
| `Earth1922` | `Geophysics.Earth1922 : Weather n` (Geophysics/Data.lean) | DONE | weather_<name>.json (grid × 21 ops × ratios, displays) | — | — |
| `Earth1922English` | `Geophysics.Earth1922English : Weather n` (Geophysics/Data.lean) | DONE | weather_<name>.json (grid × 21 ops × ratios, displays) | — | — |
| `Earth1925` | `Geophysics.Earth1925 : Weather n` (Geophysics/Data.lean) | DONE | weather_<name>.json (grid × 21 ops × ratios, displays) | — | — |
| `Earth1925English` | `Geophysics.Earth1925English : Weather n` (Geophysics/Data.lean) | DONE | weather_<name>.json (grid × 21 ops × ratios, displays) | — | — |
| `Earth1956` | `Geophysics.Earth1956 : Weather n` (Geophysics/Data.lean) | DONE | weather_<name>.json (grid × 21 ops × ratios, displays) | — | — |
| `Earth1956English` | `Geophysics.Earth1956English : Weather n` (Geophysics/Data.lean) | DONE | weather_<name>.json (grid × 21 ops × ratios, displays) | — | — |
| `Earth1959` | `Geophysics.Earth1959 : Weather n` (Geophysics/Data.lean) | DONE | weather_<name>.json (grid × 21 ops × ratios, displays) | — | — |
| `Earth1959English` | `Geophysics.Earth1959English : Weather n` (Geophysics/Data.lean) | DONE | weather_<name>.json (grid × 21 ops × ratios, displays) | — | — |
| `Earth1962` | `Geophysics.Earth1962 : Weather n` (Geophysics/Data.lean) | DONE | weather_<name>.json (grid × 21 ops × ratios, displays) | — | — |
| `Earth1962English` | `Geophysics.Earth1962English : Weather n` (Geophysics/Data.lean) | DONE | weather_<name>.json (grid × 21 ops × ratios, displays) | — | — |
| `Earth1966` | `Geophysics.Earth1966 : Weather n` (Geophysics/Data.lean) | DONE | weather_<name>.json (grid × 21 ops × ratios, displays) | — | — |
| `Earth1966English` | `Geophysics.Earth1966English : Weather n` (Geophysics/Data.lean) | DONE | weather_<name>.json (grid × 21 ops × ratios, displays) | — | — |
| `Earth1976` | `Geophysics.Earth1976 : Weather n` (Geophysics/Data.lean) | DONE | weather_<name>.json (grid × 21 ops × ratios, displays) | — | — |
| `Earth1976English` | `Geophysics.Earth1976English : Weather n` (Geophysics/Data.lean) | DONE | weather_<name>.json (grid × 21 ops × ratios, displays) | — | — |
| `English` | `Sys.English` | DONE | re-exported UnitSystem | — | — |
| `Eris` | `Geophysics.Eris : Planet` (Geophysics/Data.lean) | DONE | planets.json | — | — |
| `FluidState` | `Geophysics.FluidState` (Geophysics/Gas.lean) | DONE | weather_custom.json / fluidstate.json / planets.json; `Weather.integrate`, `Atmosphere.weather`, `W.state h`, `toUnits` cover the callable forms | — | — |
| `Geophysics` | `Geophysics` (lib) | SKIP | module name | — | — |
| `H2` | `Geophysics.H2` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `He` | `Geophysics.He` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `Helium` | `Geophysics.Helium` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `Hydrogen` | `Geophysics.Hydrogen` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `H₂` | `Geophysics.H2` | PARTIAL | Unicode-subscript alias not defined (ASCII only) | S | P2 |
| `Jupiter` | `Geophysics.Jupiter : Planet` (Geophysics/Data.lean) | DONE | planets.json | — | — |
| `Kr` | `Geophysics.Kr` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `Krypton` | `Geophysics.Krypton` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `Mars` | `Geophysics.Mars : Planet` (Geophysics/Data.lean) | DONE | planets.json | — | — |
| `Mercury` | `Geophysics.Mercury : Planet` (Geophysics/Data.lean) | DONE | planets.json | — | — |
| `Methane` | `Geophysics.Methane` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `Metric` | `Sys.Metric` | DONE | re-exported UnitSystem | — | — |
| `MoleGas` | `Geophysics.MoleGas` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `Moon` | `Geophysics.Moon : Planet` (Geophysics/Data.lean) | DONE | planets.json | — | — |
| `N2` | `Geophysics.N2` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `Ne` | `Geophysics.Ne` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `Neon` | `Geophysics.Neon` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `Neptune` | `Geophysics.Neptune : Planet` (Geophysics/Data.lean) | DONE | planets.json | — | — |
| `Nitrogen` | `Geophysics.Nitrogen` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `Nitrox` | `Geophysics.Nitrox` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `N₂` | `Geophysics.N2` | PARTIAL | Unicode-subscript alias not defined (ASCII only) | S | P2 |
| `O2` | `Geophysics.O2` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `Oxygen` | `Geophysics.Oxygen` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `O₂` | `Geophysics.O2` | PARTIAL | Unicode-subscript alias not defined (ASCII only) | S | P2 |
| `Planet` | `Geophysics.Planet` (Geophysics/Planet.lean) | DONE | weather_custom.json / fluidstate.json / planets.json; `Weather.integrate`, `Atmosphere.weather`, `W.state h`, `toUnits` cover the callable forms | — | — |
| `Pluto` | `Geophysics.Pluto : Planet` (Geophysics/Data.lean) | DONE | planets.json | — | — |
| `Saturn` | `Geophysics.Saturn : Planet` (Geophysics/Data.lean) | DONE | planets.json | — | — |
| `Standard` | `Geophysics.Standard : Weather n` (Geophysics/Data.lean); `standard year english` mirrors `ENV["STDATM"]` | DONE | weather_<name>.json (grid × 21 ops × ratios, displays) | — | — |
| `Sun` | `Geophysics.Sun : Planet` (Geophysics/Data.lean) | DONE | planets.json | — | — |
| `SutherlandGas` | `Geophysics.SutherlandGas` constructor (Geophysics/Gas.lean) | DONE | gases.json (constructed data + all properties) | — | — |
| `Traces` | `Geophysics.Traces` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `TriatomicGas` | `Geophysics.TriatomicGas` constructor (Geophysics/Gas.lean) | DONE | gases.json (constructed data + all properties) | — | — |
| `US22` | `Geophysics.US22 : Atmosphere n` (Geophysics/Data.lean) | DONE | weather_*.json layer tables | — | — |
| `US22E` | `Geophysics.US22E : Atmosphere n` (Geophysics/Data.lean) | DONE | weather_*.json layer tables | — | — |
| `US25` | `Geophysics.US25 : Atmosphere n` (Geophysics/Data.lean) | DONE | weather_*.json layer tables | — | — |
| `US25E` | `Geophysics.US25E : Atmosphere n` (Geophysics/Data.lean) | DONE | weather_*.json layer tables | — | — |
| `US56` | `Geophysics.US56 : Atmosphere n` (Geophysics/Data.lean) | DONE | weather_*.json layer tables | — | — |
| `US56E` | `Geophysics.US56E : Atmosphere n` (Geophysics/Data.lean) | DONE | weather_*.json layer tables | — | — |
| `US59` | `Geophysics.US59 : Atmosphere n` (Geophysics/Data.lean) | DONE | weather_*.json layer tables | — | — |
| `US59E` | `Geophysics.US59E : Atmosphere n` (Geophysics/Data.lean) | DONE | weather_*.json layer tables | — | — |
| `US62` | `Geophysics.US62 : Atmosphere n` (Geophysics/Data.lean) | DONE | weather_*.json layer tables | — | — |
| `US62E` | `Geophysics.US62E : Atmosphere n` (Geophysics/Data.lean) | DONE | weather_*.json layer tables | — | — |
| `US66` | `Geophysics.US66 : Atmosphere n` (Geophysics/Data.lean) | DONE | weather_*.json layer tables | — | — |
| `US66E` | `Geophysics.US66E : Atmosphere n` (Geophysics/Data.lean) | DONE | weather_*.json layer tables | — | — |
| `US76` | `Geophysics.US76 : Atmosphere n` (Geophysics/Data.lean) | DONE | weather_*.json layer tables | — | — |
| `US76E` | `Geophysics.US76E : Atmosphere n` (Geophysics/Data.lean) | DONE | weather_*.json layer tables | — | — |
| `Uranus` | `Geophysics.Uranus : Planet` (Geophysics/Data.lean) | DONE | planets.json | — | — |
| `Venus` | `Geophysics.Venus : Planet` (Geophysics/Data.lean) | DONE | planets.json | — | — |
| `Weather` | `Geophysics.Weather` (Geophysics/Atmosphere.lean) | DONE | weather_custom.json / fluidstate.json / planets.json; `Weather.integrate`, `Atmosphere.weather`, `W.state h`, `toUnits` cover the callable forms | — | — |
| `Xe` | `Geophysics.Xe` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `Xenon` | `Geophysics.Xenon` (Geophysics/Data.lean) | DONE | gases.json | — | — |
| `air` | `Geophysics.air` (Geophysics/Data.lean) | DONE | gases.json; Julia StackOverflow defect fixed (policy skip) | — | — |
| `angularfrequency` | `Planet.angularfrequency` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `aspectratio` | `Planet.aspectratio` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `boltzmann` | `Mole.boltzmann` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `centripetal` | `Planet.centripetal` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `deflection` | `Planet.deflection` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `deflectiongeocentric` | `Planet.deflectiongeocentric` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `deflectiongeodetic` | `Planet.deflectiongeodetic` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `density` | `Weather.density h U`, `Weather.eval .density`, `FluidState.density` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `densityratio` | `Weather.ratio .density h` / `Column.ratio` | PARTIAL | no named function `densityratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `dynamicformfactor` | `Planet.dynamicformfactor` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `eccentricity` | `Planet.eccentricity` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `eccentricity2` | `Planet.eccentricity2` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `elasticity` | `Weather.elasticity h U`, `Weather.eval .elasticity`, `FluidState.elasticity` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `elasticityratio` | `Weather.ratio .elasticity h` / `Column.ratio` | PARTIAL | no named function `elasticityratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `electronmass` | `Mole.electronmass` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `flattening` | `Planet.flattening` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `fluid` | `Weather.fluid` | DONE | weather_*.json / planets.json | — | — |
| `freedom` | `Weather.freedom h U`, `Weather.eval .freedom`, `FluidState.freedom`, `Mole.{n} T U` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `freedomratio` | `Weather.ratio .freedom h` / `Column.ratio` | PARTIAL | no named function `freedomratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `frequency` | `Planet.frequency` (Geophysics/Planet.lean) / `Mole.frequency` | DONE | planets.json; gases.json | — | — |
| `gasconstant` | `Mole.gasconstant` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `gravitation` | `Planet.gravitation` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `gravity` | `Planet.gravity ϕ`, `Planet.gravitySpherical`, `Planet.gravityAt h θ`, `Weather.gravity h`, `Weather.gravitySea`, `Mole.gravity` | DONE | planets.json, weather_*.json | — | — |
| `gravitycomponents` | `Planet.gravitycomponents` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `gravitygeodetic` | `Planet.gravitygeodetic` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `heatcapacity` | `Weather.heatcapacity h U`, `Weather.eval .heatcapacity`, `FluidState.heatcapacity` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `heatpressure` | `Weather.heatpressure h U`, `Weather.eval .heatpressure`, `FluidState.heatpressure`, `Mole.{n} T U` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `heatpressureratio` | `Weather.ratio .heatpressure h` / `Column.ratio` | PARTIAL | no named function `heatpressureratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `heatratio` | `Weather.heatratio h U`, `Weather.eval .heatratio`, `FluidState.heatratio`, `Mole.{n} T U` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `heatratioratio` | `Weather.ratio .heatratio h` / `Column.ratio` | PARTIAL | no named function `heatratioratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `heatvolume` | `Weather.heatvolume h U`, `Weather.eval .heatvolume`, `FluidState.heatvolume`, `Mole.{n} T U` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `heatvolumeratio` | `Weather.ratio .heatvolume h` / `Column.ratio` | PARTIAL | no named function `heatvolumeratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `intensity` | `Weather.intensity h U`, `Weather.eval .intensity`, `FluidState.intensity` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `intensityratio` | `Weather.ratio .intensity h` / `Column.ratio` | PARTIAL | no named function `intensityratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `kinematic` | `Weather.kinematic h U`, `Weather.eval .kinematic`, `FluidState.kinematic` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `kinematicratio` | `Weather.ratio .kinematic h` / `Column.ratio` | PARTIAL | no named function `kinematicratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `latitudegeocentric` | `Planet.latitudegeocentric` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `latitudegeodetic` | `Planet.latitudegeodetic` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `latitudeparametric` | `Planet.latitudeparametric` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `layer` | `Weather.layer` | DONE | weather_*.json / planets.json | — | — |
| `lightspeed` | `Mole.lightspeed` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `lineareccentricity` | `Planet.lineareccentricity` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `lorentz` | `Mole.lorentz` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `luminousefficacy` | `Mole.luminousefficacy` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `mass` | `Planet.mass` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `molarmass` | `Mole.molarmass` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `molecularmass` | `Mole.molecularmass` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `oblateness` | `Planet.oblateness` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `period` | `Planet.period` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `planck` | `Mole.planck` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `planckreduced` | `Mole.planckreduced` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `prandtl` | `Weather.prandtl h U`, `Weather.eval .prandtl`, `FluidState.prandtl`, `Mole.{n} T U` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `prandtlratio` | `Weather.ratio .prandtl h` / `Column.ratio` | PARTIAL | no named function `prandtlratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `pressure` | `Weather.pressure h U`, `Weather.eval .pressure`, `FluidState.pressure` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `pressureratio` | `Weather.ratio .pressure h` / `Column.ratio` | PARTIAL | no named function `pressureratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `q` | `Planet.q` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `q0` | `Planet.q0` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `q01` | `Planet.q01` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `q1` | `Planet.q1` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `radian` | `Mole.radian` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `radius` | `Weather.radius`, `Planet.radius` | DONE | weather_*.json / planets.json | — | — |
| `radiusgeodetic` | `Planet.radiusgeodetic` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `rationalization` | `Mole.rationalization` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `secondzonalharmonic` | `Planet.secondzonalharmonic` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `semimajor` | `Planet.semimajor` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `semiminor` | `Planet.semiminor` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `sonicspeed` | `Weather.sonicspeed h U`, `Weather.eval .sonicspeed`, `FluidState.sonicspeed`, `Mole.{n} T U` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `sonicspeedratio` | `Weather.ratio .sonicspeed h` / `Column.ratio` | PARTIAL | no named function `sonicspeedratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `specificenergy` | `Weather.specificenergy h U`, `Weather.eval .specificenergy`, `FluidState.specificenergy`, `Mole.{n} T U` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `specificenergyratio` | `Weather.ratio .specificenergy h` / `Column.ratio` | PARTIAL | no named function `specificenergyratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `specificenthalpy` | `Weather.specificenthalpy h U`, `Weather.eval .specificenthalpy`, `FluidState.specificenthalpy`, `Mole.{n} T U` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `specificenthalpyratio` | `Weather.ratio .specificenthalpy h` / `Column.ratio` | PARTIAL | no named function `specificenthalpyratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `specificimpedance` | `Weather.specificimpedance h U`, `Weather.eval .specificimpedance`, `FluidState.specificimpedance` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `specificimpedanceratio` | `Weather.ratio .specificimpedance h` / `Column.ratio` | PARTIAL | no named function `specificimpedanceratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `specificvolume` | `Weather.specificvolume h U`, `Weather.eval .specificvolume`, `FluidState.specificvolume` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `specificvolumeratio` | `Weather.ratio .specificvolume h` / `Column.ratio` | PARTIAL | no named function `specificvolumeratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `specificweight` | `Weather.specificweight h U`, `Weather.eval .specificweight`, `FluidState.specificweight` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `specificweightratio` | `Weather.ratio .specificweight h` / `Column.ratio` | PARTIAL | no named function `specificweightratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `speed` | `Planet.speed` (Geophysics/Planet.lean) | DONE | planets.json | — | — |
| `sutherlandconductivity` | `Mole.sutherlandconductivity` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `sutherlandviscosity` | `Mole.sutherlandviscosity` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `temperature` | `Weather.temperature h U`, `Weather.eval .temperature`, `FluidState.temperature` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `temperatureratio` | `Weather.ratio .temperature h` / `Column.ratio` | PARTIAL | no named function `temperatureratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `thermalconductivity` | `Weather.thermalconductivity h U`, `Weather.eval .thermalconductivity`, `FluidState.thermalconductivity`, `Mole.{n} T U` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `thermalconductivityratio` | `Weather.ratio .thermalconductivity h` / `Column.ratio` | PARTIAL | no named function `thermalconductivityratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `thermaldiffusivity` | `Weather.thermaldiffusivity h U`, `Weather.eval .thermaldiffusivity`, `FluidState.thermaldiffusivity` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `thermaldiffusivityratio` | `Weather.ratio .thermaldiffusivity h` / `Column.ratio` | PARTIAL | no named function `thermaldiffusivityratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `units` | `Weather.units`, `FluidState.units`, `Atmosphere.units` | DONE | — | — | — |
| `vacuumpermeability` | `Mole.vacuumpermeability` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `vibration` | `Mole.vibration` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `viscosity` | `Weather.viscosity h U`, `Weather.eval .viscosity`, `FluidState.viscosity`, `Mole.{n} T U` | DONE | weather_*.json (grid, layer primitives, cross-unit forms) + fluidstate.json + gases.json | — | — |
| `viscosityratio` | `Weather.ratio .viscosity h` / `Column.ratio` | PARTIAL | no named function `viscosityratio` (only the `Op`-indexed form); values tested (weather_*.json) | S | P2 |
| `wavenumber` | `Mole.wavenumber` (Geophysics/Gas.lean) | DONE | gases.json | — | — |
| `README example `gravity(h)`, `temperature(h)`, `pressure(h)`, `sonicspeed(h)`` | `Standard.gravity 1000.0` etc. | DONE | Lean = Julia v0.3.8 bit for bit (9.803570410328458, 281.6610206800807, 89876.36320119529, 336.50428292372095); the README's printed numbers are stale in Julia itself | — | — |
| `any user-built `UnitSystem` as `U`` | `U : Sys` (48 named systems) | PARTIAL | Geophysics functions take a `Sys`, so custom systems (e.g. an `EntropySystem`) cannot be used | M | P2 |
| `Similitude branch (`usingSimilitude`)` | `Geophysics.Typed` (`Qty U d` API) | DONE | Tests/Geophysics/Typed.lean | — | — |
| `PERF: altitude functions (Earth1959, 10⁶ pts)` | `Column.eval` | PARTIAL | Lean vs Julia ns/eval: temperature 8.2/3.6, pressure 24.3/14.7, density 24.3/15.2 (slower); sonicspeed 79.7/198.8, viscosity 16.2/54.7, kinematic 31.6/76.1 (faster) | S | P1 |
| `PERF: `gravity(ϕ, Earth)`` | `Planet.gravity` | PARTIAL | 19.2 ns vs Julia 2.8 ns: Somigliana constants (γₑ, γₚ, k) recomputed per call instead of cached per planet | S | P1 |

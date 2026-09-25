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

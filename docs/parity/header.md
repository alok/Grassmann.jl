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

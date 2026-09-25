import Bench.Harness
import Bench.Harness.Optional
import Bench.Math
import Bench.JuliaBase
import Bench.StaticVectors
import Bench.DirectSum
import Bench.UnitSystems
import Bench.MeshTopology
import Bench.Fatou
import Bench.Geophysics

/-!
Benchmarks (`lake exe bench`, driver `Bench/Main.lean`). Every suite runs on the harness of
`Bench.Harness` and has a Julia twin under `oracle/bench/`; `scripts/bench/compare.py` joins
the two result files into `docs/perf/latest.md`. See `docs/perf/README.md`.
-/

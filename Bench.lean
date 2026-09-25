import Bench.Harness
import Bench.Harness.Optional
import Bench.Math
import Bench.MeshTopology
import Bench.Fatou

/-!
Benchmarks (`lake exe bench`, driver `Bench/Main.lean`). Every suite runs on the harness of
`Bench.Harness` and has a Julia twin under `oracle/bench/`; `scripts/bench/compare.py` joins
the two result files into `docs/perf/latest.md`. See `docs/perf/README.md`.
-/

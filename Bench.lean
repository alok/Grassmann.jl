import Bench.Harness
import Bench.Harness.Optional
import Bench.Math
import Bench.JuliaBase
import Bench.StaticVectors
import Bench.DirectSum
import Bench.UnitSystems
import Bench.Dendriform
import Bench.Wilkinson
import Bench.MeshTopology
import Bench.Fatou
import Bench.Grassmann
import Bench.Geophysics
import Bench.Dynamic
import Bench.Composite
import Bench.Forms
import Bench.Cartan
import Bench.Adapode

/-!
Benchmarks (`lake exe bench`, driver `Bench/Main.lean`). Every suite runs on the harness of
`Bench.Harness` and has a Julia twin under `oracle/bench/`; `scripts/bench/compare.py` joins
the two result files into `docs/perf/latest.md`. See `docs/perf/README.md`.
-/

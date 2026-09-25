import Bench.Grassmann.Spaces
import Bench.Grassmann.Extra
import Bench.Grassmann.Batch

/-!
# `grassmann`: the typed algebra at `Float`

Julia twin: `oracle/bench/grassmann.jl` (Grassmann 0.8.46). Keys `grassmann/<space>/<op>`, ns
per operation over rings of 1024 random operands (`Bench.Grassmann.Common`), for the standard
spaces with pre-generated kernels (`ℝ2`, `ℝ3`, `ℝ4`, `STA`, `PGA2`, `PGA3`, `CGA2`, `CGA3`).
The cases are listed in `Bench.Grassmann.Products` (typed operations, all groups in `ℝ3`, `STA`,
`PGA3`, `CGA3`, the core groups elsewhere) and `Bench.Grassmann.Batch` (batch kernels against
Julia's `map`/`map!`); results and findings in docs/PERF.md.
-/

namespace Bench.Grassmann

open _root_.Grassmann DirectSum Bench

/-- The suite. -/
def run : Suite := ⟨"grassmann", do
  casesR2; casesR3; casesR4; casesSTA; casesPGA2; casesPGA3; casesCGA2; casesCGA3
  batchR3; batchSTA; batchPGA3; batchCGA3⟩

end Bench.Grassmann

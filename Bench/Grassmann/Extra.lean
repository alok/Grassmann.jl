import Bench.Grassmann.Products

/-!
# The typed cases of the other standard spaces (`ℝ2`, `ℝ4`, `PGA2`, `CGA2`): products,
sandwiches, reverse and Hodge complements (the inner products, norms, linear combinations, unary
maps and fused cases run in the four benchmark spaces). `ℝ5` through `basis!` was measured once
(docs/PERF.md, 2026-09-25) and is not part of the suite: its generated kernels alone add some
60 MB to a module's `.olean`.
-/

namespace Bench.Grassmann

open _root_.Grassmann DirectSum Bench

/-- The case groups of the other spaces. -/
def coreCases : CaseSet :=
  { inner := false, norms := false, linear := false, unary := false, fused := false, floors := false }

set_option maxHeartbeats 1000000 in
/-- `ℝ2`. -/ def casesR2 : BenchM Unit := space_cases% "ℝ2" ℝ2 1 coreCases
set_option maxHeartbeats 1000000 in
/-- `ℝ4`. -/ def casesR4 : BenchM Unit := space_cases% "ℝ4" ℝ4 3 coreCases
set_option maxHeartbeats 1000000 in
/-- `PGA2`. -/ def casesPGA2 : BenchM Unit := space_cases% "PGA2" PGA2 5 coreCases
set_option maxHeartbeats 1000000 in
/-- `CGA2`. -/ def casesCGA2 : BenchM Unit := space_cases% "CGA2" CGA2 7 coreCases

end Bench.Grassmann

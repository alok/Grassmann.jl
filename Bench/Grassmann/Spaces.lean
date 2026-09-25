import Bench.Grassmann.Products

/-!
# The typed cases of the four benchmark spaces (`ℝ3`, `STA`, `PGA3`, `CGA3`): every case group
(one definition per space, each expanding `space_cases%` at its concrete space).
-/

namespace Bench.Grassmann

open _root_.Grassmann DirectSum Bench

set_option maxHeartbeats 1000000 in
/-- `ℝ3`. -/ def casesR3 : BenchM Unit := space_cases% "ℝ3" ℝ3 2 { inverses := true, spinorInverses := true }
set_option maxHeartbeats 1000000 in
/-- `STA`. -/ def casesSTA : BenchM Unit := space_cases% "STA" STA 4 {}
set_option maxHeartbeats 1000000 in
/-- `PGA3`. -/ def casesPGA3 : BenchM Unit := space_cases% "PGA3" PGA3 6 { inverses := true }
set_option maxHeartbeats 1000000 in
/-- `CGA3`. -/ def casesCGA3 : BenchM Unit := space_cases% "CGA3" CGA3 8 {}

end Bench.Grassmann

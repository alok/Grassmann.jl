import Bench.Grassmann.Products

/-!
# `grassmann`: the typed algebra at `Float`

Julia twin: `oracle/bench/grassmann.jl` (Grassmann 0.8.46). Keys `grassmann/<space>/<op>`, ns
per operation over rings of 1024 random operands (`Bench.Grassmann.Common`), for the standard
spaces with pre-generated kernels (`ℝ2`, `ℝ3`, `ℝ4`, `STA`, `PGA2`, `PGA3`, `CGA2`, `CGA3`) and
`ℝ5` through `basis!` (kernels generated where the space is declared, as a user's would be).
The cases are listed in `Bench.Grassmann.Products`; results and findings in docs/PERF.md.
-/

namespace Bench.Grassmann

open _root_.Grassmann DirectSum Bench

namespace R5
/-! `ℝ5` through `basis!`: the space, its blades and its generated kernels. -/
basis! S!"+++++"
end R5

/-! One definition per space (each expands `space_cases%` at its concrete space). -/

set_option maxHeartbeats 1000000 in
/-- `ℝ2`. -/ def casesR2 : BenchM Unit := space_cases% "ℝ2" ℝ2 1 { inverses := true, spinorInverses := true }
set_option maxHeartbeats 1000000 in
/-- `ℝ3`. -/ def casesR3 : BenchM Unit := space_cases% "ℝ3" ℝ3 2 { inverses := true, spinorInverses := true }
set_option maxHeartbeats 1000000 in
/-- `ℝ4`. -/ def casesR4 : BenchM Unit := space_cases% "ℝ4" ℝ4 3 { inverses := true }
set_option maxHeartbeats 1000000 in
/-- `STA`. -/ def casesSTA : BenchM Unit := space_cases% "STA" STA 4 {}
set_option maxHeartbeats 1000000 in
/-- `PGA2`. -/ def casesPGA2 : BenchM Unit := space_cases% "PGA2" PGA2 5 { inverses := true }
set_option maxHeartbeats 1000000 in
/-- `PGA3`. -/ def casesPGA3 : BenchM Unit := space_cases% "PGA3" PGA3 6 { inverses := true }
set_option maxHeartbeats 1000000 in
/-- `CGA2`. -/ def casesCGA2 : BenchM Unit := space_cases% "CGA2" CGA2 7 {}
set_option maxHeartbeats 1000000 in
/-- `CGA3`. -/ def casesCGA3 : BenchM Unit := space_cases% "CGA3" CGA3 8 {}
set_option maxHeartbeats 1000000 in
/-- `ℝ5` (kernels from `basis!`). -/ def casesR5 : BenchM Unit := space_cases% "ℝ5" R5.V 9 { inverses := true }

/-- The suite. -/
def run : Suite := ⟨"grassmann", do
  casesR2; casesR3; casesR4; casesSTA; casesPGA2; casesPGA3; casesCGA2; casesCGA3; casesR5⟩

end Bench.Grassmann

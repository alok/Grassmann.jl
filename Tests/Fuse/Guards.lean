/-
Build-time fusion checks (`Grassmann.Fuse`): every `fuse_checks%` group in every standard space
at `Float`, the exact `Int` checks, a diagonal metric with non-unit coefficients and a space
with the reference kernels only, each run through the interpreter while this module builds (a
mismatch fails the build). They add nothing to the `.olean` (straight-line code grows as the
square of the storage size, and compiling every group of every space would store hundreds of
megabytes of generated code); `Tests.Fuse.Run` runs a compiled subset under `lake test`.
-/
import Tests.Fuse.Checks

open Grassmann DirectSum StaticVectors

namespace FuseTests

namespace Diag
/-! A diagonal metric with non-unit coefficients (generated kernels, `Fuse.coef` constants). -/
basis! D!"1,2,-3"
end Diag

namespace RefOnly
/-! A space with the reference kernels only (no generated instance). -/
basis! (kernels := false) S!"+-++"
end RefOnly

/-- `#fuse_guard checks seed`: run a group of fusion checks at build time; any mismatch (or a
group with no checks) is an error. -/
syntax (name := fuseGuard) "#fuse_guard " term:max num : command

macro_rules
  | `(#fuse_guard $f $seed) => `(#eval show IO Unit from do
      let t := ($f : Nat → Tally → Tally) $seed {}
      if t.fail > 0 then throw (IO.userError s!"fusion mismatch: {t.messages}")
      if t.pass == 0 then throw (IO.userError "no fusion checks ran"))

set_option maxHeartbeats 4000000

#fuse_guard (fuse_checks% "ℝ2" ℝ2 Float) 1
#fuse_guard (fuse_checks% "ℝ4" ℝ4 Float) 3
#fuse_guard (fuse_checks% "STA" STA Float) 4
#fuse_guard (fuse_checks% "PGA2" PGA2 Float) 5
#fuse_guard (fuse_checks% "CGA2" CGA2 Float) 7
#fuse_guard (fuse_checks% "CGA3" CGA3 Float) 8
#fuse_guard (fuse_checks_dense% "ℝ2" ℝ2 Float) 11
#fuse_guard (fuse_checks_dense% "STA" STA Float) 14
#fuse_guard (fuse_checks_dense% "PGA3" PGA3 Float) 16
#fuse_guard (fuse_checks_dense% "CGA2" CGA2 Float) 17
#fuse_guard (fuse_checks_float% "PGA3" PGA3 Float) 26
#fuse_guard (fuse_checks_float% "CGA2" CGA2 Float) 27
#fuse_guard (fuse_checks_float% "CGA3" CGA3 Float) 28
#fuse_guard (fuse_checks% "CGA3/Int" CGA3 Int) 38
#fuse_guard (fuse_checks_dense% "ℝ3/Int" ℝ3 Int) 32
#fuse_guard (fuse_checks_dense% "D⟨1,2,-3⟩" Diag.V Float) 41
#fuse_guard (fuse_checks% "D⟨1,2,-3⟩/Int" Diag.V Int) 42
#fuse_guard (fuse_checks_dense% "D⟨1,2,-3⟩/Int" Diag.V Int) 43
#fuse_guard (fuse_checks% "reference ⟨+-++⟩" RefOnly.V Float) 44
#fuse_guard (fuse_checks_dense% "reference ⟨+-++⟩" RefOnly.V Float) 45

end FuseTests

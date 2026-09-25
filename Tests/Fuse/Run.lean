/-
The fusion suite (`codegen/fuse`, run by `lake test`): the compiled `fuse_checks%` of `ℝ3`,
`PGA3` and a diagonal metric with non-unit coefficients, and fusion in code that is generic over
the space (nothing to fuse: the expression is left exactly as written). The other spaces and
coefficient types are checked at build time (`Tests.Fuse.Guards`).
-/
import Tests.Fuse.Guards

open Grassmann DirectSum StaticVectors

namespace FuseTests

set_option maxHeartbeats 2000000

/-- The compiled checks (the build-time guards of `Tests.Fuse.Guards` cover every other space
and group through the interpreter; compiled code is checked here, where the C compiler's
floating-point code generation is part of what is tested). -/
def compiledChecks : List (Nat → Tally → Tally) :=
  [ fuse_checks% "ℝ3" ℝ3 Float, fuse_checks_dense% "ℝ3" ℝ3 Float, fuse_checks_float% "ℝ3" ℝ3 Float,
    fuse_checks% "PGA3" PGA3 Float, fuse_checks% "ℝ3/Int" ℝ3 Int, fuse_checks% "D⟨1,2,-3⟩" Diag.V Float,
    fuse_checks_float% "D⟨1,2,-3⟩" Diag.V Float, batch_checks% "ℝ3" ℝ3 ]

/-- Code generic over the space: `fused%` leaves the expression as written (and it still
computes the typed operations). -/
def generic (V : TensorBundle) [Kernels V] (a b : Multivector V Float) : Multivector V Float :=
  fused% (a * b + a)

/-- Run the suite. -/
def run : IO Tally := do
  let mut t : Tally := {}
  for (f, i) in compiledChecks.zipIdx do t := f (100 + i) t
  -- the generic definition agrees with the typed operations
  t := check2 "generic space (unfused)" (fun (a b : Multivector ℝ3 Float) => a * b + a)
    (fun a b => generic ℝ3 a b) 300 t
  return t

end FuseTests

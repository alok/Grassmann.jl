/-
Code-generation suites (DESIGN.md §5.2, `Grassmann.Kernel.Codegen`):

* `codegen/kernels`: every generated kernel of every standard space against the
  reference kernels on random `Int` and `Float` operands (run-time dispatch, the
  generic compiled kernels); `buildFrom = build` on every specification; the
  emission policy's coverage (`Tests/Codegen/Kernels.lean`);
* `codegen/dispatch`: the compile-time dispatch check (`verify_kernel_dispatch`: every
  specification reduces to its kernel) reported against the policy's counts; the
  `decide` spot checks run at build time (`Tests/Codegen/Dispatch.lean`);
* `codegen/typed`: the typed operations at `Float` (specialized kernels, as in user
  code) against the reference, and `basis!`'s emission (`Tests/Codegen/Typed.lean`);
* `codegen/fuse`: expression fusion (`fused%`) and batch kernels (`batch%`) against the typed
  operations, compiled (`Tests/Fuse/Run.lean`); every other space and coefficient type is
  checked while `Tests/Fuse/Guards.lean` builds.
-/
import Tests.Codegen.Kernels
import Tests.Codegen.Dispatch
import Tests.Codegen.Typed
import Tests.Fuse.Run

open Grassmann DirectSum Grassmann.Kernel.Codegen CodegenTests

/-- The compile-time dispatch counts against the specifications of the policy. -/
def CodegenTests.Dispatch.run : IO Tally := do
  let counts : List (String × TensorBundle × Nat) :=
    [("ℝ2", ℝ2, Dispatch.dispatchedR2), ("ℝ3", ℝ3, Dispatch.dispatchedR3),
     ("ℝ4", ℝ4, Dispatch.dispatchedR4), ("STA", STA, Dispatch.dispatchedSTA),
     ("PGA2", PGA2, Dispatch.dispatchedPGA2), ("PGA3", PGA3, Dispatch.dispatchedPGA3),
     ("CGA2", CGA2, Dispatch.dispatchedCGA2), ("CGA3", CGA3, Dispatch.dispatchedCGA3)]
  let mut t : Tally := {}
  for (name, V, k) in counts do
    let expected := (planAll V (Policy.default V.n)).size + (planSandwiches V).size
    t := t.check (k == expected && k > 0) s!"{name}: {k} dispatches verified, {expected} specifications"
  return t

/-- Run every code-generation suite; returns `(passed, failed)`. -/
def Tests.Codegen.run : IO (Nat × Nat) := do
  let suites : List (String × IO Tally) :=
    [("codegen/kernels", Kernels.run), ("codegen/dispatch", Dispatch.run), ("codegen/typed", Typed.run),
     ("codegen/fuse", FuseTests.run)]
  let mut pass := 0
  let mut fail := 0
  for (name, suite) in suites do
    let t ← suite
    t.report name
    pass := pass + t.pass
    fail := fail + t.fail
  return (pass, fail)

/-
Shared helpers of the code-generation suites: the standard spaces with generated
kernels and random packed vectors.
-/
import Grassmann
import Grassmann.Kernel.Generated
import Tests.Grassmann.Common

open Grassmann DirectSum StaticVectors AbstractTensors Grassmann.Kernel.Codegen

namespace CodegenTests

export GrassmannTests (Tally)

/-- The pre-generated spaces (`Grassmann.Kernel.Generated`). -/
def standardSpaces : List (String × TensorBundle) :=
  [("ℝ2", ℝ2), ("ℝ3", ℝ3), ("ℝ4", ℝ4), ("STA", STA), ("PGA2", PGA2), ("PGA3", PGA3),
   ("CGA2", CGA2), ("CGA3", CGA3)]

/-- A random integer vector with entries in `[-3, 3]`. -/
def randInt (n : Nat) : Tests.Gen (Values Int n) := do
  let xs ← Tests.Gen.array n (Tests.Gen.int (-3) 3)
  return Values.ofFn fun i => xs[i.1]!

/-- A random float vector with entries in `[-1, 1)`. -/
def randFloat (n : Nat) : Tests.Gen (Values Float n) := do
  let xs ← Tests.Gen.array n (Tests.Gen.floatIn (-1) 1)
  return Values.ofFn fun i => xs[i.1]!

/-- A short description of a specification. -/
def describe (s : Spec) : String :=
  s!"{fieldTag s.field} {opTag s.key.op} {layoutTag s.key.la}×{layoutTag s.key.lb}→{layoutTag s.key.lc}"

end CodegenTests

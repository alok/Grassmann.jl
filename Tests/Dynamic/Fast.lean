/-
`dynamic/fast`: the fast paths of `Grassmann.Dynamic.Fast` against Julia's loops.

In the spaces with `DynKernels.fast` (`ℝ2`, `ℝ3`, `ℝ4`, `STA`), the operator instances
(`*`, `∧`, `∨`, `⋅`, `~`, `involute`, `clifford`, `⋆`, `!`, `complementLeft`, `+`) take the
generated kernels for container products and unary maps. They must give the same kind and the
same `Float` bits (sign of zero included) as the dynamic layer's Julia-loop functions
(`TA.mul`, `TA.wedge`, …, which the oracle goldens check against Julia). Operands: every
container kind with random entries, a quarter of them `±0.0`, the rest integers and random
fractions (so summation order would show).
-/
import Tests.Dynamic.Common
import Grassmann.Kernel.Generated

open Grassmann DirectSum StaticVectors AbstractTensors GrassmannTests

namespace DynamicTests

/-- A random `Float` entry: `±0.0`, a small integer or a random fraction. -/
def randEntry : Tests.Gen Float := do
  match ← Tests.Gen.nat 8 with
  | 0 => return 0.0
  | 1 => return -0.0
  | 2 | 3 | 4 => return Float.ofInt (← Tests.Gen.int (-3) 3)
  | _ => return (Float.ofInt (← Tests.Gen.int (-1000) 1000)) / 7.0

/-- Random values of a given length. -/
def randVals (n : Nat) : Tests.Gen (Values Float n) := do
  let mut xs : Array Float := #[]
  for _ in [0:n] do xs := xs.push (← randEntry)
  return Values.ofFn fun i => xs[i.1]!

/-- A random container of `V` (a chain of any grade, a spinor, a co-spinor or a multivector). -/
def randContainer (V : TensorBundle) : Tests.Gen (TA V Float) := do
  match ← Tests.Gen.nat 4 with
  | 0 => let g ← Tests.Gen.nat (V.n + 1); return .chain g ⟨← randVals _⟩
  | 1 => return .spinor ⟨← randVals _⟩
  | 2 => return .cospinor ⟨← randVals _⟩
  | _ => return .multi ⟨← randVals _⟩

/-- Same kind and same bits. -/
def sameTA {V : TensorBundle} (x y : TA V Float) : Bool :=
  x.kind == y.kind && x.grade? == y.grade? && denseBits x == denseBits y

/-- Check the fast operators of one space against the Julia loops. -/
def fastSpace (V : TensorBundle) [Kernels V] [DynKernels V] (name : String) (seed : UInt64) (count : Nat)
    (t : Tally) : Tally := Id.run do
  let mut t := t
  let xs := Tests.Gen.run seed.toNat (Tests.Gen.array (2 * count) (randContainer V))
  for k in [0:count] do
    let a := xs[2 * k]!
    let b := xs[2 * k + 1]!
    let bin := [("*", TA.mulF a b, TA.mul a b), ("∧", TA.wedgeF a b, TA.wedge a b),
      ("∨", TA.veeF a b, TA.vee a b), ("⋅", TA.contractionF a b, TA.contraction a b),
      ("+", a + b, TA.add a b)]
    for (op, fast, slow) in bin do
      t := t.check (sameTA fast slow) s!"{name} {op}: `{fast}` vs `{slow}` for `{a}`, `{b}`"
    let un := [("~", TA.reverseF a, TA.reverse a), ("involute", TA.involuteF a, TA.involute a),
      ("clifford", TA.cliffordF a, TA.clifford a), ("⋆", TA.hodgeF a, TA.hodge a),
      ("!", TA.complementrightF a, TA.complementright a),
      ("complementleft", TA.complementleftF a, TA.complementleft a)]
    for (op, fast, slow) in un do
      t := t.check (sameTA fast slow) s!"{name} {op}: `{fast}` vs `{slow}` for `{a}`"
  return t

/-- The space's instances as run-time values (so the checks run the generic code once instead
of specializing every fast path per space at compile time; the values are the same). -/
@[noinline] def fastInsts (V : TensorBundle) [k : Kernels V] [d : DynKernels V] : Kernels V × DynKernels V :=
  (k, d)

/-- `dynamic/fast`: every fast space, 400 random operand pairs each. -/
def fastRun : IO Tally := do
  let mut t : Tally := {}
  let (k2, d2) := fastInsts ℝ2
  let (k3, d3) := fastInsts ℝ3
  let (k4, d4) := fastInsts ℝ4
  let (ks, ds) := fastInsts STA
  t := @fastSpace ℝ2 k2 d2 "ℝ2" 11 400 t
  t := @fastSpace ℝ3 k3 d3 "ℝ3" 12 400 t
  t := @fastSpace ℝ4 k4 d4 "ℝ4" 13 400 t
  t := @fastSpace STA ks ds "STA" 14 400 t
  -- the flag itself: generated spaces with a non-degenerate diagonal metric only
  t := t.check (DynKernels.fast ℝ3 && !DynKernels.fast PGA3 && !DynKernels.fast CGA3) "DynKernels flags"
  t := t.check ((ℝ3).dynFastShape && (STA).dynFastShape && !(PGA3).dynFastShape && !(CGA3).dynFastShape)
    "dynFastShape"
  return t

end DynamicTests

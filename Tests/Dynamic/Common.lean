/-
Shared helpers for the dynamic-layer suites: random dynamic elements of every linear kind
with small integer coefficients (SplitMix64 through `Tests.Util.Random`, so every failure
reproduces from its seed), element builders and a bitwise `Float` comparison.
-/
import Grassmann.Dynamic
import Tests.Grassmann.Common

open Grassmann DirectSum StaticVectors AbstractTensors GrassmannTests

namespace DynamicTests

/-- A random blade of `V` (bit pattern below `2ⁿ`). -/
def randBlade (V : TensorBundle) : Tests.Gen UInt64 := do
  return (← Tests.Gen.nat (2 ^ V.n)).toUInt64

/-- A random blade other than the scalar and the pseudoscalar (the blade of a
`Couple`/`PseudoCouple`); the scalar blade when `n ≤ 1`. -/
def randInnerBlade (V : TensorBundle) : Tests.Gen UInt64 := do
  if V.n ≤ 1 then return 0
  return (1 + (← Tests.Gen.nat (2 ^ V.n - 2))).toUInt64

/-- A random linear dynamic element: `𝟎`, `One`, a blade, a `Single`, a `Chain` of a
random grade, a `Spinor`, `CoSpinor` or `Multivector`, a `Couple` or `PseudoCouple`. -/
def randTA (V : TensorBundle) : Tests.Gen (TA V Int) := do
  let int := Tests.Gen.int (-3) 3
  match ← Tests.Gen.nat 10 with
  | 0 => return .zero
  | 1 => return .one
  | 2 => let b ← randBlade V; return (if b == 0 then .one else .blade b)
  | 3 => return .single (← randBlade V) (← int)
  | 4 => let g ← Tests.Gen.nat (V.n + 1); return .chain g (← randChain V g)
  | 5 => return .spinor (← randHalf V false)
  | 6 => return .cospinor (← randHalf V true)
  | 7 => return .multi (← randMV V)
  | 8 => return .couple (← randInnerBlade V) (← int) (← int)
  | _ => return .pseudo (← randInnerBlade V) (← int) (← int)

/-- A chain from a list of entries (missing entries are zero). -/
def chainOfList {α : Type} [Coeff α] (V : TensorBundle) (g : Nat) (xs : List α) : TA V α :=
  .chain g ⟨Values.ofFn fun i => xs.getD i.1 Coeff.zero⟩

/-- A multivector from a list of entries in Julia's storage order. -/
def multiOfList {α : Type} [Coeff α] (V : TensorBundle) (xs : List α) : TA V α :=
  .multi ⟨Values.ofFn fun i => xs.getD i.1 Coeff.zero⟩

/-- A spinor from a list of entries in Julia's storage order. -/
def spinorOfList {α : Type} [Coeff α] (V : TensorBundle) (xs : List α) : TA V α :=
  .spinor ⟨Values.ofFn fun i => xs.getD i.1 Coeff.zero⟩

/-- The dense entries of an element as bit patterns (a `Float` comparison that keeps the
sign of zero). -/
def denseBits {V : TensorBundle} (x : TA V Float) : List UInt64 :=
  x.toDense.v.toList.map Float.toBits

/-- The dense entries as integers. -/
def denseInts {V : TensorBundle} (x : TA V Int) : List Int := x.toDense.v.toList

/-- Euclidean 3-space `ℝ³` (Julia `S"+++"`). -/
def E3 : TensorBundle := S!"+++"

/-- Conformal 2D (Julia `S"∞∅++"`). -/
def CGA2 : TensorBundle := S!"∞∅++"

end DynamicTests

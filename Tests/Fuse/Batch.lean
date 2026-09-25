/-
Batch kernels (`Grassmann.Batch`): `batch% f` on random batches equals `f` applied elementwise
through the typed operations (bit for bit up to the sign of zero), for batches of different
lengths (the shortest sets the length), and `batchInto%` equals `batch%` whether or not the
output storage has the right size.
-/
import Tests.Fuse.Common
import Grassmann.Batch

open Grassmann DirectSum StaticVectors

namespace FuseTests

/-- A random batch of `n` elements. -/
def randBatch {X : Type} [Rand X] [BatchElem X] (n : Nat) : Tests.Gen (Batch X) := do
  let mut xs := #[]
  for _ in [0:n] do xs := xs.push (← (Rand.gen : Tests.Gen X))
  return Batch.ofArray xs

/-- Compare a two-operand batch kernel (and its `into` form) with the elementwise typed
function on batches of lengths `n` and `n + 3`. -/
def bcheck2 {X Y Z : Type} [Rand X] [Rand Y] [BatchElem X] [BatchElem Y] [BatchElem Z] [Same Z]
    (name : String) (f : X → Y → Z) (k : Batch X → Batch Y → Batch Z)
    (kInto : Batch Z → Batch X → Batch Y → Batch Z) (seed : Nat) (t : Tally) : Tally := Id.run do
  let n := 37
  let ((a, b), _) := StateT.run (do return (← randBatch (X := X) n, ← randBatch (X := Y) (n + 3)) :
    Tests.Gen _) (Tests.Rng.ofSeed seed)
  let expect := (Array.range n).map fun i => f (a.get i) (b.get i)
  let same (r : Batch Z) : Bool :=
    r.len == n && (Array.range n).all fun i => (expect[i]?).any (Same.same (r.get i))
  let r := k a b
  let r1 := kInto (Batch.zeros n) a b
  let r2 := kInto (Batch.zeros 1) a b
  return t.check (same r && same r1 && same r2) s!"{name}: batch ≠ elementwise"

/-- Compare a one-operand batch kernel with the elementwise typed function. -/
def bcheck1 {X Z : Type} [Rand X] [BatchElem X] [BatchElem Z] [Same Z]
    (name : String) (f : X → Z) (k : Batch X → Batch Z) (seed : Nat) (t : Tally) : Tally := Id.run do
  let n := 29
  let (a, _) := StateT.run (randBatch (X := X) n) (Tests.Rng.ofSeed seed)
  let r := k a
  return t.check (r.len == n && (Array.range n).all fun i => Same.same (r.get i) (f (a.get i)))
    s!"{name}: batch ≠ elementwise"

/-- `bcheck "name" (x : X) (y : Y) => e`: `batch%`/`batchInto%` of `e` against `e` elementwise. -/
syntax "bcheck " term:max ("(" ident " : " term ")")+ " => " term : term

macro_rules
  | `(bcheck $nm ($a : $ta) => $e) =>
    `(bcheck1 $nm (fun ($a : $ta) => $e) (batch% fun ($a : $ta) => $e))
  | `(bcheck $nm ($a : $ta) ($b : $tb) => $e) =>
    `(bcheck2 $nm (fun ($a : $ta) ($b : $tb) => $e) (batch% fun ($a : $ta) ($b : $tb) => $e)
      (batchInto% fun ($a : $ta) ($b : $tb) => $e))

/-- `batch_checks% "label" V`: the batch checks of space `V`. -/
syntax (name := batchChecksStx) "batch_checks% " str term:max : term

macro_rules
  | `(batch_checks% $label $V) => `(show Nat → Tally → Tally from fun seed t0 => Id.run do
      let s (k : Nat) := seed * 89 + k
      let nm (x : String) := $label ++ " batch " ++ x
      let mut t := t0
      t := (bcheck (nm "R*v*~R") (R : Spinor $V Float) (v : Chain $V 1 Float) => (R * v * ~R : CoSpinor $V Float)) (s 1) t
      t := (bcheck (nm "v ⊘ R") (R : Spinor $V Float) (v : Chain $V 1 Float) => (v ⊘ R : Chain $V 1 Float)) (s 2) t
      t := (bcheck (nm "s*t") (x : Spinor $V Float) (y : Spinor $V Float) => (x * y : Spinor $V Float)) (s 3) t
      t := (bcheck (nm "u∧w") (u : Chain $V 1 Float) (w : Chain $V 1 Float) => (u ∧ w : Chain $V 2 Float)) (s 4) t
      t := (bcheck (nm "c*u") (c : Chain $V 2 Float) (u : Chain $V 1 Float) => (c * u : CoSpinor $V Float)) (s 5) t
      t := (bcheck (nm "~s") (x : Spinor $V Float) => (~x : Spinor $V Float)) (s 6) t
      t := (bcheck (nm "u⁻¹") (u : Chain $V 1 Float) => u⁻¹) (s 7) t
      t := (bcheck (nm "a*b") (a : Multivector $V Float) (b : Multivector $V Float) => a * b) (s 8) t
      return t)

end FuseTests

/-
Properties of the dynamic layer over random integer elements of every linear kind, in
`E2`-`E4`, `M4`, `PGA3`, `CGA3` and `DUAL3`:

* `laws`: the dense value commutes with `+`, `-`, negation and scalar multiplication
  (the executable counterpart of `TA.toDense_add` … `TA.toDense_smul`);
* `products`: the dense values of `⟑ ∧ ∨ contraction` (whatever kind Julia's dispatch
  returns, and whichever of Julia's loops computes it) agree with the reference plan
  kernels on the dense operands;
* `equal`: `x == x`, the symmetry of `==`, and `x == y ↔ dense x = dense y` between
  containers.
-/
import Tests.Dynamic.Common

open Grassmann DirectSum StaticVectors AbstractTensors GrassmannTests

namespace DynamicTests

/-- The number of random pairs per space. -/
def pairs : Nat := 150

/-- Run a check over random pairs in every test space. -/
def overPairs (seed : Nat) (check : (V : TensorBundle) → [Kernels V] → String → TA V Int → TA V Int → Tally → Tally) :
    Tally := Id.run do
  let mut t : Tally := {}
  for (name, V) in spaces, k in [0:spaces.length] do
    let xs := Tests.Gen.run (seed + k) (Tests.Gen.array (2 * pairs) (randTA V))
    for i in [0:pairs] do
      t := check V name xs[2 * i]! xs[2 * i + 1]! t
  return t

/-- `laws`: `toDense` commutes with `+`, `-`, negation and scalars. -/
def lawsRun : IO Tally := pure <| overPairs 11 fun _ _ name a b t =>
  let da := a.toDense
  let db := b.toDense
  let s : Int := 3
  let t := t.check ((a + b).toDense == da + db) s!"{name}: toDense ({a} + {b})"
  let t := t.check ((-a).toDense == -da) s!"{name}: toDense (-{a})"
  let t := t.check ((a - b).toDense == da - db) s!"{name}: toDense ({a} - {b})"
  t.check ((s • a).toDense == s • da) s!"{name}: toDense (3 • {a})"

/-- The core products and their DirectSum operations. -/
def coreOps : List (TA.POp × BinOp × String) :=
  [(.mul, .mul, "⟑"), (.wedge, .wedge, "∧"), (.vee, .vee, "∨"), (.contraction, .contraction, "⋅")]

/-- `products`: dense values of the core products against the reference plans. -/
def productsRun : IO Tally := pure <| overPairs 23 fun V _ name a b t =>
  coreOps.foldl (init := t) fun t (op, bop, sym) =>
    let got := (TA.prod op a b).toDense.v
    let want : Values Int (2 ^ V.n) :=
      Kernel.refBin V bop .full .full .full a.toDense.v b.toDense.v
    t.check (got == want) s!"{name}: {a} {sym} {b} = {TA.prod op a b}"

/-- Whether an element is a container (`Chain`, halves, `Multivector`). -/
def isContainer {V : TensorBundle} : TA V Int → Bool
  | .chain .. | .spinor _ | .cospinor _ | .multi _ => true
  | _ => false

/-- `equal`: reflexivity, symmetry, and dense equality between containers. -/
def equalRun : IO Tally := pure <| overPairs 37 fun _ _ name a b t =>
  let t := t.check (a.equal a) s!"{name}: {a} == itself"
  let t := t.check (a.equal b == b.equal a) s!"{name}: {a} == {b} is not symmetric"
  if isContainer a && isContainer b then
    t.check (a.equal b == (a.toDense == b.toDense)) s!"{name}: {a} == {b} vs dense"
  else t

end DynamicTests

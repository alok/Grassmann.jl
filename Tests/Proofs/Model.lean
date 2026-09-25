/-
Property tests: the implementation against the proved specification model.

`Grassmann.Proofs.Tables` checks the blade tables by kernel evaluation for
`n ≤ 4`. Here the *compiled* implementation (typed `Multivector`/`Chain`
products through the reference kernels and their plan interpreter) is compared
with the specification `Grassmann.Spec.Cl` evaluated at run time, on random
integer multivectors in larger spaces (`n = 5 … 7`, Euclidean, Lorentzian,
split, degenerate and general diagonal metrics):

* the geometric and exterior products of full multivectors;
* every `Chain G × Chain H` geometric product (the typed kernels, whose plans
  land in the even/odd halves);
* reversion, grade involution, right complement and Hodge star;
* the fast 64-bit sign kernel `Bits.reorderParity` against its naive
  specification on random masks (proved for all masks; tested as a check of
  the compiled code).
-/
import Grassmann
import Grassmann.Spec
import Grassmann.Proofs
import Tests.Util.Random

open Grassmann DirectSum StaticVectors Grassmann.Spec

namespace Tests.Proofs

/-- Pass/fail counts and the first failure messages. -/
structure Tally where
  /-- Checks that passed. -/
  pass : Nat := 0
  /-- Checks that failed. -/
  fail : Nat := 0
  /-- The first failure messages. -/
  messages : Array String := #[]

namespace Tally

/-- Record a Boolean check. -/
def check (t : Tally) (cond : Bool) (msg : String) : Tally :=
  if cond then { t with pass := t.pass + 1 }
  else { t with fail := t.fail + 1, messages := if t.messages.size < 20 then t.messages.push msg else t.messages }

/-- Print a summary line and the failures. -/
def report (t : Tally) (name : String) : IO Unit := do
  IO.println s!"[{name}] pass={t.pass} fail={t.fail}"
  for m in t.messages do IO.println s!"[{name}]   FAIL {m}"

end Tally

/-- A test space: its name, the implementation's space and the spec metric. -/
structure TestSpace where
  /-- Display name. -/
  name : String
  /-- The implementation's space. -/
  V : TensorBundle
  /-- The diagonal metric of the spec model (length `V.n`). -/
  metric : List Int

/-- The spaces tested (all beyond the `decide` range `n ≤ 4`). -/
def spaces : List TestSpace :=
  [ ⟨"E5", S!"+++++", [1, 1, 1, 1, 1]⟩, ⟨"M5", S!"-++++", [-1, 1, 1, 1, 1]⟩,
    ⟨"S33", S!"++-+--", [1, 1, -1, 1, -1, -1]⟩, ⟨"PGA4", D!"0,1,1,1,1", [0, 1, 1, 1, 1]⟩,
    ⟨"D5", D!"1,2,-3,5,-1", [1, 2, -3, 5, -1]⟩, ⟨"E6", S!"++++++", [1, 1, 1, 1, 1, 1]⟩,
    ⟨"E7", S!"+++++++", [1, 1, 1, 1, 1, 1, 1]⟩ ]

/-- The spec metric as a function on `Fin n`. -/
def metricFn (n : Nat) (m : List Int) : Fin n → Int := fun i => m.getD i.1 0

/-- All `n`-bit blades. -/
def blades (n : Nat) : List (BitVec n) := (List.range (2 ^ n)).map (BitVec.ofNat n ·)

/-- An implementation multivector read as a spec multivector. -/
def toSpec {V : TensorBundle} {n : Nat} (g : Fin n → Int) (m : Multivector V Int) : Cl g :=
  ⟨fun c => m.coeff (Grassmann.Proofs.mask c)⟩

/-- Implementation and spec multivectors agree on every blade. -/
def agrees {V : TensorBundle} {n : Nat} {g : Fin n → Int} (m : Multivector V Int) (s : Cl g) : Bool :=
  (blades n).all fun c => m.coeff (Grassmann.Proofs.mask c) == s.coeff c

/-- A random multivector with entries in `[-3, 3]`. -/
def randMV (V : TensorBundle) : Tests.Gen (Multivector V Int) := do
  let xs ← Tests.Gen.array (2 ^ V.n) (Tests.Gen.int (-3) 3)
  return Multivector.ofFn fun i => xs[i.1]!

/-- A random grade-`k` chain. -/
def randChain (V : TensorBundle) (k : Nat) : Tests.Gen (Chain V k Int) := do
  let xs ← Tests.Gen.array (Leibniz.binomial V.n k) (Tests.Gen.int (-3) 3)
  return ⟨Values.ofFn fun i => xs[i.1]!⟩

/-- Products and unary operations of full multivectors against the spec. -/
def fullChecks (s : TestSpace) (trials : Nat) : Tests.Gen Tally := do
  let V := s.V
  let n := V.n
  let g := metricFn n s.metric
  let mut t : Tally := {}
  for k in [0:trials] do
    let x ← randMV V
    let y ← randMV V
    let sx := toSpec g x
    let sy := toSpec g y
    let tag := s!"{s.name} trial {k}"
    t := t.check (agrees (x * y) (sx * sy)) s!"{tag}: x * y ≠ spec"
    t := t.check (agrees ((x ∧ y : Multivector V Int)) (Cl.wedge sx sy)) s!"{tag}: x ∧ y ≠ spec"
    t := t.check (agrees x.reverse (Cl.reverse sx)) s!"{tag}: ~x ≠ spec"
    t := t.check (agrees x.involute (Cl.involute sx)) s!"{tag}: involute x ≠ spec"
    t := t.check (agrees x.complementright (Cl.compl sx)) s!"{tag}: !x ≠ spec"
    t := t.check (agrees x.hodge (Cl.hodge sx)) s!"{tag}: ⋆x ≠ spec"
  return t

/-- The typed `Chain G × Chain H` geometric products against the spec. -/
def chainChecks (s : TestSpace) : Tests.Gen Tally := do
  let V := s.V
  let n := V.n
  let g := metricFn n s.metric
  let mut t : Tally := {}
  for p in [0:n + 1] do
    for q in [0:n + 1] do
      let x ← randChain V p
      let y ← randChain V q
      let r : Multivector V Int := toMultivector (x * y)
      let sx := toSpec g (toMultivector x)
      let sy := toSpec g (toMultivector y)
      t := t.check (agrees r (sx * sy)) s!"{s.name} grades {p},{q}: chain product ≠ spec"
  return t

/-- The 64-bit sign kernel against its naive specification. -/
def signChecks (trials : Nat) : Tests.Gen Tally := do
  let mut t : Tally := {}
  for _ in [0:trials] do
    let a ← Tests.Gen.nat (2 ^ 64)
    let b ← Tests.Gen.nat (2 ^ 64)
    t := t.check (Bits.reorderParity a.toUInt64 b.toUInt64 == Bits.reorderParitySpec 64 a b)
      s!"reorderParity {a} {b} ≠ spec"
  return t

/-- Run the model suites; returns `(passed, failed)`. -/
def run : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  for s in spaces do
    let trials := if s.V.n ≥ 7 then 2 else 6
    let t := Tests.Gen.run (7 + s.V.n) (fullChecks s trials)
    t.report s!"proofs/model {s.name}"
    let c := Tests.Gen.run (11 + s.V.n) (chainChecks s)
    c.report s!"proofs/chains {s.name}"
    pass := pass + t.pass + c.pass
    fail := fail + t.fail + c.fail
  let t := Tests.Gen.run 42 (signChecks 2000)
  t.report "proofs/sign"
  return (pass + t.pass, fail + t.fail)

end Tests.Proofs

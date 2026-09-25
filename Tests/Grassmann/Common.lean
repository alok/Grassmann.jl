/-
Shared helpers for the Grassmann core suites: a pass/fail tally, the test
spaces, and random elements with small integer coefficients (SplitMix64,
`Tests.Util.Random`, so every failure reproduces from the fixed seed).
-/
import Grassmann
import Tests.Util.Random

open Grassmann DirectSum StaticVectors

namespace GrassmannTests

/-- Pass/fail counts, skips by reason, and the first failure messages. -/
structure Tally where
  /-- Checks that passed. -/
  pass : Nat := 0
  /-- Checks that failed. -/
  fail : Nat := 0
  /-- Skipped checks by reason. -/
  skips : Array (String × Nat) := #[]
  /-- The first failure messages. -/
  messages : Array String := #[]
  deriving Inhabited

namespace Tally

/-- Record a passing check. -/
def ok (t : Tally) : Tally := { t with pass := t.pass + 1 }

/-- Record a failing check (at most 40 messages are kept). -/
def bad (t : Tally) (msg : String) : Tally :=
  { t with fail := t.fail + 1, messages := if t.messages.size < 40 then t.messages.push msg else t.messages }

/-- Record a Boolean check. -/
def check (t : Tally) (cond : Bool) (msg : String) : Tally := if cond then t.ok else t.bad msg

/-- Record a skipped check with its reason. -/
def skip (t : Tally) (why : String) : Tally :=
  match t.skips.findIdx? (·.1 == why) with
  | some i => { t with skips := t.skips.modify i fun (c, k) => (c, k + 1) }
  | none => { t with skips := t.skips.push (why, 1) }

/-- Merge two tallies. -/
def merge (a b : Tally) : Tally :=
  { pass := a.pass + b.pass, fail := a.fail + b.fail
    skips := b.skips.foldl (fun acc (w, k) =>
      match acc.findIdx? (·.1 == w) with
      | some i => acc.modify i fun (c, j) => (c, j + k)
      | none => acc.push (w, k)) a.skips
    messages := (a.messages ++ b.messages).extract 0 40 }

/-- Print a summary line, the skip counts and the failures. -/
def report (t : Tally) (name : String) : IO Unit := do
  IO.println s!"[{name}] pass={t.pass} fail={t.fail}"
  for (c, k) in t.skips do IO.println s!"[{name}]   skipped {c}: {k}"
  for m in t.messages do IO.println s!"[{name}]   FAIL {m}"

end Tally

/-- The property-test spaces: Euclidean `E2`-`E4`, spacetime `M4` (STA),
projective `PGA3` (degenerate), conformal `CGA3` (null basis, Gram metric) and
the dual (covector) space `DUAL3`. -/
def spaces : List (String × TensorBundle) :=
  [ ("E2", S!"++"), ("E3", S!"+++"), ("E4", S!"++++"), ("M4", S!"-+++"),
    ("PGA3", D!"0,1,1,1"), ("CGA3", S!"∞∅+++"), ("DUAL3", (S!"+++")′) ]

/-- Every storage layout of an `n`-generator space. -/
def layouts (n : Nat) : List Layout :=
  (List.range (n + 1)).map Layout.chain ++ [.even, .odd, .full]

/-- A random vector with entries in `[lo, hi]`. -/
def randValues (n : Nat) (lo : Int := -3) (hi : Int := 3) : Tests.Gen (Values Int n) := do
  let xs ← Tests.Gen.array n (Tests.Gen.int lo hi)
  return Values.ofFn fun i => xs[i.1]!

/-- A random chain. -/
def randChain (V : TensorBundle) (G : Nat) : Tests.Gen (Chain V G Int) := return ⟨← randValues _⟩

/-- A random half. -/
def randHalf (V : TensorBundle) (p : Bool) : Tests.Gen (Half V p Int) := return ⟨← randValues _⟩

/-- A random multivector. -/
def randMV (V : TensorBundle) : Tests.Gen (Multivector V Int) := return ⟨← randValues _⟩

/-- Integer coefficients as rationals. -/
def toRat {V : TensorBundle} (m : Multivector V Int) : Multivector V Rat := m.map (fun (k : Int) => (k : Rat))

/-- `(-1)^k` as an integer. -/
def sgn (k : Nat) : Int := if k % 2 == 0 then 1 else -1

end GrassmannTests

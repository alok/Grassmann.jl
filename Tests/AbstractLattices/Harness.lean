import Lean.Data.Json

/-!
Minimal pass/fail harness shared by the small-algebra suites (AbstractLattices,
PrimitiveBits, DeMorgan, Dendriform). Each suite runs in `TestM`, counts checks, prints
the first few failures, and returns `(passed, failed)` to the `lake test` driver.
-/

namespace Tests.Small

/-- Running tally of a suite. -/
structure Tally where
  /-- number of passing checks -/
  passed : Nat := 0
  /-- number of failing checks -/
  failed : Nat := 0

/-- Test monad: a tally threaded through `IO`. -/
abbrev TestM := StateT Tally IO

/-- Failures beyond this many per suite are counted but not printed. -/
def maxPrinted : Nat := 25

/-- Record one check. `detail` is only forced on failure. -/
def check (label : String) (ok : Bool) (detail : Unit → String := fun _ => "") : TestM Unit := do
  if ok then
    modify fun t => { t with passed := t.passed + 1 }
  else
    let t ← get
    if t.failed < maxPrinted then
      IO.eprintln s!"  FAIL {label}: {detail ()}"
    set { t with failed := t.failed + 1 }

/-- Record an equality check, printing both sides on failure. -/
def checkEq {α : Type} [BEq α] [ToString α] (label : String) (got expected : α) : TestM Unit :=
  check label (got == expected) fun _ => s!"got {got}, expected {expected}"

/-- Run a suite and report its tally. -/
def runSuite (name : String) (m : TestM Unit) : IO (Nat × Nat) := do
  let (_, t) ← m.run {}
  IO.println s!"{name}: {t.passed} passed, {t.failed} failed"
  return (t.passed, t.failed)

/-- Load a JSON golden file (paths are relative to the repository root, where
`lake test` runs). -/
def readJson (path : System.FilePath) : IO Lean.Json := do
  let s ← IO.FS.readFile path
  match Lean.Json.parse s with
  | .ok j => return j
  | .error e => throw <| IO.userError s!"{path}: {e}"

/-- Field access that throws a readable error. -/
def jField (j : Lean.Json) (k : String) : TestM Lean.Json :=
  match j.getObjVal? k with
  | .ok v => return v
  | .error e => throw <| IO.userError s!"missing field {k}: {e}"

/-- Array access that throws a readable error. -/
def jArr (j : Lean.Json) : TestM (Array Lean.Json) :=
  match j.getArr? with
  | .ok v => return v
  | .error e => throw <| IO.userError e

/-- String access that throws a readable error. -/
def jStr (j : Lean.Json) : TestM String :=
  match j.getStr? with
  | .ok v => return v
  | .error e => throw <| IO.userError e

/-- Natural-number access (JSON number or decimal string, for BigInts). -/
def jNat (j : Lean.Json) : TestM Nat :=
  match j.getNat? with
  | .ok v => return v
  | .error _ =>
    match j.getStr? with
    | .ok s => match s.toNat? with
      | some n => return n
      | none => throw <| IO.userError s!"not a natural: {s}"
    | .error e => throw <| IO.userError e

/-- Integer access (JSON number or decimal string). -/
def jInt (j : Lean.Json) : TestM Int :=
  match j.getInt? with
  | .ok v => return v
  | .error _ =>
    match j.getStr? with
    | .ok s => match s.toInt? with
      | some n => return n
      | none => throw <| IO.userError s!"not an integer: {s}"
    | .error e => throw <| IO.userError e

/-- Bool access (also accepts 0/1). -/
def jBool (j : Lean.Json) : TestM Bool :=
  match j.getBool? with
  | .ok v => return v
  | .error e =>
    match j.getNat? with
    | .ok n => return n != 0
    | .error _ => throw <| IO.userError e

/-- Array of naturals. -/
def jNats (j : Lean.Json) : TestM (Array Nat) := do
  (← jArr j).mapM jNat

/-- Array of Bools. -/
def jBools (j : Lean.Json) : TestM (Array Bool) := do
  (← jArr j).mapM jBool

/-- Array of strings. -/
def jStrs (j : Lean.Json) : TestM (Array String) := do
  (← jArr j).mapM jStr

/-- `field` then `jNat`, etc.: shorthands for the common `c["k"]` pattern. -/
def gNat (j : Lean.Json) (k : String) : TestM Nat := do jNat (← jField j k)
/-- String field. -/
def gStr (j : Lean.Json) (k : String) : TestM String := do jStr (← jField j k)
/-- Bool field. -/
def gBool (j : Lean.Json) (k : String) : TestM Bool := do jBool (← jField j k)
/-- Array field. -/
def gArr (j : Lean.Json) (k : String) : TestM (Array Lean.Json) := do jArr (← jField j k)
/-- Array-of-naturals field. -/
def gNats (j : Lean.Json) (k : String) : TestM (Array Nat) := do jNats (← jField j k)

end Tests.Small

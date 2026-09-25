/-
Shared helpers for the DirectSum test suites: a pass/fail/defect tally, exact
JSON number decoding, and Julia's container display rules (used to compare the
printed form of multi-term blade results).
-/
import DirectSum
import DirectSum.BladeAlgebra
import Lean.Data.Json

open Lean DirectSum DirectSum.Bits

namespace DirectSumTests

/-- Pass/fail counts, documented-defect skips by class, and the first failures. -/
structure Tally where
  /-- Checks that agree with the oracle. -/
  pass : Nat := 0
  /-- Checks that disagree. -/
  fail : Nat := 0
  /-- Skipped checks, by documented defect class. -/
  defects : Array (String × Nat) := #[]
  /-- The first failure messages. -/
  messages : Array String := #[]

namespace Tally

/-- Record a passing check. -/
def ok (t : Tally) : Tally := { t with pass := t.pass + 1 }

/-- Record a failing check with a message (at most 40 are kept). -/
def bad (t : Tally) (msg : String) : Tally :=
  { t with fail := t.fail + 1, messages := if t.messages.size < 40 then t.messages.push msg else t.messages }

/-- Record a check skipped because of a documented Julia defect. -/
def defect (t : Tally) (cls : String) : Tally :=
  match t.defects.findIdx? (·.1 == cls) with
  | some i => { t with defects := t.defects.modify i fun (c, k) => (c, k + 1) }
  | none => { t with defects := t.defects.push (cls, 1) }

/-- Record a Boolean check. -/
def check (t : Tally) (cond : Bool) (msg : String) : Tally := if cond then t.ok else t.bad msg

/-- Print a summary line, the defect counts and the failures. -/
def report (t : Tally) (name : String) : IO Unit := do
  IO.println s!"[{name}] pass={t.pass} fail={t.fail}"
  for (c, k) in t.defects do IO.println s!"[{name}]   skipped (documented Julia defect) {c}: {k}"
  for m in t.messages do IO.println s!"[{name}]   FAIL {m}"

end Tally

/-- Exact value of a JSON number. -/
def jsonRat (n : JsonNumber) : Rat := (n.mantissa : Rat) / ((10 ^ n.exponent : Nat) : Rat)

/-- A JSON field as a natural number (masks are `< 2^63`). -/
def jNat (j : Json) (k : String) : Nat :=
  match j.getObjValD k with
  | .num n => (jsonRat n).num.toNat
  | _ => 0

/-- A JSON field as an integer. -/
def jInt (j : Json) (k : String) : Int :=
  match j.getObjValD k with
  | .num n => (jsonRat n).num
  | _ => 0

/-- A JSON field as a string. -/
def jStr (j : Json) (k : String) : String := (j.getObjValD k).getStr?.toOption.getD ""

/-- A JSON field as an array. -/
def jArr (j : Json) (k : String) : Array Json := (j.getObjValD k).getArr?.toOption.getD #[]

/-- Merge and drop zeros, sorted by mask, for order-insensitive comparison. -/
def normTerms (t : Terms) : Array (UInt64 × Rat) :=
  (Terms.nonzero (t.foldl (fun acc (k, c) => Terms.add acc k c) #[])).qsort (fun a b => a.1 < b.1)

/-- Julia `showterm` (` + x` / ` - |x|`) of one component. -/
def showTermJ (V : TensorBundle) (c : Rat) (b : UInt64) (float : Bool) : String :=
  if c < 0 then " - " ++ V.showTerm (-c) b float else " + " ++ V.showTerm c b float

/-- Julia container kinds that a sum of blades can print as. -/
inductive Kind where
  | zero | single | chain (g : Nat) | couple (b : UInt64) | pseudo (b : UInt64)
  | spinor | cospinor | multi
  deriving BEq, Repr, Inhabited

/-- Julia's type name for a kind. -/
def Kind.name : Kind → String
  | .zero => "Zero" | .single => "Single" | .chain _ => "Chain" | .couple _ => "Couple"
  | .pseudo _ => "PseudoCouple" | .spinor => "Spinor" | .cospinor => "CoSpinor" | .multi => "Multivector"

/-- Julia's `+` promotion lattice (port-notes/grassmann-types.md §4.5) folded left
over the terms of a sum: the container Julia's `+(Single…)` produces. -/
def sumKind (V : TensorBundle) (t : Terms) : Kind :=
  let ok := !V.istangent && !V.hasconformal
  let gv := V.grade
  let par := fun (g : Nat) => g % 2
  let step := fun (st : Kind × UInt64) (term : UInt64 × Rat) =>
    let (k, first) := st
    let b := term.1
    let gb := popcount b
    let byParity := fun (gs : List Nat) =>
      if gs.all (par · == 0) then Kind.spinor else if gs.all (par · == 1) then .cospinor else .multi
    let k' := match k with
      | .zero => Kind.single
      | .single =>
        let ga := popcount first
        if first == b then .single
        else if ok && ga == 0 then .couple b
        else if ok && gb == 0 then .couple first
        else if ok && ga == gv then .pseudo b
        else if ok && gb == gv then .pseudo first
        else if ga == gb then .chain ga
        else byParity [ga, gb]
      | .chain g => if gb == g then .chain g else byParity [g, gb]
      | .couple c => if b == c || gb == 0 then .couple c else byParity [0, popcount c, gb]
      | .pseudo c => if b == c || gb == gv then .pseudo c else byParity [popcount c, gv, gb]
      | .spinor => if par gb == 0 then .spinor else .multi
      | .cospinor => if par gb == 1 then .cospinor else .multi
      | .multi => .multi
    (k', if k == .zero then b else first)
  (t.foldl step (Kind.zero, 0)).1

/-- Julia's display of a container of kind `k` holding the (exact) terms `t`
(port-notes/grassmann-types.md §5.4). Numbers print as `Int` or `Float64`. -/
def showContainer (V : TensorBundle) (k : Kind) (t : Terms) (float : Bool) : String :=
  let coef := fun (b : UInt64) => (t.find? (·.1 == b)).map (·.2) |>.getD 0
  let n := V.n
  let series := fun (bs : Array UInt64) (firstPlain : Bool) =>
    bs.zipIdx.foldl (init := "") fun acc (b, i) =>
      if i == 0 then (if firstPlain then acc ++ showNum (coef b) float else acc ++ V.showTerm (coef b) b float)
      else acc ++ showTermJ V (coef b) b float
  match k with
  | .zero => "𝟎"
  | .single => match t[0]? with | some (b, c) => V.showTerm c b float | none => "𝟎"
  | .chain g => series (Leibniz.indexBasis n g) false
  | .couple b => showNum (coef 0) float ++ showTermJ V (coef b) b float
  | .pseudo b => V.showTerm (coef b) b float ++ showTermJ V (coef (lowMask n)) (lowMask n) float
  | .spinor => series (Leibniz.indexEven n) true
  | .cospinor => series (Leibniz.indexOdd n) false
  | .multi =>
    let rest := (Leibniz.indexBasisAll n).filter fun b => b != 0 && coef b != 0
    if rest.isEmpty then showNum (coef 0) float ++ "v⃖"
    else rest.foldl (fun acc b => acc ++ showTermJ V (coef b) b float) (showNum (coef 0) float)

/-- Julia prints `-0.0` for signed zeros that exact arithmetic cannot see; map
` - 0.0` to ` + 0.0` and a leading `-0.0` to `0.0` before comparing. -/
def normSignedZero (s : String) : String :=
  let rec go : List Char → List Char
    | ' ' :: '-' :: ' ' :: '0' :: '.' :: '0' :: rest =>
      match rest with
      | c :: _ => if c.isDigit then ' ' :: '-' :: ' ' :: '0' :: '.' :: '0' :: go rest
                  else ' ' :: '+' :: ' ' :: '0' :: '.' :: '0' :: go rest
      | [] => [' ', '+', ' ', '0', '.', '0']
    | c :: rest => c :: go rest
    | [] => []
  let cs := s.toList
  let cs := match cs with
    | '-' :: '0' :: '.' :: '0' :: rest =>
      (match rest with | c :: _ => if c.isDigit then cs else '0' :: '.' :: '0' :: rest | [] => ['0', '.', '0'])
    | _ => cs
  String.ofList (go cs)

end DirectSumTests

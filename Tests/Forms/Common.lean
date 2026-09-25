import Grassmann
import Grassmann.Forms
import Tests.FieldAlgebra.Harness

/-!
# Shared helpers for the Forms golden tests

Goldens live in `oracle/golden/forms/*.json` (written by `oracle/forms/gen.jl`):
integers are JSON numbers, floats IEEE bit patterns `"0x…"`, complex numbers `[re, im]`,
matrices row lists, a Julia exception `{"E": "<Type>: …"}`.

Every comparison states its mode:

* `bits`: exact (integers equal, floats bit for bit, `NaN`s identified): the functions
  whose Julia algorithm is ported operation for operation;
* `approx rtol`: `|a − b| ≤ rtol·max(|a|, |b|, 1)` componentwise: iterative numerics
  (eigenvalues from the dense solver vs LAPACK, the matrix logarithm) and closed forms
  through the C library's `acos`/`cos` (Julia uses openlibm).

A golden Julia error is counted as skipped (the port fixes or replaces the behaviour; the
test files say which).
-/

namespace Tests.FormsTests

open Lean Tests.Units Grassmann DirectSum StaticVectors AbstractTensors JuliaBase

/-- A scalar as the goldens encode it. -/
inductive Num where
  | int (x : Int)
  | flt (x : Float)
  | cpx (re im : Float)
  deriving Inhabited

/-- A value that the goldens can hold. -/
class ToNum (α : Type) where
  /-- The scalar. -/
  toNum : α → Num

instance : ToNum Int := ⟨.int⟩
instance : ToNum Nat := ⟨fun n => .int n⟩
instance : ToNum Float := ⟨.flt⟩
instance : ToNum (Complex Float) := ⟨fun z => .cpx z.re z.im⟩
instance : ToNum Rat := ⟨fun r => if r.den == 1 then .int r.num else .flt (F64.ofRat r)⟩

/-- Render a scalar for failure messages. -/
def Num.show : Num → String
  | .int x => toString x
  | .flt x => s!"{F64.showString x}"
  | .cpx a b => s!"({F64.showString a}, {F64.showString b})"

/-- Decode a golden scalar. -/
def jnum (j : Json) : Option Num :=
  match j with
  | .num n => if n.exponent == 0 then some (.int n.mantissa) else some (.flt n.toFloat)
  | .str s => if s.startsWith "0x" then some (.flt (Float.ofBits (hexU64 s))) else none
  | .bool b => some (.int (if b then 1 else 0))
  | .arr #[a, b] => match jnum a, jnum b with
    | some (.flt x), some (.flt y) => some (.cpx x y)
    | some (.int x), some (.int y) => some (.cpx (Float.ofInt x) (Float.ofInt y))
    | _, _ => none
  | _ => none

/-- Comparison mode. -/
inductive Mode where
  /-- Exact. -/
  | bits
  /-- Relative tolerance. -/
  | approx (rtol : Float)

/-- Float closeness `|a − b| ≤ rtol·max(|a|, |b|, 1)` (NaNs identified). -/
def close (rtol a b : Float) : Bool :=
  (a.isNaN && b.isNaN) || a == b || (a - b).abs ≤ rtol * F64.max (F64.max a.abs b.abs) 1

/-- Compare two scalars. -/
def numEq (m : Mode) (a b : Num) : Bool :=
  let fl := fun (x y : Float) => match m with
    | .bits => sameBits x y || (x == 0 && y == 0 && false)
    | .approx r => close r x y
  match a, b with
  | .int x, .int y => x == y
  | .int x, .flt y | .flt y, .int x => fl (Float.ofInt x) y
  | .flt x, .flt y => fl x y
  | .cpx a b, .cpx c d => fl a c && fl b d
  | .flt x, .cpx c d | .cpx c d, .flt x => fl x c && fl 0 d
  | .int x, .cpx c d | .cpx c d, .int x => fl (Float.ofInt x) c && fl 0 d

/-- A Julia error recorded in a golden. -/
def jerr? (j : Json) : Option String :=
  match j.getObjVal? "E" with
  | .ok (.str s) => some s
  | _ => none

/-- A tally of checks plus the Julia-error entries that were skipped. -/
structure Tally where
  /-- The checks. -/
  s : Suite
  /-- Golden entries recording a Julia error (not compared). -/
  skipped : Nat := 0

namespace Tally

/-- A new tally. -/
def new (name : String) : Tally := ⟨{ name }, 0⟩

/-- Record a Boolean check. -/
def ok (t : Tally) (b : Bool) (msg : Unit → String) : Tally := { t with s := t.s.check b msg }

/-- Skip a golden that records a Julia error. -/
def skip (t : Tally) : Tally := { t with skipped := t.skipped + 1 }

/-- Compare a scalar with a golden scalar. -/
def num (t : Tally) (m : Mode) (got : Num) (want : Json) (what : Unit → String) : Tally :=
  if (jerr? want).isSome then t.skip else
  match jnum want with
  | some w => t.ok (numEq m got w) fun _ => s!"{what ()}: got {got.show}, want {w.show}"
  | none => t.ok false fun _ => s!"{what ()}: malformed golden {want.compress}"

/-- Compare a list of scalars with a golden array. -/
def nums (t : Tally) (m : Mode) (got : List Num) (want : Json) (what : Unit → String) : Tally :=
  if (jerr? want).isSome then t.skip else
  let ws := arr want
  if ws.size != got.length then
    t.ok false fun _ => s!"{what ()}: length {got.length} vs {ws.size} ({want.compress})"
  else
    let bad := (got.zip ws.toList).zipIdx.filter fun ((g, w), _) =>
      match jnum w with | some w => !numEq m g w | none => true
    t.ok bad.isEmpty fun _ =>
      let ((g, w), i) := bad.head!
      s!"{what ()}[{i}]: got {g.show}, want {w.compress} (all: {got.map Num.show})"

/-- Compare a list of scalars with a golden array as multisets (greedy matching
within the tolerance): eigenvalues whose order is decided by rounding noise, e.g.
real parts `±1e-17` of a skew-symmetric matrix sorted by `(re, im)`. -/
def numsSet (t : Tally) (m : Mode) (got : List Num) (want : Json) (what : Unit → String) : Tally :=
  if (jerr? want).isSome then t.skip else
  let ws := (arr want).toList.filterMap jnum
  if ws.length != got.length then
    t.ok false fun _ => s!"{what ()}: length {got.length} vs {ws.length}"
  else
    let rest := ws.foldl (fun (acc : Option (List Num)) w => acc.bind fun gs =>
      match gs.findIdx? (numEq m · w) with
      | some i => some (gs.eraseIdx i)
      | none => none) (some got)
    t.ok rest.isSome fun _ => s!"{what ()}: {got.map Num.show} vs {ws.map Num.show} (as multisets)"

/-- Compare a matrix (rows) with a golden row list. -/
def mat (t : Tally) (m : Mode) (got : List (List Num)) (want : Json) (what : Unit → String) : Tally :=
  if (jerr? want).isSome then t.skip else
  let ws := arr want
  if ws.size != got.length then
    t.ok false fun _ => s!"{what ()}: {got.length} rows vs {ws.size}"
  else
    let flatG := got.flatten
    let flatW := ws.toList.flatMap fun r => (arr r).toList
    if flatG.length != flatW.length then t.ok false fun _ => s!"{what ()}: shape mismatch"
    else
      let bad := (flatG.zip flatW).zipIdx.filter fun ((g, w), _) =>
        match jnum w with | some w => !numEq m g w | none => true
      t.ok bad.isEmpty fun _ =>
        let ((g, w), i) := bad.head!
        s!"{what ()}[{i}]: got {g.show}, want {w.compress}"

/-- Compare a string with a golden string. -/
def str (t : Tally) (got : String) (want : Json) (what : Unit → String) : Tally :=
  match want with
  | .str w => t.ok (got == w) fun _ => s!"{what ()}:\n got  {got}\n want {w}"
  | _ => t.skip

/-- Print the report; returns `(passed, failed)`. -/
def report (t : Tally) : IO (Nat × Nat) := do
  let r ← t.s.report
  if t.skipped > 0 then IO.println s!"    ({t.skipped} Julia-error entries skipped)"
  return r

end Tally

/-- Load a Forms golden. -/
def load (name : String) : IO Json := loadJson s!"forms/{name}.json"

/-- The cases of a golden. -/
def cases (j : Json) : Array Json := arr (fld j "cases")

/-- Golden integer rows. -/
def intRows (j : Json) : List (List Int) := (arr j).toList.map fun r => (arr r).toList.map int

/-- Golden float rows (bit patterns). -/
def floatRows (j : Json) : List (List Float) :=
  (arr j).toList.map fun r => (arr r).toList.map fun x =>
    match jnum x with | some (.flt f) => f | some (.int i) => Float.ofInt i | _ => 0

/-- Golden integer list. -/
def ints (j : Json) : List Int := (arr j).toList.map int

/-- Golden float list. -/
def flts (j : Json) : List Float :=
  (arr j).toList.map fun x => match jnum x with | some (.flt f) => f | some (.int i) => Float.ofInt i | _ => 0

/-- A list of values as scalars. -/
def ns {α : Type} [ToNum α] (xs : List α) : List Num := xs.map ToNum.toNum

/-- A matrix of values as scalars. -/
def nss {α : Type} [ToNum α] (xs : List (List α)) : List (List Num) := xs.map ns

/-- The rows of an operator as scalars. -/
def opRows {V W : TensorBundle} {ld lc : Layout} {α : Type} [Coeff α] [ToNum α]
    (T : TensorOperator V ld W lc α) : List (List Num) := nss T.toRows

/-- The coefficients of a coefficient vector as scalars. -/
def vals {α : Type} [Coeff α] [ToNum α] {n : Nat} (v : Values α n) : List Num := ns v.toList

/-- `ℝⁿ` as Julia's `Submanifold(n)` (what `Endomorphism(::Matrix)` uses). -/
abbrev En (n : Nat) : TensorBundle := TensorBundle.euclidean n

/-- A golden space `{"n": n}`, `{"sig": "-++"}` or `{"diag": "2,3,5"}`. -/
def spaceOf (j : Json) : TensorBundle :=
  match (fld j "n").getNat? with
  | .ok n => TensorBundle.euclidean n
  | .error _ =>
    match (fld j "sig").getStr? with
    | .ok s => (DirectSum.TensorBundle.parseSignature s).toOption.getD (TensorBundle.euclidean 0)
    | .error _ =>
      match (fld j "diag").getStr? with
      | .ok s => (DirectSum.TensorBundle.parseDiagonal s).toOption.getD (TensorBundle.euclidean 0)
      | .error _ => TensorBundle.euclidean 0

/-- An endomorphism of `ℝⁿ` from rows (Julia `Endomorphism(A)`). -/
def endo {α : Type} [Coeff α] (V : TensorBundle) (rows : List (List α)) : Endomorphism V (.chain 1) α :=
  (TensorOperator.ofRows? rows).getD TensorOperator.zero

/-- A grade-`g` chain from a list (zero if the length is wrong). -/
def chainOf {α : Type} [Coeff α] (V : TensorBundle) (g : Nat) (xs : List α) : Chain V g α :=
  (Chain.ofList? xs).getD Chain.zero

/-- A multivector from a list. -/
def mvOf {α : Type} [Coeff α] (V : TensorBundle) (xs : List α) : Multivector V α :=
  (Multivector.ofList? xs).getD Multivector.zero

end Tests.FormsTests

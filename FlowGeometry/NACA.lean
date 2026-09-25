import FlowGeometry.Airfoil
import Lean.Elab.Term

/-!
# The `NACA"…"` designation grammar

Julia's `@NACA_str` (`airfoils.jl:150-167`) tries four PCRE patterns in turn, each as an
*unanchored search* (the first match anywhere in the string), and builds the airfoil with
`p = 150` samples from the `Meta.parse`d groups:

| family | pattern | airfoil |
|---|---|---|
| 5-digit | `(\d{2}[01])(\d{2}(?>\.\d+)?)(?:-)?(?(?<=-)(\d{2}(?>\.\d+)?))?` | `British(NACA5{g1}, g3 ? Modified{g2,g3} : ClarkY{g2})` |
| 4-digit | `(\d{2})(\d{2}(?>\.\d+)?)(?:-)?(?(?<=-)(\d{2}(?>\.\d+)?))?` | `American(NACA4{g1}, g3 ? Modified{g2,g3} : ClarkY{g2})` |
| 1-series | `1(\d)(?>-)(?:\((?=…\)))?(\d(?>\.\d+)?)(?:(?<=\d)\))?(?:\((?=…\)))?(\d{2}(?>\.\d+)?)(?:(?<=\d)\))?` | `American(NACA6{g2}, Modified{g1,g3})` |
| 6A-series | the same after `6(\d)(?>A)` | `American(NACA6A{g2}, Modified{g1,g3})` |

The matchers below are those patterns written out. Every choice in them is greedy and none of the
alternatives PCRE could backtrack to can succeed where the greedy one fails (an optional parenthesis
is only taken when its lookahead guarantees what follows, and after a dropped decimal the next
element needs a digit where a `.` stands), so a deterministic scan per start position is exact:
the 460 strings of `oracle/golden/flowgeometry/parse.json` (the designations, edge cases and
random strings of the grammar's alphabet) all parse to Julia's types or fail as Julia does.
Julia's mapping of the 1- and 6A-series groups (`Modified{t = min-pressure digit, m = thickness}`)
is kept (port notes §8.4.10). `\d` is ASCII here (Julia's PCRE `\d` also matches other Unicode
decimal digits).
-/

namespace FlowGeometry

namespace NACA

/-- An ASCII digit. -/
@[inline] def isDig (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- Character `i`, or a sentinel past the end. -/
@[inline] def chr (s : Array Char) (i : Nat) : Char := s[i]?.getD '\x00'

/-- `\d+` at `i`: the end of the digit run (`i` when there is none). -/
def digitsEnd (s : Array Char) (i : Nat) : Nat :=
  go (s.size + 1) i
where
  /-- the scan -/
  go : Nat → Nat → Nat
    | 0, j => j
    | k + 1, j => if isDig (chr s j) then go k (j + 1) else j

/-- `(?>\.\d+)?` at `i`: the end of the decimal part, or `i` when there is none. -/
def decimalEnd (s : Array Char) (i : Nat) : Nat :=
  if chr s i == '.' && isDig (chr s (i + 1)) then digitsEnd s (i + 1) else i

/-- `\d{2}(?>\.\d+)?` at `i`: its end. -/
def num2 (s : Array Char) (i : Nat) : Option Nat :=
  if isDig (chr s i) && isDig (chr s (i + 1)) then some (decimalEnd s (i + 2)) else none

/-- `\d(?>\.\d+)?` at `i`: its end. -/
def num1 (s : Array Char) (i : Nat) : Option Nat :=
  if isDig (chr s i) then some (decimalEnd s (i + 1)) else none

/-- The substring `[i, j)`. -/
def sub (s : Array Char) (i j : Nat) : String := String.ofList (s.extract i j).toList

/-- The captured groups of a match. -/
structure Groups where
  /-- group 1 -/
  g1 : String
  /-- group 2 -/
  g2 : String
  /-- group 3 (unset when the optional part did not match) -/
  g3 : Option String

/-- The tail `(\d{2}(?>\.\d+)?)(?:-)?(?(?<=-)(\d{2}(?>\.\d+)?))?` of the 4- and 5-digit patterns,
after group 1 ending at `i`. -/
def digitTail (s : Array Char) (g1 : String) (i : Nat) : Option Groups := do
  let e2 ← num2 s i
  let g2 := sub s i e2
  if chr s e2 == '-' then
    match num2 s (e2 + 1) with
    | some e3 => return ⟨g1, g2, some (sub s (e2 + 1) e3)⟩
    | none => return ⟨g1, g2, none⟩
  else return ⟨g1, g2, none⟩

/-- The 5-digit pattern at start `i`. -/
def five (s : Array Char) (i : Nat) : Option Groups :=
  if isDig (chr s i) && isDig (chr s (i + 1)) && (chr s (i + 2) == '0' || chr s (i + 2) == '1') then
    digitTail s (sub s i (i + 3)) (i + 3)
  else none

/-- The 4-digit pattern at start `i`. -/
def four (s : Array Char) (i : Nat) : Option Groups :=
  if isDig (chr s i) && isDig (chr s (i + 1)) then digitTail s (sub s i (i + 2)) (i + 2) else none

/-- The common tail of the 1- and 6A-series patterns after group 1, from `j`:
`(?:\((?=\d(?>\.\d+)?\)))?(\d(?>\.\d+)?)(?:(?<=\d)\))?(?:\((?=\d{2}(?>\.\d+)?\)))?(\d{2}(?>\.\d+)?)`. -/
def seriesTail (s : Array Char) (g1 : String) (j : Nat) : Option Groups := do
  let j := if chr s j == '(' && (match num1 s (j + 1) with | some e => chr s e == ')' | none => false)
    then j + 1 else j
  let e2 ← num1 s j
  let g2 := sub s j e2
  let j := if chr s e2 == ')' then e2 + 1 else e2
  let j := if chr s j == '(' && (match num2 s (j + 1) with | some e => chr s e == ')' | none => false)
    then j + 1 else j
  let e3 ← num2 s j
  return ⟨g1, g2, some (sub s j e3)⟩

/-- The 1-series pattern `1(\d)(?>-)…` at start `i`. -/
def sixteen (s : Array Char) (i : Nat) : Option Groups :=
  if chr s i == '1' && isDig (chr s (i + 1)) && chr s (i + 2) == '-' then
    seriesTail s (sub s (i + 1) (i + 2)) (i + 3)
  else none

/-- The 6A-series pattern `6(\d)(?>A)…` at start `i`. -/
def sixA (s : Array Char) (i : Nat) : Option Groups :=
  if chr s i == '6' && isDig (chr s (i + 1)) && chr s (i + 2) == 'A' then
    seriesTail s (sub s (i + 1) (i + 2)) (i + 3)
  else none

/-- Julia `match(r, s)`: the leftmost start position where the pattern matches. -/
def search (pat : Array Char → Nat → Option Groups) (s : Array Char) : Option Groups :=
  (List.range (s.size + 1)).findSome? (pat s)

/-- Julia `NACA"s"` with `p` samples (`airfoils.jl:150-167`); `error("not valid")` otherwise. -/
def parse? (str : String) (p : Nat := 150) : Except String Airfoil :=
  let s := str.toList.toArray
  match search five s with
  | some g =>
    .ok (.british (.naca5 (g.g1.toNat?.getD 0) p) (tail g p))
  | none =>
  match search four s with
  | some g => .ok (.american (.naca4 (g.g1.toNat?.getD 0) p) (tail g p))
  | none =>
  match search sixteen s with
  | some g => .ok (.american (Profile.naca6Default (Num.parse g.g2) p) (series g p))
  | none =>
  match search sixA s with
  | some g => .ok (.american (.naca6A (Num.parse g.g2) p) (series g p))
  | none => .error "not valid"
where
  /-- the thickness of the 4- and 5-digit designations -/
  tail (g : Groups) (p : Nat) : Profile :=
    match g.g3 with
    | some m => Profile.modifiedM (Num.parse g.g2) (Num.parse m) p
    | none => Profile.clarkYDefault (Num.parse g.g2) p
  /-- the thickness of the 1- and 6A-series designations -/
  series (g : Groups) (p : Nat) : Profile :=
    Profile.modifiedM (Num.parse g.g1) (Num.parse (g.g3.getD "")) p

/-- `parse?`, with the zero airfoil for an invalid designation (use `NACA!"…"` to reject those
while elaborating). -/
def parse! (s : String) (p : Nat := 150) : Airfoil :=
  match parse? s p with
  | .ok a => a
  | .error _ => default

end NACA

open Lean Elab Term in
/-- `NACA!"2412"`: Julia's `NACA"2412"` string macro (`airfoils.jl:150`), an `Airfoil` with 150
samples per surface. An invalid designation is an elaboration error ("not valid"), as Julia's
macro fails at expansion. -/
elab "NACA!" s:str : term => do
  let str := s.getString
  match NACA.parse? str with
  | .ok _ => elabTerm (← `(FlowGeometry.NACA.parse! $s)) (some (mkConst ``FlowGeometry.Airfoil))
  | .error e => throwError "NACA\"{str}\": {e}"

end FlowGeometry

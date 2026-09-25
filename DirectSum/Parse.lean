/-
String grammars for spaces and the literal syntax `S!"…"`, `D!"…"`, `V!"…"`,
`ℝ^n` (Julia `@S_str`, `@D_str`, `@V_str`, `ℝ^n`; DirectSum.jl
`src/DirectSum.jl:139-150, 205, 410-438`).

The macros run the parser at elaboration time and emit a `TensorBundle`
structure literal, so `abbrev CGA3 := S!"∞∅+++"` unfolds to a constructor
application and a malformed string is a compile-time error (the analogue of
Julia's macro-expansion-time evaluation).

Accepted grammars (Julia's quirks Q1–Q3 are *not* replicated):

* `S!`: `^(∞)?(∅)?[+-]*$`, or Julia's legacy digit form `ndo[metric]` with
  `d, o ∈ {0,1}` and `metric < 2ⁿ` (`S!"3"` = `⟨+++⟩`, `S!"5110"` = `⟨∞∅+++⟩`).
* `D!`: comma-separated numbers: integers, decimals (`1.5`), rationals
  (`1//2` or `1/2`).
* `V!`: all digits → the `Int` space (`V!"3"` = Julia `3`); contains `,` →
  `D!`; otherwise `S!`.
-/
import DirectSum.SpaceOps

namespace DirectSum

open Bits Lean

namespace TensorBundle

/-- Parse a signature string (Julia `Signature(str)`). -/
def parseSignature (s : String) : Except String TensorBundle :=
  let cs := s.toList
  if !cs.isEmpty && cs.all Char.isDigit then
    -- Julia digit grammar: pad to 5 characters when shorter than 4
    let cs := if cs.length < 4 then cs ++ List.replicate (5 - cs.length) '0' else cs
    let dig := fun (c : Char) => c.toNat - '0'.toNat
    let n := dig cs[0]!
    let d := dig cs[1]!
    let o := dig cs[2]!
    let m := (String.ofList (cs.drop 3)).toNat!
    if d > 1 || o > 1 then .error s!"S\"{s}\": option digits must be 0 or 1 (Julia quirk Q2)"
    else if d + o > n then .error s!"S\"{s}\": more null generators than dimensions"
    else if m ≥ 2 ^ n then .error s!"S\"{s}\": metric {m} does not fit in {n} generators (Julia quirk Q2)"
    else .ok (ofCode n (d == 1) (o == 1) m.toUInt64)
  else
    let inf := cs.head? == some '∞'
    let rest := if inf then cs.tail else cs
    let origin := rest.head? == some '∅'
    let rest := if origin then rest.tail else rest
    if !rest.all (fun c => c == '+' || c == '-') then
      .error s!"S\"{s}\": expected (∞)(∅)[+-]* (Julia quirk Q3 positions are rejected)"
    else
      let n := cs.length
      -- ∞ counts as `+`, ∅ as `-` (Julia replaces the glyphs before reading bits)
      let signs := (if inf then ['+'] else []) ++ (if origin then ['-'] else []) ++ rest
      let neg := signs.zipIdx.foldl (fun acc (c, k) => if c == '-' then acc ||| shl 1 k else acc) 0
      if n > 62 then .error s!"S\"{s}\": at most 62 generators" else
      .ok { n, metric := .signature neg, hasinf := inf, hasorigin := origin }

/-- Parse one diagonal entry: `-3`, `1.5`, `1//2`, `1/2`. -/
def parseRat (s : String) : Except String Rat :=
  let s := s.trimAscii.toString
  let (neg, body) := if s.startsWith "-" then (true, (s.drop 1).toString)
    else if s.startsWith "+" then (false, (s.drop 1).toString) else (false, s)
  let sgn := fun (r : Rat) => if neg then -r else r
  let nat? := fun (t : String) => if !t.isEmpty && t.all Char.isDigit then some t.toNat! else none
  match body.splitOn "//" with
  | [p, q] => match nat? p, nat? q with
    | some a, some b => if b == 0 then .error s!"zero denominator in {s}" else .ok (sgn ((a : Rat) / b))
    | _, _ => .error s!"not a number: {s}"
  | _ => match body.splitOn "/" with
    | [p, q] => match nat? p, nat? q with
      | some a, some b => if b == 0 then .error s!"zero denominator in {s}" else .ok (sgn ((a : Rat) / b))
      | _, _ => .error s!"not a number: {s}"
    | _ => match body.splitOn "." with
      | [p] => match nat? p with
        | some a => .ok (sgn a)
        | none => .error s!"not a number: {s}"
      | [p, f] => match nat? (if p.isEmpty then "0" else p), nat? f with
        | some a, some b => .ok (sgn ((a : Rat) + (b : Rat) / (10 ^ f.length : Nat)))
        | _, _ => .error s!"not a number: {s}"
      | _ => .error s!"not a number: {s}"

/-- Parse a diagonal-form string (Julia `DiagonalForm(str)`), e.g. `"1,1,1,0"`. -/
def parseDiagonal (s : String) : Except String TensorBundle := do
  let vals ← (s.splitOn ",").toArray.mapM parseRat
  if vals.size > 62 then throw s!"D\"{s}\": at most 62 generators"
  return diag vals

/-- Parse a space string (Julia `TensorBundle(str)`, corrected per quirk Q1):
digits → `Int` space, commas → `DiagonalForm`, otherwise `Signature`. -/
def parseBundle (s : String) : Except String TensorBundle :=
  if !s.isEmpty && s.all Char.isDigit then
    let n := s.toNat!
    if n > 62 then .error s!"V\"{s}\": at most 62 generators" else .ok (euclidean n)
  else if s.contains ',' then parseDiagonal s
  else parseSignature s

/-! ## Structure literals -/

/-- Syntax for a natural-number literal. -/
private def natLit (n : Nat) : Term := Syntax.mkNumLit (toString n)

/-- Syntax for a rational constant. -/
private def ratLit (r : Rat) : MacroM Term := do
  let num := natLit r.num.natAbs
  let base ← if r.den == 1 then `(($num : Rat)) else `((($num : Rat) / ($(natLit r.den) : Rat)))
  if r.num < 0 then `((-$base)) else pure base

/-- Syntax for a Boolean constant. -/
private def boolLit (b : Bool) : MacroM Term := if b then `(true) else `(false)

/-- Syntax for an integer constant. -/
private def intLit (i : Int) : MacroM Term :=
  if i < 0 then `((-$(natLit i.natAbs) : Int)) else `(($(natLit i.natAbs) : Int))

/-- A structure literal elaborating to `V` (used by `S!`, `D!`, `V!`, `ℝ^`). -/
def toSyntax (V : TensorBundle) : MacroM Term := do
  let metric ← match V.metric with
    | .signature s => `(DirectSum.Metric.signature ($(natLit s.toNat) : UInt64))
    | .euclid => `(DirectSum.Metric.euclid)
    | .diagonal d => do
      let xs ← d.mapM ratLit
      `(DirectSum.Metric.diagonal #[$xs,*])
    | .tensor g => do
      let rows ← g.mapM fun row => do
        let xs ← row.mapM ratLit
        `(#[$xs,*])
      `(DirectSum.Metric.tensor #[$rows,*])
  `(({ n := $(natLit V.n), metric := $metric, hasinf := $(← boolLit V.hasinf),
       hasorigin := $(← boolLit V.hasorigin), dyadmode := $(← intLit V.dyadmode),
       polymode := $(← boolLit V.polymode), diffvars := $(natLit V.diffvars),
       diffmode := $(natLit V.diffmode), name := $(natLit V.name) } : DirectSum.TensorBundle))

end TensorBundle

/-- `S!"-+++"`: a `Signature` literal (Julia `S"-+++"`); `∞`/`∅` prefixes give
conformal/projective spaces (`S!"∞∅+++"`). -/
syntax:max (name := sigLit) "S!" str : term

/-- `D!"1,2,-3"`: a `DiagonalForm` literal (Julia `D"1,2,-3"`). -/
syntax:max (name := diagLit) "D!" str : term

/-- `V!"…"`: Julia `V"…"` with the corrected grammar (digits, commas, signs). -/
syntax:max (name := bundleLit) "V!" str : term

/-- `ℝ^n`: the Euclidean `Signature` of dimension `n` (Julia `ℝ^n`). A numeral
`n` elaborates to a structure literal; any other term to `TensorBundle.sig n`. -/
syntax:max "ℝ^" term:max : term

private def expandWith (p : String → Except String TensorBundle) (s : TSyntax `str) :
    MacroM Term :=
  match p s.getString with
  | .ok V => V.toSyntax
  | .error e => Macro.throwErrorAt s e

macro_rules
  | `(S! $s) => expandWith TensorBundle.parseSignature s
  | `(D! $s) => expandWith TensorBundle.parseDiagonal s
  | `(V! $s) => expandWith TensorBundle.parseBundle s
  | `(ℝ^ $n) => match n.raw.isNatLit? with
    | some k => (TensorBundle.sig k).toSyntax
    | none => `(DirectSum.TensorBundle.sig $n)

end DirectSum

/-
Runtime string parsers for `TensorBundle` (`parseSignature`, `parseRat`, `parseDiagonal`,
`parseBundle`), split out of `DirectSum.Parse` so `DirectSum.Parse`'s compile-time macros
(`S!"..."`, `D!"..."`, `V!"..."`, `ℝ^n`) can `public meta import DirectSum.ParseCore` while
keeping `DirectSum` strictly `Init`-only.
-/
module

public import DirectSum.SpaceOps

@[expose] public section

namespace DirectSum

open Bits

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

end TensorBundle

end DirectSum

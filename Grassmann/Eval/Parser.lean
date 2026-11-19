import Grassmann.Scene.Types

/-!
# Unified Geometric Algebra & Scalar Expression Parser (`Grassmann.Eval.Parser`)

Promotes and generalizes the parser architecture from `Tests/Golden/DocsParse.lean`
into a first-class `Init`-only parser supporting BOTH:
- **Grassmann.jl / Michael Reed syntax**: `v12`, `v∞`, `v∅`, `∧`, `∨`, `⋅`, `⨼`, `⨽`,
  `⋆`, `~`, `!`, `>>>`, `⊘`, `S"-+++"`, `D"0,1,1,1"`, `ℝ3`, numeric juxtaposition (`2v1`, `0.5e12`)
- **Ganja.js / Steven De Keninck syntax**: `1e12`, `0.5e03`, `e0..e5`, `no`, `ni`,
  `^`, `&`, `|`, `<<`, `>>>`, `~`, `!`, `**`, `.Normalized`, `.Reverse`, `.Dual`,
  `.Conjugate`, `.Length`, `.Grade(k)`, `let x = ...; ...`, `handle(id, x, y, z)`,
  `Cl(p,q,r)`
- **Scalar / Surface / Implicit Equations**: `z = sin(x*2+t)*cos(y*2)`,
  `x^2 + y^2 - 1 = 0` (equations `a = b` parse as `eq a b` so contour solvers evaluate `a - b`).
-/

namespace Grassmann.Eval

/-- Tokens produced by the unified GA / scalar lexer. -/
inductive Tok where
  | num (val : Float) (raw : String)
  | blade (prefixChar : Char) (sub : String) -- e.g. `e12`, `e03`, `v12`, `v∞`, `v∅`
  | ident (name : String)
  | str (body : String)
  | op (sym : String)
  | kw (name : String) -- `let`, `in`, `true`, `false`
  | sep -- `;` or newline
  deriving Repr, BEq, Inhabited

/-- Abstract syntax tree for GA expressions, CoffeeShop scripts, and scalar equations. -/
inductive Expr where
  | num (val : Float)
  | blade (prefixChar : Char) (sub : String)
  | ident (name : String)
  | str (body : String)
  | unary (op : String) (e : Expr)
  | binary (op : String) (lhs rhs : Expr)
  | call (name : String) (args : Array Expr)
  | field (obj : Expr) (name : String)
  | method (obj : Expr) (name : String) (args : Array Expr)
  | list (elems : Array Expr)
  | letBind (name : String) (val : Expr)
  | eq (lhs rhs : Expr) -- `lhs = rhs` (equation or binding)
  | seq (stmts : Array Expr)
  deriving Repr, Inhabited

/-! ## Lexer -/

private def isSubDigit (c : Char) : Bool :=
  c.isDigit || ('₀' ≤ c && c ≤ '₉') || c == '∞' || c == '∅'

private def normSubChar (c : Char) : Char :=
  if '₀' ≤ c && c ≤ '₉' then Char.ofNat (48 + (c.toNat - '₀'.toNat))
  else c

private def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == 'π' || c == 'ℯ' || c == 'θ' || c == 'φ' ||
    c == 'α' || c == 'β' || c == 'γ' || c == 'ω' || c == 'λ' || c == 'ℝ' ||
    c == '∞' || c == '∅'

private def isIdentCont (c : Char) : Bool :=
  isIdentStart c || isSubDigit c

private def multiOps : List String :=
  [">>>", "<<", ">>", "**", "==", "!=", "<=", ">=", "->"]

private def singleOps : String :=
  "+-*/^&|∧∨⋅⨼⨽⋆~!⊘=,:()[]{}."

private def parseFloatLiteral (s : String) : Float :=
  let cs := s.toList
  let intPart := cs.takeWhile Char.isDigit
  let r1 := cs.drop intPart.length
  let (fracPart, r2) := match r1 with
    | '.' :: r =>
      let fp := r.takeWhile Char.isDigit
      (fp, r.drop fp.length)
    | _ => ([], r1)
  let (expNeg, expDigits) := match r2 with
    | 'E' :: '+' :: r | 'e' :: '+' :: r => (false, r.takeWhile Char.isDigit)
    | 'E' :: '-' :: r | 'e' :: '-' :: r => (true, r.takeWhile Char.isDigit)
    | 'E' :: r => (false, r.takeWhile Char.isDigit)
    | _ => (false, [])
  let d2f (ds : List Char) : Float :=
    ds.foldl (fun acc c => acc * 10.0 + (c.toNat - 48).toFloat) 0.0
  let mant := d2f intPart + d2f fracPart / Float.pow 10.0 fracPart.length.toFloat
  let expVal := expDigits.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0
  if expVal == 0 then mant
  else if expNeg then mant / Float.pow 10.0 expVal.toFloat
  else mant * Float.pow 10.0 expVal.toFloat

/-- Check if an identifier is a basis blade literal like `e0`, `e12`, `e0123`, `v12`, `v∞`, `v∅`, `e_12`. -/
private def splitBladeIdent? (name : String) : Option (Char × String) :=
  match name.toList with
  | pfx :: rest =>
    if (pfx == 'e' || pfx == 'v' || pfx == 'E') && !rest.isEmpty then
      let cleaned := match rest with | '_' :: r => r | r => r
      if !cleaned.isEmpty && cleaned.all isSubDigit then
        some (pfx, String.ofList (cleaned.map normSubChar))
      else none
    else none
  | [] => none

/-- Tokenize a GA expression or multi-line script.
Handles ganja.js algebraic literals (`1e12`, `0.5e03`, `.25e1`) as `num · blade`
and Grassmann.jl juxtaposition (`2v12`, `3(x+1)`). -/
partial def tokenize (input : String) : Except String (Array Tok) :=
  go input.toList #[]
where
  go (cs : List Char) (acc : Array Tok) : Except String (Array Tok) :=
    match cs with
    | [] => .ok acc
    | c :: rest =>
      if c == '\n' || c == ';' then
        go rest (acc.push .sep)
      else if c.isWhitespace then
        go rest acc
      else if c == '/' && rest.head? == some '/' then
        go (rest.dropWhile (· != '\n')) acc
      else if c == '#' then
        go (rest.dropWhile (· != '\n')) acc
      else if c == '"' then
        let body := rest.takeWhile (· != '"')
        let after := rest.drop (body.length + 1)
        go after (acc.push (.str (String.ofList body)))
      else if c == '0' && (rest.head? == some 'x' || rest.head? == some 'X') then
        let hexChars := (rest.drop 1).takeWhile fun ch =>
          ch.isDigit || ('a' ≤ ch && ch ≤ 'f') || ('A' ≤ ch && ch ≤ 'F')
        let val := hexChars.foldl (fun n ch =>
          let d := if ch.isDigit then ch.toNat - 48
                   else if 'a' ≤ ch && ch ≤ 'f' then 10 + (ch.toNat - 97)
                   else 10 + (ch.toNat - 65)
          n * 16 + d) 0
        go (rest.drop (1 + hexChars.length)) (acc.push (.num val.toFloat ("0x" ++ String.ofList hexChars)))
      else if c.isDigit || (c == '.' && (rest.head?.map Char.isDigit).getD false) then
        let all := c :: rest
        let intPart := all.takeWhile Char.isDigit
        let r1 := all.drop intPart.length
        let (fracPart, r2) := match r1 with
          | '.' :: r =>
            let fp := r.takeWhile Char.isDigit
            ('.' :: fp, r.drop fp.length)
          | _ => ([], r1)
        -- Distinguish scientific notation `1.0e-5` / `1E3` from ganja blade literal `1e12` / `0.5e03`
        let (expPart, r3) := match r2 with
          | 'E' :: '+' :: r =>
            let ed := r.takeWhile Char.isDigit
            ('E' :: '+' :: ed, r.drop ed.length)
          | 'E' :: '-' :: r =>
            let ed := r.takeWhile Char.isDigit
            ('E' :: '-' :: ed, r.drop ed.length)
          | 'E' :: r =>
            let ed := r.takeWhile Char.isDigit
            if ed.isEmpty then ([], r2) else ('E' :: ed, r.drop ed.length)
          | 'e' :: '+' :: r =>
            let ed := r.takeWhile Char.isDigit
            ('e' :: '+' :: ed, r.drop ed.length)
          | 'e' :: '-' :: r =>
            let ed := r.takeWhile Char.isDigit
            ('e' :: '-' :: ed, r.drop ed.length)
          | _ => ([], r2)
        let raw := String.ofList (intPart ++ fracPart ++ expPart)
        let v := parseFloatLiteral raw
        let acc := acc.push (.num v raw)
        -- Implicit multiplication for `1e12`, `2v1`, `2pi`, `2(x+1)`
        match r3 with
        | d :: _ =>
          if isIdentStart d || d == '(' then go r3 (acc.push (.op "·"))
          else go r3 acc
        | [] => go r3 acc
      else if isIdentStart c then
        let tail := rest.takeWhile isIdentCont
        let name := String.ofList (c :: tail)
        let after := rest.drop tail.length
        if name == "let" || name == "var" || name == "const" || name == "in" ||
           name == "true" || name == "false" then
          go after (acc.push (.kw (if name == "var" || name == "const" then "let" else name)))
        else
          match splitBladeIdent? name with
          | some (pfx, sub) => go after (acc.push (.blade pfx sub))
          | none => go after (acc.push (.ident name))
      else
        let sAll := String.ofList (c :: rest)
        match multiOps.find? (fun o => sAll.startsWith o) with
        | some o => go ((c :: rest).drop o.length) (acc.push (.op o))
        | none =>
          if singleOps.contains c then go rest (acc.push (.op (String.singleton c)))
          else .error s!"unexpected character '{c}'"

/-! ## Recursive-Descent / Pratt Parser -/

private structure ParseSt where
  toks : Array Tok
  pos  : Nat

private def ParseSt.peek (st : ParseSt) : Option Tok := st.toks[st.pos]?
private def ParseSt.bump (st : ParseSt) : ParseSt := { st with pos := st.pos + 1 }

private def ParseSt.skipSeps (st : ParseSt) : ParseSt :=
  let rec go (i : Nat) : Nat :=
    if h : i < st.toks.size then
      match st.toks[i] with
      | .sep => go (i + 1)
      | _ => i
    else i
  { st with pos := go st.pos }

private def binPrec (op : String) : Option (Nat × Bool) :=
  -- (precedence, isRightAssoc)
  match op with
  | "+" | "-"                 => some (10, false)
  | ">>>" | "⊘"               => some (15, true)
  | "|"                       => some (20, false)
  | "*" | "/" | "·" | "⋅" | "⨼" | "⨽" => some (30, false)
  | "&" | "∨"                 => some (35, false)
  | "^" | "∧" | "<<" | ">>"   => some (40, false)
  | "**"                      => some (50, true)
  | _                         => none

mutual

private partial def parsePrimary (st : ParseSt) : Except String (Expr × ParseSt) := do
  match st.peek with
  | none => throw "unexpected end of expression"
  | some (.num v _) => return (.num v, st.bump)
  | some (.blade p sub) => return (.blade p sub, st.bump)
  | some (.str s) => return (.str s, st.bump)
  | some (.kw "true") => return (.num 1.0, st.bump)
  | some (.kw "false") => return (.num 0.0, st.bump)
  | some (.ident name) =>
    let st1 := st.bump
    match st1.peek with
    | some (.op "(") =>
      let (args, st2) ← parseArgList st1.bump ")"
      return (.call name args, st2)
    | _ => return (.ident name, st1)
  | some (.op "(") =>
    let (e, st1) ← parseExpr 0 st.bump
    match st1.peek with
    | some (.op ")") => return (e, st1.bump)
    | _ => throw "expected ')'"
  | some (.op "[") =>
    let (elems, st1) ← parseArgList st.bump "]"
    return (.list elems, st1)
  | some (.op "-") =>
    let (e, st1) ← parseUnary st.bump
    return (.unary "-" e, st1)
  | some (.op "+") =>
    parseUnary st.bump
  | some (.op "~") =>
    let (e, st1) ← parseUnary st.bump
    return (.unary "~" e, st1)
  | some (.op "!") =>
    let (e, st1) ← parseUnary st.bump
    return (.unary "!" e, st1)
  | some (.op "⋆") =>
    let (e, st1) ← parseUnary st.bump
    return (.unary "⋆" e, st1)
  | some tok => throw s!"unexpected token {repr tok}"

private partial def parseUnary (st : ParseSt) : Except String (Expr × ParseSt) := do
  let (base, st1) ← parsePrimary st
  parsePostfix base st1

private partial def parsePostfix (lhs : Expr) (st : ParseSt) : Except String (Expr × ParseSt) := do
  match st.peek with
  | some (.op ".") =>
    let st1 := st.bump
    match st1.peek with
    | some (.ident fname) =>
      let st2 := st1.bump
      match st2.peek with
      | some (.op "(") =>
        let (args, st3) ← parseArgList st2.bump ")"
        parsePostfix (.method lhs fname args) st3
      | _ => parsePostfix (.field lhs fname) st2
    | _ => throw "expected field/method name after '.'"
  | _ => return (lhs, st)

private partial def parseArgList (st : ParseSt) (closeSym : String) :
    Except String (Array Expr × ParseSt) := do
  let mut st := st.skipSeps
  let mut out : Array Expr := #[]
  if st.peek == some (.op closeSym) then return (out, st.bump)
  repeat
    let (e, st1) ← parseExpr 0 st.skipSeps
    out := out.push e
    let st2 := st1.skipSeps
    match st2.peek with
    | some (.op ",") => st := st2.bump
    | some (.op s) =>
      if s == closeSym then return (out, st2.bump)
      else throw s!"expected ',' or '{closeSym}'"
    | _ => throw s!"expected ',' or '{closeSym}'"
  return (out, st)

private partial def parseExpr (minPrec : Nat) (st : ParseSt) :
    Except String (Expr × ParseSt) := do
  let (lhs0, st0) ← parseUnary st
  let rec loop (lhs : Expr) (st : ParseSt) : Except String (Expr × ParseSt) := do
    match st.peek with
    | some (.op sym) =>
      match binPrec sym with
      | some (prec, isRight) =>
        if prec < minPrec then return (lhs, st)
        let nextMin := if isRight then prec else prec + 1
        let (rhs, st1) ← parseExpr nextMin st.bump
        loop (.binary sym lhs rhs) st1
      | none => return (lhs, st)
    | _ => return (lhs, st)
  loop lhs0 st0

private partial def parseStmt (st : ParseSt) : Except String (Expr × ParseSt) := do
  let st := st.skipSeps
  match st.peek with
  | some (.kw "let") =>
    let st1 := st.bump
    match st1.peek with
    | some (.ident name) =>
      let st2 := st1.bump
      if st2.peek != some (.op "=") then throw s!"expected '=' after let {name}"
      let (rhs, st3) ← parseExpr 0 st2.bump
      return (.letBind name rhs, st3)
    | _ => throw "expected identifier after 'let'"
  | _ =>
    let (lhs, st1) ← parseExpr 0 st
    if st1.peek == some (.op "=") then
      let (rhs, st2) ← parseExpr 0 st1.bump
      match lhs with
      | .ident name => return (.eq (.ident name) rhs, st2)
      | _ => return (.eq lhs rhs, st2)
    else
      return (lhs, st1)

end

/-- Parse a single expression or equation (e.g. `sin(x*2+t)*cos(y*2)` or `x^2 + y^2 = 1`). -/
def parseExprString (input : String) : Except String Expr := do
  let toks ← tokenize input
  let (e, st) ← parseStmt { toks, pos := 0 }
  let st := st.skipSeps
  if st.pos < st.toks.size then
    throw s!"trailing tokens starting at {repr st.peek}"
  return e

/-- Parse a multi-statement CoffeeShop script (`let A = ...; let B = ...; A & B`). -/
def parseScript (input : String) : Except String (Array Expr) := do
  let toks ← tokenize input
  let mut st : ParseSt := ({ toks, pos := 0 } : ParseSt).skipSeps
  let mut stmts : Array Expr := #[]
  while st.pos < st.toks.size do
    let (s, st1) ← parseStmt st
    stmts := stmts.push s
    st := st1.skipSeps
  return stmts

end Grassmann.Eval

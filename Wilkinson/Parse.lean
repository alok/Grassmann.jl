import Wilkinson.Expr

/-!
# Parsing Julia expression strings

`jl⟪ … ⟫` quotes Julia syntax at elaboration time; `JExpr.parse` does the same
at run time, for the golden files (which store Julia's `string(::Expr)`) and for
the REDUCE emulation (`Wilkinson.Reduce`), whose forms reach Julia as REDUCE's
linear output re-parsed by Julia's parser. The tree shapes are what matter
(`exprval` counts calls and literals), so the rules of Julia's parser
(`src/julia-parser.scm`) are followed for this fragment:

* `+` chains flatten into one n-ary call only while consecutive (`a + b - c + d`
  is `+(-(+(a, b), c), d)`), `*` chains likewise; `-`, `/`, `//` are binary and
  left-associative; `^` is right-associative;
* a `-` written directly before a number is part of the literal (`-2x^2` is
  `*(-2, x^2)`, `x^-2` is `^(x, -2)`), unless the number is raised to a power
  (`-2^2` is `-(2^2)`); `- 2` with a space is the call `-(2)`;
* unary minus binds looser than `^` and tighter than `*` (`-x^2` is `-(x^2)`,
  `-x*y` is `*(-x, y)`);
* juxtaposition `2x`, `2(x+1)`, `1.5e3x` multiplies a numeric literal by the
  following power-level operand.
-/

namespace Wilkinson

namespace JExpr

/-- Tokens of the expression fragment. -/
inductive Tok where
  /-- A numeric literal (its source text). -/
  | num (text : String)
  /-- An identifier. -/
  | ident (name : String)
  /-- An operator, parenthesis or comma: `+ - * / // ^ ( ) ,`. -/
  | op (s : String)
  deriving BEq, Inhabited, Repr

/-- A token with whether whitespace precedes it. -/
structure PTok where
  /-- The token. -/
  tok : Tok
  /-- Whitespace before it (Julia distinguishes `-2` from `- 2`). -/
  spaced : Bool
  deriving Inhabited

/-- Identifier characters (letters, digits, `_`, `!`, and non-ASCII such as `ϵ`). -/
def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '!' || c.toNat > 127

/-- Identifier start characters. -/
def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_' || c.toNat > 127

/-- Scan a numeric literal: digits, an optional fraction, an optional exponent
(`e`/`E` only when followed by a digit or a sign and a digit). -/
def scanNumber (cs : List Char) : List Char × List Char :=
  let (intPart, rest) := cs.span Char.isDigit
  let (frac, rest) := match rest with
    | '.' :: r => let (f, r) := r.span Char.isDigit; ('.' :: f, r)
    | r => ([], r)
  let (ex, rest) := match rest with
    | e :: s :: d :: r =>
      if (e == 'e' || e == 'E') && (s == '+' || s == '-') && d.isDigit then
        let (ds, r) := r.span Char.isDigit; (e :: s :: d :: ds, r)
      else if (e == 'e' || e == 'E') && s.isDigit then
        let (ds, r) := (d :: r).span Char.isDigit; (e :: s :: ds, r)
      else ([], rest)
    | e :: d :: r =>
      if (e == 'e' || e == 'E') && d.isDigit then
        let (ds, r) := r.span Char.isDigit; (e :: d :: ds, r)
      else ([], rest)
    | r => ([], r)
  (intPart ++ frac ++ ex, rest)

/-- Tokenize, recording preceding whitespace. -/
def tokenize (s : String) : Except String (Array PTok) :=
  go s.toList false #[] (s.length + 1)
where
  /-- Fuelled by the input length. -/
  go : List Char → Bool → Array PTok → Nat → Except String (Array PTok)
    | [], _, acc, _ => .ok acc
    | _, _, _, 0 => .error "tokenizer out of fuel"
    | c :: cs, sp, acc, fuel + 1 =>
      if c == ' ' || c == '\t' || c == '\n' then go cs true acc fuel
      else if c.isDigit || (c == '.' && (cs.head?.map Char.isDigit).getD false) then
        let (n, rest) := scanNumber (c :: cs)
        go rest false (acc.push ⟨.num (String.ofList n), sp⟩) fuel
      else if isIdentStart c then
        let (n, rest) := (c :: cs).span isIdentChar
        go rest false (acc.push ⟨.ident (String.ofList n), sp⟩) fuel
      else if c == '/' && cs.head? == some '/' then
        go cs.tail false (acc.push ⟨.op "//", sp⟩) fuel
      else if "+-*/^(),".contains c then go cs false (acc.push ⟨.op c.toString, sp⟩) fuel
      else .error s!"unexpected character '{c}'"

/-- A numeric literal's value: an `Int` if it has no `.`/exponent, else a `Float64`. -/
def numLit (text : String) (neg : Bool) : Except String JExpr :=
  if text.all Char.isDigit then
    match text.toNat? with
    | some n => .ok (.int (if neg then -(n : Int) else n))
    | none => .error s!"bad integer {text}"
  else
    let t := if text.startsWith "." then "0" ++ text else text
    let t := if t.endsWith "." then t ++ "0" else t
    match Lean.Json.parse t with
    | .ok (.num n) => .ok (.f64 (if neg then -n.toFloat else n.toFloat))
    | _ => .error s!"bad float {text}"

/-- Recursive-descent parser state: the tokens and a position. -/
structure PState where
  /-- Tokens. -/
  toks : Array PTok
  /-- Current position. -/
  pos : Nat

/-- Parser monad. -/
abbrev P := StateT PState (Except String)

/-- Peek at the current token. -/
def peek : P (Option PTok) := do let s ← get; return s.toks[s.pos]?

/-- Peek `k` tokens ahead. -/
def peekAt (k : Nat) : P (Option PTok) := do let s ← get; return s.toks[s.pos + k]?

/-- Advance one token. -/
def advance : P Unit := modify fun s => { s with pos := s.pos + 1 }

/-- Is the token the operator `o`? -/
def isOp (t : Option PTok) (o : String) : Bool := match t with
  | some ⟨.op s, _⟩ => s == o
  | _ => false

/-- Can the token start a juxtaposed operand (`x`, `(`) directly after a number? -/
def juxtaposes (t : Option PTok) : Bool := match t with
  | some ⟨.ident _, false⟩ => true
  | some ⟨.op "(", false⟩ => true
  | _ => false

mutual

/-- `expr := sum`, with minimum binding precedence `minPrec`
(`+ -` 11, `* /` 12, `//` 13). -/
partial def parseBinary (minPrec : Nat) : P JExpr := do
  let lhs ← parseUnary
  loop lhs minPrec none
where
  /-- Operator loop; `chain` is the operator of an n-ary chain `lhs` is still open for. -/
  loop (lhs : JExpr) (minPrec : Nat) (chain : Option String) : P JExpr := do
    let t ← peek
    let o := match t with | some ⟨.op s, _⟩ => s | _ => ""
    let p := prec o
    if o == "^" || o == "(" || o == ")" || o == "," || p == 0 || p < minPrec then return lhs
    advance
    let rhs ← parseBinary (p + 1)
    let node : JExpr :=
      if (o == "+" || o == "*") && chain == some o then
        match lhs with
        | .call op args => .call op (args ++ [rhs])
        | _ => .call o [lhs, rhs]
      else .call o [lhs, rhs]
    loop node minPrec (if o == "+" || o == "*" then some o else none)

/-- Unary minus/plus, then the power level. -/
partial def parseUnary : P JExpr := do
  let t ← peek
  if isOp t "-" || isOp t "+" then
    let o := if isOp t "-" then "-" else "+"
    let n ← peekAt 1
    let after ← peekAt 2
    match n with
    | some ⟨.num text, false⟩ =>
      if isOp after "^" then
        advance
        return .call o [← parsePower]
      else
        advance; advance
        let lit ← StateT.lift (numLit text (o == "-"))
        juxt lit
    | _ =>
      advance
      return .call o [← parseUnary]
  else parsePower

/-- A primary, optionally raised to a (right-associative) power. -/
partial def parsePower : P JExpr := do
  let base ← parsePrimary
  if isOp (← peek) "^" then
    advance
    let ex ← parseUnary
    return .call "^" [base, ex]
  else
    match base with
    | .lit (.int _) | .lit (.f64 _) => juxt base
    | _ => return base

/-- Numeric-literal juxtaposition `2x^2`, `2(x+1)`. -/
partial def juxt (lit : JExpr) : P JExpr := do
  if juxtaposes (← peek) then
    let rhs ← parsePower
    return .call "*" [lit, rhs]
  else return lit

/-- Literals, identifiers and parenthesised expressions. -/
partial def parsePrimary : P JExpr := do
  match ← peek with
  | some ⟨.num text, _⟩ => advance; StateT.lift (numLit text false)
  | some ⟨.ident name, _⟩ => advance; return .sym name
  | some ⟨.op "(", _⟩ =>
    -- `(op)(a, b, …)`: an operator called as a function (Julia prints `*(a)` so)
    match ← peekAt 1, ← peekAt 2 with
    | some ⟨.op o, _⟩, some ⟨.op ")", _⟩ =>
      if o == "(" || o == ")" || o == "," then throw "empty parentheses" else
      advance; advance; advance
      unless isOp (← peek) "(" do throw "expected '(' after an operator name"
      advance
      let args ← parseArgs #[]
      return .call o args.toList
    | _, _ =>
      advance
      let e ← parseBinary 0
      unless isOp (← peek) ")" do throw "expected ')'"
      advance
      return e
  | some ⟨t, _⟩ => throw s!"unexpected token {repr t}"
  | none => throw "unexpected end of input"

/-- Comma-separated arguments up to the closing parenthesis. -/
partial def parseArgs (acc : Array JExpr) : P (Array JExpr) := do
  let e ← parseBinary 0
  let acc := acc.push e
  if isOp (← peek) "," then advance; parseArgs acc
  else if isOp (← peek) ")" then advance; return acc
  else throw "expected ',' or ')'"

end

/-- Parse a Julia expression string (the fragment `Wilkinson` uses) into a `JExpr`. -/
def parse (s : String) : Except String JExpr := do
  let toks ← tokenize s
  let (e, st) ← (parseBinary 0).run ⟨toks, 0⟩
  if st.pos < toks.size then throw s!"trailing input at token {st.pos}"
  return e

end JExpr

end Wilkinson

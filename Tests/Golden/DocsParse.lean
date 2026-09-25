/-!
# A parser for the Julia statements of the docs oracle

The docs suite (`oracle/golden/docs/*.json`, docs/port-notes/oracle-schema.md §8.8) records
README and documentation statements evaluated REPL-style in a Julia sandbox. The evaluator of
`Tests.Golden.Docs` replays them on the dynamic layer; this module parses the subset of Julia
they use into an `Expr`:

* literals: integers, decimals (`1.0e10`), `π`, `im`, string macros (`S"-++"`, `basis"3"`);
* identifiers with Unicode (`v₁₂`, `v∞∅`, `𝕚`, `ℝ3`, `∂1`, `θ`), `ans`;
* numeric juxtaposition (`2v1`, `0.5v12`, `3v123+2v1`: a literal times the power-level
  operand after it, Julia's rule `2x^2 = 2(x^2)`);
* Julia's precedence levels: assignment, `->`, tuples, comparisons (`==`, `≈`, `<`, `>`,
  `∈`, `⊇`, `∥`, chained), `:`, the plus level (`+ - | ∨ ⊕ ⊖ ∪`), the times level
  (`* / \ ∧ ⋅ ⨼ ⨽ ⟑ ∗ ⊛ × ⊘ ⊙ ⊠ ⊗ ∩`), `//`, the bitshift level (`<< >> >>>`), prefix
  operators (`- + ~ ! ⋆ ↑ ↓ |`), `^` (right associative), postfix `'`, calls, indexing,
  type parameters (`Chain{V,1}`), field access (`Λ(3).v21`);
* statements: `a = …`, `a, b = …`, `f(x) = …`, `function f(x) … end`, `;` sequences,
  lambdas `a -> …`, macro calls (`@basis ℝ^3 E e`), vectors and comprehensions
  (`[!b for b in Λ(4).b]`).

Anything else is a parse error; the evaluator then reports the statement as unimplemented.
-/

namespace Tests.ElementOracle.Docs

/-- A token. -/
inductive Tok where
  /-- A numeric literal (its text). -/
  | num (s : String)
  /-- An identifier. -/
  | ident (s : String)
  /-- A string macro `pfx"body"` (`pfx` may be empty for a plain string). -/
  | str (pfx body : String)
  /-- An operator or punctuation. -/
  | op (s : String)
  /-- A keyword (`function`, `end`, `for`, `in`, `return`, `begin`). -/
  | kw (s : String)
  /-- A macro name (`@basis`). -/
  | mac (s : String)
  /-- A statement separator (newline). -/
  | nl
  deriving Repr, BEq, Inhabited

/-- A parsed expression. -/
inductive Expr where
  /-- A numeric literal. -/
  | num (s : String)
  /-- An identifier. -/
  | ident (s : String)
  /-- A string macro. -/
  | str (pfx body : String)
  /-- `@name args…`. -/
  | mac (name : String) (args : Array Expr)
  /-- `f(args…)`. -/
  | call (f : Expr) (args : Array Expr)
  /-- `T{args…}`. -/
  | curly (f : Expr) (args : Array Expr)
  /-- `a[args…]`. -/
  | index (a : Expr) (args : Array Expr)
  /-- `a.name`. -/
  | field (a : Expr) (name : String)
  /-- A binary operator. -/
  | bin (op : String) (a b : Expr)
  /-- A prefix operator. -/
  | un (op : String) (a : Expr)
  /-- Postfix adjoint `a'`. -/
  | adj (a : Expr)
  /-- A tuple `(a, b, …)`. -/
  | tuple (xs : Array Expr)
  /-- A vector `[a, b, …]`. -/
  | vect (xs : Array Expr)
  /-- `[body for v in src]`. -/
  | compr (body : Expr) (v : String) (src : Expr)
  /-- Chained comparisons `a op₁ b op₂ c`. -/
  | cmp (ops : Array String) (xs : Array Expr)
  /-- `lhs = rhs`. -/
  | assign (lhs rhs : Expr)
  /-- `(params) -> body`. -/
  | lam (params : Array String) (body : Expr)
  /-- `a; b; …`. -/
  | block (xs : Array Expr)
  /-- `function f(params) body end` or `f(params) = body`. -/
  | fdef (name : String) (params : Array String) (body : Expr)
  /-- `return e`. -/
  | ret (e : Expr)
  deriving Repr, Inhabited

/-! ## Tokenizer -/

/-- Characters that may start an identifier. -/
def identStart (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == '∂' || c == 'ϵ' || c == '∇' || c == 'Δ' || c == 'ℝ' ||
    c == '𝟎' || c == 'χ' || c == '𝒫' || c == 'π' || c == 'ℯ' || c == '∠' ||
    (c.val ≥ 0x370 && c.val ≤ 0x3FF) ||      -- Greek
    (c.val ≥ 0x1D400 && c.val ≤ 0x1D7FF) ||  -- mathematical alphanumerics (𝕚 𝕛 𝕜)
    (c.val ≥ 0x2100 && c.val ≤ 0x214F && c != '⅋')  -- letterlike symbols

/-- Characters that may continue an identifier. -/
def identCont (c : Char) : Bool :=
  identStart c || c.isDigit || c == '∞' || c == '∅' || c == '!' ||
    ('₀' ≤ c && c ≤ '₉') || ('⁰' ≤ c && c ≤ '⁹') || c == '¹' || c == '²' || c == '³' ||
    c == '⃖' || c == '′'

/-- Multi-character operators, longest first. -/
def multiOps : List String :=
  [">>>", "...", "->", "==", "!=", "<=", ">=", "<<", ">>", "//", "::", "&&", "||", ".+", ".*", "./"]

/-- Single-character operators and punctuation. -/
def singleOps : String :=
  "+-*/\\^∧∨⋅⨼⨽⟑⊖∗⊛×⊘|<>~!⋆∥⊙⊠⊗∈⊕:=,;()[]{}.'↑↓∩∪⊇≈√∘"

/-- Keywords. -/
def keywords : List String := ["function", "end", "for", "in", "return", "begin", "do"]

/-- Tokenize, with the whitespace-sensitivity the parser needs: a numeric literal directly
followed by an identifier or `(` becomes `num, op "·"` (juxtaposition), and `'` directly
after an operand is the adjoint (an opening `'` would be a character literal, which the
docs do not use). -/
partial def tokenize (s : String) : Except String (Array Tok) :=
  go s.toList #[]
where
  go : List Char → Array Tok → Except String (Array Tok)
    | [], acc => .ok acc
    | c :: cs, acc =>
      if c == '\n' then go cs (acc.push .nl)
      else if c.isWhitespace then go cs acc
      else if c == '#' then go (cs.dropWhile (· != '\n')) acc
      else if c.isDigit || (c == '.' && (cs.head?.map Char.isDigit).getD false) then
        let (lit, rest) := number (c :: cs)
        let acc := acc.push (.num lit)
        match rest with
        | d :: _ => if identStart d || d == '(' then go rest (acc.push (.op "·")) else go rest acc
        | [] => go rest acc
      else if c == '@' then
        let name := cs.takeWhile identCont
        go (cs.drop name.length) (acc.push (.mac (String.ofList name)))
      else if c == '"' then
        let body := cs.takeWhile (· != '"')
        go (cs.drop (body.length + 1)) (acc.push (.str "" (String.ofList body)))
      else if identStart c then
        let name := String.ofList (c :: cs.takeWhile identCont)
        let rest := cs.drop (name.length - 1)
        match rest with
        | '"' :: r =>
          let body := r.takeWhile (· != '"')
          go (r.drop (body.length + 1)) (acc.push (.str name (String.ofList body)))
        | _ =>
          if keywords.contains name then go rest (acc.push (.kw name))
          else go rest (acc.push (.ident name))
      else
        match multiOps.find? (fun o => (String.ofList (c :: cs)).startsWith o) with
        | some o => go ((c :: cs).drop o.length) (acc.push (.op o))
        | none =>
          if singleOps.contains c then go cs (acc.push (.op (String.singleton c)))
          else .error s!"unexpected character {c}"
  /-- A numeric literal: digits, an optional fraction and exponent (`1.0e-10`). -/
  number (cs : List Char) : String × List Char :=
    let int := cs.takeWhile Char.isDigit
    let r := cs.drop int.length
    let (frac, r) := match r with
      | '.' :: d :: r' => if d.isDigit then
          let f := (d :: r').takeWhile Char.isDigit
          ('.' :: f, (d :: r').drop f.length)
        else ([], r)
      | _ => ([], r)
    let (exp, r) := match r with
      | 'e' :: r' =>
        let (sgn, r'') := match r' with
          | '-' :: x => (['-'], x)
          | '+' :: x => (['+'], x)
          | x => ([], x)
        let ds := r''.takeWhile Char.isDigit
        if ds.isEmpty then ([], r) else ('e' :: sgn ++ ds, r''.drop ds.length)
      | _ => ([], r)
    (String.ofList (int ++ frac ++ exp), r)

/-! ## Parser -/

/-- Parser state: the tokens and the position. -/
structure PState where
  /-- The tokens. -/
  toks : Array Tok
  /-- The next position. -/
  pos : Nat := 0

/-- The parser monad. -/
abbrev P := StateT PState (Except String)

/-- The next token (`nl` at the end). -/
def peek : P Tok := do
  let s ← get
  return s.toks[s.pos]?.getD .nl

/-- The token after the next. -/
def peek2 : P Tok := do
  let s ← get
  return s.toks[s.pos + 1]?.getD .nl

/-- Whether the input is exhausted. -/
def atEnd : P Bool := do
  let s ← get
  return s.pos ≥ s.toks.size

/-- Consume one token. -/
def advance : P Unit := modify fun s => { s with pos := s.pos + 1 }

/-- Consume the operator `o` or fail. -/
def expectOp (o : String) : P Unit := do
  if (← peek) == .op o then advance else throw s!"`{o}` expected, got {repr (← peek)}"

/-- Whether the next token is the operator `o` (consuming it if so). -/
def acceptOp (o : String) : P Bool := do
  if (← peek) == .op o then advance; return true else return false

/-- Skip newlines. -/
partial def skipNl : P Unit := do
  if (← peek) == .nl && !(← atEnd) then advance; skipNl

/-- Comparison operators (Julia's comparison level). -/
def cmpOps : List String := ["==", "!=", "≈", "<", ">", "<=", ">=", "∈", "⊇", "∥"]
/-- Plus-level operators. -/
def plusOps : List String := ["+", "-", "|", "∨", "⊕", "⊖", "∪"]
/-- Times-level operators (`·` is numeric juxtaposition, handled at the power level). -/
def timesOps : List String := ["*", "/", "\\", "∧", "⋅", "⨼", "⨽", "⟑", "∗", "⊛", "×", "⊘", "⊙", "⊠", "⊗", "∩", "∘"]
/-- Bitshift-level operators. -/
def shiftOps : List String := ["<<", ">>", ">>>"]
/-- Prefix operators. -/
def prefixOps : List String := ["-", "+", "~", "!", "⋆", "↑", "↓", "|", "√"]

mutual

/-- A statement sequence: `;`/newline separated statements (a block if more than one). -/
partial def pBlock (stop : Tok → Bool) : P Expr := do
  let mut xs : Array Expr := #[]
  repeat
    skipNl
    while (← acceptOp ";") do skipNl
    if (← atEnd) || stop (← peek) then break
    xs := xs.push (← pStmt)
  return if xs.size == 1 then xs[0]! else .block xs

/-- One statement: `function`, `return`, an assignment or an expression. -/
partial def pStmt : P Expr := do
  match ← peek with
  | .kw "function" =>
    advance
    let sig ← pPostfix
    let body ← pBlock (· == .kw "end")
    unless (← peek) == .kw "end" do throw "`end` expected"
    advance
    match sig with
    | .call (.ident f) ps => return .fdef f (← ps.mapM paramName) body
    | _ => throw "function signature expected"
  | .kw "return" => advance; return .ret (← pAssign)
  | _ => pAssign

/-- `lhs = rhs` (a call on the left is a function definition). -/
partial def pAssign : P Expr := do
  let lhs ← pTuple
  if (← acceptOp "=") then
    let rhs ← pAssign
    match lhs with
    | .call (.ident f) ps => return .fdef f (← ps.mapM paramName) rhs
    | _ => return .assign lhs rhs
  else return lhs

/-- A comma-separated tuple (without parentheses). -/
partial def pTuple : P Expr := do
  let e ← pLambda
  if (← peek) == .op "," then
    let mut xs := #[e]
    while (← acceptOp ",") do
      if (← peek) == .op "=" || (← peek) == .op ")" then break
      xs := xs.push (← pLambda)
    return .tuple xs
  else return e

/-- `params -> body`. -/
partial def pLambda : P Expr := do
  let e ← pCmp
  if (← acceptOp "->") then
    let body ← pLambda
    let ps ← match e with
      | .ident x => pure #[x]
      | .tuple xs => xs.mapM paramName
      | _ => throw "lambda parameters expected"
    return .lam ps body
  else return e

/-- Chained comparisons. -/
partial def pCmp : P Expr := do
  let e ← pColon
  let mut ops : Array String := #[]
  let mut xs := #[e]
  repeat
    match ← peek with
    | .op o =>
      if cmpOps.contains o then
        advance; ops := ops.push o; xs := xs.push (← pColon)
      else break
    | .kw "in" => advance; ops := ops.push "∈"; xs := xs.push (← pColon)
    | _ => break
  return if ops.isEmpty then e else .cmp ops xs

/-- `a : b`. -/
partial def pColon : P Expr := do
  let e ← pPlus
  if (← acceptOp ":") then return .bin ":" e (← pPlus) else return e

/-- The plus level (left associative). -/
partial def pPlus : P Expr := do
  let mut e ← pTimes
  repeat
    match ← peek with
    | .op o => if plusOps.contains o then advance; e := .bin o e (← pTimes) else break
    | _ => break
  return e

/-- The times level (left associative). -/
partial def pTimes : P Expr := do
  let mut e ← pRational
  repeat
    match ← peek with
    | .op o => if timesOps.contains o then advance; e := .bin o e (← pRational) else break
    | _ => break
  return e

/-- `a // b`. -/
partial def pRational : P Expr := do
  let mut e ← pShift
  while (← acceptOp "//") do e := .bin "//" e (← pShift)
  return e

/-- The bitshift level. -/
partial def pShift : P Expr := do
  let mut e ← pUnary
  repeat
    match ← peek with
    | .op o => if shiftOps.contains o then advance; e := .bin o e (← pUnary) else break
    | _ => break
  return e

/-- Prefix operators. -/
partial def pUnary : P Expr := do
  match ← peek with
  | .op o =>
    if prefixOps.contains o then
      advance
      return .un o (← pUnary)
    else pPower
  | _ => pPower

/-- `a ^ b` (right associative; the exponent may carry a sign) and numeric juxtaposition. -/
partial def pPower : P Expr := do
  let base ← pPostfix
  let base ← match base with
    | .num _ =>
      if (← acceptOp "·") then pure (.bin "*" base (← pPower)) else pure base
    | _ => pure base
  if (← acceptOp "^") then return .bin "^" base (← pUnary) else return base

/-- Calls, indexing, type parameters, fields and the adjoint. -/
partial def pPostfix : P Expr := do
  let mut e ← pAtom
  repeat
    match ← peek with
    | .op "(" => advance; e := .call e (← pArgs ")")
    | .op "[" => advance; e := .index e (← pArgs "]")
    | .op "{" => advance; e := .curly e (← pArgs "}")
    | .op "'" => advance; e := .adj e
    | .op "." =>
      match ← peek2 with
      | .ident f => advance; advance; e := .field e f
      | _ => break
    | _ => break
  return e

/-- Comma-separated arguments up to the closing bracket. -/
partial def pArgs (close : String) : P (Array Expr) := do
  let mut xs : Array Expr := #[]
  skipNl
  if (← acceptOp close) then return xs
  repeat
    skipNl
    xs := xs.push (← pLambda)
    skipNl
    if (← acceptOp close) then break
    expectOp ","
  return xs

/-- An atom. -/
partial def pAtom : P Expr := do
  match ← peek with
  | .num s => advance; return .num s
  | .ident s => advance; return .ident s
  | .str p b => advance; return .str p b
  | .mac m =>
    advance
    if (← peek) == .op "(" then advance; return .mac m (← pArgs ")")
    -- space-separated arguments up to the end of the statement
    let mut args : Array Expr := #[]
    repeat
      match ← peek with
      | .nl => break
      | .op ";" => break
      | _ => if (← atEnd) then break else args := args.push (← pUnary)
    return .mac m args
  | .op "(" =>
    advance
    skipNl
    if (← acceptOp ")") then return .tuple #[]
    let e ← pBlock (· == .op ")")
    expectOp ")"
    return e
  | .op "[" =>
    advance
    if (← acceptOp "]") then return .vect #[]
    let first ← pLambda
    match ← peek with
    | .kw "for" =>
      advance
      let v ← match ← peek with
        | .ident v => advance; pure v
        | _ => throw "comprehension variable expected"
      match ← peek with
      | .kw "in" => advance
      | .op "∈" => advance
      | .op "=" => advance
      | _ => throw "`in` expected"
      let src ← pLambda
      expectOp "]"
      return .compr first v src
    | _ =>
      let mut xs := #[first]
      while (← acceptOp ",") do xs := xs.push (← pLambda)
      expectOp "]"
      return .vect xs
  | .op o =>
    -- an operator used as a value (`cayley(V, <)`)
    match ← peek2 with
    | .op "," | .op ")" => advance; return .ident o
    | _ => throw s!"unexpected operator {o}"
  | t => throw s!"unexpected {repr t}"

/-- A parameter name. -/
partial def paramName : Expr → P String
  | .ident x => pure x
  | _ => throw "parameter name expected"

end

/-- Parse one docs statement. -/
def parse (s : String) : Except String Expr := do
  let toks ← tokenize s
  let (e, st) ← (pBlock (fun _ => false)).run { toks }
  if st.pos < toks.size then throw s!"trailing tokens at {st.pos}"
  return e

end Tests.ElementOracle.Docs

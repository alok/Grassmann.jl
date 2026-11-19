import Grassmann.Scene.Types

/-!
# Unified Geometric Algebra & LiveScript v2 Parser (`Grassmann.Eval.Parser`)

Strictly `Init`-only (ZERO `Lean.*`/`Std.*` imports) parser supporting BOTH:
- **Grassmann.jl / Michael Reed syntax**: `v12`, `v∞`, `v∅`, `∧`, `∨`, `⋅`, `⨼`, `⨽`,
  `⋆`, `~`, `!`, `>>>`, `⊘`, `S"-+++"`, `D"0,1,1,1"`, `ℝ3`, numeric juxtaposition (`2v1`, `0.5e12`)
- **Ganja.js / Steven De Keninck CoffeeShop syntax**: `Algebra(p, q, r)`, `@basis PGA3`,
  `1e12`, `0.5e03`, `e0..e5`, `no`, `ni`, `^`, `&`, `|`, `<<`, `>>>`, `~`, `!`, `**`,
  `.Normalized`, `.Reverse`, `.Dual`, `.Conjugate`, `.Length`, `.Grade(k)`, `0x44aaff` hex colors,
  `graph([0x44aaff, A, B, "A & B", A & B])`, `handle(id, x, y, z)`, `Cl(p, q, r)`
- **LiveScript v2 programming constructs**:
  - Multi-statement scripts with `let`/`var`/`const` or bare `A = ...` bindings
  - User helper functions: `fn f(x, y) = expr` (and `def f(x) = expr`, `(x, y) => expr`)
  - Bounded loops: `for i in 0..N { ... }` and list comprehensions: `[expr for i in 0..N]`
  - Conditionals: `if cond { a } else { b }` and ternary `cond ? a : b`
  - Comparisons: `<`, `>`, `<=`, `>=`, `==`, `!=`
  - Exact `Line L, Col C:` diagnostics on every lexer & syntax error!

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) & Steven De Keninck (`enkimute` / `ganja.js`).
-/

namespace Grassmann.Eval

/-- 1-based source location for crisp inline editor diagnostics. -/
structure Span where
  line : Nat := 1
  col  : Nat := 1
  deriving Repr, BEq, Inhabited

/-- Tokens produced by the unified GA / LiveScript v2 lexer. -/
inductive Tok where
  | num   (val : Float) (raw : String)
  | color (hex : UInt32) (raw : String) -- e.g. `0x44aaff`
  | blade (prefixChar : Char) (sub : String) -- e.g. `e12`, `e03`, `v12`, `v∞`, `v∅`
  | ident (name : String)
  | str   (body : String)
  | op    (sym : String)
  | kw    (name : String) -- `let`, `fn`, `for`, `in`, `if`, `else`, `return`, `true`, `false`
  | atBasis -- `@basis`
  | sep   -- `;` or newline
  deriving Repr, BEq, Inhabited

/-- Token annotated with its exact 1-based source `(line, col)` span. -/
structure SpannedTok where
  tok  : Tok
  span : Span
  deriving Repr, BEq, Inhabited

/-- Abstract syntax tree for GA expressions, LiveScript v2 scripts, and scalar equations. -/
inductive Expr where
  | num        (val : Float)
  | color      (hex : UInt32)
  | blade      (prefixChar : Char) (sub : String)
  | ident      (name : String)
  | str        (body : String)
  | unary      (op : String) (e : Expr)
  | binary     (op : String) (lhs rhs : Expr)
  | call       (name : String) (args : Array Expr)
  | field      (obj : Expr) (name : String)
  | method     (obj : Expr) (name : String) (args : Array Expr)
  | index      (obj : Expr) (idx : Expr)
  | list       (elems : Array Expr)
  | letBind    (name : String) (val : Expr)
  | eq         (lhs rhs : Expr) -- `lhs = rhs` (equation or binding)
  | seq        (stmts : Array Expr)
  | setAlgebra (spec : String)
  | fnDef      (name : String) (params : Array String) (body : Expr)
  | lambda     (params : Array String) (body : Expr)
  | forLoop    (varName : String) (lo hi : Expr) (body : Array Expr)
  | listComp   (elem : Expr) (varName : String) (lo hi : Expr)
  | ifExpr     (cond tBranch fBranch : Expr)
  deriving Repr, Inhabited

/-! ## Lexer (with Exact Line/Column Tracking) -/

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
  [">>>", "<<", ">>", "**", "==", "!=", "<=", ">=", "=>", "->", "..", "&&", "||"]

private def singleOps : String :=
  "+-*/^&|∧∨⋅⨼⨽⋆~!⊘=,:()[]{}.<>?"

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

private def isHexChar (ch : Char) : Bool :=
  ch.isDigit || ('a' ≤ ch && ch ≤ 'f') || ('A' ≤ ch && ch ≤ 'F')

private def hexDigitVal (ch : Char) : Nat :=
  if ch.isDigit then ch.toNat - 48
  else if 'a' ≤ ch && ch ≤ 'f' then 10 + (ch.toNat - 97)
  else 10 + (ch.toNat - 65)

/-- Tokenize a LiveScript v2 / GA expression with 1-based `(line, col)` spans.
Handles ganja.js algebraic literals (`1e12`, `0.5e03`), hex colors (`0x44aaff`),
Grassmann.jl juxtaposition (`2v12`, `3(x+1)`), `@basis`, `..`, `//` / `/* */` / `#` comments. -/
def tokenizeSpanned (input : String) : Except String (Array SpannedTok) := Id.run do
  let cs := input.toList.toArray
  let n := cs.size
  let mut i := 0
  let mut line := 1
  let mut col := 1
  let mut acc : Array SpannedTok := #[]
  while i < n do
    let c := cs[i]!
    let sp : Span := { line, col }
    if c == '\n' then
      acc := acc.push { tok := .sep, span := sp }
      i := i + 1; line := line + 1; col := 1
    else if c == ';' then
      acc := acc.push { tok := .sep, span := sp }
      i := i + 1; col := col + 1
    else if c == '\r' then
      i := i + 1
    else if c.isWhitespace then
      i := i + 1; col := col + 1
    else if c == '/' && i + 1 < n && cs[i + 1]! == '/' then
      i := i + 2; col := col + 2
      while i < n && cs[i]! != '\n' do i := i + 1; col := col + 1
    else if c == '/' && i + 1 < n && cs[i + 1]! == '*' then
      i := i + 2; col := col + 2
      let mut closed := false
      while i + 1 < n do
        if cs[i]! == '*' && cs[i + 1]! == '/' then
          i := i + 2; col := col + 2; closed := true; break
        else if cs[i]! == '\n' then
          i := i + 1; line := line + 1; col := 1
        else
          i := i + 1; col := col + 1
      if !closed then
        return .error s!"Line {sp.line}, Col {sp.col}: unterminated block comment '/*'"
    else if c == '#' then
      i := i + 1; col := col + 1
      while i < n && cs[i]! != '\n' do i := i + 1; col := col + 1
    else if c == '@' then
      let start := i + 1
      let mut j := start
      while j < n && isIdentCont cs[j]! do j := j + 1
      let kw := (String.ofList ((cs.extract start j).toList)).toLower
      if kw == "basis" || kw == "algebra" then
        acc := acc.push { tok := .atBasis, span := sp }
        col := col + (j - i); i := j
      else
        return .error s!"Line {sp.line}, Col {sp.col}: unknown directive '@{kw}' (expected '@basis')"
    else if c == '"' || c == '\'' then
      let quoteCh := c
      i := i + 1; col := col + 1
      let mut buf : List Char := []
      let mut closed := false
      while i < n do
        let ch := cs[i]!
        if ch == '\\' && i + 1 < n then
          let nxt := cs[i + 1]!
          let esc := match nxt with | 'n' => '\n' | 't' => '\t' | _ => nxt
          buf := esc :: buf
          i := i + 2; col := col + 2
        else if ch == quoteCh then
          i := i + 1; col := col + 1; closed := true; break
        else if ch == '\n' then
          return .error s!"Line {sp.line}, Col {sp.col}: unterminated string literal"
        else
          buf := ch :: buf
          i := i + 1; col := col + 1
      if !closed then
        return .error s!"Line {sp.line}, Col {sp.col}: unterminated string literal"
      acc := acc.push { tok := .str (String.ofList buf.reverse), span := sp }
    else if c == '0' && i + 1 < n && (cs[i + 1]! == 'x' || cs[i + 1]! == 'X') then
      let start := i + 2
      let mut j := start
      let mut val : UInt32 := 0
      while j < n && isHexChar cs[j]! do
        val := val * 16 + (hexDigitVal cs[j]!).toUInt32
        j := j + 1
      if j == start then
        return .error s!"Line {sp.line}, Col {sp.col}: expected hex digits after '0x'"
      let raw := "0x" ++ String.ofList ((cs.extract start j).toList)
      acc := acc.push { tok := .color val raw, span := sp }
      col := col + (j - i); i := j
    else if c.isDigit || (c == '.' && i + 1 < n && cs[i + 1]!.isDigit) then
      let start := i
      while i < n && cs[i]!.isDigit do i := i + 1; col := col + 1
      -- Do NOT consume '.' if followed by another '.' (range `0..10`!)
      if i < n && cs[i]! == '.' && !(i + 1 < n && cs[i + 1]! == '.') then
        i := i + 1; col := col + 1
        while i < n && cs[i]!.isDigit do i := i + 1; col := col + 1
      -- Scientific notation `1.0e-5`, `1E3` vs ganja blade literal `1e12`, `0.5e03`
      if i < n && (cs[i]! == 'E' || cs[i]! == 'e') then
        let isUpperE := cs[i]! == 'E'
        if i + 2 < n && (cs[i + 1]! == '+' || cs[i + 1]! == '-') && cs[i + 2]!.isDigit then
          i := i + 2; col := col + 2
          while i < n && cs[i]!.isDigit do i := i + 1; col := col + 1
        else if isUpperE && i + 1 < n && cs[i + 1]!.isDigit then
          i := i + 1; col := col + 1
          while i < n && cs[i]!.isDigit do i := i + 1; col := col + 1
      let raw := String.ofList ((cs.extract start i).toList)
      let v := parseFloatLiteral raw
      acc := acc.push { tok := .num v raw, span := sp }
      -- Implicit multiplication for `1e12`, `2v1`, `2pi`, `2(x+1)`
      if i < n && (isIdentStart cs[i]! || cs[i]! == '(') then
        acc := acc.push { tok := .op "·", span := { line, col } }
    else if isIdentStart c then
      let start := i
      i := i + 1; col := col + 1
      while i < n && isIdentCont cs[i]! do i := i + 1; col := col + 1
      let name := String.ofList ((cs.extract start i).toList)
      if name == "let" || name == "var" || name == "const" then
        acc := acc.push { tok := .kw "let", span := sp }
      else if name == "fn" || name == "def" || name == "function" then
        acc := acc.push { tok := .kw "fn", span := sp }
      else if name == "for" || name == "in" || name == "if" || name == "else" ||
              name == "return" || name == "true" || name == "false" then
        acc := acc.push { tok := .kw name, span := sp }
      else
        match splitBladeIdent? name with
        | some (pfx, sub) => acc := acc.push { tok := .blade pfx sub, span := sp }
        | none            => acc := acc.push { tok := .ident name, span := sp }
    else
      -- Try longest matching multi-char operator first
      let remLen := n - i
      let matchedMulti : Option String :=
        multiOps.find? fun o =>
          let ocs := o.toList.toArray
          if ocs.size ≤ remLen then
            (Array.range ocs.size).all fun k => cs[i + k]! == ocs[k]!
          else false
      match matchedMulti with
      | some o =>
        acc := acc.push { tok := .op o, span := sp }
        i := i + o.length; col := col + o.length
      | none =>
        if singleOps.contains c then
          acc := acc.push { tok := .op (String.singleton c), span := sp }
          i := i + 1; col := col + 1
        else
          return .error s!"Line {sp.line}, Col {sp.col}: unexpected character '{c}'"
  return .ok acc

/-- Backwards-compatible token stream without spans. -/
def tokenize (input : String) : Except String (Array Tok) := do
  let stoks ← tokenizeSpanned input
  return stoks.map (·.tok)

/-! ## Recursive-Descent / Pratt Parser (with Exact `Line L, Col C` Diagnostics) -/

private structure ParseSt where
  toks : Array SpannedTok
  pos  : Nat

private def ParseSt.peekS (st : ParseSt) : Option SpannedTok := st.toks[st.pos]?
private def ParseSt.peek  (st : ParseSt) : Option Tok := st.peekS.map (·.tok)
private def ParseSt.bump  (st : ParseSt) : ParseSt := { st with pos := st.pos + 1 }

private def ParseSt.curSpan (st : ParseSt) : Span :=
  match st.peekS with
  | some s => s.span
  | none =>
    if h : 0 < st.toks.size then st.toks[st.toks.size - 1].span
    else { line := 1, col := 1 }

private def parseErr {α : Type} (st : ParseSt) (msg : String) : Except String α :=
  let sp := st.curSpan
  .error s!"Line {sp.line}, Col {sp.col}: {msg}"

private def ParseSt.skipSeps (st : ParseSt) : ParseSt :=
  let rec go (i : Nat) : Nat :=
    if h : i < st.toks.size then
      match st.toks[i].tok with
      | .sep => go (i + 1)
      | _ => i
    else i
  { st with pos := go st.pos }

private def binPrec (op : String) : Option (Nat × Bool) :=
  -- (precedence, isRightAssoc)
  match op with
  | "||"                      => some (3, false)
  | "&&"                      => some (4, false)
  | "==" | "!=" | "<" | ">" | "<=" | ">=" => some (6, false)
  | "+" | "-"                 => some (10, false)
  | ">>>" | "⊘"               => some (15, true)
  | "|"                       => some (20, false)
  | "*" | "/" | "·" | "⋅" | "⨼" | "⨽" => some (30, false)
  | "&" | "∨"                 => some (35, false)
  | "^" | "∧" | "<<" | ">>"   => some (40, false)
  | "**"                      => some (50, true)
  | _                         => none

/-- Check whether `(` starts an arrow lambda `(a, b) => body` by looking ahead safely. -/
private def tryParseLambdaParams (st : ParseSt) : Option (Array String × ParseSt) := Id.run do
  -- `st` is positioned right AFTER `(`
  let mut s := st.skipSeps
  let mut params : Array String := #[]
  if s.peek == some (.op ")") then
    let sAfter := s.bump.skipSeps
    if sAfter.peek == some (.op "=>") then return some (#[], sAfter.bump)
    else return none
  while true do
    match s.peek with
    | some (.ident p) =>
      params := params.push p
      s := s.bump.skipSeps
      match s.peek with
      | some (.op ",") => s := s.bump.skipSeps
      | some (.op ")") =>
        let sAfter := s.bump.skipSeps
        if sAfter.peek == some (.op "=>") then return some (params, sAfter.bump)
        else return none
      | _ => return none
    | _ => return none
  return none

mutual

private partial def parsePrimary (st : ParseSt) : Except String (Expr × ParseSt) := do
  match st.peek with
  | none => parseErr st "unexpected end of expression"
  | some (.num v _) => return (.num v, st.bump)
  | some (.color hex _) => return (.color hex, st.bump)
  | some (.blade p sub) => return (.blade p sub, st.bump)
  | some (.str s) => return (.str s, st.bump)
  | some (.kw "true") => return (.num 1.0, st.bump)
  | some (.kw "false") => return (.num 0.0, st.bump)
  | some (.kw "if") => parseIfExpr st.bump
  | some (.ident name) =>
    let st1 := st.bump
    match st1.peek with
    | some (.op "=>") =>
      let (body, st2) ← parseExpr 0 st1.bump.skipSeps
      return (.lambda #[name] body, st2)
    | some (.op "(") =>
      -- Special-case `Algebra(p, q, r)` header call!
      if name == "Algebra" then
        let (args, st2) ← parseArgList st1.bump ")"
        let specStr :=
          match args.toList with
          | [.num p, .num q, .num r] => s!"Cl({p.toUInt32.toNat},{q.toUInt32.toNat},{r.toUInt32.toNat})"
          | [.num p, .num q]         => s!"Cl({p.toUInt32.toNat},{q.toUInt32.toNat},0)"
          | [.str s]                 => s
          | [.ident s]               => s
          | _                        => "PGA3"
        return (.setAlgebra specStr, st2)
      else
        let (args, st2) ← parseArgList st1.bump ")"
        return (.call name args, st2)
    | _ => return (.ident name, st1)
  | some (.op "(") =>
    let stAfterOpen := st.bump
    match tryParseLambdaParams stAfterOpen with
    | some (params, stBody) =>
      let (body, st2) ← parseExpr 0 stBody.skipSeps
      return (.lambda params body, st2)
    | none =>
      let (e, st1) ← parseExpr 0 stAfterOpen.skipSeps
      let st1' := st1.skipSeps
      match st1'.peek with
      | some (.op ")") => return (e, st1'.bump)
      | _ => parseErr st1' "expected closing ')'"
  | some (.op "[") => parseListOrComp st.bump
  | some (.op "{") =>
    let (stmts, st1) ← parseBlock st.bump
    return (.seq stmts, st1)
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
  | some tok => parseErr st s!"unexpected token {repr tok}"

private partial def parseListOrComp (st : ParseSt) : Except String (Expr × ParseSt) := do
  let st0 := st.skipSeps
  if st0.peek == some (.op "]") then return (.list #[], st0.bump)
  let (first, st1) ← parseExpr 0 st0
  let st1' := st1.skipSeps
  match st1'.peek with
  | some (.kw "for") =>
    let st2 := st1'.bump.skipSeps
    match st2.peek with
    | some (.ident varName) =>
      let st3 := st2.bump.skipSeps
      if st3.peek != some (.kw "in") then
        parseErr st3 "expected 'in' after comprehension variable"
      else
        let (lo, st4) ← parseExpr 0 st3.bump.skipSeps
        let st4' := st4.skipSeps
        if st4'.peek != some (.op "..") then
          parseErr st4' "expected '..' range operator in list comprehension"
        else
          let (hi, st5) ← parseExpr 0 st4'.bump.skipSeps
          let st5' := st5.skipSeps
          if st5'.peek != some (.op "]") then
            parseErr st5' "expected ']' closing list comprehension"
          else
            return (.listComp first varName lo hi, st5'.bump)
    | _ => parseErr st2 "expected loop variable name after 'for'"
  | some (.op "]") => return (.list #[first], st1'.bump)
  | some (.op ",") =>
    let mut elems : Array Expr := #[first]
    let mut s := st1'.bump.skipSeps
    if s.peek == some (.op "]") then return (.list elems, s.bump)
    repeat
      let (e, s1) ← parseExpr 0 s.skipSeps
      elems := elems.push e
      let s2 := s1.skipSeps
      match s2.peek with
      | some (.op ",") =>
        let s3 := s2.bump.skipSeps
        if s3.peek == some (.op "]") then return (.list elems, s3.bump)
        s := s3
      | some (.op "]") => return (.list elems, s2.bump)
      | _ => return ← parseErr s2 "expected ',' or ']'"
    return (.list elems, s)
  | _ => parseErr st1' "expected ',', 'for', or ']'"

private partial def parseIfExpr (st : ParseSt) : Except String (Expr × ParseSt) := do
  let (cond, st1) ← parseExpr 0 st.skipSeps
  let st1' := st1.skipSeps
  let (tBranch, st2) ←
    if st1'.peek == some (.op "{") then
      let (bs, s) ← parseBlock st1'.bump
      pure (.seq bs, s)
    else parseExpr 0 st1'
  let st2' := st2.skipSeps
  if st2'.peek == some (.kw "else") then
    let st3 := st2'.bump.skipSeps
    let (fBranch, st4) ←
      if st3.peek == some (.op "{") then
        let (bs, s) ← parseBlock st3.bump
        pure (.seq bs, s)
      else parseExpr 0 st3
    return (.ifExpr cond tBranch fBranch, st4)
  else
    return (.ifExpr cond tBranch (.num 0.0), st2')

private partial def parseBlock (st : ParseSt) : Except String (Array Expr × ParseSt) := do
  let mut s := st.skipSeps
  let mut out : Array Expr := #[]
  while s.peek != some (.op "}") do
    if s.peek.isNone then
      return ← parseErr s "unterminated '{' block (expected '}')"
    let (stmt, s1) ← parseStmt s
    out := out.push stmt
    s := s1.skipSeps
  return (out, s.bump)

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
    | _ => parseErr st1 "expected field/method name after '.'"
  | some (.op "[") =>
    let (idx, st1) ← parseExpr 0 st.bump.skipSeps
    let st1' := st1.skipSeps
    if st1'.peek != some (.op "]") then
      parseErr st1' "expected ']' after index expression"
    else
      parsePostfix (.index lhs idx) st1'.bump
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
    | some (.op ",") =>
      let st3 := st2.bump.skipSeps
      if st3.peek == some (.op closeSym) then return (out, st3.bump)
      st := st3
    | some (.op s) =>
      if s == closeSym then return (out, st2.bump)
      else return ← parseErr st2 s!"expected ',' or '{closeSym}'"
    | _ => return ← parseErr st2 s!"expected ',' or '{closeSym}'"
  return (out, st)

private partial def parseBinExpr (minPrec : Nat) (st : ParseSt) :
    Except String (Expr × ParseSt) := do
  let (lhs0, st0) ← parseUnary st
  let rec loop (lhs : Expr) (st : ParseSt) : Except String (Expr × ParseSt) := do
    match st.peek with
    | some (.op sym) =>
      match binPrec sym with
      | some (prec, isRight) =>
        if prec < minPrec then return (lhs, st)
        let nextMin := if isRight then prec else prec + 1
        let (rhs, st1) ← parseBinExpr nextMin st.bump
        loop (.binary sym lhs rhs) st1
      | none => return (lhs, st)
    | _ => return (lhs, st)
  loop lhs0 st0

private partial def parseExpr (minPrec : Nat) (st : ParseSt) :
    Except String (Expr × ParseSt) := do
  let (lhs, st1) ← parseBinExpr minPrec st
  if minPrec == 0 && st1.peek == some (.op "?") then
    let (tBranch, st2) ← parseExpr 0 st1.bump.skipSeps
    let st2' := st2.skipSeps
    if st2'.peek != some (.op ":") then
      parseErr st2' "expected ':' in ternary expression 'cond ? a : b'"
    else
      let (fBranch, st3) ← parseExpr 0 st2'.bump.skipSeps
      return (.ifExpr lhs tBranch fBranch, st3)
  else
    return (lhs, st1)

private partial def parseIdentParams (st : ParseSt) : Except String (Array String × ParseSt) := do
  let mut s := st.skipSeps
  let mut params : Array String := #[]
  if s.peek == some (.op ")") then return (params, s.bump)
  repeat
    match s.peek with
    | some (.ident p) =>
      params := params.push p
      let s1 := s.bump.skipSeps
      match s1.peek with
      | some (.op ",") => s := s1.bump.skipSeps
      | some (.op ")") => return (params, s1.bump)
      | _ => return ← parseErr s1 "expected ',' or ')' in parameter list"
    | _ => return ← parseErr s "expected parameter identifier"
  return (params, s)

private partial def parseStmt (st : ParseSt) : Except String (Expr × ParseSt) := do
  let st := st.skipSeps
  match st.peek with
  | some .atBasis =>
    let st1 := st.bump
    match st1.peek with
    | some (.ident alg) =>
      let st2 := st1.bump
      -- Handle `@basis Cl(3,0,1)`
      if st2.peek == some (.op "(") then
        let (args, st3) ← parseArgList st2.bump ")"
        let spec :=
          match args.toList with
          | [.num p, .num q, .num r] => s!"Cl({p.toUInt32.toNat},{q.toUInt32.toNat},{r.toUInt32.toNat})"
          | [.num p, .num q]         => s!"Cl({p.toUInt32.toNat},{q.toUInt32.toNat},0)"
          | _                        => alg
        return (.setAlgebra spec, st3)
      else
        return (.setAlgebra alg, st2)
    | some (.str alg) => return (.setAlgebra alg, st1.bump)
    | _ => parseErr st1 "expected algebra name after '@basis' (e.g. PGA3, CGA3, STA, Cl(3,0,1))"
  | some (.kw "fn") =>
    let st1 := st.bump
    match st1.peek with
    | some (.ident fname) =>
      let st2 := st1.bump
      if st2.peek != some (.op "(") then
        parseErr st2 s!"expected '(' after fn {fname}"
      else
        let (params, st3) ← parseIdentParams st2.bump
        let st3' := st3.skipSeps
        if st3'.peek == some (.op "=") then
          let (body, st4) ← parseExpr 0 st3'.bump.skipSeps
          return (.fnDef fname params body, st4)
        else if st3'.peek == some (.op "{") then
          let (stmts, st4) ← parseBlock st3'.bump
          return (.fnDef fname params (.seq stmts), st4)
        else
          parseErr st3' s!"expected '=' or '\{' in definition of fn {fname}"
    | _ => parseErr st1 "expected function name after 'fn'"
  | some (.kw "for") =>
    let st1 := st.bump
    match st1.peek with
    | some (.ident varName) =>
      let st2 := st1.bump
      if st2.peek != some (.kw "in") then
        parseErr st2 s!"expected 'in' after 'for {varName}'"
      else
        let (lo, st3) ← parseExpr 0 st2.bump
        if st3.peek != some (.op "..") then
          parseErr st3 "expected '..' range in for-loop (e.g. for i in 0..10 { ... })"
        else
          let (hi, st4) ← parseExpr 0 st3.bump
          let st4' := st4.skipSeps
          if st4'.peek != some (.op "{") then
            parseErr st4' "expected '{' for loop body"
          else
            let (body, st5) ← parseBlock st4'.bump
            return (.forLoop varName lo hi body, st5)
    | _ => parseErr st1 "expected loop variable identifier after 'for'"
  | some (.kw "return") =>
    parseExpr 0 st.bump
  | some (.kw "let") =>
    let st1 := st.bump
    match st1.peek with
    | some (.ident name) =>
      let st2 := st1.bump
      if st2.peek != some (.op "=") then parseErr st2 s!"expected '=' after let {name}"
      else
        let (rhs, st3) ← parseExpr 0 st2.bump.skipSeps
        return (.letBind name rhs, st3)
    | _ => parseErr st1 "expected identifier after 'let'"
  | _ =>
    let (lhs, st1) ← parseExpr 0 st
    if st1.peek == some (.op "=") then
      let (rhs, st2) ← parseExpr 0 st1.bump.skipSeps
      match lhs with
      | .ident name => return (.eq (.ident name) rhs, st2)
      | _ => return (.eq lhs rhs, st2)
    else
      return (lhs, st1)

end

/-- Parse a single expression or equation (e.g. `sin(x*2+t)*cos(y*2)` or `x^2 + y^2 = 1`). -/
def parseExprString (input : String) : Except String Expr := do
  let toks ← tokenizeSpanned input
  let (e, st) ← parseStmt { toks, pos := 0 }
  let st := st.skipSeps
  if st.pos < st.toks.size then
    parseErr st s!"unexpected trailing token {repr st.peek}"
  else
    return e

/-- Parse a multi-statement CoffeeShop LiveScript v2 script. -/
def parseScript (input : String) : Except String (Array Expr) := do
  let toks ← tokenizeSpanned input
  let mut st : ParseSt := ({ toks, pos := 0 } : ParseSt).skipSeps
  let mut stmts : Array Expr := #[]
  while st.pos < st.toks.size do
    let (s, st1) ← parseStmt st
    stmts := stmts.push s
    st := st1.skipSeps
  return stmts

end Grassmann.Eval

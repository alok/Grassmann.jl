import Lean.Data.Json
import JuliaBase.Float
import Wilkinson.BigFloat

/-!
# Julia expressions

Wilkinson and SyntaxTree operate on Julia `Expr` trees: `:call` nodes whose
first argument is an operator symbol, with `Symbol` and numeric-literal leaves.
`JExpr` is that fragment. Two facts about Julia's trees matter for the
expression value `exprval` and must be reproduced exactly:

* the parser flattens `a + b + c` and `a * b * c` into single n-ary calls,
  while `a - b - c` nests (and parenthesised sums do not flatten);
* `2x` is `*(2, x)`, `-2` is a literal, `-x` is the call `-(x)`, and
  `1//2` is the call `//(1, 2)`.

`jl⟪ … ⟫` quotes Julia syntax into a `JExpr` with those rules, and
`JExpr.toJulia` prints exactly as Julia's `string(::Expr)` does
(`base/show.jl`, `show_unquoted`/`show_list`: precedence-based parentheses,
juxtaposed `2x`, unary minus rules).
-/

namespace Wilkinson

open JuliaBase

/-- Numeric literal types that occur in Wilkinson's expressions (after
`SyntaxTree.sub` converts them). -/
inductive Lit where
  /-- Julia `Int64` literal. -/
  | int (v : Int)
  /-- `Float64` literal. -/
  | f64 (v : Float)
  /-- `Float32` literal. -/
  | f32 (v : Float32)
  /-- `BigFloat` literal (after `sub(BigFloat, …)`). -/
  | big (v : Big)
  deriving Inhabited, BEq

/-- Julia `Expr` fragment: symbols, literals and operator calls. -/
inductive JExpr where
  /-- A `Symbol` leaf (`:x`, `:ϵ`). -/
  | sym (name : String)
  /-- A numeric literal. -/
  | lit (v : Lit)
  /-- `Expr(:call, op, args...)`. -/
  | call (op : String) (args : List JExpr)
  deriving Inhabited, BEq

/-- `show` of a literal. `BigFloat` prints its `Float64` rounding (Julia would
print all significant digits). -/
def Lit.toJulia : Lit → String
  | .int v => toString v
  | .f64 v => F64.showString v
  | .f32 v => F32.showString v
  | .big v => F64.showString v.toFloat

/-- Negative literal test (`item isa Real && item < 0`). -/
def Lit.isNeg : Lit → Bool
  | .int v => v < 0
  | .f64 v => v < 0
  | .f32 v => v < 0
  | .big v => v.isNeg

namespace JExpr

/-- Integer literal. -/
def int (n : Int) : JExpr := .lit (.int n)
/-- `Float64` literal. -/
def f64 (x : Float) : JExpr := .lit (.f64 x)

/-! ## Printing (Julia `string(::Expr)`) -/

/-- Julia `Base.operator_precedence` for the operators Wilkinson uses. -/
def prec : String → Nat
  | "+" | "-" => 11
  | "*" | "/" | "\\" => 12
  | "//" => 13
  | "^" => 15
  | _ => 0

/-- Julia's `uni_ops` restricted to arithmetic. -/
def isUnaryOp (op : String) : Bool := op == "+" || op == "-"

/-- Julia's `show_unquoted(io, ex, indent, prec)` for this fragment. -/
partial def render (e : JExpr) (ctx : Int) : String :=
  match e with
  | .sym s => s
  | .lit l => l.toJulia
  | .call op args =>
    let fp : Int := prec op
    match op, args with
    -- scalar multiplication "2x"
    | "*", [.lit l, .sym s] =>
      if (match l with | .int _ | .f64 _ | .f32 _ => true | .big _ => false) &&
         !(s.startsWith "e" || s.startsWith "E" || s.startsWith "f") then
        let body := showList [.lit l, .sym s] "" fp
        if fp ≤ ctx then "(" ++ body ++ ")" else body
      else binary op args fp ctx
    | _, [a] =>
      if isUnaryOp op then
        match a with
        | .call .. => op ++ "(" ++ showList [a] ", " fp ++ ")"
        | _ => op ++ render a fp
      else if fp > 0 then "(" ++ op ++ ")(" ++ showList args ", " 0 ++ ")"
      else op ++ "(" ++ showList args ", " 0 ++ ")"
    | _, _ => binary op args fp ctx
where
  /-- Julia `show_list`: the first item is parenthesised in a `^` context when it
  is a unary call or a negative literal. -/
  showList (items : List JExpr) (sep : String) (p : Int) : String :=
    sep.intercalate <| items.zipIdx.map fun (item, i) =>
      let parens := i == 0 && p ≥ 15 &&
        (match item with
         | .call o [_] => isUnaryOp o
         | .lit l => l.isNeg
         | _ => false)
      if parens then "(" ++ render item 0 ++ ")" else render item p
  /-- Binary (or n-ary `+`/`*`) operator call. -/
  binary (op : String) (args : List JExpr) (fp ctx : Int) : String :=
    if fp > 0 && (args.length == 2 || (args.length > 2 && (op == "+" || op == "*"))) then
      let body := showList args s!" {op} " fp
      if fp ≤ ctx then "(" ++ body ++ ")" else body
    else op ++ "(" ++ showList args ", " 0 ++ ")"

/-- Julia `string(ex)`. -/
def toJulia (e : JExpr) : String := render e (-1)

instance : ToString JExpr := ⟨toJulia⟩

/-! ## JSON codec (the golden files' encoding of Julia `Expr`s) -/

open Lean in
/-- Decode `{"sym": s}`, `{"int": "n"}`, `{"f64": "repr"}`, `{"call": op, "args": [...]}`. -/
partial def ofJson (j : Json) : Except String JExpr := do
  match j.getObjVal? "sym" with
  | .ok (.str s) => return .sym s
  | _ =>
  match j.getObjVal? "int" with
  | .ok (.str s) => match s.toInt? with
    | some n => return .int n
    | none => throw s!"bad int {s}"
  | _ =>
  match j.getObjVal? "f64" with
  | .ok (.str s) =>
    match Json.parse s with
    | .ok (.num n) => return .f64 (if s.startsWith "-0.0" && n.mantissa == 0 then -0.0 else n.toFloat)
    | _ => throw s!"bad float {s}"
  | _ =>
  let op ← j.getObjValAs? String "call"
  let args ← j.getObjValAs? (Array Json) "args"
  return .call op (← args.toList.mapM ofJson)

/-! ## Structure -/

/-- Number of nodes (for fuel). -/
def size : JExpr → Nat
  | .call _ args => 1 + sizeList args
  | _ => 1
where
  /-- Sum over a list. -/
  sizeList : List JExpr → Nat
    | [] => 0
    | a :: as => size a + sizeList as

end JExpr

/-! ## `jl⟪ … ⟫`: Julia expression quotation -/

/-- Julia expression syntax. -/
declare_syntax_cat jexpr

syntax num : jexpr
syntax scientific : jexpr
/-- A negative literal (`x^-2`, `x - -2`). -/
syntax:max (name := jexprNegNum) "-" noWs num : jexpr
/-- A negative float literal. -/
syntax:max (name := jexprNegSci) "-" noWs scientific : jexpr
syntax ident : jexpr
syntax "(" jexpr ")" : jexpr
syntax:65 jexpr:65 " + " jexpr:66 : jexpr
syntax:65 jexpr:65 " - " jexpr:66 : jexpr
syntax:70 jexpr:70 " * " jexpr:71 : jexpr
syntax:70 jexpr:70 " / " jexpr:71 : jexpr
syntax:72 jexpr:72 " // " jexpr:73 : jexpr
syntax:75 jexpr:76 " ^ " jexpr:75 : jexpr
syntax:73 "-" jexpr:75 : jexpr
/-- Juxtaposition `2x`, `2x^2`, `2(x+1)`: binds looser than `^`, tighter than `*`. -/
syntax:74 num noWs jexpr:75 : jexpr
/-- Juxtaposition with a float coefficient. -/
syntax:74 scientific noWs jexpr:75 : jexpr
/-- Negative-literal juxtaposition `-2x` (Julia reads `-2` as one literal). -/
syntax:74 "-" noWs num noWs jexpr:75 : jexpr
/-- Negative float juxtaposition `-1.5x`. -/
syntax:74 "-" noWs scientific noWs jexpr:75 : jexpr

/-- `jl⟪ x^9 - 2 ⟫ : JExpr`, parsed with Julia's flattening rules. -/
syntax "jl⟪" jexpr "⟫" : term

open Lean

mutual

/-- Translate Julia syntax to a `JExpr` term. Unparenthesised `+`/`*` chains
flatten into one n-ary call, as Julia's parser does. -/
partial def jexprToTerm (stx : TSyntax `jexpr) : MacroM (TSyntax `term) :=
  if stx.raw.isOfKind choiceKind then
    -- `-2` parses both as a literal and as unary minus: Julia reads a literal
    let alts := stx.raw.getArgs
    match alts.find? (fun a => a.getKind == ``jexprNegNum || a.getKind == ``jexprNegSci) with
    | some a => jexprToTerm ⟨a⟩
    | none => jexprToTerm ⟨alts[0]!⟩
  else if stx.raw.getKind == ``jexprNegNum then
    let n : TSyntax `num := ⟨stx.raw[1]⟩
    `(JExpr.int (-$n))
  else if stx.raw.getKind == ``jexprNegSci then
    let s : TSyntax `scientific := ⟨stx.raw[1]⟩
    `(JExpr.f64 (-$s))
  else jexprToTerm' stx

/-- The generic syntax kinds. -/
partial def jexprToTerm' : TSyntax `jexpr → MacroM (TSyntax `term)
  | `(jexpr| $n:num) => `(JExpr.int $n)
  | `(jexpr| $s:scientific) => `(JExpr.f64 $s)
  | `(jexpr| $x:ident) => `(JExpr.sym $(quote x.getId.toString))
  | `(jexpr| ($e)) => jexprToTerm e
  | `(jexpr| $n:num$e:jexpr) => do `(JExpr.call "*" [JExpr.int $n, $(← jexprToTerm e)])
  | `(jexpr| $s:scientific$e:jexpr) => do `(JExpr.call "*" [JExpr.f64 $s, $(← jexprToTerm e)])
  | `(jexpr| -$n:num$e:jexpr) => do `(JExpr.call "*" [JExpr.int (-$n), $(← jexprToTerm e)])
  | `(jexpr| -$s:scientific$e:jexpr) => do `(JExpr.call "*" [JExpr.f64 (-$s), $(← jexprToTerm e)])
  | `(jexpr| - $e) => do `(JExpr.call "-" [$(← jexprToTerm e)])
  | `(jexpr| $a + $b) => do jexprNary "+" (← jexprFlatten "+" a) b
  | `(jexpr| $a * $b) => do jexprNary "*" (← jexprFlatten "*" a) b
  | `(jexpr| $a - $b) => do `(JExpr.call "-" [$(← jexprToTerm a), $(← jexprToTerm b)])
  | `(jexpr| $a / $b) => do `(JExpr.call "/" [$(← jexprToTerm a), $(← jexprToTerm b)])
  | `(jexpr| $a // $b) => do `(JExpr.call "//" [$(← jexprToTerm a), $(← jexprToTerm b)])
  | `(jexpr| $a ^ $b) => do `(JExpr.call "^" [$(← jexprToTerm a), $(← jexprToTerm b)])
  | _ => Macro.throwUnsupported

/-- Operands of an unparenthesised chain of `op`. -/
partial def jexprFlatten (op : String) (e : TSyntax `jexpr) : MacroM (Array (TSyntax `term)) := do
  if op == "+" then
    if let `(jexpr| $a + $b) := e then return (← jexprFlatten op a).push (← jexprToTerm b)
  if op == "*" then
    if let `(jexpr| $a * $b) := e then return (← jexprFlatten op a).push (← jexprToTerm b)
  return #[← jexprToTerm e]

/-- Build an n-ary call from a flattened chain and its last operand. -/
partial def jexprNary (op : String) (init : Array (TSyntax `term)) (b : TSyntax `jexpr) :
    MacroM (TSyntax `term) := do
  let args := init.push (← jexprToTerm b)
  `(JExpr.call $(quote op) [$args,*])

end

macro_rules
  | `(jl⟪ $e ⟫) => jexprToTerm e

end Wilkinson

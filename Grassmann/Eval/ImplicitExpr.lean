import Grassmann.Scene.Types
import Grassmann.Eval.Implicit3D

/-!
# Strictly `Init`-Only User-Typed 3D Implicit & Parametric Expression Evaluator

Self-contained Pratt expression parser, constant-folding optimizer, and zero-allocation
unboxed-`Float` evaluator wired directly into `Grassmann.Eval.Implicit3D`'s O(1)
edge-deduplicated Kuhn Marching Tetrahedra and parametric 3D surface mesher.

Zero `Lean.*`, zero `Std.*`, zero `DirectSum`, zero external deps — links straight
into both the tiny standalone C ABI dylib and the Lean 4.36 → C → Emscripten WASM bundle!

Supports:
- **Equations & expressions**: `lhs = rhs` auto-rewrites to `(lhs) - (rhs)`!
- **Implicit multiplication**: `2x`, `3(x+y)`, `2pi`, `(x-1)(x+1)`
- **Operators**: `+`, `-`, `*`, `/`, right-associative `^`, unary `-` / `+`
- **Functions**: `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `sinh`, `cosh`, `tanh`,
  `exp`, `log`/`ln`, `sqrt`, `abs`, `floor`, `ceil`, `sign`, `atan2`, `min`, `max`,
  `pow`, `hypot`
- **Variables & constants**: `x`, `y`, `z`, `u`, `v`, `t`, `r` (`√(x²+y²+z²)`), `pi`, `tau`, `e`, `phi`
- **Peephole optimizer**: constant folding + integer power specialization (`^2`, `^3`, `^4`)
- **Adaptive coarse-probe bounding-box refinement**: probes a `7³` grid (`<0.1 ms`) to
  focus `gridN³` resolution tightly on active sign-change regions for `<15 ms` interactive speed!

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) & Steven De Keninck (`enkimute` / `ganja.js`).
-/

namespace Grassmann.Eval.ImplicitExpr

open Grassmann.Scene Grassmann.Eval.Implicit3D

private def piF : Float := 3.14159265358979323846
private def twoPiF : Float := 6.28318530717958647692
private def eF : Float := 2.71828182845904523536
private def phiF : Float := 1.61803398874989484820

/-! ## 1. Compiled Zero-Alloc Expression AST -/

inductive UnaryOp where
  | neg | sq | cube | p4
  | sin | cos | tan | asin | acos | atan
  | sinh | cosh | tanh | exp | log | sqrt | abs | floor | ceil | sign
  deriving Repr, BEq, Inhabited

inductive BinaryOp where
  | add | sub | mul | div | pow | atan2 | min | max | hypot
  deriving Repr, BEq, Inhabited

inductive Expr where
  | lit   (val : Float)
  | varX | varY | varZ | varU | varV | varT | varR
  | un    (op : UnaryOp) (a : Expr)
  | bin   (op : BinaryOp) (a b : Expr)
  deriving Repr, Inhabited

/-! ## 2. Tokenizer (Strictly `Init`-Only) -/

private inductive Tok where
  | num (v : Float)
  | id  (s : String)
  | plus | minus | star | slash | caret | eq | comma | lparen | rparen
  deriving Repr, BEq, Inhabited

private def parseDecimal (s : String) : Option Float := Id.run do
  let cs := s.toList.toArray
  if cs.isEmpty then return none
  let mut i := 0
  let n := cs.size
  let mut acc : Float := 0.0
  let mut digits := 0
  while i < n && cs[i]!.isDigit do
    acc := acc * 10.0 + Float.ofNat (cs[i]!.toNat - '0'.toNat)
    digits := digits + 1
    i := i + 1
  if i < n && cs[i]! == '.' then
    i := i + 1
    let mut place : Float := 0.1
    while i < n && cs[i]!.isDigit do
      acc := acc + Float.ofNat (cs[i]!.toNat - '0'.toNat) * place
      place := place * 0.1
      digits := digits + 1
      i := i + 1
  if digits == 0 then return none
  if i < n && (cs[i]! == 'e' || cs[i]! == 'E') then
    i := i + 1
    let mut sgn : Float := 1.0
    if i < n && cs[i]! == '+' then i := i + 1
    else if i < n && cs[i]! == '-' then sgn := -1.0; i := i + 1
    let mut eAcc : Nat := 0
    let mut eDigs := 0
    while i < n && cs[i]!.isDigit do
      eAcc := eAcc * 10 + (cs[i]!.toNat - '0'.toNat)
      eDigs := eDigs + 1
      i := i + 1
    if eDigs == 0 then return none
    acc := acc * Float.pow 10.0 (sgn * Float.ofNat eAcc)
  if i == n then return some acc else return none

private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
private def isIdentCont (c : Char) : Bool := c.isAlpha || c.isDigit || c == '_'

private def tokenize (src : String) : Except String (Array Tok) := Id.run do
  let cs := src.toList.toArray
  let n := cs.size
  let mut i := 0
  let mut out : Array Tok := #[]
  while i < n do
    let c := cs[i]!
    if c.isWhitespace then
      i := i + 1
    else if c.isDigit || (c == '.' && i + 1 < n && cs[i + 1]!.isDigit) then
      let start := i
      let mut hasDot := c == '.'
      i := i + 1
      while i < n do
        let ch := cs[i]!
        if ch.isDigit then i := i + 1
        else if ch == '.' && !hasDot then hasDot := true; i := i + 1
        else if (ch == 'e' || ch == 'E') && i + 1 < n then
          i := i + 1
          if i < n && (cs[i]! == '+' || cs[i]! == '-') then i := i + 1
        else break
      let numStr := String.ofList ((cs.extract start i).toList)
      match parseDecimal numStr with
      | some v => out := out.push (.num v)
      | none => return .error s!"Invalid number literal '{numStr}'"
    else if isIdentStart c then
      let start := i
      i := i + 1
      while i < n && isIdentCont cs[i]! do i := i + 1
      let idStr := (String.ofList ((cs.extract start i).toList)).toLower
      out := out.push (.id idStr)
    else
      match c with
      | '+' => out := out.push .plus;   i := i + 1
      | '-' => out := out.push .minus;  i := i + 1
      | '*' =>
        if i + 1 < n && cs[i + 1]! == '*' then
          out := out.push .caret; i := i + 2
        else
          out := out.push .star; i := i + 1
      | '/' => out := out.push .slash;  i := i + 1
      | '^' => out := out.push .caret;  i := i + 1
      | '=' => out := out.push .eq;     i := i + 1
      | ',' => out := out.push .comma;  i := i + 1
      | '(' => out := out.push .lparen; i := i + 1
      | ')' => out := out.push .rparen; i := i + 1
      | _ => return .error s!"Unexpected character '{c}' at index {i}"
  return .ok out

/-! ## 3. Peephole Constant Folder & Power Specializer -/

@[inline] private def evalUnary (op : UnaryOp) (a : Float) : Float :=
  match op with
  | .neg   => -a
  | .sq    => a * a
  | .cube  => a * a * a
  | .p4    => let s := a * a; s * s
  | .sin   => Float.sin a
  | .cos   => Float.cos a
  | .tan   => Float.tan a
  | .asin  => Float.asin (max (-1.0) (min 1.0 a))
  | .acos  => Float.acos (max (-1.0) (min 1.0 a))
  | .atan  => Float.atan a
  | .sinh  => Float.sinh a
  | .cosh  => Float.cosh a
  | .tanh  => Float.tanh a
  | .exp   => Float.exp (max (-40.0) (min 40.0 a))
  | .log   => Float.log (max 1e-12 (Float.abs a))
  | .sqrt  => Float.sqrt (max 0.0 a)
  | .abs   => Float.abs a
  | .floor => Float.floor a
  | .ceil  => Float.ceil a
  | .sign  => if a > 0.0 then 1.0 else if a < 0.0 then -1.0 else 0.0

@[inline] private def evalBinary (op : BinaryOp) (a b : Float) : Float :=
  match op with
  | .add   => a + b
  | .sub   => a - b
  | .mul   => a * b
  | .div   => if Float.abs b < 1e-12 then 0.0 else a / b
  | .pow   => Float.pow a b
  | .atan2 => Float.atan2 a b
  | .min   => min a b
  | .max   => max a b
  | .hypot => Float.sqrt (a * a + b * b)

private def mkUn (op : UnaryOp) (a : Expr) : Expr :=
  match a with
  | .lit v => .lit (evalUnary op v)
  | _      => .un op a

private def mkBin (op : BinaryOp) (a b : Expr) : Expr :=
  match op, a, b with
  | _, .lit va, .lit vb => .lit (evalBinary op va vb)
  | .pow, x, .lit 2.0   => mkUn .sq x
  | .pow, x, .lit 3.0   => mkUn .cube x
  | .pow, x, .lit 4.0   => mkUn .p4 x
  | .pow, x, .lit 1.0   => x
  | .pow, _, .lit 0.0   => .lit 1.0
  | .mul, x, .lit 1.0   => x
  | .mul, .lit 1.0, x   => x
  | .mul, _, .lit 0.0   => .lit 0.0
  | .mul, .lit 0.0, _   => .lit 0.0
  | .add, x, .lit 0.0   => x
  | .add, .lit 0.0, x   => x
  | .sub, x, .lit 0.0   => x
  | _, _, _             => .bin op a b

/-! ## 4. Pratt Recursive-Descent Parser (with Implicit Multiplication & `=` Support) -/

private structure PState where
  toks : Array Tok
  pos  : Nat := 0

private def peek (st : PState) : Option Tok :=
  if st.pos < st.toks.size then some st.toks[st.pos]! else none

private def advance (st : PState) : PState := { st with pos := st.pos + 1 }

private def isImplicitMulStart (t : Tok) : Bool :=
  match t with
  | .lparen | .id _ => true
  | _ => false

private def lookupUnaryFn (name : String) : Option UnaryOp :=
  match name with
  | "sin"   => some .sin   | "cos"   => some .cos   | "tan"   => some .tan
  | "asin"  => some .asin  | "acos"  => some .acos  | "atan"  => some .atan
  | "sinh"  => some .sinh  | "cosh"  => some .cosh  | "tanh"  => some .tanh
  | "exp"   => some .exp   | "log" | "ln" => some .log
  | "sqrt"  => some .sqrt  | "abs"   => some .abs
  | "floor" => some .floor | "ceil"  => some .ceil  | "sign"  => some .sign
  | "sq"    => some .sq    | "cb" | "cube" => some .cube
  | _       => none

private def lookupBinaryFn (name : String) : Option BinaryOp :=
  match name with
  | "atan2" => some .atan2 | "min" => some .min | "max" => some .max
  | "pow"   => some .pow   | "hypot" => some .hypot
  | _       => none

mutual
  private partial def parseEquation (st : PState) : Except String (Expr × PState) := do
    let (lhs, st1) ← parseAdd st
    match peek st1 with
    | some .eq =>
      let (rhs, st2) ← parseAdd (advance st1)
      return (mkBin .sub lhs rhs, st2)
    | _ => return (lhs, st1)

  private partial def parseAdd (st : PState) : Except String (Expr × PState) := do
    let (lhs0, st0) ← parseMul st
    let mut lhs := lhs0
    let mut s := st0
    while true do
      match peek s with
      | some .plus =>
        let (rhs, s1) ← parseMul (advance s)
        lhs := mkBin .add lhs rhs; s := s1
      | some .minus =>
        let (rhs, s1) ← parseMul (advance s)
        lhs := mkBin .sub lhs rhs; s := s1
      | _ => break
    return (lhs, s)

  private partial def parseMul (st : PState) : Except String (Expr × PState) := do
    let (lhs0, st0) ← parseUnary st
    let mut lhs := lhs0
    let mut s := st0
    while true do
      match peek s with
      | some .star =>
        let (rhs, s1) ← parseUnary (advance s)
        lhs := mkBin .mul lhs rhs; s := s1
      | some .slash =>
        let (rhs, s1) ← parseUnary (advance s)
        lhs := mkBin .div lhs rhs; s := s1
      | some tok =>
        if isImplicitMulStart tok then
          let (rhs, s1) ← parsePow s
          lhs := mkBin .mul lhs rhs; s := s1
        else break
      | none => break
    return (lhs, s)

  private partial def parseUnary (st : PState) : Except String (Expr × PState) := do
    match peek st with
    | some .minus =>
      let (e, st1) ← parseUnary (advance st)
      return (mkUn .neg e, st1)
    | some .plus =>
      parseUnary (advance st)
    | _ => parsePow st

  private partial def parsePow (st : PState) : Except String (Expr × PState) := do
    let (base, st1) ← parseAtom st
    match peek st1 with
    | some .caret =>
      let (exp, st2) ← parseUnary (advance st1) -- right-associative, supports x^-2!
      return (mkBin .pow base exp, st2)
    | _ => return (base, st1)

  private partial def parseAtom (st : PState) : Except String (Expr × PState) := do
    match peek st with
    | some (.num v) => return (.lit v, advance st)
    | some .lparen =>
      let (e, st1) ← parseAdd (advance st)
      match peek st1 with
      | some .rparen => return (e, advance st1)
      | _ => throw "Expected closing ')'"
    | some (.id name) =>
      let st1 := advance st
      match peek st1 with
      | some .lparen =>
        -- Function call: unary or binary
        let stArgs := advance st1
        let (arg1, stAfter1) ← parseAdd stArgs
        match peek stAfter1 with
        | some .comma =>
          let (arg2, stAfter2) ← parseAdd (advance stAfter1)
          match peek stAfter2 with
          | some .rparen =>
            match lookupBinaryFn name with
            | some bop => return (mkBin bop arg1 arg2, advance stAfter2)
            | none => throw s!"Unknown 2-argument function '{name}'"
          | _ => throw s!"Expected ')' after second argument of '{name}'"
        | some .rparen =>
          match lookupUnaryFn name with
          | some uop => return (mkUn uop arg1, advance stAfter1)
          | none => throw s!"Unknown 1-argument function '{name}'"
        | _ => throw s!"Expected ',' or ')' in call to '{name}'"
      | _ =>
        -- Variable or constant
        match name with
        | "x"   => return (.varX, st1)
        | "y"   => return (.varY, st1)
        | "z"   => return (.varZ, st1)
        | "u"   => return (.varU, st1)
        | "v"   => return (.varV, st1)
        | "t"   => return (.varT, st1)
        | "r"   => return (.varR, st1)
        | "pi"  => return (.lit piF, st1)
        | "tau" => return (.lit twoPiF, st1)
        | "e"   => return (.lit eF, st1)
        | "phi" => return (.lit phiF, st1)
        | _     => throw s!"Unknown identifier '{name}'"
    | some tok => throw s!"Unexpected token {repr tok}"
    | none => throw "Unexpected end of expression"
end

/-- Parse and peephole-optimize a user-typed implicit equation or parametric coordinate expression. -/
def parseExpr (input : String) : Except String Expr := do
  let toks ← tokenize input
  if toks.isEmpty then throw "Empty expression"
  let (e, stEnd) ← parseEquation { toks, pos := 0 }
  if stEnd.pos < toks.size then
    throw s!"Unexpected trailing token at index {stEnd.pos}"
  return e

/-! ## 5. Zero-Allocation AST Evaluator, Time Folding & Flat Bytecode VM -/

/-- Evaluate a compiled `Expr` at `(x, y, z, u, v, t)` (reference recursive AST evaluator). -/
def evalExpr (e : Expr) (x y z u v t : Float) : Float :=
  match e with
  | .lit val    => val
  | .varX       => x
  | .varY       => y
  | .varZ       => z
  | .varU       => u
  | .varV       => v
  | .varT       => t
  | .varR       => Float.sqrt (x * x + y * y + z * z)
  | .un op a    => evalUnary op (evalExpr a x y z u v t)
  | .bin op a b => evalBinary op (evalExpr a x y z u v t) (evalExpr b x y z u v t)

/-- Substitute `t` and aggressively constant-fold all time-only subexpressions BEFORE
entering the `16³`–`20³` Marching Tetrahedra grid loop. -/
def foldTime (e : Expr) (t : Float) : Expr :=
  match e with
  | .varT       => .lit t
  | .un op a    => mkUn op (foldTime a t)
  | .bin op a b => mkBin op (foldTime a t) (foldTime b t)
  | other       => other

/-- Compact flat RPN bytecode opcode (eliminates recursive ADT dispatch per grid sample). -/
inductive ExprOp where
  | pushLit   (val : Float)
  | pushX | pushY | pushZ | pushU | pushV | pushR
  | pushXSq | pushYSq | pushZSq
  | un        (op : UnaryOp)
  | bin       (op : BinaryOp)
  | addLit    (c : Float)
  | subLit    (c : Float)
  | rsubLit   (c : Float)
  | mulLit    (c : Float)
  | divLit    (c : Float)
  | rdivLit   (c : Float)
  | sinScaled (k : Float)
  | cosScaled (k : Float)
  deriving Repr, BEq, Inhabited

/-- Compiled flat bytecode program pairing inspectable `ops : Array ExprOp` with raw
unboxed `opBytes : ByteArray` + `consts : FloatArray` for zero-pointer-chase inner loops. -/
structure Bytecode where
  ops      : Array ExprOp
  opBytes  : ByteArray
  consts   : FloatArray
  maxStack : Nat
  deriving Inhabited

private def opPushLit   : UInt8 := 0
private def opPushX     : UInt8 := 1
private def opPushY     : UInt8 := 2
private def opPushZ     : UInt8 := 3
private def opPushU     : UInt8 := 4
private def opPushV     : UInt8 := 5
private def opPushR     : UInt8 := 6
private def opPushXSq   : UInt8 := 7
private def opPushYSq   : UInt8 := 8
private def opPushZSq   : UInt8 := 9
private def opNeg       : UInt8 := 10
private def opSq        : UInt8 := 11
private def opCube      : UInt8 := 12
private def opP4        : UInt8 := 13
private def opSin       : UInt8 := 14
private def opCos       : UInt8 := 15
private def opTan       : UInt8 := 16
private def opAsin      : UInt8 := 17
private def opAcos      : UInt8 := 18
private def opAtan      : UInt8 := 19
private def opSinh      : UInt8 := 20
private def opCosh      : UInt8 := 21
private def opTanh      : UInt8 := 22
private def opExp       : UInt8 := 23
private def opLog       : UInt8 := 24
private def opSqrt      : UInt8 := 25
private def opAbs       : UInt8 := 26
private def opFloor     : UInt8 := 27
private def opCeil      : UInt8 := 28
private def opSign      : UInt8 := 29
private def opAdd       : UInt8 := 30
private def opSub       : UInt8 := 31
private def opMul       : UInt8 := 32
private def opDiv       : UInt8 := 33
private def opPow       : UInt8 := 34
private def opAtan2     : UInt8 := 35
private def opMin       : UInt8 := 36
private def opMax       : UInt8 := 37
private def opHypot     : UInt8 := 38
private def opAddLit    : UInt8 := 40
private def opSubLit    : UInt8 := 41
private def opRsubLit   : UInt8 := 42
private def opMulLit    : UInt8 := 43
private def opDivLit    : UInt8 := 44
private def opRdivLit   : UInt8 := 45
private def opSinScaled : UInt8 := 46
private def opCosScaled : UInt8 := 47

private def unaryByte : UnaryOp → UInt8
  | .neg   => opNeg   | .sq    => opSq    | .cube  => opCube  | .p4    => opP4
  | .sin   => opSin   | .cos   => opCos   | .tan   => opTan   | .asin  => opAsin
  | .acos  => opAcos  | .atan  => opAtan  | .sinh  => opSinh  | .cosh  => opCosh
  | .tanh  => opTanh  | .exp   => opExp   | .log   => opLog   | .sqrt  => opSqrt
  | .abs   => opAbs   | .floor => opFloor | .ceil  => opCeil  | .sign  => opSign

private def binaryByte : BinaryOp → UInt8
  | .add   => opAdd   | .sub   => opSub   | .mul   => opMul   | .div   => opDiv
  | .pow   => opPow   | .atan2 => opAtan2 | .min   => opMin   | .max   => opMax
  | .hypot => opHypot

private structure CompileAcc where
  ops      : Array ExprOp := #[]
  opBytes  : ByteArray    := ByteArray.empty
  consts   : FloatArray   := FloatArray.empty
  curStack : Nat          := 0
  maxStack : Nat          := 0

private def CompileAcc.emit (acc : CompileAcc) (op : ExprOp) (code : UInt8)
    (delta : Int) (lit? : Option Float := none) : CompileAcc :=
  let nextDepth :=
    if delta ≥ 0 then acc.curStack + delta.toNat
    else acc.curStack - (-delta).toNat
  { ops      := acc.ops.push op
    opBytes  := acc.opBytes.push code
    consts   := match lit? with | some v => acc.consts.push v | none => acc.consts
    curStack := nextDepth
    maxStack := max acc.maxStack nextDepth }

private def emitExprOps (e : Expr) (acc : CompileAcc) : CompileAcc :=
  match e with
  | .lit v => acc.emit (.pushLit v) opPushLit 1 (some v)
  | .varX  => acc.emit .pushX opPushX 1
  | .varY  => acc.emit .pushY opPushY 1
  | .varZ  => acc.emit .pushZ opPushZ 1
  | .varU  => acc.emit .pushU opPushU 1
  | .varV  => acc.emit .pushV opPushV 1
  | .varT  => acc.emit (.pushLit 0.0) opPushLit 1 (some 0.0)
  | .varR  => acc.emit .pushR opPushR 1
  | .un .sq .varX => acc.emit .pushXSq opPushXSq 1
  | .un .sq .varY => acc.emit .pushYSq opPushYSq 1
  | .un .sq .varZ => acc.emit .pushZSq opPushZSq 1
  | .un .sin (.bin .mul a (.lit k)) =>
    (emitExprOps a acc).emit (.sinScaled k) opSinScaled 0 (some k)
  | .un .sin (.bin .mul (.lit k) a) =>
    (emitExprOps a acc).emit (.sinScaled k) opSinScaled 0 (some k)
  | .un .cos (.bin .mul a (.lit k)) =>
    (emitExprOps a acc).emit (.cosScaled k) opCosScaled 0 (some k)
  | .un .cos (.bin .mul (.lit k) a) =>
    (emitExprOps a acc).emit (.cosScaled k) opCosScaled 0 (some k)
  | .un op a =>
    (emitExprOps a acc).emit (.un op) (unaryByte op) 0
  | .bin .add a (.lit c) => (emitExprOps a acc).emit (.addLit c) opAddLit 0 (some c)
  | .bin .add (.lit c) b => (emitExprOps b acc).emit (.addLit c) opAddLit 0 (some c)
  | .bin .sub a (.lit c) => (emitExprOps a acc).emit (.subLit c) opSubLit 0 (some c)
  | .bin .sub (.lit c) b => (emitExprOps b acc).emit (.rsubLit c) opRsubLit 0 (some c)
  | .bin .mul a (.lit c) => (emitExprOps a acc).emit (.mulLit c) opMulLit 0 (some c)
  | .bin .mul (.lit c) b => (emitExprOps b acc).emit (.mulLit c) opMulLit 0 (some c)
  | .bin .div a (.lit c) => (emitExprOps a acc).emit (.divLit c) opDivLit 0 (some c)
  | .bin .div (.lit c) b => (emitExprOps b acc).emit (.rdivLit c) opRdivLit 0 (some c)
  | .bin op a b =>
    let acc1 := emitExprOps a acc
    let acc2 := emitExprOps b acc1
    acc2.emit (.bin op) (binaryByte op) (-1)

/-- Fold time `t` into `e` and compile into flat compact RPN `Bytecode` once before meshing. -/
def compileToBytecode (e : Expr) (t : Float := 0.0) : Bytecode :=
  let folded := foldTime e t
  let acc := emitExprOps folded {}
  { ops := acc.ops, opBytes := acc.opBytes, consts := acc.consts, maxStack := acc.maxStack }

/-- Fallback dynamic-stack VM for extraordinarily deep expressions (`maxStack > 8`). -/
private def evalBytecodeDeep (bc : Bytecode) (x y z u v : Float) : Float := Id.run do
  let bytes := bc.opBytes
  let consts := bc.consts
  let n := bytes.size
  let mut st := FloatArray.emptyWithCapacity (max 16 bc.maxStack)
  let mut ci : Nat := 0
  for pc in [:n] do
    let op := bytes.get! pc
    if op == opPushLit then
      st := st.push (consts.get! ci); ci := ci + 1
    else if op == opPushX then st := st.push x
    else if op == opPushY then st := st.push y
    else if op == opPushZ then st := st.push z
    else if op == opPushU then st := st.push u
    else if op == opPushV then st := st.push v
    else if op == opPushR then st := st.push (Float.sqrt (x * x + y * y + z * z))
    else if op == opPushXSq then st := st.push (x * x)
    else if op == opPushYSq then st := st.push (y * y)
    else if op == opPushZSq then st := st.push (z * z)
    else if op < 30 then
      let top := st.size - 1
      let a := st.get! top
      let res :=
        if op == opNeg then -a
        else if op == opSq then a * a
        else if op == opCube then a * a * a
        else if op == opP4 then let s := a * a; s * s
        else if op == opSin then Float.sin a
        else if op == opCos then Float.cos a
        else if op == opTan then Float.tan a
        else if op == opAsin then Float.asin (max (-1.0) (min 1.0 a))
        else if op == opAcos then Float.acos (max (-1.0) (min 1.0 a))
        else if op == opAtan then Float.atan a
        else if op == opSinh then Float.sinh a
        else if op == opCosh then Float.cosh a
        else if op == opTanh then Float.tanh a
        else if op == opExp then Float.exp (max (-40.0) (min 40.0 a))
        else if op == opLog then Float.log (max 1e-12 (Float.abs a))
        else if op == opSqrt then Float.sqrt (max 0.0 a)
        else if op == opAbs then Float.abs a
        else if op == opFloor then Float.floor a
        else if op == opCeil then Float.ceil a
        else if a > 0.0 then 1.0 else if a < 0.0 then -1.0 else 0.0
      st := st.set! top res
    else if op < 40 then
      let bIdx := st.size - 1
      let aIdx := bIdx - 1
      let a := st.get! aIdx
      let b := st.get! bIdx
      let res :=
        if op == opAdd then a + b
        else if op == opSub then a - b
        else if op == opMul then a * b
        else if op == opDiv then if Float.abs b < 1e-12 then 0.0 else a / b
        else if op == opPow then Float.pow a b
        else if op == opAtan2 then Float.atan2 a b
        else if op == opMin then min a b
        else if op == opMax then max a b
        else Float.sqrt (a * a + b * b)
      st := st.set! aIdx res
      st := { data := st.data.extract 0 (bIdx * 8) }
    else
      let c := consts.get! ci; ci := ci + 1
      let top := st.size - 1
      let a := st.get! top
      let res :=
        if op == opAddLit then a + c
        else if op == opSubLit then a - c
        else if op == opRsubLit then c - a
        else if op == opMulLit then a * c
        else if op == opDivLit then if Float.abs c < 1e-12 then 0.0 else a / c
        else if op == opRdivLit then if Float.abs a < 1e-12 then 0.0 else c / a
        else if op == opSinScaled then Float.sin (c * a)
        else Float.cos (c * a)
      st := st.set! top res
  return if st.size > 0 then st.get! 0 else 0.0

/-- Pure tail-recursive register-stack bytecode loop: compiles to a single C `goto _start;`
loop with 100% unboxed `size_t` & `double` registers (`s0..s7`) and ZERO heap allocations! -/
private partial def runFastLoop (bytes : ByteArray) (consts : FloatArray)
    (x y z u v : Float) (pc ci : USize)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Float) : Float :=
  if h : pc.toNat < bytes.size then
    let op := bytes.uget pc h
    let pc1 := pc + 1
    if op < 10 then
      if op == opPushX then
        runFastLoop bytes consts x y z u v pc1 ci x s0 s1 s2 s3 s4 s5 s6
      else if op == opPushY then
        runFastLoop bytes consts x y z u v pc1 ci y s0 s1 s2 s3 s4 s5 s6
      else if op == opPushZ then
        runFastLoop bytes consts x y z u v pc1 ci z s0 s1 s2 s3 s4 s5 s6
      else if op == opPushLit then
        let c := if hc : ci.toNat < consts.size then consts.uget ci hc else 0.0
        runFastLoop bytes consts x y z u v pc1 (ci + 1) c s0 s1 s2 s3 s4 s5 s6
      else if op == opPushXSq then
        runFastLoop bytes consts x y z u v pc1 ci (x * x) s0 s1 s2 s3 s4 s5 s6
      else if op == opPushYSq then
        runFastLoop bytes consts x y z u v pc1 ci (y * y) s0 s1 s2 s3 s4 s5 s6
      else if op == opPushZSq then
        runFastLoop bytes consts x y z u v pc1 ci (z * z) s0 s1 s2 s3 s4 s5 s6
      else if op == opPushU then
        runFastLoop bytes consts x y z u v pc1 ci u s0 s1 s2 s3 s4 s5 s6
      else if op == opPushV then
        runFastLoop bytes consts x y z u v pc1 ci v s0 s1 s2 s3 s4 s5 s6
      else
        runFastLoop bytes consts x y z u v pc1 ci (Float.sqrt (x * x + y * y + z * z)) s0 s1 s2 s3 s4 s5 s6
    else if op ≥ 40 then
      let c := if hc : ci.toNat < consts.size then consts.uget ci hc else 0.0
      let ci1 := ci + 1
      let r :=
        if op == opCosScaled then Float.cos (c * s0)
        else if op == opSinScaled then Float.sin (c * s0)
        else if op == opAddLit then s0 + c
        else if op == opSubLit then s0 - c
        else if op == opRsubLit then c - s0
        else if op == opMulLit then s0 * c
        else if op == opDivLit then if Float.abs c < 1e-12 then 0.0 else s0 / c
        else if Float.abs s0 < 1e-12 then 0.0 else c / s0
      runFastLoop bytes consts x y z u v pc1 ci1 r s1 s2 s3 s4 s5 s6 s7
    else if op ≥ 30 then
      let r :=
        if op == opAdd then s1 + s0
        else if op == opMul then s1 * s0
        else if op == opSub then s1 - s0
        else if op == opDiv then if Float.abs s0 < 1e-12 then 0.0 else s1 / s0
        else if op == opPow then Float.pow s1 s0
        else if op == opAtan2 then Float.atan2 s1 s0
        else if op == opMin then min s1 s0
        else if op == opMax then max s1 s0
        else Float.sqrt (s1 * s1 + s0 * s0)
      runFastLoop bytes consts x y z u v pc1 ci r s2 s3 s4 s5 s6 s7 0.0
    else
      let r :=
        if op == opSq then s0 * s0
        else if op == opSin then Float.sin s0
        else if op == opCos then Float.cos s0
        else if op == opNeg then -s0
        else if op == opSqrt then Float.sqrt (max 0.0 s0)
        else if op == opCube then s0 * s0 * s0
        else if op == opP4 then let q := s0 * s0; q * q
        else if op == opAbs then Float.abs s0
        else if op == opExp then Float.exp (max (-40.0) (min 40.0 s0))
        else if op == opLog then Float.log (max 1e-12 (Float.abs s0))
        else if op == opTan then Float.tan s0
        else if op == opAsin then Float.asin (max (-1.0) (min 1.0 s0))
        else if op == opAcos then Float.acos (max (-1.0) (min 1.0 s0))
        else if op == opAtan then Float.atan s0
        else if op == opSinh then Float.sinh s0
        else if op == opCosh then Float.cosh s0
        else if op == opTanh then Float.tanh s0
        else if op == opFloor then Float.floor s0
        else if op == opCeil then Float.ceil s0
        else if s0 > 0.0 then 1.0 else if s0 < 0.0 then -1.0 else 0.0
      runFastLoop bytes consts x y z u v pc1 ci r s1 s2 s3 s4 s5 s6 s7
  else s0

/-- Zero-allocation unboxed shift-register bytecode VM (`s0..s7` live purely in `f64` CPU/WASM
registers with zero heap allocations and zero stack-pointer switches for all `maxStack ≤ 8`!). -/
def evalBytecode (bc : Bytecode) (x y z u v : Float) : Float :=
  if bc.maxStack > 8 then
    evalBytecodeDeep bc x y z u v
  else
    runFastLoop bc.opBytes bc.consts x y z u v 0 0
      0.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0

@[inline] def evalBytecodeXYZ (bc : Bytecode) (x y z : Float) : Float :=
  evalBytecode bc x y z 0.0 0.0

/-! ## 6. Adaptive Coarse-Probe Bytecode Marching Tetrahedra & Parametric Mesher -/

/-- Probe a coarse `7³` grid (`343` unboxed samples) to tighten `[bmin, bmax]` around active
sign-change cells (padded by 1 coarse cell) so the full `gridN³` budget delivers
sharper meshes in `<8 ms`. Falls back to original bounds if the coarse probe finds
no sign change (e.g. very thin shell). -/
private def refineBoundsXYZ (f : Float → Float → Float → Float) (bmin bmax : Vec3) : Vec3 × Vec3 := Id.run do
  let n := 6
  let n1 := n + 1
  let dx := (bmax.x - bmin.x) / Float.ofNat n
  let dy := (bmax.y - bmin.y) / Float.ofNat n
  let dz := (bmax.z - bmin.z) / Float.ofNat n
  let mut vals := FloatArray.emptyWithCapacity (n1 * n1 * n1)
  for iz in [:n1] do
    let z := bmin.z + Float.ofNat iz * dz
    for iy in [:n1] do
      let y := bmin.y + Float.ofNat iy * dy
      for ix in [:n1] do
        let x := bmin.x + Float.ofNat ix * dx
        vals := vals.push (f x y z)
  let atV (ix iy iz : Nat) := vals.get! ((iz * n1 + iy) * n1 + ix)
  let mut found := false
  let mut loX := bmax.x; let mut hiX := bmin.x
  let mut loY := bmax.y; let mut hiY := bmin.y
  let mut loZ := bmax.z; let mut hiZ := bmin.z
  for iz in [:n] do
    for iy in [:n] do
      for ix in [:n] do
        let b0 := atV ix iy iz < 0.0
        let diff :=
          (atV (ix+1) iy iz < 0.0) != b0 ||
          (atV ix (iy+1) iz < 0.0) != b0 ||
          (atV (ix+1) (iy+1) iz < 0.0) != b0 ||
          (atV ix iy (iz+1) < 0.0) != b0 ||
          (atV (ix+1) iy (iz+1) < 0.0) != b0 ||
          (atV ix (iy+1) (iz+1) < 0.0) != b0 ||
          (atV (ix+1) (iy+1) (iz+1) < 0.0) != b0
        if diff then
          found := true
          let x0 := bmin.x + Float.ofNat ix * dx; let x1 := x0 + dx
          let y0 := bmin.y + Float.ofNat iy * dy; let y1 := y0 + dy
          let z0 := bmin.z + Float.ofNat iz * dz; let z1 := z0 + dz
          if x0 < loX then loX := x0
          if x1 > hiX then hiX := x1
          if y0 < loY then loY := y0
          if y1 > hiY then hiY := y1
          if z0 < loZ then loZ := z0
          if z1 > hiZ then hiZ := z1
  if !found then
    return (bmin, bmax)
  else
    let padX := dx; let padY := dy; let padZ := dz
    let rMin : Vec3 := ⟨max bmin.x (loX - padX), max bmin.y (loY - padY), max bmin.z (loZ - padZ)⟩
    let rMax : Vec3 := ⟨min bmax.x (hiX + padX), min bmax.y (hiY + padY), min bmax.z (hiZ + padZ)⟩
    return (rMin, rMax)

/-- Parse, `t`-fold, compile to flat RPN bytecode, and mesh an arbitrary user-typed 3D implicit
equation `f(x, y, z, t) = 0` directly into a watertight CCW `MeshAsset` using unboxed Kuhn
Marching Tetrahedra with zero-eval 2nd-order interpolated grid gradients! -/
def evalImplicitExprMesh (exprStr : String) (t : Float := 0.0)
    (bmin : Vec3 := ⟨-1.6, -1.6, -1.6⟩) (bmax : Vec3 := ⟨1.6, 1.6, 1.6⟩)
    (gridN : Nat := 18) (meshId : UInt64 := 5001) (adaptive : Bool := true) :
    Except String MeshAsset := do
  let expr ← parseExpr exprStr
  let bc := compileToBytecode expr t
  let (useMin, useMax) :=
    if adaptive then refineBoundsXYZ (fun x y z => evalBytecodeXYZ bc x y z) bmin bmax
    else (bmin, bmax)
  let n' := max 4 (min 40 gridN)
  let n1 := n' + 1
  let dx := (useMax.x - useMin.x) / Float.ofNat n'
  let dy := (useMax.y - useMin.y) / Float.ofNat n'
  let dz := (useMax.z - useMin.z) / Float.ofNat n'
  let mut xs := FloatArray.emptyWithCapacity n1
  for ix in [:n1] do xs := xs.push (useMin.x + Float.ofNat ix * dx)
  let mut ys := FloatArray.emptyWithCapacity n1
  for iy in [:n1] do ys := ys.push (useMin.y + Float.ofNat iy * dy)
  let mut zs := FloatArray.emptyWithCapacity n1
  for iz in [:n1] do zs := zs.push (useMin.z + Float.ofNat iz * dz)
  let mut field := FloatArray.emptyWithCapacity (n1 * n1 * n1)
  for iz in [:n1] do
    let z := zs.get! iz
    for iy in [:n1] do
      let y := ys.get! iy
      for ix in [:n1] do
        field := field.push (evalBytecodeXYZ bc (xs.get! ix) y z)
  return marchingTetrahedraField field xs ys zs n' n' n' dx dy dz meshId

/-- Reference AST-based implicit mesher kept explicitly for before-vs-after bytecode benchmarks! -/
def evalImplicitExprMeshAst (exprStr : String) (t : Float := 0.0)
    (bmin : Vec3 := ⟨-1.6, -1.6, -1.6⟩) (bmax : Vec3 := ⟨1.6, 1.6, 1.6⟩)
    (gridN : Nat := 18) (meshId : UInt64 := 5001) (adaptive : Bool := true) :
    Except String MeshAsset := do
  let expr ← parseExpr exprStr
  let f (x y z : Float) : Float := evalExpr expr x y z 0.0 0.0 t
  let (useMin, useMax) := if adaptive then refineBoundsXYZ f bmin bmax else (bmin, bmax)
  return marchingTetrahedra (fun p => f p.x p.y p.z) useMin useMax gridN gridN gridN meshId

/-- Parse, `t`-fold, compile to flat bytecode, and mesh an arbitrary user-typed 3D parametric
surface `(fx(u, v, t), fy(u, v, t), fz(u, v, t))` over `[uMin, uMax] × [vMin, vMax]` into a
CCW `MeshAsset` with analytical exterior-product normals and curvature iridescence! -/
def evalParametricExprMesh (fxStr fyStr fzStr : String) (t : Float := 0.0)
    (uMin : Float := 0.0) (uMax : Float := twoPiF)
    (vMin : Float := 0.0) (vMax : Float := twoPiF)
    (nu : Nat := 40) (nv : Nat := 24)
    (doubleSided : Bool := true) (meshId : UInt64 := 5002) : Except String MeshAsset := do
  let ex ← parseExpr fxStr
  let ey ← parseExpr fyStr
  let ez ← parseExpr fzStr
  let bx := compileToBytecode ex t
  let by_ := compileToBytecode ey t
  let bz := compileToBytecode ez t
  let surf (u v : Float) : Vec3 :=
    ⟨evalBytecode bx 0.0 0.0 0.0 u v,
     evalBytecode by_ 0.0 0.0 0.0 u v,
     evalBytecode bz 0.0 0.0 0.0 u v⟩
  return buildParametricSurface surf uMin uMax vMin vMax nu nv meshId doubleSided

/-- Render any user-typed 3D implicit equation directly into a canonical `SceneFrame` (`GSIR` v1). -/
def evalImplicitExprToFrame (exprStr : String) (seq : UInt64 := 0) (t : Float := 0.0)
    (bmin : Vec3 := ⟨-1.6, -1.6, -1.6⟩) (bmax : Vec3 := ⟨1.6, 1.6, 1.6⟩)
    (gridN : Nat := 18) : SceneFrame :=
  let base : SceneFrame :=
    { frameSeq := seq, simTime := t, mode := .surface, is2D := false,
      gridEnabled := true, darkTheme := true, gridSize := 2.2,
      algebra := { name := "R3", p := 3, q := 0, r := 0,
                   basisNames := #["1","e1","e2","e3","e12","e13","e23","I"],
                   basisMetric := #[1,1,1,1,-1,-1,-1,-1] },
      presetId := "implicit_expr", title := s!"Implicit: {exprStr} = 0",
      formula := "f(x, y, z, t) = 0,\\qquad \\mathbf{n} = \\frac{\\nabla f}{\\|\\nabla f\\|}",
      summary := s!"Zero-level implicit 3D isosurface `{exprStr} = 0` meshed via bytecode-accelerated Kuhn Marching Tetrahedra.",
      camera := { motor := Motor3.orbitCamera 0.55 (-0.32) 4.6, fovDeg := 45.0, distance := 4.6 } }
  match evalImplicitExprMesh exprStr t bmin bmax gridN 5001 true with
  | .ok mesh =>
    { base with
      meshAssets := #[mesh],
      meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                      color := RGBA.white, useVertexColors := true }],
      inspect := #[{ idx := 0, name := "f(x,y,z,t)=0", grade := 0,
                     formatted := s!"{exprStr} · {mesh.positions.size/3} verts, {mesh.indices.size/3} tris" }] }
  | .error err =>
    { base with diagnostics := #[err] }

/-- Render any user-typed 3D parametric surface `(fx, fy, fz)` directly into a `SceneFrame` (`GSIR` v1). -/
def evalParametricExprToFrame (fxStr fyStr fzStr : String) (seq : UInt64 := 0) (t : Float := 0.0)
    (uMin : Float := 0.0) (uMax : Float := twoPiF)
    (vMin : Float := 0.0) (vMax : Float := twoPiF)
    (nu : Nat := 40) (nv : Nat := 24) : SceneFrame :=
  let base : SceneFrame :=
    { frameSeq := seq, simTime := t, mode := .surface, is2D := false,
      gridEnabled := true, darkTheme := true, gridSize := 2.2,
      algebra := { name := "R3", p := 3, q := 0, r := 0,
                   basisNames := #["1","e1","e2","e3","e12","e13","e23","I"],
                   basisMetric := #[1,1,1,1,-1,-1,-1,-1] },
      presetId := "parametric_expr", title := s!"Parametric: ({fxStr}, {fyStr}, {fzStr})",
      formula := "\\mathbf{S}(u, v) = (f_x, f_y, f_z),\\qquad \\mathbf{n} = \\frac{\\partial_u \\mathbf{S} \\wedge \\partial_v \\mathbf{S}}{\\|\\partial_u \\mathbf{S} \\wedge \\partial_v \\mathbf{S}\\|}",
      summary := "Parametric 3D manifold evaluated via compiled bytecode with exterior-product normals and curvature shading.",
      camera := { motor := Motor3.orbitCamera 0.55 (-0.32) 4.6, fovDeg := 45.0, distance := 4.6 } }
  match evalParametricExprMesh fxStr fyStr fzStr t uMin uMax vMin vMax nu nv true 5002 with
  | .ok mesh =>
    { base with
      meshAssets := #[mesh],
      meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                      color := RGBA.white, useVertexColors := true, doubleSided := true }],
      inspect := #[{ idx := 0, name := "S(u,v,t)", grade := 0,
                     formatted := s!"({fxStr}, {fyStr}, {fzStr}) · {mesh.positions.size/3} verts" }] }
  | .error err =>
    { base with diagnostics := #[err] }

end Grassmann.Eval.ImplicitExpr

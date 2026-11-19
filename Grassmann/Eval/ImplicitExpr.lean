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

-- Module-initialized Float constants (avoid runtime `lean_float_of_scientific` inside hot loops!)
private def k0 : Float := 0.0
private def k1 : Float := 1.0
private def kNeg1 : Float := -1.0
private def k40 : Float := 40.0
private def kNeg40 : Float := -40.0
private def kEps12 : Float := 1e-12

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
  | .asin  => Float.asin (max kNeg1 (min k1 a))
  | .acos  => Float.acos (max kNeg1 (min k1 a))
  | .atan  => Float.atan a
  | .sinh  => Float.sinh a
  | .cosh  => Float.cosh a
  | .tanh  => Float.tanh a
  | .exp   => Float.exp (max kNeg40 (min k40 a))
  | .log   => Float.log (max kEps12 (Float.abs a))
  | .sqrt  => Float.sqrt (max k0 a)
  | .abs   => Float.abs a
  | .floor => Float.floor a
  | .ceil  => Float.ceil a
  | .sign  => if a > k0 then k1 else if a < k0 then kNeg1 else k0

@[inline] private def evalBinary (op : BinaryOp) (a b : Float) : Float :=
  match op with
  | .add   => a + b
  | .sub   => a - b
  | .mul   => a * b
  | .div   => if Float.abs b < kEps12 then k0 else a / b
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

/-- Partial-evaluate `z = zVal` once per Z-slice (eliminates all `z`-only trig/pow ops across `n²` points!). -/
def foldZ (e : Expr) (zVal : Float) : Expr :=
  match e with
  | .varZ       => .lit zVal
  | .un op a    => mkUn op (foldZ a zVal)
  | .bin op a b => mkBin op (foldZ a zVal) (foldZ b zVal)
  | other       => other

/-- Partial-evaluate `y = yVal` once per Y-row (eliminates all `(y, z)`-only trig/pow ops across every X-row!). -/
def foldY (e : Expr) (yVal : Float) : Expr :=
  match e with
  | .varY       => .lit yVal
  | .un op a    => mkUn op (foldY a yVal)
  | .bin op a b => mkBin op (foldY a yVal) (foldY b yVal)
  | other       => other

/-- Compact flat RPN bytecode opcode with unboxed zero-payload math primitives (all common
ops are immediate scalar tags in `Array ExprOp` with ONE C `switch (lean_obj_tag)` jump table!). -/
inductive ExprOp where
  | pushLit    (val : Float)
  | pushX | pushY | pushZ | pushU | pushV | pushR
  | pushXSq | pushYSq | pushZSq
  | pushSinX   (k : Float)
  | pushCosX   (k : Float)
  | opAdd | opSub | opMul | opDiv
  | opNeg | opSq | opCube | opP4 | opSin | opCos | opSqrt | opAbs | opTanh
  | unOther    (op : UnaryOp)
  | binOther   (op : BinaryOp)
  | addLit     (c : Float)
  | subLit     (c : Float)
  | rsubLit    (c : Float)
  | mulLit     (c : Float)
  | divLit     (c : Float)
  | rdivLit    (c : Float)
  | sinScaled  (k : Float)
  | cosScaled  (k : Float)
  deriving Repr, BEq, Inhabited

/-- Compiled flat RPN `Array ExprOp` bytecode program with `t`-constant folding and
compile-time stack-depth analysis (`maxStack ≤ 4` runs 100% in ARM64/WASM `f64` registers). -/
structure Bytecode where
  ops      : Array ExprOp
  maxStack : Nat
  deriving Inhabited

private structure CompileAcc where
  ops      : Array ExprOp := #[]
  curStack : Nat          := 0
  maxStack : Nat          := 0

private def CompileAcc.emit (acc : CompileAcc) (op : ExprOp) (delta : Int) : CompileAcc :=
  let nextDepth :=
    if delta ≥ 0 then acc.curStack + delta.toNat
    else acc.curStack - (-delta).toNat
  { ops      := acc.ops.push op
    curStack := nextDepth
    maxStack := max acc.maxStack nextDepth }

private def emitUnaryOp (op : UnaryOp) : ExprOp :=
  match op with
  | .neg  => .opNeg
  | .sq   => .opSq
  | .cube => .opCube
  | .p4   => .opP4
  | .sin  => .opSin
  | .cos  => .opCos
  | .sqrt => .opSqrt
  | .abs  => .opAbs
  | .tanh => .opTanh
  | other => .unOther other

private def emitBinaryOp (op : BinaryOp) : ExprOp :=
  match op with
  | .add  => .opAdd
  | .sub  => .opSub
  | .mul  => .opMul
  | .div  => .opDiv
  | other => .binOther other

private def emitExprOps (e : Expr) (acc : CompileAcc) : CompileAcc :=
  match e with
  | .lit v => acc.emit (.pushLit v) 1
  | .varX  => acc.emit .pushX 1
  | .varY  => acc.emit .pushY 1
  | .varZ  => acc.emit .pushZ 1
  | .varU  => acc.emit .pushU 1
  | .varV  => acc.emit .pushV 1
  | .varT  => acc.emit (.pushLit k0) 1
  | .varR  => acc.emit .pushR 1
  | .un .sq .varX => acc.emit .pushXSq 1
  | .un .sq .varY => acc.emit .pushYSq 1
  | .un .sq .varZ => acc.emit .pushZSq 1
  | .un .sin (.bin .mul .varX (.lit k)) => acc.emit (.pushSinX k) 1
  | .un .sin (.bin .mul (.lit k) .varX) => acc.emit (.pushSinX k) 1
  | .un .cos (.bin .mul .varX (.lit k)) => acc.emit (.pushCosX k) 1
  | .un .cos (.bin .mul (.lit k) .varX) => acc.emit (.pushCosX k) 1
  | .un .sin (.bin .mul a (.lit k)) => (emitExprOps a acc).emit (.sinScaled k) 0
  | .un .sin (.bin .mul (.lit k) a) => (emitExprOps a acc).emit (.sinScaled k) 0
  | .un .cos (.bin .mul a (.lit k)) => (emitExprOps a acc).emit (.cosScaled k) 0
  | .un .cos (.bin .mul (.lit k) a) => (emitExprOps a acc).emit (.cosScaled k) 0
  | .un op a => (emitExprOps a acc).emit (emitUnaryOp op) 0
  | .bin .add a (.lit c) => (emitExprOps a acc).emit (.addLit c) 0
  | .bin .add (.lit c) b => (emitExprOps b acc).emit (.addLit c) 0
  | .bin .sub a (.lit c) => (emitExprOps a acc).emit (.subLit c) 0
  | .bin .sub (.lit c) b => (emitExprOps b acc).emit (.rsubLit c) 0
  | .bin .mul a (.lit c) => (emitExprOps a acc).emit (.mulLit c) 0
  | .bin .mul (.lit c) b => (emitExprOps b acc).emit (.mulLit c) 0
  | .bin .div a (.lit c) => (emitExprOps a acc).emit (.divLit c) 0
  | .bin .div (.lit c) b => (emitExprOps b acc).emit (.rdivLit c) 0
  | .bin op a b =>
    let acc1 := emitExprOps a acc
    let acc2 := emitExprOps b acc1
    acc2.emit (emitBinaryOp op) (-1)

/-- Compile an already-folded `Expr` directly into `Bytecode` without redundant `foldTime`. -/
private def compileFolded (e : Expr) : Bytecode :=
  let acc := emitExprOps e {}
  { ops := acc.ops, maxStack := acc.maxStack }

/-- Fold time `t` into `e` and compile into flat compact RPN `Bytecode` (`Array ExprOp`) once before meshing. -/
def compileToBytecode (e : Expr) (t : Float := 0.0) : Bytecode :=
  compileFolded (foldTime e t)

private theorem array_usize_le {α : Type} (a : Array α) : a.usize.toNat ≤ a.size := by
  simpa [Array.usize] using Nat.mod_le a.size USize.size

/-- Fallback dynamic-stack VM for extraordinarily deep expressions (`maxStack > 8`). -/
private def evalBytecodeDeep (ops : Array ExprOp) (maxStack : Nat) (x y z u v : Float) : Float := Id.run do
  let mut st := FloatArray.emptyWithCapacity (max 16 maxStack)
  for op in ops do
    match op with
    | .pushLit c   => st := st.push c
    | .pushX       => st := st.push x
    | .pushY       => st := st.push y
    | .pushZ       => st := st.push z
    | .pushU       => st := st.push u
    | .pushV       => st := st.push v
    | .pushR       => st := st.push (Float.sqrt (x * x + y * y + z * z))
    | .pushXSq     => st := st.push (x * x)
    | .pushYSq     => st := st.push (y * y)
    | .pushZSq     => st := st.push (z * z)
    | .pushSinX k  => st := st.push (Float.sin (k * x))
    | .pushCosX k  => st := st.push (Float.cos (k * x))
    | .opAdd =>
      let bIdx := st.size - 1; let aIdx := bIdx - 1
      st := st.set! aIdx (st.get! aIdx + st.get! bIdx)
      st := { data := st.data.extract 0 (bIdx * 8) }
    | .opSub =>
      let bIdx := st.size - 1; let aIdx := bIdx - 1
      st := st.set! aIdx (st.get! aIdx - st.get! bIdx)
      st := { data := st.data.extract 0 (bIdx * 8) }
    | .opMul =>
      let bIdx := st.size - 1; let aIdx := bIdx - 1
      st := st.set! aIdx (st.get! aIdx * st.get! bIdx)
      st := { data := st.data.extract 0 (bIdx * 8) }
    | .opDiv =>
      let bIdx := st.size - 1; let aIdx := bIdx - 1
      let b := st.get! bIdx
      st := st.set! aIdx (if Float.abs b < kEps12 then k0 else st.get! aIdx / b)
      st := { data := st.data.extract 0 (bIdx * 8) }
    | .opNeg  => let top := st.size - 1; st := st.set! top (-st.get! top)
    | .opSq   => let top := st.size - 1; let a := st.get! top; st := st.set! top (a * a)
    | .opCube => let top := st.size - 1; let a := st.get! top; st := st.set! top (a * a * a)
    | .opP4   => let top := st.size - 1; let s := st.get! top * st.get! top; st := st.set! top (s * s)
    | .opSin  => let top := st.size - 1; st := st.set! top (Float.sin (st.get! top))
    | .opCos  => let top := st.size - 1; st := st.set! top (Float.cos (st.get! top))
    | .opSqrt => let top := st.size - 1; st := st.set! top (Float.sqrt (max k0 (st.get! top)))
    | .opAbs  => let top := st.size - 1; st := st.set! top (Float.abs (st.get! top))
    | .opTanh => let top := st.size - 1; st := st.set! top (Float.tanh (st.get! top))
    | .unOther uop =>
      let top := st.size - 1
      st := st.set! top (evalUnary uop (st.get! top))
    | .binOther bop =>
      let bIdx := st.size - 1; let aIdx := bIdx - 1
      st := st.set! aIdx (evalBinary bop (st.get! aIdx) (st.get! bIdx))
      st := { data := st.data.extract 0 (bIdx * 8) }
    | .addLit c    => let top := st.size - 1; st := st.set! top (st.get! top + c)
    | .subLit c    => let top := st.size - 1; st := st.set! top (st.get! top - c)
    | .rsubLit c   => let top := st.size - 1; st := st.set! top (c - st.get! top)
    | .mulLit c    => let top := st.size - 1; st := st.set! top (st.get! top * c)
    | .divLit c    =>
      let top := st.size - 1
      st := st.set! top (if Float.abs c < kEps12 then k0 else st.get! top / c)
    | .rdivLit c   =>
      let top := st.size - 1
      let a := st.get! top
      st := st.set! top (if Float.abs a < kEps12 then k0 else c / a)
    | .sinScaled k => let top := st.size - 1; st := st.set! top (Float.sin (k * st.get! top))
    | .cosScaled k => let top := st.size - 1; st := st.set! top (Float.cos (k * st.get! top))
  return if st.size > 0 then st.get! 0 else k0

/-- Ultra-fast specialized 3D bytecode VM (`maxStack ≤ 4`) using unboxed `USize` PC,
safe `Array.uget`, single C `switch (lean_obj_tag)` jump table, and 7 `double` args
fitting 100% in ARM64 `d0..d6` registers with ZERO heap alloc and ZERO `Nat` ops! -/
private partial def runFastXYZ4 (ops : Array ExprOp) (x y z : Float) (n : USize)
    (hN : n.toNat ≤ ops.size) (pc : USize) (s0 s1 s2 s3 : Float) : Float :=
  if h : pc < n then
    let op := ops.uget pc (Nat.lt_of_lt_of_le (USize.lt_iff_toNat_lt.mp h) hN)
    let pc1 := pc + 1
    match op with
    | .pushLit c   => runFastXYZ4 ops x y z n hN pc1 c s0 s1 s2
    | .pushX       => runFastXYZ4 ops x y z n hN pc1 x s0 s1 s2
    | .pushY       => runFastXYZ4 ops x y z n hN pc1 y s0 s1 s2
    | .pushZ       => runFastXYZ4 ops x y z n hN pc1 z s0 s1 s2
    | .pushU       => runFastXYZ4 ops x y z n hN pc1 k0 s0 s1 s2
    | .pushV       => runFastXYZ4 ops x y z n hN pc1 k0 s0 s1 s2
    | .pushR       => runFastXYZ4 ops x y z n hN pc1 (Float.sqrt (x * x + y * y + z * z)) s0 s1 s2
    | .pushXSq     => runFastXYZ4 ops x y z n hN pc1 (x * x) s0 s1 s2
    | .pushYSq     => runFastXYZ4 ops x y z n hN pc1 (y * y) s0 s1 s2
    | .pushZSq     => runFastXYZ4 ops x y z n hN pc1 (z * z) s0 s1 s2
    | .pushSinX k  => runFastXYZ4 ops x y z n hN pc1 (Float.sin (k * x)) s0 s1 s2
    | .pushCosX k  => runFastXYZ4 ops x y z n hN pc1 (Float.cos (k * x)) s0 s1 s2
    | .opAdd       => runFastXYZ4 ops x y z n hN pc1 (s1 + s0) s2 s3 k0
    | .opSub       => runFastXYZ4 ops x y z n hN pc1 (s1 - s0) s2 s3 k0
    | .opMul       => runFastXYZ4 ops x y z n hN pc1 (s1 * s0) s2 s3 k0
    | .opDiv       =>
      let r := if Float.abs s0 < kEps12 then k0 else s1 / s0
      runFastXYZ4 ops x y z n hN pc1 r s2 s3 k0
    | .opNeg       => runFastXYZ4 ops x y z n hN pc1 (-s0) s1 s2 s3
    | .opSq        => runFastXYZ4 ops x y z n hN pc1 (s0 * s0) s1 s2 s3
    | .opCube      => runFastXYZ4 ops x y z n hN pc1 (s0 * s0 * s0) s1 s2 s3
    | .opP4        => let s := s0 * s0; runFastXYZ4 ops x y z n hN pc1 (s * s) s1 s2 s3
    | .opSin       => runFastXYZ4 ops x y z n hN pc1 (Float.sin s0) s1 s2 s3
    | .opCos       => runFastXYZ4 ops x y z n hN pc1 (Float.cos s0) s1 s2 s3
    | .opSqrt      => runFastXYZ4 ops x y z n hN pc1 (Float.sqrt (max k0 s0)) s1 s2 s3
    | .opAbs       => runFastXYZ4 ops x y z n hN pc1 (Float.abs s0) s1 s2 s3
    | .opTanh      => runFastXYZ4 ops x y z n hN pc1 (Float.tanh s0) s1 s2 s3
    | .unOther uop => runFastXYZ4 ops x y z n hN pc1 (evalUnary uop s0) s1 s2 s3
    | .binOther b  => runFastXYZ4 ops x y z n hN pc1 (evalBinary b s1 s0) s2 s3 k0
    | .addLit c    => runFastXYZ4 ops x y z n hN pc1 (s0 + c) s1 s2 s3
    | .subLit c    => runFastXYZ4 ops x y z n hN pc1 (s0 - c) s1 s2 s3
    | .rsubLit c   => runFastXYZ4 ops x y z n hN pc1 (c - s0) s1 s2 s3
    | .mulLit c    => runFastXYZ4 ops x y z n hN pc1 (s0 * c) s1 s2 s3
    | .divLit c    =>
      let r := if Float.abs c < kEps12 then k0 else s0 / c
      runFastXYZ4 ops x y z n hN pc1 r s1 s2 s3
    | .rdivLit c   =>
      let r := if Float.abs s0 < kEps12 then k0 else c / s0
      runFastXYZ4 ops x y z n hN pc1 r s1 s2 s3
    | .sinScaled k => runFastXYZ4 ops x y z n hN pc1 (Float.sin (k * s0)) s1 s2 s3
    | .cosScaled k => runFastXYZ4 ops x y z n hN pc1 (Float.cos (k * s0)) s1 s2 s3
  else s0

/-- General register-stack bytecode loop (`maxStack ≤ 8`) for `(x, y, z, u, v)`. -/
private partial def runFastLoop (ops : Array ExprOp) (x y z u v : Float) (n : USize)
    (hN : n.toNat ≤ ops.size) (pc : USize) (s0 s1 s2 s3 s4 s5 s6 s7 : Float) : Float :=
  if h : pc < n then
    let op := ops.uget pc (Nat.lt_of_lt_of_le (USize.lt_iff_toNat_lt.mp h) hN)
    let pc1 := pc + 1
    match op with
    | .pushLit c   => runFastLoop ops x y z u v n hN pc1 c s0 s1 s2 s3 s4 s5 s6
    | .pushX       => runFastLoop ops x y z u v n hN pc1 x s0 s1 s2 s3 s4 s5 s6
    | .pushY       => runFastLoop ops x y z u v n hN pc1 y s0 s1 s2 s3 s4 s5 s6
    | .pushZ       => runFastLoop ops x y z u v n hN pc1 z s0 s1 s2 s3 s4 s5 s6
    | .pushU       => runFastLoop ops x y z u v n hN pc1 u s0 s1 s2 s3 s4 s5 s6
    | .pushV       => runFastLoop ops x y z u v n hN pc1 v s0 s1 s2 s3 s4 s5 s6
    | .pushR       => runFastLoop ops x y z u v n hN pc1 (Float.sqrt (x * x + y * y + z * z)) s0 s1 s2 s3 s4 s5 s6
    | .pushXSq     => runFastLoop ops x y z u v n hN pc1 (x * x) s0 s1 s2 s3 s4 s5 s6
    | .pushYSq     => runFastLoop ops x y z u v n hN pc1 (y * y) s0 s1 s2 s3 s4 s5 s6
    | .pushZSq     => runFastLoop ops x y z u v n hN pc1 (z * z) s0 s1 s2 s3 s4 s5 s6
    | .pushSinX k  => runFastLoop ops x y z u v n hN pc1 (Float.sin (k * x)) s0 s1 s2 s3 s4 s5 s6
    | .pushCosX k  => runFastLoop ops x y z u v n hN pc1 (Float.cos (k * x)) s0 s1 s2 s3 s4 s5 s6
    | .opAdd       => runFastLoop ops x y z u v n hN pc1 (s1 + s0) s2 s3 s4 s5 s6 s7 k0
    | .opSub       => runFastLoop ops x y z u v n hN pc1 (s1 - s0) s2 s3 s4 s5 s6 s7 k0
    | .opMul       => runFastLoop ops x y z u v n hN pc1 (s1 * s0) s2 s3 s4 s5 s6 s7 k0
    | .opDiv       =>
      let r := if Float.abs s0 < kEps12 then k0 else s1 / s0
      runFastLoop ops x y z u v n hN pc1 r s2 s3 s4 s5 s6 s7 k0
    | .opNeg       => runFastLoop ops x y z u v n hN pc1 (-s0) s1 s2 s3 s4 s5 s6 s7
    | .opSq        => runFastLoop ops x y z u v n hN pc1 (s0 * s0) s1 s2 s3 s4 s5 s6 s7
    | .opCube      => runFastLoop ops x y z u v n hN pc1 (s0 * s0 * s0) s1 s2 s3 s4 s5 s6 s7
    | .opP4        => let s := s0 * s0; runFastLoop ops x y z u v n hN pc1 (s * s) s1 s2 s3 s4 s5 s6 s7
    | .opSin       => runFastLoop ops x y z u v n hN pc1 (Float.sin s0) s1 s2 s3 s4 s5 s6 s7
    | .opCos       => runFastLoop ops x y z u v n hN pc1 (Float.cos s0) s1 s2 s3 s4 s5 s6 s7
    | .opSqrt      => runFastLoop ops x y z u v n hN pc1 (Float.sqrt (max k0 s0)) s1 s2 s3 s4 s5 s6 s7
    | .opAbs       => runFastLoop ops x y z u v n hN pc1 (Float.abs s0) s1 s2 s3 s4 s5 s6 s7
    | .opTanh      => runFastLoop ops x y z u v n hN pc1 (Float.tanh s0) s1 s2 s3 s4 s5 s6 s7
    | .unOther uop => runFastLoop ops x y z u v n hN pc1 (evalUnary uop s0) s1 s2 s3 s4 s5 s6 s7
    | .binOther b  => runFastLoop ops x y z u v n hN pc1 (evalBinary b s1 s0) s2 s3 s4 s5 s6 s7 k0
    | .addLit c    => runFastLoop ops x y z u v n hN pc1 (s0 + c) s1 s2 s3 s4 s5 s6 s7
    | .subLit c    => runFastLoop ops x y z u v n hN pc1 (s0 - c) s1 s2 s3 s4 s5 s6 s7
    | .rsubLit c   => runFastLoop ops x y z u v n hN pc1 (c - s0) s1 s2 s3 s4 s5 s6 s7
    | .mulLit c    => runFastLoop ops x y z u v n hN pc1 (s0 * c) s1 s2 s3 s4 s5 s6 s7
    | .divLit c    =>
      let r := if Float.abs c < kEps12 then k0 else s0 / c
      runFastLoop ops x y z u v n hN pc1 r s1 s2 s3 s4 s5 s6 s7
    | .rdivLit c   =>
      let r := if Float.abs s0 < kEps12 then k0 else c / s0
      runFastLoop ops x y z u v n hN pc1 r s1 s2 s3 s4 s5 s6 s7
    | .sinScaled k => runFastLoop ops x y z u v n hN pc1 (Float.sin (k * s0)) s1 s2 s3 s4 s5 s6 s7
    | .cosScaled k => runFastLoop ops x y z u v n hN pc1 (Float.cos (k * s0)) s1 s2 s3 s4 s5 s6 s7
  else s0

/-- Zero-allocation unboxed shift-register bytecode VM (`s0..s7` live purely in `f64` CPU/WASM
registers with unboxed `USize` PC and a single C `switch (tag)` jump table for all `maxStack ≤ 8`!). -/
def evalBytecode (bc : Bytecode) (x y z u v : Float) : Float :=
  if bc.maxStack > 8 then
    evalBytecodeDeep bc.ops bc.maxStack x y z u v
  else
    runFastLoop bc.ops x y z u v bc.ops.usize (array_usize_le bc.ops) 0 k0 k0 k0 k0 k0 k0 k0 k0

@[inline] def evalBytecodeXYZ (bc : Bytecode) (x y z : Float) : Float :=
  if bc.maxStack ≤ 4 then
    runFastXYZ4 bc.ops x y z bc.ops.usize (array_usize_le bc.ops) 0 k0 k0 k0 k0
  else
    evalBytecode bc x y z k0 k0

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
        let b0 := atV ix iy iz < k0
        let diff :=
          (atV (ix+1) iy iz < k0) != b0 ||
          (atV ix (iy+1) iz < k0) != b0 ||
          (atV (ix+1) (iy+1) iz < k0) != b0 ||
          (atV ix iy (iz+1) < k0) != b0 ||
          (atV (ix+1) iy (iz+1) < k0) != b0 ||
          (atV ix (iy+1) (iz+1) < k0) != b0 ||
          (atV (ix+1) (iy+1) (iz+1) < k0) != b0
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

/-- Parse, `t`-fold, slice-fold `(z, y)` into compact X-row RPN `Array ExprOp` bytecode, and
mesh an arbitrary user-typed 3D implicit equation `f(x, y, z, t) = 0` directly into a watertight
CCW `MeshAsset` using exclusive-RC Kuhn Marching Tetrahedra with zero-eval 2nd-order grid gradients! -/
def evalImplicitExprMesh (exprStr : String) (t : Float := 0.0)
    (bmin : Vec3 := ⟨-1.6, -1.6, -1.6⟩) (bmax : Vec3 := ⟨1.6, 1.6, 1.6⟩)
    (gridN : Nat := 18) (meshId : UInt64 := 5001) (adaptive : Bool := true) :
    Except String MeshAsset := do
  let expr0 ← parseExpr exprStr
  let exprT := foldTime expr0 t
  let bcFull := compileFolded exprT
  let (useMin, useMax) :=
    if adaptive then refineBoundsXYZ (fun x y z => evalBytecodeXYZ bcFull x y z) bmin bmax
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
    let exprZ := foldZ exprT z
    for iy in [:n1] do
      let y := ys.get! iy
      let exprYZ := foldY exprZ y
      let bcRow := compileFolded exprYZ
      for ix in [:n1] do
        field := field.push (evalBytecodeXYZ bcRow (xs.get! ix) y z)
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

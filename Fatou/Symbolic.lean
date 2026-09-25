import Fatou.Kernel
import Fatou.CAS

/-!
# The symbolic front-end: maps from Julia expressions

Fatou.jl's front-ends take a Julia `Expr` (`juliafill(:(z^2 + c))`, `newton(:(z^3 - 1); m)`):
the map is compiled with `SyntaxTree.genlatest`, in Newton mode REDUCE derives the Newton map
`factor(z - m*(E/df(E, z)))`, and the titles and basins come from REDUCE's LaTeX
(`src/Fatou.jl:93-118`, `src/internals.jl`). This module does the same without Julia or REDUCE:

* the expression is read by `Wilkinson.JExpr.parse` (Julia's parser for this fragment);
* `Fatou.CAS` derives the Newton map and the LaTeX (see its scope note);
* the map is *evaluated with Julia's semantics*: every subexpression has Julia's type (`Int`,
  `Float64`, `Complex{Bool}` for `im`, `Complex{Int}`, `ComplexF64`, `ℯ`, `π`), constant
  subexpressions are folded exactly as Julia computes them, and each remaining operation is the
  one Julia dispatches to (`x * z` scales, `im * z` multiplies by `Complex{Bool}`, `z^3` is the
  literal power, `/` is the robust complex division, …). A map therefore iterates bit for bit
  like Fatou.jl's whenever its expression tree is Julia's.

Two ways to get a map:

* `juliafill!`, `mandelbrot!`, `newton!` (term elaborators) parse and differentiate at
  **elaboration time** and generate an ordinary Lean lambda over `C64`, so the escape-time
  kernel specializes on it exactly as on a hand-written map (full speed);
* `Symbolic.ofString` does everything at run time and evaluates the map by walking a lowered
  tree (convenient, much slower).

```lean
open Fatou in
#eval (fatou (newton! "z^3 - 1" { n := 100, ϵ := some 0.1, N := 25, iter := true })).title
-- "f : z ↦ z ^ 3 - 1, m = 1, iter."
```
-/

namespace Fatou

open JuliaBase Wilkinson

namespace Sym

/-! ## Julia values -/

/-- A constant Julia value with its type. -/
inductive JVal where
  /-- `Int64` -/
  | int (n : Int)
  /-- `Float64` -/
  | float (x : Float)
  /-- `Complex{Bool}` (`im`) -/
  | cbool (re im : Bool)
  /-- `Complex{Int}` -/
  | cint (re im : Int)
  /-- `ComplexF64` -/
  | c64 (re im : Float)
  /-- the irrational `ℯ` -/
  | euler
  /-- the irrational `π` -/
  | pi
  deriving Inhabited

/-- Julia `Float64(ℯ)`. -/
def eulerF : Float := Float.ofBits 0x4005BF0A8B145769

namespace JVal

/-- Is it real (`Int`, `Float64`, an irrational)? -/
def isReal : JVal → Bool
  | int _ | float _ | euler | pi => true
  | _ => false

/-- A real value as `Float64` (Julia's conversion). -/
def toFloat : JVal → Float
  | int n => Float.ofInt n
  | float x => x
  | euler => eulerF
  | pi => F64.pi
  | _ => 0

/-- A value as `ComplexF64` (Julia's promotion). -/
def toC64 : JVal → C64
  | cbool a b => ⟨if a then 1 else 0, if b then 1 else 0⟩
  | cint a b => ⟨Float.ofInt a, Float.ofInt b⟩
  | c64 a b => ⟨a, b⟩
  | v => ⟨v.toFloat, 0⟩

/-- Integer parts of an integer-valued complex (`Complex{Bool}`/`Complex{Int}`/`Int`). -/
def toCInt? : JVal → Option (Int × Int)
  | int n => some (n, 0)
  | cbool a b => some (if a then 1 else 0, if b then 1 else 0)
  | cint a b => some (a, b)
  | _ => none

/-- The value as a Fatou `Number` (for the multiplicity `m`). -/
def toNumber : JVal → Number
  | int n => .int n
  | float x => .float x
  | cbool a b => .complexInt (if a then 1 else 0) (if b then 1 else 0)
  | cint a b => .complexInt a b
  | c64 a b => .complexFloat a b
  | v => .float v.toFloat

end JVal

/-! ## The operations Julia dispatches to

Each is Julia's method for the operand types (Julia 1.13 `base/complex.jl`). -/

/-- `x + z` (complex.jl:327). -/
@[inline] def addRC (x : Float) (z : C64) : C64 := ⟨x + z.re, z.im⟩
/-- `z + x` (complex.jl:328). -/
@[inline] def addCR (z : C64) (x : Float) : C64 := ⟨x + z.re, z.im⟩
/-- `z - x` (complex.jl:334). -/
@[inline] def subCR (z : C64) (x : Float) : C64 := ⟨z.re - x, z.im⟩
/-- `x - z` (complex.jl:329-333). -/
@[inline] def subRC (x : Float) (z : C64) : C64 := ⟨x - z.re, -z.im⟩
/-- `x * z` (complex.jl:335). -/
@[inline] def mulRC (x : Float) (z : C64) : C64 := ⟨x * z.re, x * z.im⟩
/-- `z * x` (complex.jl:336). -/
@[inline] def mulCR (z : C64) (x : Float) : C64 := ⟨x * z.re, x * z.im⟩
/-- `z / x` (complex.jl:348). -/
@[inline] def divCR (z : C64) (x : Float) : C64 := ⟨z.re / x, z.im / x⟩
/-- `x / z = x * inv(z)` (complex.jl:347). -/
@[inline] def divRC (x : Float) (z : C64) : C64 := C64.realDiv x z
/-- `z + w`. -/
@[inline] def addCC (z w : C64) : C64 := ⟨z.re + w.re, z.im + w.im⟩
/-- `z - w`. -/
@[inline] def subCC (z w : C64) : C64 := ⟨z.re - w.re, z.im - w.im⟩
/-- `z * w` (complex.jl:290). -/
@[inline] def mulCC (z w : C64) : C64 := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
/-- `z / w`, the robust division (complex.jl:350-). -/
@[inline] def divCC (z w : C64) : C64 := C64.div z w
/-- `-z`. -/
@[inline] def negC (z : C64) : C64 := ⟨-z.re, -z.im⟩
/-- `im * z` (`Complex{Bool} * ComplexF64`, complex.jl:290 with `Bool * Float64`,
bool.jl: `false * x = copysign(0, x)`). -/
@[inline] def mulIC (z : C64) : C64 := ⟨C64.falseTimes z.re - z.im, C64.falseTimes z.im + z.re⟩
/-- `z * im`. -/
@[inline] def mulCI (z : C64) : C64 := ⟨C64.falseTimes z.re - z.im, z.re + C64.falseTimes z.im⟩
/-- `x + y`. -/
@[inline] def addRR (x y : Float) : Float := x + y
/-- `x - y`. -/
@[inline] def subRR (x y : Float) : Float := x - y
/-- `x * y`. -/
@[inline] def mulRR (x y : Float) : Float := x * y
/-- `x / y`. -/
@[inline] def divRR (x y : Float) : Float := x / y
/-- `-x`. -/
@[inline] def negR (x : Float) : Float := -x
/-- `z ^ n` for a literal integer `n` (`literal_pow`). -/
@[inline] def powLit (z : C64) (n : Int) : C64 := C64.literalPow z n
/-- `z ^ n` for a computed integer `n` (`power_by_squaring`). -/
@[inline] def powInt (z : C64) (n : Int) : C64 := C64.powInt z n
/-- `z ^ w` (`_cpow`). -/
@[inline] def powCC (z w : C64) : C64 := ComplexF64.pow z w
/-- `ℯ ^ z = exp(z)` (mathconstants.jl). -/
@[inline] def expC (z : C64) : C64 := C64.exp z

/-! ## Lowering: Julia types, constant folding -/

/-- The operations of a lowered map. -/
inductive Fn where
  | addRC | addCR | subCR | subRC | mulRC | mulCR | divCR | divRC
  | addCC | subCC | mulCC | divCC | negC | mulIC | mulCI
  | addRR | subRR | mulRR | divRR | negR
  | powLit (n : Int) | powInt (n : Int) | powCC
  | exp | sin | cos | tan | sinh | cosh | log | sqrt
  | abs | abs2 | angle | real | imag
  deriving Inhabited, BEq

/-- A lowered map: the variables `z`, `c` (both `ComplexF64`), folded constants, and
operations. -/
inductive Low where
  /-- the iterate -/
  | z
  /-- the parameter -/
  | c
  /-- a real constant -/
  | rconst (x : Float)
  /-- a complex constant -/
  | cconst (re im : Float)
  /-- an operation -/
  | op (f : Fn) (args : List Low)
  deriving Inhabited

/-- Is the result of a dynamic node complex (otherwise real)? -/
def Fn.complex : Fn → Bool
  | .addRR | .subRR | .mulRR | .divRR | .negR | .abs | .abs2 | .angle | .real | .imag => false
  | _ => true

/-- A lowered subexpression: a folded constant, or a dynamic node with its type. -/
inductive Node where
  /-- a constant -/
  | const (v : JVal)
  /-- a dynamic complex value -/
  | cx (l : Low)
  /-- a dynamic real value -/
  | re (l : Low)
  deriving Inhabited

open JVal in
/-- Julia's `+ - * /` on two constants (exact for integers and `Complex{Int}`). -/
def foldBin (o : String) (a b : JVal) : Except String JVal := do
  match a, b with
  | int x, int y =>
    match o with
    | "+" => return int (x + y)
    | "-" => return int (x - y)
    | "*" => return int (x * y)
    | "/" => return float (Float.ofInt x / Float.ofInt y)
    | "%" => return int (x.tmod y)
    | _ => throw s!"unsupported {o}"
  | _, _ =>
    if a.isReal && b.isReal then
      let x := a.toFloat
      let y := b.toFloat
      match o with
      | "+" => return float (x + y)
      | "-" => return float (x - y)
      | "*" => return float (x * y)
      | "/" => return float (x / y)
      | _ => throw s!"unsupported {o}"
    else
      -- integer complex arithmetic stays exact (`Complex{Int}`); `/` promotes
      match a.toCInt?, b.toCInt?, o with
      | some (p, q), some (r, s), "+" => return cint (p + r) (q + s)
      | some (p, q), some (r, s), "-" => return cint (p - r) (q - s)
      | some (p, q), some (r, s), "*" => return cint (p * r - q * s) (p * s + q * r)
      | _, _, _ =>
        -- a real times `Complex{Bool}` keeps Julia's `false * x = copysign(0, x)`
        match a, b, o with
        | float x, cbool p q, "*" => return c64 (if p then x else C64.falseTimes x) (if q then x else C64.falseTimes x)
        | cbool p q, float x, "*" => return c64 (if p then x else C64.falseTimes x) (if q then x else C64.falseTimes x)
        | _, _, _ =>
          let z := a.toC64
          let w := b.toC64
          if a.isReal then
            let x := a.toFloat
            match o with
            | "+" => let r := addRC x w; return c64 r.re r.im
            | "-" => let r := subRC x w; return c64 r.re r.im
            | "*" => let r := mulRC x w; return c64 r.re r.im
            | "/" => let r := divRC x w; return c64 r.re r.im
            | _ => throw s!"unsupported {o}"
          else if b.isReal then
            let y := b.toFloat
            match o with
            | "+" => let r := addCR z y; return c64 r.re r.im
            | "-" => let r := subCR z y; return c64 r.re r.im
            | "*" => let r := mulCR z y; return c64 r.re r.im
            | "/" => let r := divCR z y; return c64 r.re r.im
            | _ => throw s!"unsupported {o}"
          else
            match o with
            | "+" => let r := addCC z w; return c64 r.re r.im
            | "-" => let r := subCC z w; return c64 r.re r.im
            | "*" => let r := mulCC z w; return c64 r.re r.im
            | "/" => let r := divCC z w; return c64 r.re r.im
            | _ => throw s!"unsupported {o}"

/-- A constant as a lowered operand of the given kind. -/
def constLow (v : JVal) : Low :=
  if v.isReal then .rconst v.toFloat else let z := v.toC64; .cconst z.re z.im

/-- The node's lowered form, promoted to complex (Julia's promotion of a real operand is
never needed: mixed operations use the real methods). -/
def Node.low : Node → Low
  | .const v => constLow v
  | .cx l => l
  | .re l => l

open JVal in
/-- A binary operation on nodes, choosing Julia's method from the operand types. -/
def binNode (o : String) (a b : Node) : Except String Node := do
  match a, b with
  | .const x, .const y => return .const (← foldBin o x y)
  | .re x, .re y => match o with
    | "+" => return .re (.op .addRR [x, y])
    | "-" => return .re (.op .subRR [x, y])
    | "*" => return .re (.op .mulRR [x, y])
    | "/" => return .re (.op .divRR [x, y])
    | _ => throw s!"unsupported {o}"
  | .re x, .const v | .const v, .re x =>
    if v.isReal then
      let (l, r) := match a with | .re _ => (x, Low.rconst v.toFloat) | _ => (Low.rconst v.toFloat, x)
      match o with
      | "+" => return .re (.op .addRR [l, r])
      | "-" => return .re (.op .subRR [l, r])
      | "*" => return .re (.op .mulRR [l, r])
      | "/" => return .re (.op .divRR [l, r])
      | _ => throw s!"unsupported {o}"
    else throw "complex constants with real dynamic values are not supported"
  | _, _ =>
    -- at least one complex operand
    let (aR, aL) : Option Low × Low := match a with
      | .const v => if v.isReal then (some (.rconst v.toFloat), constLow v) else (none, constLow v)
      | .re l => (some l, l)
      | .cx l => (none, l)
    let (bR, bL) : Option Low × Low := match b with
      | .const v => if v.isReal then (some (.rconst v.toFloat), constLow v) else (none, constLow v)
      | .re l => (some l, l)
      | .cx l => (none, l)
    let isIm : Node → Bool := fun n => match n with
      | .const (cbool false true) => true
      | _ => false
    match o with
    | "+" => match aR, bR with
      | some x, _ => return .cx (.op .addRC [x, bL])
      | _, some y => return .cx (.op .addCR [aL, y])
      | _, _ => return .cx (.op .addCC [aL, bL])
    | "-" => match aR, bR with
      | some x, _ => return .cx (.op .subRC [x, bL])
      | _, some y => return .cx (.op .subCR [aL, y])
      | _, _ => return .cx (.op .subCC [aL, bL])
    | "*" =>
      if isIm a then return .cx (.op .mulIC [bL])
      else if isIm b then return .cx (.op .mulCI [aL])
      else match aR, bR with
        | some x, _ => return .cx (.op .mulRC [x, bL])
        | _, some y => return .cx (.op .mulCR [aL, y])
        | _, _ => return .cx (.op .mulCC [aL, bL])
    | "/" => match aR, bR with
      | some x, _ => return .cx (.op .divRC [x, bL])
      | _, some y => return .cx (.op .divCR [aL, y])
      | _, _ => return .cx (.op .divCC [aL, bL])
    | _ => throw s!"unsupported {o} on complex values"

/-- The functions of a complex argument. -/
def complexFn? : String → Option Fn
  | "exp" => some .exp | "sin" => some .sin | "cos" => some .cos | "tan" => some .tan
  | "sinh" => some .sinh | "cosh" => some .cosh | "log" => some .log | "sqrt" => some .sqrt
  | "abs" => some .abs | "abs2" => some .abs2 | "angle" => some .angle
  | "real" => some .real | "imag" => some .imag
  | _ => none

/-- Julia's value of a function at a real constant (`JuliaBase` kernels). -/
def realFn? (f : String) (x : Float) : Option Float :=
  match f with
  | "exp" => some (F64.exp x) | "log" => some (F64.log x) | "sqrt" => some x.sqrt
  | "sin" => some (F64.sin x) | "cos" => some (F64.cos x) | "tan" => some (F64.tan x)
  | "sinh" => some (F64.sinh x) | "cosh" => some (F64.cosh x) | "abs" => some x.abs
  | "abs2" => some (x * x) | "real" => some x | "imag" => some 0
  | _ => none

/-- Evaluate a lowered map (the reference semantics of the generated lambdas). -/
partial def Low.eval (z c : C64) : Low → C64 ⊕ Float
  | .z => .inl z
  | .c => .inl c
  | .rconst x => .inr x
  | .cconst a b => .inl ⟨a, b⟩
  | .op f args =>
    let vs := args.map (Low.eval z c)
    let C (i : Nat) : C64 := match vs[i]? with | some (.inl w) => w | some (.inr x) => ⟨x, 0⟩ | none => ⟨0, 0⟩
    let R (i : Nat) : Float := match vs[i]? with | some (.inr x) => x | some (.inl w) => w.re | none => 0
    match f with
    | .addRC => .inl (addRC (R 0) (C 1)) | .addCR => .inl (addCR (C 0) (R 1))
    | .subRC => .inl (subRC (R 0) (C 1)) | .subCR => .inl (subCR (C 0) (R 1))
    | .mulRC => .inl (mulRC (R 0) (C 1)) | .mulCR => .inl (mulCR (C 0) (R 1))
    | .divRC => .inl (divRC (R 0) (C 1)) | .divCR => .inl (divCR (C 0) (R 1))
    | .addCC => .inl (addCC (C 0) (C 1)) | .subCC => .inl (subCC (C 0) (C 1))
    | .mulCC => .inl (mulCC (C 0) (C 1)) | .divCC => .inl (divCC (C 0) (C 1))
    | .negC => .inl (negC (C 0)) | .mulIC => .inl (mulIC (C 0)) | .mulCI => .inl (mulCI (C 0))
    | .addRR => .inr (R 0 + R 1) | .subRR => .inr (R 0 - R 1)
    | .mulRR => .inr (R 0 * R 1) | .divRR => .inr (R 0 / R 1) | .negR => .inr (-R 0)
    | .powLit n => .inl (powLit (C 0) n) | .powInt n => .inl (powInt (C 0) n)
    | .powCC => .inl (powCC (C 0) (C 1))
    | .exp => .inl (C64.exp (C 0)) | .sin => .inl (C64.sin (C 0)) | .cos => .inl (C64.cos (C 0))
    | .tan => .inl (C64.tan (C 0)) | .sinh => .inl (C64.sinh (C 0))
    | .cosh => .inl (C64.cosh (C 0)) | .log => .inl (C64.log (C 0))
    | .sqrt => .inl (C64.sqrt (C 0))
    | .abs => .inr (C64.abs (C 0)) | .abs2 => .inr (C64.abs2 (C 0))
    | .angle => .inr (C64.angle (C 0)) | .real => .inr (C 0).re | .imag => .inr (C 0).im

/-- `-v` of a constant (Julia's unary minus keeps the type). -/
def negConst : JVal → JVal
  | .int n => .int (-n)
  | .float x => .float (-x)
  | .cbool a b => .cint (if a then -1 else 0) (if b then -1 else 0)
  | .cint a b => .cint (-a) (-b)
  | .c64 a b => .c64 (-a) (-b)
  | v => .float (-v.toFloat)

/-- Unary minus of a node. -/
def negNode : Node → Node
  | .const v => .const (negConst v)
  | .cx l => .cx (.op .negC [l])
  | .re l => .re (.op .negR [l])

/-- A constant raised to a literal integer power (Julia `literal_pow`). -/
def powConstLit (v : JVal) (n : Int) : JVal :=
  match v with
  | .int x => if n ≥ 0 then .int (x ^ n.toNat) else .float (1 / Float.ofInt (x ^ n.natAbs))
  | .float x => .float (F64.powInt x n)
  | _ => let r := powLit v.toC64 n; .c64 r.re r.im

/-- `ℯ ^ w` = `exp(w)`. -/
def expNode : Node → Node
  | .const v =>
    if v.isReal then .const (.float (F64.exp v.toFloat))
    else let r := C64.exp v.toC64; .const (.c64 r.re r.im)
  | .cx l => .cx (.op .exp [l])
  | .re l => .cx (.op .exp [l])

/-- `a ^ b` for a non-literal exponent (`power_by_squaring` for an integer, `_cpow` else). -/
def powNode (a b : Node) : Except String Node :=
  match a, b with
  | .cx l, .const (.int n) => .ok (.cx (.op (.powInt n) [l]))
  | .cx l, e => .ok (.cx (.op .powCC [l, e.low]))
  | .const v, .cx e => .ok (.cx (.op .powCC [constLow v, e]))
  | .const v, .const w =>
    if v.isReal && w.isReal then .ok (.const (.float (F64.pow v.toFloat w.toFloat)))
    else let r := powCC v.toC64 w.toC64; .ok (.const (.c64 r.re r.im))
  | _, _ => .error "unsupported power"

/-- A function applied to a node. -/
def fnNode (f : String) (a : Node) : Except String Node := do
  let some fn := complexFn? f | throw s!"unsupported function {f}"
  match a with
  | .const v =>
    if v.isReal then
      match realFn? f v.toFloat with
      | some x => return .const (.float x)
      | none => throw s!"unsupported function {f}"
    else
      match (Low.op fn [constLow v]).eval ⟨0, 0⟩ ⟨0, 0⟩ with
      | .inl w => return .const (.c64 w.re w.im)
      | .inr x => return .const (.float x)
  | .cx l => return (if fn.complex then .cx (.op fn [l]) else .re (.op fn [l]))
  | .re l => return (if fn.complex then .cx (.op fn [l]) else .re (.op fn [l]))

/-- The integer value of a literal exponent (`2`, or `-2` written `^-2`). -/
def litExponent? : JExpr → Option Int
  | .lit (.int n) => some n
  | _ => none

mutual

/-- Lower a Julia expression in the variables `z`, `c` with Julia's typing: constants fold,
`ℯ ^ w` is `exp(w)`, `w ^ n` with an integer literal `n` is the literal power. -/
partial def lower : JExpr → Except String Node
  | .sym s =>
    match s with
    | "z" => .ok (.cx .z)
    | "c" => .ok (.cx .c)
    | "im" => .ok (.const (.cbool false true))
    | "ℯ" => .ok (.const .euler)
    | "π" | "pi" => .ok (.const .pi)
    | _ => .error s!"unknown symbol {s}"
  | .lit (.int n) => .ok (.const (.int n))
  | .lit (.f64 x) => .ok (.const (.float x))
  | .lit _ => .error "unsupported literal"
  | .call op args => lowerCall op args

/-- Lower a call. -/
partial def lowerCall (op : String) (args : List JExpr) : Except String Node := do
  match args with
  | [] => throw s!"{op} without arguments"
  | [a] =>
    if op == "+" then lower a
    else if op == "-" then return negNode (← lower a)
    else fnNode op (← lower a)
  | a :: rest =>
    if op == "+" || op == "*" then
      rest.foldlM (fun acc b => do binNode op acc (← lower b)) (← lower a)
    else if op == "-" || op == "/" then
      match rest with
      | [b] => binNode op (← lower a) (← lower b)
      | _ => throw s!"{op} with more than two arguments"
    else if op == "^" then
      match rest with
      | [b] =>
        let base ← lower a
        match base, litExponent? b with
        | .const .euler, _ => return expNode (← lower b)
        | .cx l, some n => return .cx (.op (.powLit n) [l])
        | .const v, some n => return .const (powConstLit v n)
        | _, _ => powNode base (← lower b)
      | _ => throw "^ with more than two arguments"
    else throw s!"unsupported call {op}"

end

/-- The complex-valued map `(z, c) ↦ E` of a lowered expression. -/
def Node.map (n : Node) : C64 → C64 → C64 := fun z c =>
  match n.low.eval z c with
  | .inl w => w
  | .inr x => ⟨x, 0⟩

/-- Evaluate a Julia expression constant (e.g. a multiplicity `m`). -/
def constOf (s : String) : Except String JVal := do
  match ← lower (← JExpr.parse s) with
  | .const v => return v
  | _ => throw s!"{s} is not a constant"

end Sym

/-! ## `Symbolic`: a map with its expression -/

/-- A Fatou map defined by a Julia expression (Fatou.jl's `Define(E; …)` input): the compiled
functions and the strings Fatou derives from `E`. -/
structure Symbolic where
  /-- Julia `string(E)`, the input expression -/
  src : String
  /-- `E` compiled (`(z, c) ↦ E`) -/
  f : C64 → C64 → C64
  /-- the iterated map: `E`, or in Newton mode the Newton map -/
  F : C64 → C64 → C64
  /-- Julia `string` of the iterated map (REDUCE's Newton map as reproduced by `Fatou.CAS`) -/
  mapSrc : String
  /-- Newton mode -/
  newt : Bool
  /-- the multiplicity `m` (Julia's type kept for printing) -/
  m : Number
  /-- REDUCE's `latex(E)` for the PyPlot title (`string(E)` if the CAS cannot read `E`) -/
  latex : String

namespace Symbolic

open CAS

/-- The Newton map's expression and the LaTeX of `E`, from the CAS. -/
def derive (E : JExpr) (newt : Bool) (m : Number) : Except String (JExpr × String) := do
  let latex := match simp E with
    | .ok r => latexOf r
    | .error _ => E.toJulia
  if newt then
    let mq : QI :=
      let z := m.toC64
      ⟨ratOfFloat z.re, ratOfFloat z.im⟩
    let mq := match m with
      | .int n => QI.ofInt n
      | .complexInt a b => ⟨a, b⟩
      | _ => mq
    let F ← newtonRaphson E mq
    return (← factorJExpr F, latex)
  else return (E, latex)

/-- Build a map at run time from Julia source text: `E`, Newton mode and `m` (Julia syntax,
e.g. `"1 - 1im"`), and optionally REDUCE's Newton map to iterate instead of the CAS's (for a
bit-exact raster when REDUCE's form differs, see `Fatou.CAS`). The maps are interpreted. -/
def ofString (src : String) (newt : Bool := false) (m : String := "") (map : Option String := none) :
    Except String Symbolic := do
  let E ← JExpr.parse src
  let mv : Number ← if m.isEmpty then pure (if newt then .int 1 else .int 0)
    else pure (← Sym.constOf m).toNumber
  let (Fe, latex) ← derive E newt mv
  let Fe ← match map with
    | some s => JExpr.parse s
    | none => pure Fe
  let f := (← Sym.lower E).map
  let F := (← Sym.lower Fe).map
  return { src := E.toJulia, f, F, mapSrc := Fe.toJulia, newt, m := mv, latex }

/-! ### Front-ends (Julia `juliafill`, `mandelbrot`, `newton` with an `Expr`) -/

/-- Julia `juliafill(E; …)` (`src/Fatou.jl:203-222`) for a symbolic map. -/
@[inline] def juliafill (S : Symbolic) (o : Options := {}) (Q : C64 → C64 → Float := abs2Q)
    (C : C64 → Float → Float → Float := angleColor) (real : Option (Float → Float) := none) :
    Define :=
  let d := Fatou.juliafill S.F { o with label := S.src, latex := some (o.latex.getD S.latex) } Q C real
  { d with expr := some S.src }

/-- Julia `mandelbrot(E; …)` (`src/Fatou.jl:250-271`): Newton mode (with the multiplicity of
`S`) when `S` was built as a Newton map (`m ≠ 0`). -/
@[inline] def mandelbrot (S : Symbolic) (o : Options := {}) (Q : C64 → C64 → Float := abs2Q)
    (C : C64 → Float → Float → Float := mandelColor) (real : Option (Float → Float) := none) :
    Define :=
  if S.newt then
    let F := S.F
    let f := S.f
    { spec := { o with m := some S.m }.toSpec true true 4 0, label := S.src, latex := S.latex,
      F, Q := fun z c => (f z c).abs, C, real := real.getD fun x => (F ⟨x, 0⟩ ⟨0, 0⟩).re,
      expr := some S.src }
  else
    let d := Fatou.mandelbrot S.F { o with label := S.src, latex := some (o.latex.getD S.latex) } Q C none
      real
    { d with expr := some S.src }

/-- Julia `newton(E; …)` (`src/Fatou.jl:299-318`) for a symbolic Newton map. -/
@[inline] def newton (S : Symbolic) (o : Options := {}) (C : C64 → Float → Float → Float := angleColor)
    (mandel : Bool := false) (real : Option (Float → Float) := none) : Define :=
  let F := S.F
  let f := S.f
  { spec := { o with m := some S.m }.toSpec true mandel 0.01 1, label := S.src, latex := S.latex,
    F, Q := fun z c => (f z c).abs, C, real := real.getD fun x => (F ⟨x, 0⟩ ⟨0, 0⟩).re,
    expr := some S.src }

end Symbolic

/-! ## `basin` from the stored expression -/

/-- Julia `basin(K, j)` (`src/Fatou.jl:335`, `src/internals.jl:18-32`) of a set defined from
an expression: the LaTeX set notation of the `j`-th basin, whose body is the LaTeX of the
`j`-fold composition of the (Newton) map with `c := 0` (`nL`/`jL`), printed by `Fatou.CAS`
(Newton maps in REDUCE's `factor` form, the maps of `juliafill`/`mandelbrot` with `allfac`
grouping, so `j = 1` reproduces REDUCE; deeper compositions are the same function in the
CAS's expanded normal form). -/
def Define.basinOf (K : Define) (j : Nat) : Except String String := do
  if j == 0 then return basin K.spec.newt 0 ""
  let some src := K.expr | throw "basin: the set was not defined from an expression"
  let E ← JExpr.parse src
  let body ← if K.spec.newt then do
      let m := K.spec.m
      let mq : CAS.QI := match m with
        | .int n => CAS.QI.ofInt n
        | .complexInt a b => ⟨a, b⟩
        | _ => let z := m.toC64; ⟨CAS.ratOfFloat z.re, CAS.ratOfFloat z.im⟩
      let F ← CAS.newtonRaphson E mq
      pure (CAS.latexFactor (CAS.recomp F (CAS.RF.kern (.var "z")) j))
    else do
      let f ← CAS.simp E
      pure (CAS.latexAllfac (CAS.recomp f (CAS.RF.kern (.var "z")) j))
  return basin K.spec.newt j body

/-! ## Elaboration-time maps: `juliafill!`, `mandelbrot!`, `newton!` -/

namespace Sym

open Lean Meta Elab Term

/-- The `Float` constant `x` as a module-level literal (`JuliaBase.FloatLit`), so a specialized
kernel reads it as a plain global. -/
def floatExpr (x : Float) : TermElabM Expr :=
  JuliaBase.FloatLit.litConst "f64" ``Float ``Float.ofBits (toExpr x.toBits) x.toBits.toNat

/-- The `Int` literal expression. -/
def intExpr (n : Int) : Expr := toExpr n

/-- The Lean function implementing an operation. -/
def Fn.const : Fn → Name
  | .addRC => ``Fatou.Sym.addRC | .addCR => ``Fatou.Sym.addCR
  | .subCR => ``Fatou.Sym.subCR | .subRC => ``Fatou.Sym.subRC
  | .mulRC => ``Fatou.Sym.mulRC | .mulCR => ``Fatou.Sym.mulCR
  | .divCR => ``Fatou.Sym.divCR | .divRC => ``Fatou.Sym.divRC
  | .addCC => ``Fatou.Sym.addCC | .subCC => ``Fatou.Sym.subCC
  | .mulCC => ``Fatou.Sym.mulCC | .divCC => ``Fatou.Sym.divCC
  | .negC => ``Fatou.Sym.negC | .mulIC => ``Fatou.Sym.mulIC | .mulCI => ``Fatou.Sym.mulCI
  | .addRR => ``Fatou.Sym.addRR | .subRR => ``Fatou.Sym.subRR
  | .mulRR => ``Fatou.Sym.mulRR | .divRR => ``Fatou.Sym.divRR | .negR => ``Fatou.Sym.negR
  | .powLit _ => ``Fatou.Sym.powLit | .powInt _ => ``Fatou.Sym.powInt
  | .powCC => ``Fatou.Sym.powCC
  | .exp => ``C64.exp | .sin => ``C64.sin | .cos => ``C64.cos | .tan => ``C64.tan
  | .sinh => ``C64.sinh | .cosh => ``C64.cosh | .log => ``C64.log | .sqrt => ``C64.sqrt
  | .abs => ``C64.abs | .abs2 => ``C64.abs2 | .angle => ``C64.angle
  | .real => ``JuliaBase.Complex.re | .imag => ``JuliaBase.Complex.im

/-- The Lean term of a lowered map, in the free variables `z`, `c`. -/
partial def Low.toExpr (z c : Expr) : Low → TermElabM Expr
  | .z => return z
  | .c => return c
  | .rconst x => floatExpr x
  | .cconst a b => do return mkApp2 (Lean.mkConst ``C64.mk') (← floatExpr a) (← floatExpr b)
  | .op f args => do
    let as ← args.mapM (Low.toExpr z c)
    match f with
    | .powLit n | .powInt n => return mkApp2 (Lean.mkConst f.const) as[0]! (intExpr n)
    | .real | .imag => return mkApp2 (Lean.mkConst f.const [Level.zero]) (Lean.mkConst ``Float) as[0]!
    | _ => return mkAppN (Lean.mkConst f.const) as.toArray

/-- The lambda `fun (z c : C64) => E` of a Julia expression, as a term. -/
def mapExpr (E : JExpr) : TermElabM Expr := do
  let n ← match lower E with
    | .ok n => pure n
    | .error e => throwError "cannot compile {E.toJulia}: {e}"
  let c64 := Lean.mkConst ``C64
  withLocalDeclD `z c64 fun z => withLocalDeclD `c c64 fun c => do
    let body ← match n with
      | .const v => let w := v.toC64; pure (Low.cconst w.re w.im)
      | .cx l => pure l
      | .re l => pure (Low.op .addRC [l, .cconst 0 0])
    mkLambdaFVars #[z, c] (← Low.toExpr z c body)

/-- A `Number` literal term. -/
def numberExpr : Number → TermElabM Expr
  | .int n => return mkApp (Lean.mkConst ``Number.int) (toExpr n)
  | .float x => do return mkApp (Lean.mkConst ``Number.float) (← floatExpr x)
  | .complexInt a b => return mkApp2 (Lean.mkConst ``Number.complexInt) (toExpr a) (toExpr b)
  | .complexFloat a b => do return mkApp2 (Lean.mkConst ``Number.complexFloat) (← floatExpr a) (← floatExpr b)

/-- The `Symbolic` term for source `src`, Newton mode, multiplicity text `m` and an optional
REDUCE map text, all derived at elaboration time. -/
def symbolicExpr (src : String) (newt : Bool) (m : Option String) (map : Option String) :
    TermElabM Expr := do
  let E ← match JExpr.parse src with
    | .ok e => pure e
    | .error e => throwError "cannot parse {src}: {e}"
  let mv : Number ← match m with
    | some s => match constOf s with
      | .ok v => pure v.toNumber
      | .error e => throwError "m = {s}: {e}"
    | none => pure (if newt then .int 1 else .int 0)
  let (Fe, latex) ← match Symbolic.derive E newt mv with
    | .ok r => pure r
    | .error e => throwError "cannot derive the map of {src}: {e}"
  let Fe ← match map with
    | some s => match JExpr.parse s with
      | .ok e => pure e
      | .error e => throwError "cannot parse {s}: {e}"
    | none => pure Fe
  let f ← mapExpr E
  let F ← mapExpr Fe
  return mkAppN (Lean.mkConst ``Symbolic.mk)
    #[toExpr E.toJulia, f, F, toExpr Fe.toJulia, toExpr newt, ← numberExpr mv, toExpr latex]

/-- `juliafill! "z^2 + c" opts`: Julia `juliafill(:(z^2 + c); opts…)`, the map compiled at
elaboration time. -/
syntax (name := juliafillBang) "juliafill! " str (ppSpace term:max)? : term
/-- `mandelbrot! "z^2 + c" opts`, or `mandelbrot! "z^3 - 1" (m := "1") opts` for Julia's Newton
switch (`m ≠ 0`). -/
syntax (name := mandelbrotBang) "mandelbrot! " str (" (" ident " := " str ")")* (ppSpace term:max)? :
  term
/-- `newton! "z^3 - 1" opts`, `newton! "sin(z) - 1" (m := "1 - 1im") opts`: Julia
`newton(E; m, opts…)`, the Newton map derived by `Fatou.CAS` and compiled at elaboration time.
`(map := "…")` iterates the given Julia expression instead (e.g. REDUCE's own form). -/
syntax (name := newtonBang) "newton! " str (" (" ident " := " str ")")* (ppSpace term:max)? : term
/-- `symbolic! "E"` / `symbolic! "E" (m := "m")`: the `Symbolic` value itself (Newton mode when
`m` is given). -/
syntax (name := symbolicBang) "symbolic! " str (" (" ident " := " str ")")* : term

/-- The value of `(key := "…")` among the repeated groups `s` (each group's five nodes, nested
or flattened). -/
def groupStr? (s : Syntax) (key : String) : Option String :=
  let flat : Array Syntax := s.getArgs.flatMap fun g => if g.getNumArgs == 5 then g.getArgs else #[g]
  (List.range (flat.size / 5)).findSome? fun k =>
    if flat[5 * k + 1]!.getId.toString == key then flat[5 * k + 3]!.isStrLit? else none

/-- Reject keys other than `m` and `map`. -/
def checkKeys (s : Syntax) (allowed : List String) : TermElabM Unit := do
  let flat : Array Syntax := s.getArgs.flatMap fun g => if g.getNumArgs == 5 then g.getArgs else #[g]
  for k in List.range (flat.size / 5) do
    let key := flat[5 * k + 1]!.getId.toString
    unless allowed.contains key do throwErrorAt flat[5 * k + 1]! "unknown option {key}"


/-- The options argument, or `{}`. -/
def optsTerm (s : Syntax) : TermElabM Term := do
  match s.getOptional? with
  | some t => return ⟨t⟩
  | none => `(({} : Fatou.Options))

@[term_elab juliafillBang] def elabJuliafill : TermElab := fun stx ty => do
  let S ← exprToSyntax (← symbolicExpr stx[1].isStrLit?.get! false none none)
  elabTerm (← `(Fatou.Symbolic.juliafill $S $(← optsTerm stx[2]))) ty

@[term_elab mandelbrotBang] def elabMandelbrot : TermElab := fun stx ty => do
  checkKeys stx[2] ["m"]
  let m := groupStr? stx[2] "m"
  let S ← exprToSyntax (← symbolicExpr stx[1].isStrLit?.get! m.isSome m none)
  elabTerm (← `(Fatou.Symbolic.mandelbrot $S $(← optsTerm stx[3]))) ty

@[term_elab newtonBang] def elabNewton : TermElab := fun stx ty => do
  checkKeys stx[2] ["m", "map"]
  let S ← exprToSyntax
    (← symbolicExpr stx[1].isStrLit?.get! true (groupStr? stx[2] "m") (groupStr? stx[2] "map"))
  elabTerm (← `(Fatou.Symbolic.newton $S $(← optsTerm stx[3]))) ty

@[term_elab symbolicBang] def elabSymbolic : TermElab := fun stx _ => do
  checkKeys stx[2] ["m"]
  let m := groupStr? stx[2] "m"
  symbolicExpr stx[1].isStrLit?.get! m.isSome m none

end Sym

end Fatou

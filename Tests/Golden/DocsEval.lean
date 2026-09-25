import Tests.Golden.DocsParse
import Tests.Golden.GrassmannDynamic
import Tests.Golden.Space
import Grassmann.Dynamic

/-!
# Replaying the docs statements on the dynamic layer

The interpreter behind `Tests.Golden.Docs`: it evaluates the statements parsed by
`Tests.Golden.DocsParse` in a per-shard environment (Julia's sandbox module), with Julia's
semantics for numbers (`Int64`, `Rational`, `Float64`, `Complex`, `Bool`, `π`), spaces
(`S"…"`, `ℝ^n`, `Submanifold(n)`, `Λ(V)`, `tangent`, `⊕`, `'`) and algebra elements, which
are `Grassmann.TA` values with their Julia coefficient type (`Dyn.AnyTA`). Every operator and
function maps onto the dynamic API (`TA.mul`, `TA.wedge`, `TA.exp`, `TA.inv?`, `TA.powInt`,
…); the result is encoded with its Julia kind, `V`, dense values and printed forms, and
Julia's composite displays (tuples, vectors, `typeof`, bases, function objects) are
reproduced as strings.

The interpreter is conservative: a construct it does not model (matrices, operators,
calculus, closures' displays, …) raises an error, the statement counts as unimplemented,
and so does every later statement that uses its result.
-/

namespace Tests.ElementOracle.Docs

open Grassmann DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase
  Tests.ElementOracle Tests.ElementOracle.Dyn

/-! ## Numbers -/

/-- A Julia number. -/
inductive Num where
  /-- `Int64`. -/
  | int (k : Int)
  /-- `Rational{Int64}`. -/
  | rat (q : Rat)
  /-- `Float64`. -/
  | float (x : Float)
  /-- `Complex{Int64}`. -/
  | cint (re im : Int)
  /-- `Complex{Float64}`. -/
  | cfloat (re im : Float)
  /-- `Bool`. -/
  | bool (b : Bool)
  /-- `π` (an `Irrational`: exact until it meets arithmetic). -/
  | pi
  deriving Inhabited

namespace Num

/-- The value as a `Float64` (real part). -/
def toFloat : Num → Float
  | int k => Float.ofInt k
  | rat q => F64.ofRat q
  | float x => x
  | cint re _ => Float.ofInt re
  | cfloat re _ => re
  | bool b => if b then 1 else 0
  | pi => F64.pi

/-- Julia's coefficient type. -/
def T : Num → CoeffType
  | int _ => .int64
  | rat _ => .rational
  | float _ | pi => .float64
  | cint .. => .complex .int64
  | cfloat .. => .complex .float64
  | bool _ => .bool

/-- Julia `show(x)` (`compact`: `:compact => true`). -/
def showJ (compact : Bool) : Num → String
  | int k => toString k
  | rat q => toString q.num ++ "//" ++ toString q.den
  | float x => JuliaShow.showIO compact x
  | cint re im => JuliaShow.showIO compact (⟨re, im⟩ : Complex Int)
  | cfloat re im => JuliaShow.showIO compact (⟨re, im⟩ : Complex Float)
  | bool b => if b then "true" else "false"
  | pi => "π"

/-- Convert to coefficient type `t` (Julia `promote`); `none` for a demotion. -/
def lift (t : CoeffType) (x : Num) : Option Num :=
  match t, x with
  | .int64, int k => some (int k)
  | .int64, bool b => some (int (if b then 1 else 0))
  | .rational, int k => some (rat k)
  | .rational, rat q => some (rat q)
  | .float64, int k => some (float (Float.ofInt k))
  | .float64, rat q => some (float (F64.ofRat q))
  | .float64, float f => some (float f)
  | .float64, pi => some (float F64.pi)
  | .complex .int64, int k => some (cint k 0)
  | .complex .int64, cint a b => some (cint a b)
  | .complex .float64, int k => some (cfloat (Float.ofInt k) 0)
  | .complex .float64, float f => some (cfloat f 0)
  | .complex .float64, pi => some (cfloat F64.pi 0)
  | .complex .float64, cint a b => some (cfloat (Float.ofInt a) (Float.ofInt b))
  | .complex .float64, cfloat a b => some (cfloat a b)
  | _, _ => none

/-- The promoted type of two numbers (`π` is a `Float64` in arithmetic). -/
def promoteT (a b : Num) : Option CoeffType := CoeffType.promote a.T b.T

/-- Both numbers at their promoted type. -/
def both (a b : Num) : Option (Num × Num) := do
  let t ← promoteT a b
  return (← a.lift t, ← b.lift t)

/-- Julia `a + b`, `a - b`, `a * b` on numbers. -/
def arith (op : String) (a b : Num) : Option Num := do
  match ← both a b with
  | (int x, int y) => match op with
    | "+" => some (int (x + y)) | "-" => some (int (x - y)) | "*" => some (int (x * y)) | _ => none
  | (rat x, rat y) => match op with
    | "+" => some (rat (x + y)) | "-" => some (rat (x - y)) | "*" => some (rat (x * y)) | _ => none
  | (float x, float y) => match op with
    | "+" => some (float (x + y)) | "-" => some (float (x - y)) | "*" => some (float (x * y)) | _ => none
  | (cint a b, cint c d) => match op with
    | "+" => some (cint (a + c) (b + d)) | "-" => some (cint (a - c) (b - d))
    | "*" => some (cint (a * c - b * d) (a * d + b * c)) | _ => none
  | (cfloat a b, cfloat c d) => match op with
    | "+" => some (cfloat (a + c) (b + d)) | "-" => some (cfloat (a - c) (b - d))
    | "*" => some (cfloat (a * c - b * d) (a * d + b * c)) | _ => none
  | _ => none

/-- Julia `a / b` (`Int/Int` is a `Float64`). -/
def fdiv (a b : Num) : Option Num :=
  match a, b with
  | cint .., _ | _, cint .. | cfloat .., _ | _, cfloat .. => none
  | _, _ => some (float (a.toFloat / b.toFloat))

/-- Julia `-x`. -/
def neg : Num → Option Num
  | int k => some (int (-k)) | rat q => some (rat (-q)) | float x => some (float (-x))
  | cint a b => some (cint (-a) (-b)) | cfloat a b => some (cfloat (-a) (-b))
  | pi => some (float (-F64.pi)) | bool _ => none

/-- Whether the number is zero (Julia `iszero`). -/
def isZero : Num → Bool
  | int k => k == 0 | rat q => q == 0 | float x => x == 0 | cint a b => a == 0 && b == 0
  | cfloat a b => a == 0 && b == 0 | bool b => !b | pi => false

/-- The number as an `Int`, if it is one. -/
def toInt? : Num → Option Int
  | int k => some k
  | bool b => some (if b then 1 else 0)
  | _ => none

end Num

/-! ## Values -/

/-- A Julia value of the docs sandbox. -/
inductive Val where
  /-- A number. -/
  | num (n : Num)
  /-- An algebra element of `V`; `hdl` is Julia's display of its space (the handle, or a
  subspace `⟨1__1⟩` of `V` spanned by `mask`). -/
  | elem (V : TensorBundle) (hdl : String) (mask : UInt64) (x : AnyTA V)
  /-- A space: a bare `Signature`/`DiagonalForm` (`sub = false`, Julia kind `Other`) or a
  `Submanifold` of `V` spanned by `mask` (kind `Space`). -/
  | space (V : TensorBundle) (mask : UInt64) (sub : Bool)
  /-- A basis object `Λ(V)` (`DirectSum.Basis`), of the subspace `mask`. -/
  | basis (V : TensorBundle) (mask : UInt64)
  /-- A tuple. -/
  | tuple (xs : Array Val)
  /-- A Julia `Vector`. -/
  | vec (xs : Array Val)
  /-- A `Values`/`Vector` of numbers (`[1, 2, 3]`). -/
  | values (xs : Array Num)
  /-- A type constructor with parameters (`Chain{V,1}`). -/
  | ctor (name : String) (params : Array Val)
  /-- A built-in function or operator used as a value. -/
  | fn (name : String)
  /-- A user function `name(params) = body`. -/
  | user (name : String) (params : Array String) (body : Expr)
  /-- A closure `params -> body` with the variables it captured. -/
  | closure (params : Array String) (body : Expr) (env : List (String × Val))
  /-- Julia `nothing`. -/
  | nothing
  /-- A value whose display is known but which the interpreter cannot compute with. -/
  | opaque (display : String)
  deriving Inhabited

/-- The sandbox state: the variables and the sandbox number (`Main.DocSandbox{n}`). -/
structure Env where
  /-- Variables. -/
  vars : Std.HashMap String Val := {}
  /-- The shard's number (the sandbox module `Main.DocSandbox{n}`). -/
  sandbox : Nat := 0
  /-- Recursion budget for user functions. -/
  fuel : Nat := 64

/-- The evaluation monad. -/
abbrev EvalM := StateT Env (Except String)

/-- Fail (the statement is unimplemented). -/
def unsupported {β : Type} (what : String) : EvalM β := throw what

/-- Look a variable up. -/
def getVar (x : String) : EvalM Val := do
  match (← get).vars.get? x with
  | some v => return v
  | none => unsupported s!"unbound {x}"

/-- Bind a variable. -/
def setVar (x : String) (v : Val) : EvalM Unit :=
  modify fun e => { e with vars := e.vars.insert x v }

/-! ## Spaces -/

/-- Julia space equality (`ℝ^3 == V"+++" == Manifold(3)`): same generator count, metric and
options, an `Int` manifold being the Euclidean signature. -/
def spaceEq (V W : TensorBundle) : Bool :=
  let norm := fun (X : TensorBundle) =>
    match X.metric with
    | .euclid => { X with metric := .signature 0 }
    | _ => X
  norm V == norm W

/-- The space of a value (`Manifold(x)`). -/
def spaceOf? : Val → Option (TensorBundle × UInt64)
  | .elem V _ m _ => some (V, m)
  | .space V m _ => some (V, m)
  | .basis V m => some (V, m)
  | .num (.int n) => some (TensorBundle.euclidean n.toNat, lowMask n.toNat)
  | _ => none

/-- A bare space value. -/
def bare (V : TensorBundle) : Val := .space V (lowMask V.n) false

/-- A `Submanifold` value (the full space). -/
def subOf (V : TensorBundle) : Val := .space V (lowMask V.n) true

/-- A fresh element of the full space `V`. -/
def mkElem (V : TensorBundle) (x : AnyTA V) : Val := .elem V V.showHandle (lowMask V.n) x

/-! ## Elements -/

/-- The unit blade `b` (Julia `Submanifold`, `One` for the scalar) as an `Int` element. -/
def bladeVal (V : TensorBundle) (hdl : String) (mask b : UInt64) : Val :=
  .elem V hdl mask (.int (TA.ofBlade b))

/-- Julia's value-free blade-level result as an element (`Λ(3).v21 = -1v₁₂`). -/
def ofBladeResult (V : TensorBundle) (hdl : String) (mask : UInt64) (r : BladeResult) : Val :=
  .elem V hdl mask (.int (TA.ofBladeResult r))

/-- A number as the scalar term `n·One(V)`. -/
def numTA (V : TensorBundle) : Num → Option (AnyTA V)
  | .int k => some (.int (.single 0 k))
  | .rat q => some (.rat (.single 0 q))
  | .float x => some (.float (.single 0 x))
  | .pi => some (.float (.single 0 F64.pi))
  | .cint a b => some (.cint (.single 0 ⟨a, b⟩))
  | .cfloat a b => some (.cfloat (.single 0 ⟨a, b⟩))
  | .bool b => some (.bool (.single 0 (b : Bool)))

/-- Apply `f x s` to an element and a number at their promoted coefficient type. -/
def withNumber {V : TensorBundle} (x : AnyTA V) (n : Num) (t? : Option CoeffType := none)
    (f : {α : Type} → [Coeff α] → [JuliaShow α] → [OracleScalar α] → TA V α → α → TA V α) :
    Option (AnyTA V) := do
  let s ← numTA V n
  let T ← t? <|> CoeffType.promote x.T s.T
  match ← x.promoteTo T, ← s.promoteTo T with
  | .int x, .int (.single _ k) => pure (.int (f x k))
  | .rat x, .rat (.single _ k) => pure (.rat (f x k))
  | .float x, .float (.single _ k) => pure (.float (f x k))
  | .cint x, .cint (.single _ k) => pure (.cint (f x k))
  | .cfloat x, .cfloat (.single _ k) => pure (.cfloat (f x k))
  | _, _ => none

/-- A binary operation at a common type. -/
def bin2 {V : TensorBundle} (a b : AnyTA V) (f : BinTA V) (t? : Option CoeffType := none) :
    Option (AnyTA V) := do
  let T ← t? <|> CoeffType.promote a.T b.T
  a.bin T f b

/-- An element's coefficients as `Float64` (Julia's `float`, for `/`, `inv`, `exp`, …);
complex elements are not supported by the composite functions. -/
def toF {V : TensorBundle} (x : AnyTA V) : Option (TA V Float) :=
  match x.promoteTo .float64 with
  | some (.float y) => some y
  | _ => none

/-- An element with `Float64` coefficients or exact rationals (for division): Julia's `/`
turns `Int64` into `Float64`. -/
def forDiv {V : TensorBundle} (x : AnyTA V) : Option (AnyTA V) :=
  match x with
  | .int _ | .bool _ => x.promoteTo .float64
  | .cint _ => x.promoteTo (.complex .float64)
  | _ => some x

/-- Julia `a - b` of two elements (see `Tests.Golden.GrassmannEval.arithEval`: the term-term
container branches convert before negating). -/
def elemSub {V : TensorBundle} (a b : AnyTA V) : Option (AnyTA V) := do
  let T ← CoeffType.promote a.T b.T
  let sum := fun (b : AnyTA V) => bin2 a b (fun x y => TA.add x y) (some T)
  let pre ← sum (b.un fun y => TA.neg y)
  if a.isTerm && b.isTerm && pre.isContainer then
    (b.promoteTo T).bind fun b' => sum (b'.un fun y => TA.neg y)
  else pure pre

/-- An element's dense `Float64` coefficients through `TA`. -/
def floatVal {V : TensorBundle} (x : AnyTA V) : Option (TA V Float) := toF x

/-- Apply a `TA V Float` function to an element (after Julia's `float`). -/
def viaFloat {V : TensorBundle} (x : AnyTA V) (f : TA V Float → Option (TA V Float)) : Option (AnyTA V) := do
  return .float (← f (← toF x))

/-! ## Evaluation -/

/-- Blade names bound by `@basis` (pretty and ASCII labels, Julia `labels(V)`). -/
def bladeNames (V : TensorBundle) (b : UInt64) : List String :=
  let p := V.bladeLabel b
  let a := V.bladeLabel b (label := true)
  if p == a then [p] else [p, a]

/-- Julia `@basis V` (`@basis V E e` names the space `E` and the blades `e…`): binds the
space (`Submanifold(V)`), `v` and every blade; its value is the tuple `(V, v, v₁, …)`. -/
def doBasis (V : TensorBundle) (spaceName : String := "V") (vec : Option String := none) : EvalM Val := do
  if V.n > 10 then unsupported "@basis of a large space"
  -- DirectSum labels the dual tangent generators of a mixed tangent space `ϵ¹` where Julia's
  -- basis tuple prints `ϵ₁` (integrator request, DirectSum `bladeLabel`)
  if V.istangent && V.isdyadic then unsupported "@basis of a mixed tangent space"
  setVar spaceName (subOf V)
  let hdl := V.showHandle
  let mut xs : Array Val := #[subOf V]
  for b in Leibniz.indexBasisAll V.n do
    let x := bladeVal V hdl (lowMask V.n) b
    xs := xs.push x
    for nm in bladeNames V b do
      let nm := match vec with
        | some e => (nm.replace "v" e)
        | none => nm
      setVar nm x
  return .tuple xs

/-- Parse a space string macro. -/
def spaceMacro (pfx body : String) : EvalM TensorBundle :=
  -- `D"0.3,2.4,1"` holds `Float64`s (Julia prints `1.0`); DirectSum keeps exact `Rat`s and
  -- prints `1` (integrator request, DirectSum `showDiagEntry`)
  if pfx == "D" && body.contains '.' then unsupported "mixed DiagonalForm display" else
  match pfx with
  | "S" => liftExcept (TensorBundle.parseSignature body)
  | "D" => liftExcept (TensorBundle.parseDiagonal body)
  | "V" => liftExcept (TensorBundle.parseBundle body)
  | _ => unsupported s!"string macro {pfx}"
where
  liftExcept {β : Type} : Except String β → EvalM β
    | .ok x => pure x
    | .error e => throw e

/-- Evaluate an expression that must be a space. -/
def asSpace : Val → EvalM (TensorBundle × UInt64)
  | v => match spaceOf? v with
    | some p => pure p
    | none => unsupported "space expected"

end Tests.ElementOracle.Docs

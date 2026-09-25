import Wilkinson.Expr
import Wilkinson.Range
import Wilkinson.JuliaMath

/-!
# Julia's numeric promotion, for evaluating expressions

SyntaxTree's `genfun` turns an `Expr` into a compiled Julia function; the
port interprets the tree instead. What must be preserved is *which arithmetic
runs where*: after `sub(BigFloat, e)` the literals are `BigFloat` but `x` is
still a `Float64`, so in `x^9 + 2` the power is a `Float64` power (it can
overflow to `Inf`) and only the addition is done in `BigFloat`. `JNum` is the
tagged number type and its operations follow Julia's `promote_rule`s:

`Int64 < Rational < Float32 < Float64 < BigFloat`,

with `Int / Int` producing `Float64`, `Int // Int` producing a `Rational`,
`Int64` arithmetic wrapping, and `x ^ k` for a literal `k` following
`literal_pow` for the base's type. The one deliberate deviation: `//` on floats
(a `MethodError` in Julia, which `sub` makes unavoidable) is division.
-/

namespace Wilkinson

open AbstractAnalysis

/-- A Julia number of one of the types Wilkinson evaluates in. -/
inductive JNum where
  /-- `Int64` (wrapping). -/
  | int (v : Int64)
  /-- `Rational{Int}` (kept exact). -/
  | rat (v : Rat)
  /-- `Float32`. -/
  | f32 (v : Float32)
  /-- `Float64`. -/
  | f64 (v : Float)
  /-- `BigFloat` (256 bits). -/
  | big (v : Big)
  deriving Inhabited

namespace JNum

/-- Promotion rank. -/
def rank : JNum → Nat
  | .int _ => 0 | .rat _ => 1 | .f32 _ => 2 | .f64 _ => 3 | .big _ => 4

/-- Julia `Float64(x)`. -/
def toF64 : JNum → Float
  | .int v => Float.ofInt v.toInt
  | .rat q => Float.ofInt q.num / Float.ofInt q.den
  | .f32 v => v.toFloat
  | .f64 v => v
  | .big v => v.toFloat

/-- Julia `Float32(x)`. -/
def toF32 : JNum → Float32
  | .int v => Float32.ofInt v.toInt
  | .rat q => Float32.ofInt q.num / Float32.ofInt q.den
  | .f32 v => v
  | .f64 v => v.toFloat32
  | .big v => v.toFloat32

/-- Julia `BigFloat(x)`. -/
def toBig : JNum → Big
  | .int v => BigFloat.ofInt 256 v.toInt
  | .rat q => BigFloat.ofRat 256 q
  | .f32 v => BigFloat.ofFloat32 256 v
  | .f64 v => BigFloat.ofFloat 256 v
  | .big v => v

/-- Julia `Rational(x)` for integers/rationals. -/
def toRat : JNum → Rat
  | .int v => v.toInt
  | .rat q => q
  | x => (IEEEFloat.toRat? x.toF64).getD 0

/-- Apply a binary operation after promoting both operands to the larger type. -/
@[inline] def lift (x y : JNum) (fi : Int64 → Int64 → JNum) (fq : Rat → Rat → JNum)
    (f32 : Float32 → Float32 → Float32) (f64 : Float → Float → Float) (fb : Big → Big → Big) : JNum :=
  match max x.rank y.rank with
  | 0 => match x, y with | .int a, .int b => fi a b | _, _ => .f64 0
  | 1 => fq x.toRat y.toRat
  | 2 => .f32 (f32 x.toF32 y.toF32)
  | 3 => .f64 (f64 x.toF64 y.toF64)
  | _ => .big (fb x.toBig y.toBig)

instance : Add JNum := ⟨fun x y => lift x y (fun a b => .int (a + b)) (fun a b => .rat (a + b)) (· + ·) (· + ·) (· + ·)⟩
instance : Sub JNum := ⟨fun x y => lift x y (fun a b => .int (a - b)) (fun a b => .rat (a - b)) (· - ·) (· - ·) (· - ·)⟩
instance : Mul JNum := ⟨fun x y => lift x y (fun a b => .int (a * b)) (fun a b => .rat (a * b)) (· * ·) (· * ·) (· * ·)⟩

/-- Julia `/`: `Int / Int` is a `Float64` division. -/
instance : Div JNum := ⟨fun x y => lift x y (fun a b => .f64 (Float.ofInt a.toInt / Float.ofInt b.toInt))
  (fun a b => if b == 0 then .f64 (if a == 0 then 0 / 0 else if a > 0 then 1 / 0 else -1 / 0) else .rat (a / b))
  (· / ·) (· / ·) (· / ·)⟩

/-- Julia `//`: exact on integers and rationals, plain division on floats. -/
def rdiv (x y : JNum) : JNum :=
  lift x y (fun a b => if b == 0 then .f64 (1 / 0) else .rat ((a.toInt : Rat) / (b.toInt : Rat)))
    (fun a b => if b == 0 then .f64 (1 / 0) else .rat (a / b)) (· / ·) (· / ·) (· / ·)

/-- Unary minus. -/
instance : Neg JNum := ⟨fun
  | .int v => .int (-v) | .rat q => .rat (-q) | .f32 v => .f32 (-v) | .f64 v => .f64 (-v) | .big v => .big (-v)⟩

/-- Julia `abs`. -/
def abs : JNum → JNum
  | .int v => .int (if v < 0 then -v else v)
  | .rat q => .rat (if q < 0 then -q else q)
  | .f32 v => .f32 v.abs
  | .f64 v => .f64 v.abs
  | .big v => .big v.abs

/-- Julia `Int64 ^ Int` (`power_by_squaring`, wrapping; `DomainError` for negative
exponents of bases other than `±1`, reported as `NaN`). -/
def intPow (a : Int64) (k : Int) : JNum :=
  if k ≥ 0 then .int (go a 1 k.toNat 64)
  else if a == 1 then .int 1 else if a == -1 then .int (if k % 2 == 0 then 1 else -1) else .f64 (0 / 0)
where
  /-- Square and multiply. -/
  go (b acc : Int64) (e : Nat) : Nat → Int64
    | 0 => acc
    | fuel + 1 => if e = 0 then acc else go (b * b) (if e % 2 == 1 then acc * b else acc) (e / 2) fuel

/-- Julia `x ^ k` for a literal integer exponent (`literal_pow`, by base type). -/
def powLit (x : JNum) (k : Int) : JNum :=
  match x with
  | .int a => intPow a k
  | .rat q => .rat (if k ≥ 0 then q ^ k.toNat else 1 / q ^ k.natAbs)
  | .f32 v => .f32 (literalPow32 v k)
  | .f64 v => .f64 (literalPow v k)
  | .big v => .big (v.powInt k)

/-- Julia `^(x::Float64, y::Float64)` (base/special/pow.jl:5-30): `1.0` for `x == 1`,
the compensated integer power when `y` is an integer in `pow_body`'s range, and
otherwise the C library `pow` (Julia's own `log`/`exp` kernel agrees to an ulp). -/
def powF64 (x y : Float) : Float :=
  if x == 1 then 1
  else if y.isFinite && y.floor == y && y.abs ≤ 24576 then
    let n : Int := if y ≥ 0 then y.toUInt64.toNat else -(((-y).toUInt64.toNat : Nat) : Int)
    if n == 0 then 1 else if -4096 ≤ n ∧ n ≤ 24576 then powBody x n else Float.pow x y
  else Float.pow x y

/-- Julia `x ^ y` for a computed exponent: integer exponents as `^(x, n::Integer)`,
float exponents as `^(::Float64, ::Float64)`. -/
def pow (x y : JNum) : JNum :=
  match y with
  | .int k => match x with
    | .f64 v => .f64 (powInt v k.toInt)
    | .f32 v => .f32 (powInt32 v k.toInt)
    | _ => powLit x k.toInt
  | _ => .f64 (powF64 x.toF64 y.toF64)

/-- Julia `log` by type: Julia's own `Float64`/`Float32` kernels, `BigFloat` in
`BigFloat`; integers and rationals convert to `Float64` first. -/
def log : JNum → JNum
  | .f32 v => .f32 (JuliaMath.log32 v)
  | .big v => .big v.log
  | x => .f64 (JuliaMath.log x.toF64)

/-- Is the value `+Inf`? (Julia `p[k] == Inf`.) -/
def isPosInf : JNum → Bool
  | .f32 v => v.isInf && v > 0
  | .f64 v => v.isInf && v > 0
  | .big (.inf false) => true
  | _ => false

/-- Literal to number. -/
def ofLit : Lit → JNum
  | .int v => .int (Int64.ofInt v)
  | .f64 v => .f64 v
  | .f32 v => .f32 v
  | .big v => .big v

end JNum

end Wilkinson

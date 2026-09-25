import Wilkinson.Expr
import Wilkinson.Range
import JuliaBase.Math

/-!
# Julia's numeric promotion, for evaluating expressions

SyntaxTree's `genfun` turns an `Expr` into a compiled Julia function; the
port interprets the tree instead. What must be preserved is *which arithmetic
runs where*: after `sub(BigFloat, e)` the literals are `BigFloat` but `x` is
still a `Float64`, so in `x^9 + 2` the power is a `Float64` power (it can
overflow to `Inf`) and only the addition is done in `BigFloat`. `JNum` is the
tagged number type and its operations follow Julia's `promote_rule`s:

`Int64 < Int128 < BigInt < Rational < Float32 < Float64 < BigFloat`,

except that `BigInt` meets a hardware float in `BigFloat`; `Int / Int` produces
`Float64` (`BigFloat` for `BigInt`), `Int // Int` a `Rational`, `Int64`/`Int128`
arithmetic wraps, and `x ^ k` for a literal `k` follows `literal_pow` for the
base's type. `Int128`/`BigInt` appear because REDUCE's large integers reach Julia
as `@int128_str`/`@big_str` literals, which `SyntaxTree.sub` leaves unconverted. The one deliberate deviation: `//` on floats
(a `MethodError` in Julia, which `sub` makes unavoidable) is division.
-/

namespace Wilkinson

open JuliaBase

/-- A Julia number of one of the types Wilkinson evaluates in. -/
inductive JNum where
  /-- `Int64` (wrapping). -/
  | int (v : Int64)
  /-- `Int128` (wrapping; REDUCE's integers beyond `Int64` parse as `Int128` literals). -/
  | i128 (v : Int)
  /-- `BigInt` (literals beyond `Int128`). -/
  | bigint (v : Int)
  /-- `Rational{…}` (kept exact). -/
  | rat (v : Rat)
  /-- `Float32`. -/
  | f32 (v : Float32)
  /-- `Float64`. -/
  | f64 (v : Float)
  /-- `BigFloat` (256 bits). -/
  | big (v : Big)
  deriving Inhabited

namespace JNum

/-- Type code: `Int64 < Int128 < BigInt < Rational < Float32 < Float64 < BigFloat`. -/
def kind : JNum → Nat
  | .int _ => 0 | .i128 _ => 1 | .bigint _ => 2 | .rat _ => 3 | .f32 _ => 4 | .f64 _ => 5 | .big _ => 6

/-- Julia `promote_type` on type codes: the larger type, except that `BigInt`
with a hardware float promotes to `BigFloat`. -/
def promoteKind (a b : Nat) : Nat :=
  if (a == 2 && (b == 4 || b == 5)) || (b == 2 && (a == 4 || a == 5)) then 6 else max a b

/-- Two's-complement wraparound to 128 bits. -/
def wrap128 (v : Int) : Int := (v + 2 ^ 127) % (2 ^ 128 : Int) - 2 ^ 127

/-- The integer value of an integer kind (`0` otherwise). -/
def toInt : JNum → Int
  | .int v => v.toInt | .i128 v => v | .bigint v => v | _ => 0

/-- Julia `Float64(x)` (correctly rounded for wide integers). -/
def toF64 : JNum → Float
  | .int v => Float.ofInt v.toInt
  | .i128 v | .bigint v => IEEEFloat.ofRat Float v
  | .rat q => Float.ofInt q.num / Float.ofInt q.den
  | .f32 v => v.toFloat
  | .f64 v => v
  | .big v => v.toFloat

/-- Julia `Float32(x)`. -/
def toF32 : JNum → Float32
  | .int v => Float32.ofInt v.toInt
  | .i128 v | .bigint v => IEEEFloat.ofRat Float32 v
  | .rat q => Float32.ofInt q.num / Float32.ofInt q.den
  | .f32 v => v
  | .f64 v => v.toFloat32
  | .big v => v.toFloat32

/-- Julia `BigFloat(x)`. -/
def toBig : JNum → Big
  | .int v => BigFloat.ofInt 256 v.toInt
  | .i128 v | .bigint v => BigFloat.ofInt 256 v
  | .rat q => BigFloat.ofRat 256 q
  | .f32 v => BigFloat.ofFloat32 256 v
  | .f64 v => BigFloat.ofFloat 256 v
  | .big v => v

/-- Julia `Rational(x)`. -/
def toRat : JNum → Rat
  | .int v => v.toInt
  | .i128 v | .bigint v => v
  | .rat q => q
  | x => (IEEEFloat.toRat? x.toF64).getD 0

/-- An integer result in the given integer kind (wrapping for the fixed widths). -/
def ofIntKind (k : Nat) (v : Int) : JNum :=
  match k with
  | 0 => .int (Int64.ofInt v)
  | 1 => .i128 (wrap128 v)
  | _ => .bigint v

/-- Apply a binary operation after promoting both operands (Julia `promote`). -/
@[inline] def lift (x y : JNum) (fi : Int → Int → JNum) (fq : Rat → Rat → JNum)
    (f32 : Float32 → Float32 → Float32) (f64 : Float → Float → Float) (fb : Big → Big → Big) : JNum :=
  match promoteKind x.kind y.kind with
  | 0 | 1 | 2 => fi x.toInt y.toInt
  | 3 => fq x.toRat y.toRat
  | 4 => .f32 (f32 x.toF32 y.toF32)
  | 5 => .f64 (f64 x.toF64 y.toF64)
  | _ => .big (fb x.toBig y.toBig)

/-- An integer operation, wrapped to the promoted integer kind. -/
@[inline] def liftI (x y : JNum) (op : Int → Int → Int) (fq : Rat → Rat → Rat)
    (f32 : Float32 → Float32 → Float32) (f64 : Float → Float → Float) (fb : Big → Big → Big) : JNum :=
  let k := promoteKind x.kind y.kind
  lift x y (fun a b => ofIntKind k (op a b)) (fun a b => .rat (fq a b)) f32 f64 fb

instance : Add JNum := ⟨fun x y => liftI x y (· + ·) (· + ·) (· + ·) (· + ·) (· + ·)⟩
instance : Sub JNum := ⟨fun x y => liftI x y (· - ·) (· - ·) (· - ·) (· - ·) (· - ·)⟩
instance : Mul JNum := ⟨fun x y => liftI x y (· * ·) (· * ·) (· * ·) (· * ·) (· * ·)⟩

/-- Julia `/`: integers divide as floats (`Float64`, or `BigFloat` for `BigInt`). -/
instance : Div JNum := ⟨fun x y =>
  let k := promoteKind x.kind y.kind
  lift x y (fun _ _ => if k == 2 then .big (x.toBig / y.toBig) else .f64 (x.toF64 / y.toF64))
    (fun a b => if b == 0 then .f64 (if a == 0 then 0 / 0 else if a > 0 then 1 / 0 else -1 / 0) else .rat (a / b))
    (· / ·) (· / ·) (· / ·)⟩

/-- Julia `//`: exact on integers and rationals, plain division on floats. -/
def rdiv (x y : JNum) : JNum :=
  lift x y (fun a b => if b == 0 then .f64 (1 / 0) else .rat ((a : Rat) / (b : Rat)))
    (fun a b => if b == 0 then .f64 (1 / 0) else .rat (a / b)) (· / ·) (· / ·) (· / ·)

/-- Unary minus. -/
instance : Neg JNum := ⟨fun
  | .int v => .int (-v) | .i128 v => .i128 (wrap128 (-v)) | .bigint v => .bigint (-v) | .rat q => .rat (-q)
  | .f32 v => .f32 (-v) | .f64 v => .f64 (-v) | .big v => .big (-v)⟩

/-- Julia `abs`. -/
def abs : JNum → JNum
  | .int v => .int (if v < 0 then -v else v)
  | .i128 v => .i128 (wrap128 v.natAbs)
  | .bigint v => .bigint v.natAbs
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
  | .i128 a | .bigint a =>
    if k ≥ 0 then ofIntKind x.kind (a ^ k.toNat)
    else if a == 1 then ofIntKind x.kind 1
    else if a == -1 then ofIntKind x.kind (if k % 2 == 0 then 1 else -1) else .f64 (0 / 0)
  | .rat q => .rat (if k ≥ 0 then q ^ k.toNat else 1 / q ^ k.natAbs)
  | .f32 v => .f32 (F32.literalPow v k)
  | .f64 v => .f64 (F64.literalPow v k)
  | .big v => .big (v.powInt k)

/-- Julia `^(x::Float64, y::Float64)` (base/special/pow.jl:7-30), Julia's own kernel
(`JuliaBase.F64.pow`). -/
def powF64 (x y : Float) : Float := F64.pow x y

/-- Julia `x ^ y` for a computed exponent: integer exponents as `^(x, n::Integer)`,
float exponents as `^(::Float64, ::Float64)`. -/
def pow (x y : JNum) : JNum :=
  match y with
  | .int _ | .i128 _ | .bigint _ => match x with
    | .f64 v => .f64 (F64.powInt v y.toInt)
    | .f32 v => .f32 (F32.powInt v y.toInt)
    | _ => powLit x y.toInt
  | _ => .f64 (powF64 x.toF64 y.toF64)

/-- Julia `log` by type: Julia's own `Float64`/`Float32` kernels, `BigFloat` in
`BigFloat`; integers and rationals convert to `Float64` first. -/
def log : JNum → JNum
  | .f32 v => .f32 (F32.log v)
  | .big v => .big v.log
  | .bigint v => .big (BigFloat.log (BigFloat.ofInt 256 v))
  | x => .f64 (F64.log x.toF64)

/-- Is the value `+Inf`? (Julia `p[k] == Inf`.) -/
def isPosInf : JNum → Bool
  | .f32 v => v.isInf && v > 0
  | .f64 v => v.isInf && v > 0
  | .big (.inf false) => true
  | _ => false

/-- Literal to number. -/
def ofLit : Lit → JNum
  | .int v => .int (Int64.ofInt v)
  | .bigint v => if -(2 ^ 127 : Int) ≤ v ∧ v < 2 ^ 127 then .i128 v else .bigint v
  | .f64 v => .f64 v
  | .f32 v => .f32 v
  | .big v => .big v

end JNum

end Wilkinson

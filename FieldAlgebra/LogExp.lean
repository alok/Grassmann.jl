import FieldAlgebra.Group

/-!
# `LogGroup` and `ExpGroup`: formal logarithms and exponentials of group elements

Julia `LogGroup{B,T}` (`FieldAlgebra.jl:476-523`) is the formal `log_B(g)` of a
group element `g`; `ExpGroup{B,T}` (`:527-569`) is the formal `B^g`. Julia keeps
the base `B` in a type parameter; here it is a runtime field (`LogBase`), since
bases are produced by arithmetic (`log(F)*2` has base `ℯ^(1/2)`).

Group laws: `log_B a + log_B b = log_B(ab)`, `log_B a - log_B b = log_B(a/b)`,
`log_B(a)/y = log_{B^y}(a)` and `B^a · B^b = B^(a+b)`.

Fixed Julia defects (never reachable without an error or wrong result in Julia):
`ExpGroup^y` is computed as `B^(y·a)` (Julia drops `y`, `FieldAlgebra.jl:563`),
and `exp2`/`exp10` of a `LogGroup` with another base is the formal inverse
instead of infinite recursion (`:515-516`).
-/

namespace FieldAlgebra

open FieldConstants FieldConstants.Julia

/-- The base of a formal logarithm or exponential. `num` holds a Julia number
(the `Int` bases `2` and `10` print as `log2(`/`log10(`, the `Float64` value
`exp10(0.1)` prints as `dB(`). -/
inductive LogBase where
  /-- Euler's number `ℯ` (Julia `Irrational{:ℯ}`) -/
  | e
  /-- a numeric base -/
  | num (b : JNum)
  deriving Inhabited

namespace LogBase

/-- Julia `exp10(0.1)`, the decibel base. -/
def dBValue : Float := 1.2589254117941673

/-- Numeric value of the base. -/
def toFloat : LogBase → Float
  | e => 2.718281828459045
  | num b => b.toFloat

/-- Base identity as Julia type parameters compare (`===`). -/
def ident : LogBase → LogBase → Bool
  | e, e => true
  | num a, num b => a.ident b
  | _, _ => false

/-- `B^y`: the base of `log_B(g)/y`. -/
def pow (b : LogBase) (y : JNum) : LogBase :=
  match b with
  | e => num (.float (JuliaBase.F64.exp y.toFloat))
  | num x => match x, y with
    | .int a, .int n => if n ≥ 0 then num (.int (JNum.ipow a n.toInt.toNat)) else num (.float (JuliaBase.F64.powInt (Float.ofInt a.toInt) n.toInt))
    | _, _ => num (.float (JuliaBase.F64.pow x.toFloat y.toFloat))

/-- Is this the decibel base `exp10(0.1)`? -/
def isDB : LogBase → Bool
  | num (.float x) => x.toBits == dBValue.toBits
  | _ => false

end LogBase

/-- Formal `log_B(v)` (Julia `LogGroup{B,T}`). -/
structure LogGroup (B : Basis) where
  /-- the base -/
  base : LogBase
  /-- the argument -/
  v : Group B

/-- Formal `B^v` (Julia `ExpGroup{B,T}`). -/
structure ExpGroup (B : Basis) where
  /-- the base -/
  base : LogBase
  /-- the exponent -/
  v : Group B

namespace Group
variable {B : Basis}
/-- Julia `log(g)`. -/
def log (g : Group B) : LogGroup B := ⟨.e, g⟩
/-- Julia `log2(g)`. -/
def log2 (g : Group B) : LogGroup B := ⟨.num 2, g⟩
/-- Julia `log10(g)`. -/
def log10 (g : Group B) : LogGroup B := ⟨.num 10, g⟩
/-- Julia `log(b, g)`. -/
def logb (b : JNum) (g : Group B) : LogGroup B := ⟨.num b, g⟩
/-- Julia `logdb(g) = log(exp10(0.1), g)` (`FieldAlgebra.jl:573`). -/
def logdb (g : Group B) : LogGroup B := ⟨.num (.float LogBase.dBValue), g⟩
/-- Julia `exp(g)`. -/
def exp (g : Group B) : ExpGroup B := ⟨.e, g⟩
/-- Julia `exp2(g)`. -/
def exp2 (g : Group B) : ExpGroup B := ⟨.num 2, g⟩
/-- Julia `exp10(g)`. -/
def exp10 (g : Group B) : ExpGroup B := ⟨.num 10, g⟩
/-- Julia `b^g` for a number `b`. -/
def expb (b : JNum) (g : Group B) : ExpGroup B := ⟨.num b, g⟩
end Group

namespace LogGroup
variable {B : Basis}

/-- `log_B a + log_B b = log_B(a·b)` (`FieldAlgebra.jl:519`); bases must agree. -/
def add (x y : LogGroup B) : Option (LogGroup B) :=
  if x.base.ident y.base then some ⟨x.base, x.v * y.v⟩ else none

/-- `log_B a - log_B b = log_B(a/b)` (`FieldAlgebra.jl:520`). -/
def sub (x y : LogGroup B) : Option (LogGroup B) :=
  if x.base.ident y.base then some ⟨x.base, x.v / y.v⟩ else none

/-- `log_B(a)/y = log_{B^y}(a)` (`FieldAlgebra.jl:521`). -/
def divNum (x : LogGroup B) (y : JNum) : LogGroup B := ⟨x.base.pow y, x.v⟩

/-- `log_B(a)·y = log_B(a)/inv(y)` (`FieldAlgebra.jl:522`). -/
def mulNum (x : LogGroup B) (y : JNum) : LogGroup B := x.divNum y.inv

/-- Julia `showfun` prefix (`FieldAlgebra.jl:494-498`). -/
def showFun (x : LogGroup B) : String :=
  match x.base with
  | .e => "log("
  | .num (.int 2) => "log2("
  | .num (.int 10) => "log10("
  | b => if b.isDB then "dB(" else "log(" ++ (match b with | .num n => n.toString | .e => "ℯ") ++ ","

/-- Julia `product(::LogGroup)` given the argument's value (`FieldAlgebra.jl:500-504`). -/
def productOf (x : LogGroup B) (p : Float) : Float :=
  match x.base with
  | .e => JuliaBase.F64.log p
  | .num (.int 2) => JuliaBase.F64.log2 p
  | .num (.int 10) => JuliaBase.F64.log10 p
  | b => if b.isDB then 10.0 * JuliaBase.F64.log10 p else JuliaBase.F64.log p / JuliaBase.F64.log b.toFloat

/-- Julia `iszero(::LogGroup) = isone(value(x))`. -/
def isZero (x : LogGroup B) : Bool := x.v.isOne

/-- Julia `show`: `log(…)`, then ` = value` for bases with products. -/
def print (x : LogGroup B) (product? : Option Float := none) : String :=
  x.showFun ++ x.v.showPre ++ ")" ++ match product? with
    | some p => " = " ++ JuliaBase.F64.showString (x.productOf p)
    | none => ""

end LogGroup

namespace ExpGroup
variable {B : Basis}

/-- `B^a · B^b = B^(a·b)` in multiplicative notation (`FieldAlgebra.jl:566`).
Mismatched bases (Julia multiplies the bases, which is wrong) give `none`. -/
def mul (x y : ExpGroup B) : Option (ExpGroup B) :=
  if x.base.ident y.base then some ⟨x.base, x.v * y.v⟩ else none

/-- `B^a / B^b = B^(a/b)` (`FieldAlgebra.jl:567`). -/
def div (x y : ExpGroup B) : Option (ExpGroup B) :=
  if x.base.ident y.base then some ⟨x.base, x.v / y.v⟩ else none

/-- `(B^a)^n = B^(a^n)` (fixes Julia's `ExpGroup^y`, which ignores `y`). -/
def zpow (x : ExpGroup B) (n : Int) : ExpGroup B := ⟨x.base, x.v ^ n⟩

/-- Julia `showfun` prefix (`FieldAlgebra.jl:541-544`). -/
def showFun (x : ExpGroup B) : String :=
  match x.base with
  | .e => "exp("
  | .num (.int 2) => "exp2("
  | .num (.int 10) => "exp10("
  | .num n => n.toString ++ "^("

/-- Julia `product(::ExpGroup)` given the exponent's value (`FieldAlgebra.jl:546-549`). -/
def productOf (x : ExpGroup B) (p : Float) : Float :=
  match x.base with
  | .e => JuliaBase.F64.exp p
  | .num (.int 2) => JuliaBase.F64.exp2 p
  | .num (.int 10) => JuliaBase.F64.exp10 p
  | .num n => JuliaBase.F64.pow n.toFloat p

/-- Julia `show`. -/
def print (x : ExpGroup B) (product? : Option Float := none) : String :=
  x.showFun ++ x.v.showPre ++ ")" ++ match product? with
    | some p => " = " ++ JuliaBase.F64.showString (x.productOf p)
    | none => ""

end ExpGroup

namespace LogGroup
variable {B : Basis}
/-- Julia `exp(log_ℯ g) = g`, and generally `exp(log_B g) = g^(1/log B)`. -/
def exp (x : LogGroup B) : Option (Group B) :=
  match x.base with
  | .e => some x.v
  | _ => none
end LogGroup

end FieldAlgebra

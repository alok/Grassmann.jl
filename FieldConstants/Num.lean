import FieldConstants.JNum

/-!
# `Num`: a `Constant` or a plain Julia number

FieldConstants.jl distinguishes a `Constant{N}` (payload in the type) from a
plain `Int64`/`Float64`, and the *mixed* arithmetic rules differ from the closed
ones (`FieldConstants.jl:64-100`):

* `Constant ∘ Constant` is closed: `Constant{A*B}`, `Constant{A/B}`, …;
* `Number * Constant` and `Number ± Constant` are plain;
* `Number / Constant` and `Constant / Number` compute `a*inv(b)`, two roundings;
* `x^n` for a literal `n` is `inv(x)^(-n)` for a `Constant` but Julia's
  `literal_pow` for a plain `Float64` (`x*x`, `x*x*x`, `inv(x)`, `pow_body`).

UnitSystems produces plain numbers in a handful of places (value-dispatch
overrides such as `2𝘩`-style literals, user values in `q(v, U, S)`), and they
change the last bit of downstream results, so the port tracks the distinction.
-/

namespace FieldConstants

open Julia

/-- A Julia real that is either a `FieldConstants.Constant{N}` (`const = true`)
or a plain number. -/
structure Num where
  /-- the payload -/
  v : JNum
  /-- is this a `Constant{N}`? -/
  const : Bool := true
  deriving Inhabited

namespace Num

/-- A `Constant{N}`. -/
@[inline] def c (v : JNum) : Num := ⟨v, true⟩
/-- A plain number. -/
@[inline] def p (v : JNum) : Num := ⟨v, false⟩

/-- Julia `float(x)`. -/
@[inline] def toFloat (x : Num) : Float := x.v.toFloat

/-- `literal_pow` for a plain `Int64`/`Float64` (`base/intfuncs.jl:465-488`). -/
def plainLpow : JNum → Int → JNum
  | .float x, n =>
    if n == 0 then .float 1.0 else if n == 1 then .float x
    else if n == 2 then .float (x * x) else if n == 3 then .float (x * x * x)
    else if n == -1 then .float (1.0 / x)
    else if n == -2 then (let i := 1.0 / x; .float (i * i))
    else .float (powInt x n)
  | .int a, n => if n < 0 then .float (powInt (Float.ofInt a.toInt) n) else JNum.npow (.int a) n

instance : BEq Num := ⟨fun a b => a.v == b.v⟩

/-- `Constant * Constant` is closed, anything else is plain. -/
def mul (a b : Num) : Num := ⟨a.v * b.v, a.const && b.const⟩
/-- `a / b`: one rounding for two constants or two plain numbers, `a*inv(b)`
(two roundings) when exactly one operand is a `Constant`. -/
def div (a b : Num) : Num :=
  if a.const == b.const then ⟨a.v / b.v, a.const⟩
  else ⟨a.v * b.v.inv, false⟩
/-- `a + b` (closed for two constants). -/
def add (a b : Num) : Num := ⟨a.v + b.v, a.const && b.const⟩
/-- `a - b` (closed for two constants). -/
def sub (a b : Num) : Num := ⟨a.v - b.v, a.const && b.const⟩
/-- `inv` keeps the kind. -/
def inv (a : Num) : Num := ⟨a.v.inv, a.const⟩
/-- `sqrt` keeps the kind. -/
def sqrt (a : Num) : Num := ⟨a.v.sqrt, a.const⟩
/-- `-a` keeps the kind. -/
def neg (a : Num) : Num := ⟨-a.v, a.const⟩
/-- Literal integer power: `Constant` via `inv(x)^(-n)`, plain via `literal_pow`. -/
def lpow (a : Num) (n : Int) : Num :=
  if a.const then ⟨a.v.lpow n, true⟩ else ⟨plainLpow a.v n, false⟩

instance : Mul Num := ⟨mul⟩
instance : Div Num := ⟨div⟩
instance : Add Num := ⟨add⟩
instance : Sub Num := ⟨sub⟩
instance : Neg Num := ⟨neg⟩
instance : Inv Num := ⟨inv⟩
instance : HPow Num Int Num := ⟨lpow⟩
instance (n : Nat) : OfNat Num n := ⟨c (.int (Int64.ofNat n))⟩

/-- Julia `UnitSystems.unit(x, y)`: snap `x` to `y` within `eps()^0.9`; the result
is a `Constant` when `x` is. -/
def snap (x y : Num) : Num :=
  if JNum.isApproxUnit y.v x.v then ⟨y.v, x.const⟩ else x

/-- Julia `===` (same kind, same payload bits). -/
def ident (a b : Num) : Bool := a.const == b.const && a.v.ident b.v

/-- Julia `show`: the payload (a `Constant` prints like its value). -/
protected def toString (a : Num) : String := a.v.toString

instance : ToString Num := ⟨Num.toString⟩

end Num
end FieldConstants

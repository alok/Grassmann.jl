import Similitude.Constants

/-!
# Similitude's numbers

Similitude re-evaluates UnitSystems' `initdata.jl` with `Constant(` replaced by
`identity(` (`Similitude.jl:133-155`), so the constants of its unit systems and
the values of its quantities are ordinary Julia numbers: exact groups of
physical constants (`Group{:Constants}`), plain `Int64`/`Float64` literals such
as SI1976's `8.31432`, and `Rational{Int}` values. `Scalar` is that number
tower, with Julia's mixed arithmetic:

* a plain number meets a group through `factorize` (`FieldAlgebra.jl:603-616`):
  `12 * kB = kB⋅2²3`, `2.5 * 𝘤 = 𝘤⋅2.5`, `(1//3) * 𝘤 = 𝘤/3//1`;
* `+`/`-` of groups is exact only for equal monomials (`dimension.jl:112-129`),
  otherwise it falls back to `Float64` (`𝟐 + 𝟑 = 5.0`, `𝟐 - 𝟐 = 0`);
* `Int64 / Int64` is `Float64`, literal powers follow Julia's `literal_pow`.

`UnitAlg Scalar` makes every UnitSystems formula (systems, conversions,
physics) compute Similitude's exact values.
-/

namespace Similitude

open FieldConstants FieldAlgebra UnitSystems

/-- A Julia number as Similitude computes with it. -/
inductive Scalar where
  /-- a plain `Int64` or `Float64` -/
  | num (x : JNum)
  /-- a `Rational{Int}` -/
  | rat (q : Rat)
  /-- an exact constant, Julia `Group{:Constants}` -/
  | grp (g : Consts)
  deriving Inhabited

namespace Consts

/-- Julia `^(a::Group, b::Integer)` for a *runtime* integer (`FieldAlgebra.jl:594`):
exponents scale by `b`, the coefficient is `coef^b` (`Int^negative` is a
`DomainError` in Julia unless the coefficient is `±1`; here it is computed in
`Float64`). -/
def ipow (a : Consts) (b : Int) : Consts :=
  let c := match a.c with
    | .int x => if b ≥ 0 then Coef.int (x ^ b.toNat)
      else if x == 1 then .int 1 else if x == -1 then .int (if b % 2 == 0 then 1 else -1)
      else .float (JuliaBase.F64.powInt (Float.ofInt x) b)
    | .rat q => if b ≥ 0 then .rat (q ^ b.toNat) else .rat (q⁻¹ ^ (-b).toNat)
    | .float x => .float (JuliaBase.F64.powInt x b)
  Group.mk' (a.v.smul b) c

/-- The identity `𝟏` (`phys(0)`). -/
def one : Consts := Group.one

/-- `𝟐` (`phys(38)`). -/
def two : Consts := gen 37

end Consts

namespace Scalar

/-- A plain `Int64`. -/
@[inline] def ofInt (n : Int) : Scalar := num (.int (Int64.ofInt n))
/-- A plain `Float64`. -/
@[inline] def ofFloat (x : Float) : Scalar := num (.float x)

instance (n : Nat) : OfNat Scalar n := ⟨ofInt n⟩

/-- Julia `float(x)` (`product(g)` for a group). -/
def toFloat : Scalar → Float
  | num x => x.toFloat
  | rat q => Coef.toFloat (.rat q)
  | grp g => g.product

/-- The group a plain number turns into when it meets a group: Julia
`factorize(x, Val(:Constants))`, whose fallback for a `Rational` is the number
itself (so it becomes the coefficient, `times(q, g)`). -/
def factor : Scalar → Consts
  | num (.int n) => Consts.factorize n.toInt
  | num (.float x) => Consts.factorizeF x
  | rat q => Group.mk' .zero (.rat q)
  | grp g => g

/-- `Rational` arithmetic with a plain number: `Int` keeps it `Rational`,
`Float64` makes it `Float64`. -/
@[inline] def ratOp (fq : Rat → Rat → Rat) (ff : Float → Float → Float) : Scalar → Scalar → Scalar
  | rat a, rat b => rat (fq a b)
  | rat a, num (.int b) => rat (fq a b.toInt)
  | num (.int a), rat b => rat (fq a.toInt b)
  | a, b => ofFloat (ff a.toFloat b.toFloat)

/-- Julia `*` (`FieldAlgebra.jl:591, 605-608`). -/
def mul : Scalar → Scalar → Scalar
  | grp a, grp b => grp (a * b)
  | grp a, b => grp (a * b.factor)
  | a, grp b => grp (a.factor * b)
  | num a, num b => num (a * b)
  | a, b => ratOp (· * ·) (· * ·) a b

/-- Julia `inv`: `Int64 ↦ Float64`, `Rational ↦ Rational`. -/
def inv : Scalar → Scalar
  | num x => num x.inv
  | rat q => rat q⁻¹
  | grp g => grp g⁻¹

/-- Julia `/` (`FieldAlgebra.jl:592, 609-610`): `g / x = times(g, inv(factorize(x)))`,
`x / g = x * inv(g)`, `Int64 / Int64 = Float64`. -/
def div : Scalar → Scalar → Scalar
  | grp a, grp b => grp (a / b)
  | grp a, b => grp (a * b.factor⁻¹)
  | a, grp b => mul a (grp b⁻¹)
  | num a, num b => num (a / b)
  | a, b => ratOp (· / ·) (· / ·) a b

/-- Julia `+` (`dimension.jl:112-137`): equal monomials add coefficients (equal
coefficients give `𝟐*a`), anything else is `Float64`. -/
def add : Scalar → Scalar → Scalar
  | grp a, grp b =>
    if a.v.beq b.v then
      if a.c == b.c then grp (Consts.two * a) else grp (Group.mk' a.v (a.c.add b.c))
    else ofFloat (a.product + b.product)
  | grp a, b => ofFloat (a.product + b.toFloat)
  | a, grp b => ofFloat (a.toFloat + b.product)
  | num a, num b => num (a + b)
  | a, b => ratOp (· + ·) (· + ·) a b

/-- Julia `-` (`dimension.jl:121-137`): the difference of equal constants is the
`Int` `0`. -/
def sub : Scalar → Scalar → Scalar
  | grp a, grp b =>
    if a.v.beq b.v then
      if a.c == b.c then ofInt 0 else grp (Group.mk' a.v (a.c.add b.c.neg))
    else ofFloat (a.product - b.product)
  | grp a, b => ofFloat (a.product - b.toFloat)
  | a, grp b => ofFloat (a.toFloat - b.product)
  | num a, num b => num (a - b)
  | a, b => ratOp (· - ·) (· - ·) a b

/-- Julia unary `-`. -/
def neg : Scalar → Scalar
  | num x => num (-x)
  | rat q => rat (-q)
  | grp g => grp (-g)

/-- Julia `x^n` for a *literal* integer (`literal_pow`): groups and rationals
compute `inv(x)^(-n)` for negative `n`, plain numbers use Julia's
`HWNumber`/`Float64` rules. -/
def lpow (x : Scalar) (n : Int) : Scalar :=
  match x with
  | num a => num (Num.plainLpow a n)
  | rat q => rat (if n ≥ 0 then q ^ n.toNat else q⁻¹ ^ (-n).toNat)
  | grp g => grp (g ^ n)

/-- Julia `x^n` for a runtime integer (`^(x, n::Integer)`). -/
def ipow (x : Scalar) (n : Int) : Scalar :=
  match x with
  | num a => num (JNum.npow a n)
  | rat q => rat (if n ≥ 0 then q ^ n.toNat else q⁻¹ ^ (-n).toNat)
  | grp g => grp (g.ipow n)

/-- Julia `x^r` for a `Rational` exponent. -/
def qpow (x : Scalar) (r : Rat) : Scalar :=
  match x with
  | grp g => grp (g ^ r)
  | x => ofFloat (JuliaBase.F64.pow x.toFloat (Coef.toFloat (.rat r)))

/-- Julia `sqrt` (`Float64` for plain numbers, halved exponents for groups). -/
def sqrt : Scalar → Scalar
  | grp g => grp g.sqrt
  | x => ofFloat x.toFloat.sqrt

/-- Julia `cbrt`. -/
def cbrt : Scalar → Scalar
  | grp g => grp g.cbrt
  | x => ofFloat (JuliaBase.F64.cbrt x.toFloat)

/-- Julia `isone`. -/
def isOne : Scalar → Bool
  | num x => x.isOne
  | rat q => q == 1
  | grp g => g.isOne

/-- Julia `==`: groups compare exponents and coefficients, a group equals a
float when its `product` does, numbers compare by value. -/
def beq : Scalar → Scalar → Bool
  | grp a, grp b => a == b
  | grp a, num (.float f) => a.product == f
  | num (.float f), grp b => b.product == f
  | grp _, _ => false
  | _, grp _ => false
  | num a, num b => a == b
  | rat a, rat b => a == b
  | rat a, num (.int b) => a == (b.toInt : Rat)
  | num (.int a), rat b => (a.toInt : Rat) == b
  | a, b => a.toFloat == b.toFloat

instance : BEq Scalar := ⟨beq⟩

/-- Julia `===`. -/
def ident : Scalar → Scalar → Bool
  | grp a, grp b => a.ident b
  | num a, num b => a.ident b
  | rat a, rat b => a == b
  | _, _ => false

/-- Julia `UnitSystems.unit(x, y=1)`: Similitude makes it the identity on groups
(`Similitude.jl:59-64`); a plain number within `eps()^0.9` of `1` snaps to the
`Int` `1`. -/
def snap : Scalar → Scalar → Scalar
  | grp g, _ => grp g
  | x, _ => if JNum.isApproxUnit 1 (.float x.toFloat) then ofInt 1 else x

/-- Julia `print`: `Int64` in decimal, `Float64` shortest, `Rational` as `p//q`,
groups with their value (`kB⋅NA = 8.31446261815324`). -/
protected def toString : Scalar → String
  | num x => x.toString
  | rat q => s!"{q.num}//{q.den}"
  | grp g => g.print

instance : ToString Scalar := ⟨Scalar.toString⟩

instance : Mul Scalar := ⟨mul⟩
instance : Div Scalar := ⟨div⟩
instance : Add Scalar := ⟨add⟩
instance : Sub Scalar := ⟨sub⟩
instance : Neg Scalar := ⟨neg⟩
instance : Inv Scalar := ⟨inv⟩
instance : HPow Scalar Int Scalar := ⟨lpow⟩

/-- A measured or defined constant as Similitude binds it: a generator of the
constants group (`@group2 Constants`, `dimension.jl:164-209`), `αinv = inv(α)`,
the exact `LD`, `JD` and large prefixes, and `μE☾`, which Similitude keeps as a
`FieldConstants.Constant` (a plain `Float64` here; `Similitude.jl:129`). -/
def measured : Measured → Scalar
  | .μE => ofFloat 81.300568
  | m => grp (Consts.ofMeasured m)

end Scalar

/-- Similitude's scalar: UnitSystems' formulas over `Scalar` reproduce
Similitude's exact unit-system constants, conversion ratios and physics. Value
dispatch (`special`) is off: Similitude's parameters are groups, never
`FieldConstants.Constant`s. -/
instance : UnitAlg Scalar where
  inv := Scalar.inv
  lpow := Scalar.lpow
  sqrt := Scalar.sqrt
  ilit n := .grp (Consts.factorize n)
  flit x := .ofFloat x
  tau := .grp (Consts.gen 36)
  measured := Scalar.measured
  snap := Scalar.snap
  isOne := Scalar.isOne
  ident := Scalar.ident
  eqFloat x f := x.toFloat == f
  plit n := .ofInt n

end Similitude

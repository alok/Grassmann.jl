import FieldAlgebra.Group

/-!
# Numeric values of a basis (`@group Name begin a = v … end`)

A basis declared with values (`FieldAlgebra.jl:674-737`) gets three generated
methods: `product(g)` (the numeric value of `c · ∏ bᵢ^{eᵢ}`), `factorize(x)`
(a number as a group element over the integer-valued generators) and
`hasproduct(g) = true`, which makes `show` print ` = product(g)`.

`GroupValues B` carries the per-generator values; `GroupValues.product`,
`factorize` and the `GroupProduct` instance reproduce the generated code:

* `product(g) = (∏ₙ vₙ^eₙ) * ((∏ₖ float(vₖ)^eₖ) * c)` where `k` runs over the
  generators whose value is an integer *literal* (Julia's `checkint2` on the
  macro's syntax) and `n` over the others, both left folds in basis order
  (an empty group of factors is left out);
* `factorize(x::Int)` strips each integer-valued generator in turn
  (`factorfind`), `factorize(x::Float64)` factors integral floats as integers and
  otherwise strips the `≡`-generators (`τ ≡ 2π`) by floating remainders.

Similitude's constants basis is the same construction (`dimension.jl:164-209`).
-/

namespace FieldAlgebra

/-- How a generator is evaluated numerically in `product`. -/
inductive GenValue where
  /-- a number (`FieldConstants.Constant{x}` or a float literal) -/
  | const (x : Float)
  /-- an `Irrational` evaluated by `power_by_squaring` (`φ`, `γ`) -/
  | irrational (x : Float)
  /-- `ℯ`: `ℯ^x = exp(x)` -/
  | euler
  /-- an integer literal (evaluated as `float(p)^e`) -/
  | prime (p : Nat)
  deriving Inhabited

namespace GenValue

/-- `value^e` with Julia's semantics for the generator kind and exponent type
(`Float64^Int` is `pow_body`, `Float64^Rational` is `x^(p/q)`, `φ^n` is
`power_by_squaring` (a `DomainError` for `n < 0`, here `NaN`), `ℯ^x = exp(x)`). -/
def pow (g : GenValue) (e : Expo) : Float :=
  match g, e.makeint with
  | .const x, .int n => JuliaBase.F64.powInt x n
  | .const x, e => JuliaBase.F64.pow x e.toFloat
  | .prime p, .int n => JuliaBase.F64.powInt (Float.ofNat p) n
  | .prime p, e => JuliaBase.F64.pow (Float.ofNat p) e.toFloat
  | .irrational x, .int n => if n < 0 then JuliaBase.F64.nan else JuliaBase.F64.powerBySquaring x n.toNat
  | .irrational x, e => JuliaBase.F64.pow x e.toFloat
  | .euler, e => JuliaBase.F64.exp e.toFloat

/-- Is this an integer-literal generator (Julia `checkint2`)? -/
def isInt : GenValue → Bool
  | .prime _ => true
  | _ => false

end GenValue

/-- Julia's generated `product(g)` for per-generator values `vals`
(`FieldAlgebra.jl:684-704`): non-integer generators folded left, times the
integer generators folded left times the coefficient. -/
def productWith {B : Basis} (vals : Array GenValue) (g : Group B) : Float :=
  let es := g.v.toExpos
  let idx := List.range (min vals.size es.size)
  let term (i : Nat) : Float := (vals[i]!).pow (es[i]!)
  let foldl1 : List Float → Option Float
    | [] => none
    | x :: xs => some (xs.foldl (· * ·) x)
  let c := g.c.toFloat
  let ints := idx.filter fun i => (vals[i]!).isInt
  let nonints := idx.filter fun i => !(vals[i]!).isInt
  let v := match foldl1 (ints.map term) with
    | some p => p * c
    | none => c
  match foldl1 (nonints.map term) with
  | some p => p * v
  | none => v

/-- Julia `factorfind(x, k)` on integers (`FieldAlgebra.jl:741`): strip the
factor `k`, counting it (`0` is returned unchanged with count `0`). -/
def factorfind (x : Int) (k : Int) : Int × Nat := go x 0 128
where
  /-- Fuelled loop. -/
  go (x : Int) (i : Nat) : Nat → Int × Nat
    | 0 => (x, i)
    | f + 1 => if x == 0 then (x, 0) else if x.tmod k == 0 then go (x.tdiv k) (i + 1) f else (x, i)

/-- Julia's generated `factorize(x::Int, Val(G))` (`FieldAlgebra.jl:706-713`):
strip every integer-valued generator in basis order; the cofactor is the
coefficient. -/
def factorizeWith {B : Basis} (vals : Array GenValue) (x : Int) : Group B :=
  let (x, exps) := (List.range (min vals.size B.n)).foldl (fun (x, acc) i =>
    match vals[i]! with
    | .prime p => let (x', e) := factorfind x p; (x', acc.push (i, e))
    | _ => (x, acc)) (x, (#[] : Array (Nat × Nat)))
  let v : Vector Rat B.n := Vector.ofFn fun j =>
    match exps.find? (·.1 == j.1) with
    | some (_, e) => (e : Rat)
    | none => 0
  Group.mk' (.exact v) (.int x)

/-- A basis whose generators have numeric values (Julia `@group`/`@group2` with
values). `divisors` are the generators declared with `≡` (`τ ≡ 2π`), which
`factorize` strips from non-integral floats. -/
class GroupValues (B : Basis) where
  /-- the value of each generator, in basis order -/
  values : Array GenValue
  /-- the `≡` generators and their float values -/
  divisors : Array (Nat × Float) := #[]

namespace GroupValues

variable {B : Basis} [GroupValues B]

/-- Julia `product(g)` / `float(g)`: the numeric value of a group element. -/
def product (g : Group B) : Float := productWith (values B) g

/-- Julia `factorize(x::Int, Val(G))`. -/
def factorize (x : Int) : Group B := factorizeWith (values B) x

/-- Julia `factorize(x::Float64, Val(G))` (`FieldAlgebra.jl:714-727`): an integral
float factors as an integer; otherwise the `≡` generators are stripped by
floating-point remainders and the rest is a `Float64` coefficient. -/
def factorizeF (x : Float) : Group B :=
  if JuliaBase.F64.isfinite x && x.floor == x && x.abs < 9.223372036854775807e18 then
    factorize x.toInt64.toInt
  else
    let (x, es) := (divisors B).foldl (fun (x, acc) (i, d) =>
      let (x', e) := go d x 0 64
      (x', acc.push (i, e))) (x, (#[] : Array (Nat × Nat)))
    Group.mk' (.exact (Vector.ofFn fun j =>
      match es.find? (·.1 == j.1) with | some (_, e) => (e : Rat) | none => 0)) (.float x)
where
  /-- `factorfind` on floats: strip the factor `d` while the remainder is zero. -/
  go (d : Float) (x : Float) (i : Nat) : Nat → Float × Nat
    | 0 => (x, i)
    | f + 1 =>
      if x == 0.0 then (x, 0)
      else if JuliaBase.F64.rem x d == 0.0 then go d (JuliaBase.F64.div x d) (i + 1) f else (x, i)

/-- Julia `a * g` for a number `a` on a basis with values (`FieldAlgebra.jl:605`):
`factorize(a) * g`. -/
def smulInt (a : Int) (g : Group B) : Group B := factorize a * g

/-- `a * g` for a `Float64` `a` (`factorize(a) * g`). -/
def smulFloat (a : Float) (g : Group B) : Group B := factorizeF a * g

end GroupValues

/-- A basis with values prints ` = product` (Julia `hasproduct(g) = true`). -/
instance (priority := mid) {B : Basis} [GroupValues B] : GroupProduct B :=
  ⟨fun g => some (JuliaBase.F64.showString (GroupValues.product g))⟩

end FieldAlgebra

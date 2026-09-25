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
  | .prime p, .int n => JuliaBase.F64.powInt p.toUInt64.toFloat n
  | .prime p, e => JuliaBase.F64.pow p.toUInt64.toFloat e.toFloat
  | .irrational x, .int n => if n < 0 then JuliaBase.F64.nan else JuliaBase.F64.powerBySquaring x n.toNat
  | .irrational x, e => JuliaBase.F64.pow x e.toFloat
  | .euler, e => JuliaBase.F64.exp e.toFloat

/-- Is this an integer-literal generator (Julia `checkint2`)? -/
def isInt : GenValue → Bool
  | .prime _ => true
  | _ => false

end GenValue

/-- `value^n` for an `Int` exponent (`pow` without building the `Expo`). -/
def GenValue.powI (g : GenValue) (n : Int) : Float :=
  match g with
  | .const x => JuliaBase.F64.powInt x n
  | .prime p => JuliaBase.F64.powInt p.toUInt64.toFloat n
  | .irrational x => if n < 0 then JuliaBase.F64.nan else JuliaBase.F64.powerBySquaring x n.toNat
  | .euler => JuliaBase.F64.exp (intToFloat n)

/-- `(∏ non-integer) * ((∏ integer) * c)`, leaving out empty products. -/
@[inline] def productFinish (c pi pn : Float) (hi hn : Bool) : Float :=
  let v := if hi then pi * c else c
  if hn then pn * v else v

/-- The folds of `productWith` over `Int` exponents: `pi`/`pn` accumulate the
integer and the other generators, `hi`/`hn` record that the class is nonempty. -/
def productLoopI (vals : Array GenValue) (v : Array Int) (c : Float) (i : Nat) (pi pn : Float)
    (hi hn : Bool) : Nat → Float
  | 0 => productFinish c pi pn hi hn
  | fuel + 1 =>
    if i < vals.size && i < v.size then
      let g := vals[i]!
      let e := v[i]!
      if g.isInt then
        productLoopI vals v c (i + 1) (if e == 0 then pi else pi * g.powI e) pn true hn fuel
      else
        productLoopI vals v c (i + 1) pi (if e == 0 then pn else pn * g.powI e) hi true fuel
    else productFinish c pi pn hi hn

/-- The folds of `productWith` over exponents of any element type. -/
def productLoopE (vals : Array GenValue) (es : Array Expo) (c : Float) (i : Nat) (pi pn : Float)
    (hi hn : Bool) : Nat → Float
  | 0 => productFinish c pi pn hi hn
  | fuel + 1 =>
    if i < vals.size && i < es.size then
      let g := vals[i]!
      let e := es[i]!
      if g.isInt then
        productLoopE vals es c (i + 1) (if e.isZero then pi else pi * g.pow e) pn true hn fuel
      else
        productLoopE vals es c (i + 1) pi (if e.isZero then pn else pn * g.pow e) hi true fuel
    else productFinish c pi pn hi hn

/-- Julia's generated `product(g)` for per-generator values `vals`
(`FieldAlgebra.jl:684-704`): non-integer generators folded left, times the
integer generators folded left times the coefficient.

A factor with exponent zero is `x^0 = 1.0` and multiplying by it is exact, so it is
skipped: each fold starts at `1.0` (`1.0 * t = t` bit for bit) when its class of
generators is nonempty. -/
def productWith {B : Basis} (vals : Array GenValue) (g : Group B) : Float :=
  let c := g.c.toFloat
  match g.v with
  | .int v => productLoopI vals v.toArray c 0 1.0 1.0 false false (vals.size + 1)
  | e => productLoopE vals e.toExpos c 0 1.0 1.0 false false (vals.size + 1)

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
  if x == 1 || x == -1 || x == 0 then Group.mk' .zero (.int x) else
  let (x, exps) := (List.range (min vals.size B.n)).foldl (fun (x, acc) i =>
    match vals[i]! with
    | .prime p => let (x', e) := factorfind x p; (x', if e == 0 then acc else acc.set! i e)
    | _ => (x, acc)) (x, Array.replicate B.n (0 : Int))
  Group.mk' (.int (Vector.ofFn fun j => exps[j.1]?.getD 0)) (.int x)

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
  if JuliaBase.F64.isfinite x && x.floor == x && x.abs < f64! 9.223372036854775807e18 then
    factorize x.toInt64.toInt
  else
    let (x, es) := (divisors B).foldl (fun (x, acc) (i, d) =>
      let (x', e) := go d x 0 64
      (x', acc.push (i, e))) (x, (#[] : Array (Nat × Nat)))
    Group.mk' (.int (Vector.ofFn fun j =>
      match es.find? (·.1 == j.1) with | some (_, e) => (e : Int) | none => 0)) (.float x)
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

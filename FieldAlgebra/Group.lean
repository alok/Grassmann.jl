import FieldAlgebra.Superscript

/-!
# Free abelian groups over a named basis (`FieldAlgebra.Group`)

Julia's `Group{G,T,S,N}` (`FieldAlgebra.jl:44-70`) is a monomial
`c · ∏ bᵢ^{vᵢ}` over a *named* basis `G` of `N` generators, with exponent
element type `T ∈ {Int, Rational{Int}, Float64}` and a scalar coefficient `c`.

In Lean the basis is a **type index**: `Group B` for `B : Basis`. Multiplying
elements of different bases (a USQ dimension by a physical constant, say) is a
type error, and all basis metadata (names, unit glyph) is erased from the
runtime representation, which is just the exponent vector and coefficient.

Julia's normalisation rules are reproduced exactly (they decide the printed
form): rational exponent vectors that are all integral become `Int` vectors
(`promoteints`); coefficients `1.0`/`0.0` and integral rationals become `Int`
(`promoteint`); `Float64` exponent vectors are never normalised.
-/

namespace FieldAlgebra

open FieldConstants

/-- A named basis (Julia's group name `G`, `N` and the `@group` generator
metadata). Values of this structure index `Group`. -/
structure Basis where
  /-- Julia group name `G` (`:USQ`, `:Constants`, …) -/
  name : String
  /-- number of generators `N` -/
  n : Nat
  /-- display names of the generators (`basistext`) -/
  text : Array String
  /-- Julia `strchar`: every name is a single character, so `printdims` never
  inserts `⋅` separators -/
  charNames : Bool
  /-- glyph printed for the identity element (`'𝟙'`, or `'𝟏'` for constants) -/
  unit : String := "𝟙"
  /-- LaTeX names of the generators (`latext`) -/
  latex : Array String := text

/-- A Julia group coefficient: `Int`, `Rational{Int}` or `Float64`. -/
inductive Coef where
  /-- `Int` -/
  | int (n : Int)
  /-- `Rational{Int}` -/
  | rat (q : Rat)
  /-- `Float64` -/
  | float (x : Float)
  deriving Inhabited

namespace Coef

/-- Julia `promoteint` (`FieldAlgebra.jl:84-95`): `0.0`, `1.0` and integral
rationals become `Int`. -/
def normalize : Coef → Coef
  | float x => if x == 0.0 then int 0 else if x == 1.0 then int 1 else float x
  | rat q => if q.den == 1 then int q.num else rat q
  | c => c

/-- Value as a `Float64`. -/
def toFloat : Coef → Float
  | int n => Float.ofInt n
  | rat q => JuliaBase.IEEEFloat.ofRat Float q
  | float x => x

/-- Julia `==` across coefficient kinds. -/
def beq : Coef → Coef → Bool
  | int a, int b => a == b
  | int a, rat b => (a : Rat) == b
  | rat a, int b => a == (b : Rat)
  | rat a, rat b => a == b
  | a, b => a.toFloat == b.toFloat

instance : BEq Coef := ⟨beq⟩

/-- Julia `*` with promotion. -/
def mul : Coef → Coef → Coef
  | int a, int b => int (a * b)
  | int a, rat b => rat (a * b)
  | rat a, int b => rat (a * b)
  | rat a, rat b => rat (a * b)
  | a, b => float (a.toFloat * b.toFloat)

/-- Julia `+` with promotion. -/
def add : Coef → Coef → Coef
  | int a, int b => int (a + b)
  | int a, rat b => rat (a + b)
  | rat a, int b => rat (a + b)
  | rat a, rat b => rat (a + b)
  | a, b => float (a.toFloat + b.toFloat)

/-- Julia unary `-`. -/
def neg : Coef → Coef
  | int a => int (-a)
  | rat a => rat (-a)
  | float x => float (-x)

/-- Julia `-` with promotion. -/
def sub : Coef → Coef → Coef
  | int a, int b => int (a - b)
  | int a, rat b => rat (a - b)
  | rat a, int b => rat (a - b)
  | rat a, rat b => rat (a - b)
  | a, b => float (a.toFloat - b.toFloat)

/-- Julia `/` with promotion: `Int / Int` is `Float64` (one rounding), rationals
stay rational. -/
def div : Coef → Coef → Coef
  | int a, rat b => rat (a / b)
  | rat a, int b => rat (a / b)
  | rat a, rat b => rat (a / b)
  | a, b => float (a.toFloat / b.toFloat)

/-- Julia `iszero`. -/
def isZero : Coef → Bool
  | int a => a == 0
  | rat a => a == 0
  | float x => x == 0.0

/-- Julia `inv`: `Int ↦ Float64`, `Rational ↦ Rational`. -/
def inv : Coef → Coef
  | int a => float (1.0 / Float.ofInt a)
  | rat a => rat a⁻¹
  | float x => float (1.0 / x)

/-- Julia `c^n` for an integer exponent, `n ≥ 0` (callers route negative
literal powers through `inv`). -/
def npow (c : Coef) (n : Nat) : Coef :=
  match c with
  | int a => int (a ^ n)
  | rat a => rat (a ^ n)
  | float x => float (JuliaBase.F64.powInt x n)

/-- Julia `c^r` for a rational exponent: `x^(num/den)` in `Float64`. -/
def rpow (c : Coef) (r : Rat) : Coef :=
  match c with
  | int 1 => float 1.0
  | _ => float (JuliaBase.F64.pow c.toFloat (JuliaBase.IEEEFloat.ofRat Float r))

/-- Julia `c^y` for a `Float64` exponent. -/
def fpow (c : Coef) (y : Float) : Coef := float (JuliaBase.F64.pow c.toFloat y)

/-- Julia `sqrt` (always `Float64`). -/
def sqrt (c : Coef) : Coef := float c.toFloat.sqrt
/-- Julia `cbrt` (always `Float64`; Julia's own `cbrt`, not libm's). -/
def cbrt (c : Coef) : Coef := float (JuliaBase.F64.cbrt c.toFloat)

/-- Julia `isone`. -/
def isOne : Coef → Bool
  | int a => a == 1
  | rat a => a == 1
  | float x => x == 1.0

/-- Julia `abs`. -/
def abs : Coef → Coef
  | int a => int a.natAbs
  | rat a => rat a.abs
  | float x => float x.abs

/-- Julia `print` of a coefficient after `makeint` (`showgroup_pre2`). -/
def showMakeint : Coef → String
  | int a => toString a
  | rat a => s!"{a.num}//{a.den}"
  | float x => (makeint x).toString

end Coef

/-- `Float64` vectors of a fixed length (exponents of `Group{G,Float64}`). -/
abbrev FVec (n : Nat) := {a : FloatArray // a.size = n}

/-- Build an `FVec` from an index function. -/
def FVec.ofFn {n : Nat} (f : Fin n → Float) : FVec n :=
  ⟨⟨Array.ofFn f⟩, Array.size_ofFn⟩

/-- Read an `FVec`. -/
@[inline] def FVec.get {n : Nat} (v : FVec n) (i : Fin n) : Float := v.1[i.1]'(by rw [v.2]; exact i.2)

/-- Exponent vector of a group element with its Julia element type:
`exact` covers `Int` and `Rational{Int}` (it is an `Int` vector exactly when
every entry is integral, Julia's `promoteints`), `float` is `Float64`. -/
inductive Exps (n : Nat) where
  /-- `Int`/`Rational{Int}` exponents -/
  | exact (v : Vector Rat n)
  /-- `Float64` exponents -/
  | float (v : FVec n)

namespace Exps

variable {n : Nat}

/-- Entry `i` as an `Expo`, with the vector's element type. -/
def get (e : Exps n) (i : Fin n) : Expo :=
  match e with
  | exact v => if v.all (·.den == 1) then .int v[i].num else .rat v[i]
  | float v => .float (v.get i)

/-- Entry as a `Float64`. -/
def getFloat (e : Exps n) (i : Fin n) : Float := (e.get i).toFloat

/-- All entries with the vector's element type (the `Int`/`Rational` decision is
made once, unlike repeated `get`). -/
def toExpos (e : Exps n) : Array Expo :=
  match e with
  | exact v =>
    if v.all (·.den == 1) then v.toArray.map (.int ·.num) else v.toArray.map .rat
  | float v => v.1.toList.toArray.map .float

/-- Is every exponent zero (Julia `iszero(norm(v))`)? -/
def allZero (e : Exps n) : Bool :=
  match e with
  | exact v => v.all (· == 0)
  | float v => v.1.toList.all (· == 0.0)

/-- Is this a `Float64` vector? -/
def isFloat : Exps n → Bool
  | float _ => true
  | _ => false

/-- Is this an `Int` vector (exact and all integral)? -/
def isInt : Exps n → Bool
  | exact v => v.all (·.den == 1)
  | float _ => false

/-- The zero vector (`Int` eltype). -/
def zero : Exps n := exact (Vector.replicate n 0)

/-- Unit vector `eᵢ` (`valueat(i, N, G)`). -/
def unit (i : Fin n) : Exps n := exact (Vector.ofFn fun j => if j == i then 1 else 0)

/-- Pointwise combination with Julia promotion (`Float64` contaminates). -/
def zipWith (fq : Rat → Rat → Rat) (ff : Float → Float → Float) (a b : Exps n) : Exps n :=
  match a, b with
  | exact u, exact v => exact (Vector.zipWith fq u v)
  | a, b => float (FVec.ofFn fun i => ff (a.getFloat i) (b.getFloat i))

/-- Pointwise map with Julia promotion. -/
def map (fq : Rat → Rat) (ff : Float → Float) : Exps n → Exps n
  | exact u => exact (u.map fq)
  | a => float (FVec.ofFn fun i => ff (a.getFloat i))

/-- `a + b` (group multiplication). -/
def add : Exps n → Exps n → Exps n := zipWith (· + ·) (· + ·)
/-- `a - b` (group division). -/
def sub : Exps n → Exps n → Exps n := zipWith (· - ·) (· - ·)
/-- `-a` (group inverse). -/
def neg : Exps n → Exps n := map (- ·) (- ·)
/-- `k·a` for a rational `k` (group power). -/
def smul (k : Rat) : Exps n → Exps n := map (k * ·) (JuliaBase.IEEEFloat.ofRat Float k * ·)
/-- `y·a` for a `Float64` `y`: always a `Float64` vector. -/
def fmul (y : Float) (a : Exps n) : Exps n := float (FVec.ofFn fun i => y * a.getFloat i)

/-- Julia `==` of exponent vectors (numeric, across element types). -/
def beq (a b : Exps n) : Bool :=
  match a, b with
  | exact u, exact v => u == v
  | a, b => (List.finRange n).all fun i => a.getFloat i == b.getFloat i

end Exps

/-- An element `c · ∏ bᵢ^{vᵢ}` of the free abelian group on basis `B`
(Julia `Group{G,T,S,N}`). -/
structure Group (B : Basis) where
  /-- exponent vector -/
  v : Exps B.n
  /-- scalar coefficient (normalised by `Group.mk'`) -/
  c : Coef := .int 1

namespace Group

variable {B : Basis}

/-- Normalising constructor (Julia's inner constructors). -/
def mk' (v : Exps B.n) (c : Coef) : Group B := ⟨v, c.normalize⟩

/-- The identity `𝟙` (`one(g)`). -/
def one : Group B := ⟨.zero, .int 1⟩

instance : Inhabited (Group B) := ⟨one⟩

/-- Generator `bᵢ` (`valueat(i, N, G)`); index `i` is 0-based. -/
def gen (i : Fin B.n) : Group B := ⟨.unit i, .int 1⟩

/-- Julia `==` (`FieldAlgebra.jl:78`). -/
def beq (a b : Group B) : Bool := a.v.beq b.v && a.c == b.c

instance : BEq (Group B) := ⟨beq⟩

/-- Group product (`FieldAlgebra.jl:591`). -/
def mul (a b : Group B) : Group B := mk' (a.v.add b.v) (a.c.mul b.c)
/-- Group quotient (`FieldAlgebra.jl:592`). -/
def div (a b : Group B) : Group B := mk' (a.v.sub b.v) (a.c.mul b.c.inv)
/-- Group inverse (`FieldAlgebra.jl:601`). -/
def inv (a : Group B) : Group B := mk' a.v.neg a.c.inv

/-- Julia `g^n` for a *literal* integer `n` (`literal_pow` computes
`inv(g)^(-n)` for negative `n`). -/
def zpow (a : Group B) (n : Int) : Group B :=
  if n ≥ 0 then mk' (a.v.smul n) (a.c.npow n.toNat)
  else let b := a.inv; mk' (b.v.smul (-n)) (b.c.npow (-n).toNat)

/-- Julia `g^r` for a `Rational` exponent (`FieldAlgebra.jl:595`). -/
def qpow (a : Group B) (r : Rat) : Group B := mk' (a.v.smul r) (a.c.rpow r)

/-- Julia `g^y` for a `Float64` exponent: the exponent vector becomes `Float64`. -/
def fpow (a : Group B) (y : Float) : Group B := mk' (a.v.fmul y) (a.c.fpow y)

/-- Julia `sqrt(g)` (`FieldAlgebra.jl:597-598`): `Int` exponents become `v//2`. -/
def sqrt (a : Group B) : Group B := mk' (a.v.smul (mkRat 1 2)) a.c.sqrt
/-- Julia `cbrt(g)`. -/
def cbrt (a : Group B) : Group B := mk' (a.v.smul (mkRat 1 3)) a.c.cbrt

/-- Julia unary `-g` (negates the coefficient). -/
def neg (a : Group B) : Group B := mk' a.v a.c.neg

/-- Julia `times(a::Real, b::Group)`: scale the coefficient, keep exponents. -/
def scale (k : Coef) (a : Group B) : Group B := mk' a.v (k.mul a.c)

/-- Julia `isone(g)`. -/
def isOne (a : Group B) : Bool := a.v.allZero && a.c.isOne

instance : Mul (Group B) := ⟨mul⟩
instance : Div (Group B) := ⟨div⟩
instance : Inv (Group B) := ⟨inv⟩
instance : Neg (Group B) := ⟨neg⟩
instance : HPow (Group B) Int (Group B) := ⟨zpow⟩
instance : HPow (Group B) Nat (Group B) := ⟨fun a n => zpow a n⟩
instance : HPow (Group B) Rat (Group B) := ⟨qpow⟩
instance : One (Group B) := ⟨one⟩

/-- A group element from integer exponents. -/
def ofInts (xs : List Int) (c : Coef := .int 1) : Group B :=
  mk' (.exact (Vector.ofFn fun (i : Fin B.n) => (xs.getD i.1 0 : Rat))) c

/-! ### Display (`printdims`, `showgroup`) -/

/-- Julia `printdims(io, xv, name)` (`FieldAlgebra.jl:391-412`): each nonzero
exponent as `name^e`; with `String` names a `⋅` follows an exponent of exactly
one when more factors follow. -/
def printDims (v : Exps B.n) (names : Array String) (charNames : Bool) : String := Id.run do
  let es := v.toExpos
  let mut out := ""
  for h : i in [0:es.size] do
    let e := es[i]
    out := out ++ printExpoBased (names[i]?.getD "") e.makeint
    if !charNames && e.isOne then
      if (es.extract (i + 1) es.size).any (!·.isZero) then out := out ++ "⋅"
  return out

/-- Julia `showgroup_pre2` (`FieldAlgebra.jl:431-446`): the identity glyph and
coefficient suffix (`⋅2`, `/2`, `/Inf`). -/
def showCoef (c : Coef) (v : Exps B.n) (glyph : String) : String :=
  let iz := v.allZero
  let pre := if iz && (c.isOne || c.abs.toFloat < 1.0) then glyph else ""
  if c.isOne then pre
  else if c.abs.toFloat < 1.0 then pre ++ "/" ++ c.inv.showMakeint
  else pre ++ (if iz then "" else "⋅") ++ c.showMakeint

/-- `showgroup_pre`: monomial and coefficient, with explicit names/glyph. -/
def showWith (g : Group B) (names : Array String) (charNames : Bool) (glyph : String) : String :=
  printDims g.v names charNames ++ showCoef g.c g.v glyph

/-- `showgroup_pre` with the basis' own names and glyph. -/
def showPre (g : Group B) : String := g.showWith B.text B.charNames B.unit

/-- Julia `latexdims`/`latexgroup_pre` (`FieldAlgebra.jl:192-297`): the LaTeX
monomial with `\cdot ` separators and the `\textbf{1}` identity (master branch). -/
def latexPre (g : Group B) (names : Array String := B.latex) (charNames : Bool := B.charNames)
    (glyph : String := "\\textbf{1}") : String := Id.run do
  let es := g.v.toExpos
  let mut out := ""
  for h : i in [0:es.size] do
    let e := es[i]
    out := out ++ latexpoBased (names[i]?.getD "") e.makeint
    if !charNames && e.isOne then
      if (es.extract (i + 1) es.size).any (!·.isZero) then out := out ++ "\\cdot "
  let iz := g.v.allZero
  let c := g.c
  if iz && (c.isOne || c.abs.toFloat < 1.0) then out := out ++ glyph
  if !c.isOne then
    if c.abs.toFloat < 1.0 then
      out := out ++ "/" ++ (match c.inv with
        | .float x => (match makeint x with | .float y => specialPrintFloat y | j => j.toString)
        | k => k.showMakeint)
    else
      out := out ++ (if iz then "" else "\\cdot ") ++ (match c with
        | .float x => (match makeint x with | .float y => specialPrintFloat y | j => j.toString)
        | k => k.showMakeint)
  return out

end Group

/-- Bases whose generators have numeric values print ` = product` after the
monomial (Julia `hasproduct`/`product`). The default is no product. -/
class GroupProduct (B : Basis) where
  /-- the printed numeric value of an element, if the basis has values -/
  productString? : Group B → Option String

instance (priority := low) (B : Basis) : GroupProduct B := ⟨fun _ => none⟩

/-- Julia `show(io, g::Group)` = `showgroup`: monomial, coefficient and, for
bases with values, ` = product`. -/
def Group.print {B : Basis} [GroupProduct B] (g : Group B) : String :=
  g.showPre ++ match GroupProduct.productString? g with
    | some p => " = " ++ p
    | none => ""

instance {B : Basis} [GroupProduct B] : ToString (Group B) := ⟨Group.print⟩

end FieldAlgebra

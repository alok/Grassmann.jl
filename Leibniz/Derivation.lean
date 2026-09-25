/-
Leibniz's derivations `∇` and `Δ` (Julia `Derivation{T,O}`, `Nabla`, `Laplacian`,
`Leibniz.jl src/Leibniz.jl:107-160`) and the operator vocabulary `d`, `δ`, `∂`
(`differential`, `codifferential`, `boundary`, `Leibniz.jl src/Leibniz.jl:152-155`).

A `Derivation R` is a coefficient `λ : R` times the abstract operator `∂ₖ^O vₖ`. Julia keeps
the order `O` in the type; here it is a field, so `∇^2 == Δ` and `(-∇)^3` are ordinary
values. `∇ = Derivation(I)` has a *sign* coefficient: Julia uses `Bool`, whose arithmetic is
broken (`∇ + ∇` throws `InexactError: Bool(2)`, `Bool` minus is a flip, Leibniz quirk Q7);
`Sign` keeps the display and makes `∇ + ∇ = 2∂ₖvₖ` an `Int` derivation, as Julia intends.
Mixed arithmetic follows Julia's promotion: `2 * ∇ : Derivation Int`, `2.5 * ∇`,
`∇ / 2 : Derivation Float` (`0.5∂ₖvₖ`).

Display (Julia `show`): the coefficient (nothing or `-` for a sign), `∂ₖ`, the order as a
superscript unless it is `1` (`∅` for order `0`), `v`, and `ₖ` for odd orders: `∂ₖvₖ`,
`∂ₖ²v`, `-8∂ₖ³vₖ`, `∂ₖ∅v`. Julia's superscript table stops at `36` (a `KeyError` beyond);
the port prints `?` there.

The functor `V(∇)` and the operators `d ω = V(∇) ∧ ω`, `∂ ω = ω ⋅ V(∇)`, `δ = -∂` act on
Grassmann elements; this module declares them as classes (`HasDifferential`,
`HasCodifferential`, `HasBoundary`) for Grassmann to instantiate.
-/
import Leibniz.Indices
import JuliaBase.Float

namespace Leibniz

/-- The sign `±1` of a unit derivation (Julia's `Bool` coefficient of `∇`: `true` is `+`). -/
inductive Sign where
  /-- `+1` (Julia `true`). -/
  | pos
  /-- `-1` (Julia `false`). -/
  | neg
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Sign

/-- The sign as an integer. -/
def toInt : Sign → Int
  | pos => 1
  | neg => -1

/-- Negation. -/
instance : Neg Sign := ⟨fun | pos => neg | neg => pos⟩

/-- Product of signs. -/
instance : Mul Sign := ⟨fun a b => if a == b then pos else neg⟩

instance : OfNat Sign 1 := ⟨pos⟩

end Sign

/-- Julia `Derivation{T,O}`: the coefficient `λ` times `∂ₖ^O vₖ`. -/
structure Derivation (R : Type) where
  /-- The coefficient `λ` (Julia `v.v.λ`). -/
  coeff : R
  /-- The order `O`. -/
  order : Nat
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Julia `Nabla = Derivation{Bool,1}` (by value: sign coefficients, order 1 for `∇`). -/
abbrev Nabla := Derivation Sign

/-- Julia `Laplacian = Derivation{Bool,2}` (sign coefficients, order 2 for `Δ`). -/
abbrev Laplacian := Derivation Sign

namespace Derivation

variable {R : Type}

/-- Julia `-v` (a sign flips, a number negates). -/
instance [Neg R] : Neg (Derivation R) := ⟨fun d => ⟨-d.coeff, d.order⟩⟩

/-- `λ^n` by repeated multiplication (exact for signs and integers). -/
def coeffPow [Mul R] [OfNat R 1] (x : R) : Nat → R
  | 0 => 1
  | n + 1 => coeffPow x n * x

/-- Julia `v^n`: order `O·n`, coefficient `λ^n` (for a sign: `λ` for odd `n`, `+` for even). -/
instance [Mul R] [OfNat R 1] : HPow (Derivation R) Nat (Derivation R) :=
  ⟨fun d n => ⟨coeffPow d.coeff n, d.order * n⟩⟩

/-- Julia's binary operators need equal orders (`MethodError` otherwise; this panics). -/
def sameOrder {S T U : Type} [Inhabited U] (op : S → T → U) (a : Derivation S) (b : Derivation T) :
    Derivation U :=
  if a.order == b.order then ⟨op a.coeff b.coeff, a.order⟩
  else panic! s!"MethodError: derivations of orders {a.order} and {b.order}"

instance [Add R] [Inhabited R] : Add (Derivation R) := ⟨sameOrder (· + ·)⟩
instance [Sub R] [Inhabited R] : Sub (Derivation R) := ⟨sameOrder (· - ·)⟩
instance [Mul R] [Inhabited R] : Mul (Derivation R) := ⟨sameOrder (· * ·)⟩

/-- A sign derivation as an integer one (Julia's promotion of `Bool`). -/
def toInt (d : Derivation Sign) : Derivation Int := ⟨d.coeff.toInt, d.order⟩

/-- An integer derivation as a float one. -/
def toFloat (d : Derivation Int) : Derivation Float := ⟨Float.ofInt d.coeff, d.order⟩

/-- `∇ + ∇ = 2∂ₖvₖ` (Julia throws `InexactError: Bool(2)`, quirk Q7). -/
instance : HAdd (Derivation Sign) (Derivation Sign) (Derivation Int) := ⟨fun a b => a.toInt + b.toInt⟩
/-- `∇ - ∇ = 0∂ₖvₖ`. -/
instance : HSub (Derivation Sign) (Derivation Sign) (Derivation Int) := ⟨fun a b => a.toInt - b.toInt⟩

/-- Julia `a * v` for a number `a`: `Derivation{promote_type}(a * λ)`. -/
instance [Mul R] : HMul R (Derivation R) (Derivation R) := ⟨fun a d => ⟨a * d.coeff, d.order⟩⟩
/-- Julia `v * a`. -/
instance [Mul R] : HMul (Derivation R) R (Derivation R) := ⟨fun d a => ⟨d.coeff * a, d.order⟩⟩
/-- `2 * ∇ = 2∂ₖvₖ`. -/
instance : HMul Int (Derivation Sign) (Derivation Int) := ⟨fun a d => a * d.toInt⟩
/-- `∇ * 3 = 3∂ₖvₖ`. -/
instance : HMul (Derivation Sign) Int (Derivation Int) := ⟨fun d a => d.toInt * a⟩
/-- `2.5 * ∇ = 2.5∂ₖvₖ`. -/
instance : HMul Float (Derivation Sign) (Derivation Float) := ⟨fun a d => a * d.toInt.toFloat⟩
/-- `∇ / 2 = 0.5∂ₖvₖ` (Julia's `/` of integers is a float). -/
instance : HDiv (Derivation Sign) Int (Derivation Float) := ⟨fun d a => ⟨d.toInt.toFloat.coeff / Float.ofInt a, d.order⟩⟩
/-- `(4∇) / 2 = 2.0∂ₖvₖ`. -/
instance : HDiv (Derivation Int) Int (Derivation Float) := ⟨fun d a => ⟨d.toFloat.coeff / Float.ofInt a, d.order⟩⟩
/-- `(4∇) / (2∇) = 2.0∂ₖvₖ`. -/
instance : HDiv (Derivation Int) (Derivation Int) (Derivation Float) :=
  ⟨fun a b => sameOrder (fun x y => Float.ofInt x / Float.ofInt y) a b⟩

/-- Julia `a \ v = v / a`: `2 \ ∇ = 0.5∂ₖvₖ`. -/
def ldiv (a : Int) (d : Derivation Sign) : Derivation Float := d / a

/-- The operator part of the display: `∂ₖ`, the order superscript (none for `1`), `v`, and `ₖ`
for odd orders. -/
def showOperator (order : Nat) : String :=
  "∂ₖ" ++ (if order == 1 then "" else (sups order).toString) ++ "v" ++ (if order % 2 == 1 then "ₖ" else "")

/-- Julia `show(::Derivation{Bool,O})`: `∂ₖvₖ`, `-∂ₖ³vₖ`. -/
instance : ToString (Derivation Sign) :=
  ⟨fun d => (if d.coeff == .pos then "" else "-") ++ showOperator d.order⟩

/-- Julia `show(::Derivation{Int,O})`: `2∂ₖvₖ`, `-8∂ₖ³vₖ`. -/
instance : ToString (Derivation Int) := ⟨fun d => toString d.coeff ++ showOperator d.order⟩

/-- Julia `show(::Derivation{Float64,O})`: `0.5∂ₖvₖ` (Julia's shortest float printing). -/
instance : ToString (Derivation Float) :=
  ⟨fun d => JuliaBase.F64.showString d.coeff ++ showOperator d.order⟩

end Derivation

/-- Julia `∇ = nabla = Derivation(I)`: `∂ₖvₖ`. -/
def nabla : Nabla := ⟨.pos, 1⟩

/-- Julia `Δ = laplacian = ∇^2`: `∂ₖ²v`. -/
def Δ : Laplacian := nabla ^ 2

/-- Julia `laplacian`. -/
abbrev laplacian : Laplacian := Δ

/-- `∇` (Julia `∇`, `nabla`); scoped in `Leibniz`. -/
scoped notation "∇" => Leibniz.nabla

example : nabla ^ 2 = Δ := rfl
example : (-nabla) ^ 2 = Δ := rfl
#guard toString nabla == "∂ₖvₖ" && toString Δ == "∂ₖ²v" && toString ((-nabla) ^ 3) == "-∂ₖ³vₖ"
#guard toString (nabla ^ 0) == "∂ₖ∅v"

/-! ## The exterior-calculus operators (declared here, instantiated by Grassmann) -/

/-- Julia `differential`/`d`: `d ω = Manifold(ω)(∇) ∧ ω`. -/
class HasDifferential (α : Type) (β : outParam Type) where
  /-- The exterior derivative. -/
  differential : α → β

/-- Julia `codifferential`/`δ`: `δ ω = -∂ ω`. -/
class HasCodifferential (α : Type) (β : outParam Type) where
  /-- The codifferential. -/
  codifferential : α → β

/-- Julia `boundary`/`∂`: `∂ ω = ω ⋅ Manifold(ω)(∇)`. -/
class HasBoundary (α : Type) (β : outParam Type) where
  /-- The boundary operator. -/
  boundary : α → β

export HasDifferential (differential)
export HasCodifferential (codifferential)
export HasBoundary (boundary)

/-! Julia's one-letter names `d`, `δ`, `∂` live in `Leibniz.Calculus` (open it to use them):
`d` is too common a variable name to export from `Leibniz`, which DirectSum opens. -/

namespace Calculus

/-- Julia `d = differential`. -/
abbrev d {α β : Type} [HasDifferential α β] : α → β := differential
/-- Julia `δ = codifferential`. -/
abbrev δ {α β : Type} [HasCodifferential α β] : α → β := codifferential

/-- `∂ ω` (Julia `∂ = boundary`); scoped in `Leibniz.Calculus`. -/
scoped prefix:max "∂" => HasBoundary.boundary

end Calculus

end Leibniz

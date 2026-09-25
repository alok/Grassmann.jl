import AbstractAnalysis.IEEE
import JuliaBase.Show

/-!
# Julia display and the scalar interface

`JuliaRepr` renders values the way Julia's `show` (`repr`) and `print`
(`string`) do, which is part of the oracle contract (`show(::Limit)` goldens
embed `string(::Float64)` verbatim). Scalars print through `JuliaBase`'s
`JuliaShow` (Ryu shortest round-trip for floats); `JuliaRepr` adds the
container renderings and the `isNumber` flag `show(::Limit)` dispatches on.
Complex numbers are `JuliaBase.Complex` (Gaussian integers and rationals in
the countable sets, `ComplexF64` for `unityroots`).

`JNumber` is the scalar interface of the analysis layer: exactly the parts of
Julia's `Number` tower that `Limit`, `sum`, `prod` and `supnorm` touch.
-/

namespace AbstractAnalysis

open JuliaBase

/-- Julia `cis(θ) = cos θ + i sin θ` (`JuliaBase.Complex` has no `cis`). -/
def cis (θ : Float) : Complex Float := ⟨θ.cos, θ.sin⟩

/-- Julia-style rendering: `repr` is `show`, `str` is `print`/`string`, and
`isNumber` records `typeof(x) <: Number` (it selects the one-line form of
`show(::Limit)`). -/
class JuliaRepr (α : Type) where
  /-- Julia `repr(x)` / `show(io, x)`. -/
  repr : α → String
  /-- Julia `string(x)` / `print(io, x)`. -/
  str : α → String := repr
  /-- Julia `typeof(x) <: Number`. -/
  isNumber : Bool := false

export JuliaRepr (repr)

/-- A Julia number: `show`/`print` from its `JuliaShow` instance. -/
@[reducible] def JuliaRepr.ofShow (α : Type) [JuliaShow α] : JuliaRepr α :=
  ⟨JuliaShow.showString, JuliaShow.printString, true⟩

instance : JuliaRepr Float := .ofShow Float
instance : JuliaRepr Float32 := .ofShow Float32
instance : JuliaRepr Int := .ofShow Int
instance : JuliaRepr Nat := .ofShow Nat
instance : JuliaRepr Bool := .ofShow Bool
/-- Julia `Rational` shows as `n//d` (always with the denominator). -/
instance : JuliaRepr Rat := .ofShow Rat
instance : JuliaRepr String := ⟨fun s => s!"\"{s}\"", id, false⟩

/-- Julia `show(::Complex)`: `re + imim`, `re - |im|im`, and `*im` for types
other than integers and finite floats (e.g. `0//1 + 1//1*im`). -/
instance {α : Type} [JuliaShow α] : JuliaRepr (Complex α) := .ofShow (Complex α)

/-- Julia `show` of a vector: `[a, b, c]` (element type headers omitted). -/
instance {α : Type} [JuliaRepr α] : JuliaRepr (Array α) where
  repr a := "[" ++ ", ".intercalate (a.toList.map JuliaRepr.repr) ++ "]"

/-- Julia `show` of a `Vector{Float64}` stored packed. -/
instance : JuliaRepr FloatArray where
  repr a := "[" ++ ", ".intercalate (a.toList.map F64.showString) ++ "]"

/-- Julia tuples `(a, b)`. -/
instance {α β : Type} [JuliaRepr α] [JuliaRepr β] : JuliaRepr (α × β) where
  repr p := "(" ++ JuliaRepr.repr p.1 ++ ", " ++ JuliaRepr.repr p.2 ++ ")"

/-- The scalar interface of the analysis layer: the parts of Julia's `Number`
tower that `sum`, `prod`, `supnorm` and the `Limit` residual touch. -/
class JNumber (α : Type) extends Add α, Sub α, Mul α, Neg α where
  /-- Additive identity (Julia `zero`). -/
  zero : α
  /-- Multiplicative identity (Julia `one`). -/
  one : α
  /-- Julia `Float64(x)` (the `r::Float64` field of a `Limit`). -/
  toFloat : α → Float
  /-- Julia `norm(x)` for a number (`abs`, as `Float64`). -/
  norm : α → Float
  /-- Julia `supnorm(a, a/b)` with Julia's `/` for this type (`prod`'s residual). -/
  quotResidual : α → α → Float

instance : JNumber Float where
  zero := 0
  one := 1
  toFloat := id
  norm := Float.abs
  quotResidual a b := (a - a / b).abs

instance : JNumber Int where
  zero := 0
  one := 1
  toFloat := Float.ofInt
  norm z := Float.ofInt z.natAbs
  quotResidual a b := (Float.ofInt a - Float.ofInt a / Float.ofInt b).abs

instance : JNumber Rat where
  zero := 0
  one := 1
  toFloat := IEEEFloat.ofRat Float
  norm q := IEEEFloat.ofRat Float (if q < 0 then -q else q)
  quotResidual a b := let d := a - a / b; IEEEFloat.ofRat Float (if d < 0 then -d else d)

end AbstractAnalysis

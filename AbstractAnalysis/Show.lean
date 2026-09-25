import AbstractAnalysis.JuliaFloat

/-!
# Julia display and the scalar interface

`JuliaRepr` renders values the way Julia's `show` (`repr`) and `print`
(`string`) do, which is part of the oracle contract (`show(::Limit)` goldens
embed `string(::Float64)` verbatim). `Complex` is the minimal Gaussian number
type the countable sets (`GaussianIntegers`, …) and `unityroots` need.

`JNumber` is the scalar interface of the analysis layer: exactly the parts of
Julia's `Number` tower that `Limit`, `sum`, `prod` and `supnorm` touch.
-/

namespace AbstractAnalysis

/-- Julia `Complex{T}`: a pair of real parts. -/
structure Complex (α : Type) where
  /-- Real part. -/
  re : α
  /-- Imaginary part. -/
  im : α
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace Complex

variable {α : Type}

instance [Add α] : Add (Complex α) := ⟨fun a b => ⟨a.re + b.re, a.im + b.im⟩⟩
instance [Sub α] : Sub (Complex α) := ⟨fun a b => ⟨a.re - b.re, a.im - b.im⟩⟩
instance [Neg α] : Neg (Complex α) := ⟨fun a => ⟨-a.re, -a.im⟩⟩
instance [Add α] [Sub α] [Mul α] : Mul (Complex α) :=
  ⟨fun a b => ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩⟩

/-- Complex conjugate (Julia `conj`). -/
def conj [Neg α] (z : Complex α) : Complex α := ⟨z.re, -z.im⟩

/-- Julia `abs2`. -/
def abs2 [Add α] [Mul α] (z : Complex α) : α := z.re * z.re + z.im * z.im

/-- Julia `/` on complex numbers with a field of coefficients (textbook formula;
exact for `Rat`). -/
instance [Add α] [Sub α] [Mul α] [Div α] [Neg α] : Div (Complex α) :=
  ⟨fun a b =>
    let d := b.re * b.re + b.im * b.im
    ⟨(a.re * b.re + a.im * b.im) / d, (a.im * b.re - a.re * b.im) / d⟩⟩

/-- Julia `inv(z)`. -/
def inv [Add α] [Sub α] [Mul α] [Div α] [Neg α] [OfNat α 1] [OfNat α 0] (z : Complex α) : Complex α :=
  (⟨1, 0⟩ : Complex α) / z

/-- Julia `abs(::Complex{Float64})` (`hypot`, overflow-safe). -/
def absF (z : Complex Float) : Float :=
  let a := z.re.abs
  let b := z.im.abs
  let m := max a b
  if m == 0 then 0 else if m.isInf then m else
    let s := min a b / m
    m * Float.sqrt (1 + s * s)

/-- Julia `cis(θ) = cos θ + i sin θ`. -/
def cis (θ : Float) : Complex Float := ⟨θ.cos, θ.sin⟩

end Complex

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

instance : JuliaRepr Float := ⟨Float.toJulia, Float.toJulia, true⟩
instance : JuliaRepr Float32 := ⟨JuliaFloat.float32Repr, Float32.toJulia, true⟩
instance : JuliaRepr Int := ⟨toString, toString, true⟩
instance : JuliaRepr Nat := ⟨toString, toString, true⟩
instance : JuliaRepr Bool := ⟨toString, toString, true⟩
instance : JuliaRepr String := ⟨fun s => s!"\"{s}\"", id, false⟩

/-- Julia `Rational` shows as `n//d` (always with the denominator). -/
instance : JuliaRepr Rat := ⟨fun q => s!"{q.num}//{q.den}", fun q => s!"{q.num}//{q.den}", true⟩

/-- Sign test used by complex display (Julia `signbit`). -/
class SignBit (α : Type) where
  /-- Julia `signbit(x)`. -/
  signbit : α → Bool
  /-- Julia `-x` for display of the imaginary part. -/
  negate : α → α
  /-- Whether Julia prints `im` without a `*` (integers and finite floats). -/
  bareIm : α → Bool

instance : SignBit Float := ⟨fun x => IEEEFloat.signBit x && !x.isNaN, (- ·), fun x => x.isFinite⟩
instance : SignBit Int := ⟨(· < 0), (- ·), fun _ => true⟩
instance : SignBit Rat := ⟨(· < 0), (- ·), fun _ => false⟩

/-- Julia `show(::Complex)`: `re + imim`, `re - |im|im`, and `*im` for types
other than integers and finite floats (e.g. `0//1 + 1//1*im`). -/
instance {α : Type} [JuliaRepr α] [SignBit α] : JuliaRepr (Complex α) where
  repr z :=
    let (op, i) := if SignBit.signbit z.im
      then (" - ", SignBit.negate z.im) else (" + ", z.im)
    JuliaRepr.repr z.re ++ op ++ JuliaRepr.repr i ++ (if SignBit.bareIm z.im then "" else "*") ++ "im"
  isNumber := true

/-- Julia `show` of a vector: `[a, b, c]` (element type headers omitted). -/
instance {α : Type} [JuliaRepr α] : JuliaRepr (Array α) where
  repr a := "[" ++ ", ".intercalate (a.toList.map JuliaRepr.repr) ++ "]"

/-- Julia `show` of a `Vector{Float64}` stored packed. -/
instance : JuliaRepr FloatArray where
  repr a := "[" ++ ", ".intercalate (a.toList.map Float.toJulia) ++ "]"

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

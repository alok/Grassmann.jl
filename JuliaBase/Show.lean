import JuliaBase.Float
import JuliaBase.Complex

/-!
Julia `show`/`print` for the scalar types the port prints, and the `JuliaShow` class that
carries the per-type hooks Leibniz's coefficient printer (`showvalue`, Leibniz
`src/indices.jl:185-203`) and Grassmann's `showterm` (Grassmann `src/multivectors.jl:46-58`)
dispatch on.

| Lean type | Julia type | `show` | compact | parens | star |
|---|---|---|---|---|---|
| `Int`, `Nat` | `Int64` | `-3` | same | no | `""` |
| `Bool` | `Bool` | `true` | same | no | `"*"` |
| `Float` | `Float64` | `0.1`, `1.0e-5` | 6 digits | no | `""` if finite else `"*"` |
| `Float32` | `Float32` | `1.5f0` | `1.5` | no | as `Float` |
| `Rat` | `Rational{Int64}` | `-1//3` | same | yes | `"*"` |
| `Complex α` | `Complex{T}` | `1 + 2im` | `1+2im` | yes | `"*"` |
| `UInt8`…`UInt64` | same | `0x03` | same | no | `""` |
-/

universe u

namespace JuliaBase

/-- How a Julia value prints. `compact` is the IO context's `:compact` flag (Grassmann
wraps coefficient output in `IOContext(io, :compact => true)`, multivectors.jl:39-44). -/
class JuliaShow (α : Type u) where
  /-- Julia `show(io, x)`. -/
  showIO : (compact : Bool) → α → String
  /-- Julia `print(io, x)`; the same as `show` except for strings, symbols, unsigned
  integers and `Float32`. -/
  printIO : (compact : Bool) → α → String := showIO
  /-- Leibniz `showparens(typeof(x))` (Leibniz.jl:63-73): coefficients of type `Complex`,
  `Rational`, `Expr` and non-term tensors print as `(x)v₁`. Takes the value so that a
  dynamically typed tensor can decide by its runtime kind. -/
  needsParens : α → Bool := fun _ => false
  /-- Leibniz `showstar(io, x)` (indices.jl:187-193): `""` for non-`Bool` integers and
  finite floats, `"*"` otherwise (`true*v₁`, `NaN*v₁`), `"⊗"` for tensors. -/
  showStar : α → String := fun _ => "*"
  /-- The `*` before `im` in Julia `show(::Complex)` (complex.jl:210): `""` when the
  imaginary part is `Signed` or a finite float, `"*"` otherwise (`1//2*im`, `NaN*im`). -/
  imStar : α → String := fun _ => "*"
  /-- `T <: Real && signbit(x) && !isnan(x)`: whether Grassmann `showterm` prints the term
  as ` - |x|` (multivectors.jl:47). -/
  isNegative : α → Bool := fun _ => false
  /-- `-x`, used by `showterm` after `isNegative x`. -/
  negate : α → α := id

namespace JuliaShow

variable {α : Type u} [JuliaShow α]

/-- Julia `repr(x)` = `sprint(show, x)`. -/
@[inline] def showString (x : α) : String := showIO false x

/-- Julia `repr(x; context = :compact => true)`. -/
@[inline] def showCompact (x : α) : String := showIO true x

/-- Julia `string(x)` = `sprint(print, x)`. -/
@[inline] def printString (x : α) : String := printIO false x

/-- Julia `sprint(print, x; context = :compact => true)`. -/
@[inline] def printCompact (x : α) : String := printIO true x

/-- The coefficient part of Leibniz `showvalue(io, V, B, x)` (indices.jl:195-203), i.e.
everything before the blade label: `print("(", x, ")")` if `showparens`, else
`show(x)` followed by `showstar(x)`. -/
def showValue (compact : Bool) (x : α) : String :=
  if needsParens x then "(" ++ printIO compact x ++ ")"
  else showIO compact x ++ showStar x

/-- The coefficient part of Grassmann `showterm(io, V, B, x, compact)` (multivectors.jl:46-58):
` - ` and the negated value for negative reals, else ` + ` and the value. `sepCompact` is
the caller's `:compact` flag (separators `-`/`+` without spaces); `valCompact` the flag of
the (possibly `compactio`-wrapped) stream the value is printed to. -/
def showTerm (sepCompact valCompact : Bool) (x : α) : String :=
  if isNegative x then (if sepCompact then "-" else " - ") ++ showValue valCompact (negate x)
  else (if sepCompact then "+" else " + ") ++ showValue valCompact x

end JuliaShow

/-! ## Instances -/

/-- Julia `show(::Int64)`: decimal. Lean's `Int` does not wrap, so `typemin` needs no
widening. -/
instance : JuliaShow Int where
  showIO _ x := toString x
  showStar _ := ""
  imStar _ := ""
  isNegative x := x < 0
  negate x := -x

/-- A `Nat` prints like a non-negative Julia `Int`. -/
instance : JuliaShow Nat where
  showIO _ x := toString x
  showStar _ := ""
  imStar _ := ""

/-- Julia `show(::Bool)`: `true`/`false`, starred as a coefficient (`true*v₁`). -/
instance : JuliaShow Bool where
  showIO _ x := if x then "true" else "false"

/-- Julia `show(::Float64)` (Ryu shortest; 6 significant digits when compact). -/
instance : JuliaShow Float where
  showIO := F64.showIO
  showStar x := if x.isFinite then "" else "*"
  imStar x := if x.isFinite then "" else "*"
  isNegative x := F64.signbit x && !x.isNaN
  negate x := -x

/-- Julia `show(::Float32)` at top level is typed (`1.5f0`); compact and `print` are not. -/
instance : JuliaShow Float32 where
  showIO c x := if c then F32.showCompact x else F32.showString x
  printIO c x := if c then F32.printCompact x else F32.printString x
  showStar x := if x.isFinite then "" else "*"
  imStar x := if x.isFinite then "" else "*"
  isNegative x := F32.signbit x && !x.isNaN
  negate x := -x

/-- Julia `show(::Rational)` (rational.jl:113): `num//den`, parenthesized as a coefficient. -/
instance : JuliaShow Rat where
  showIO _ x := toString x.num ++ "//" ++ toString x.den
  needsParens _ := true
  isNegative x := x.num < 0
  negate x := -x

/-- Julia `show(::Unsigned)`: zero-padded hex, `2·sizeof` digits (`0x03`, `0x0000002a`). -/
def showHexPadded (width : Nat) (n : Nat) : String :=
  let ds := Nat.toDigits 16 n
  "0x" ++ String.ofList (List.replicate (width - ds.length) '0' ++ ds)

/-- Julia `UInt8`: `show` gives `0x03`, `print` gives `3`. -/
instance : JuliaShow UInt8 where
  showIO _ x := showHexPadded 2 x.toNat
  printIO _ x := toString x.toNat
  showStar _ := ""

/-- Julia `UInt16`: `0x0003`. -/
instance : JuliaShow UInt16 where
  showIO _ x := showHexPadded 4 x.toNat
  printIO _ x := toString x.toNat
  showStar _ := ""

/-- Julia `UInt32`: `0x00000003`. -/
instance : JuliaShow UInt32 where
  showIO _ x := showHexPadded 8 x.toNat
  printIO _ x := toString x.toNat
  showStar _ := ""

/-- Julia `UInt64`: `0x0000000000000003`. -/
instance : JuliaShow UInt64 where
  showIO _ x := showHexPadded 16 x.toNat
  printIO _ x := toString x.toNat
  showStar _ := ""

/-- Julia `show(io, z::Complex)` (complex.jl:195-214): the real part, then ` + `/` - `
(`+`/`-` when compact) chosen by whether the imaginary part's own `show` starts with `-`,
that string without its sign, a `*` unless the imaginary part is `Signed` or a finite
float, and `im`. -/
def showComplex {α : Type u} [JuliaShow α] (compact : Bool) (z : Complex α) : String :=
  let r := JuliaShow.showIO compact z.re
  let i := JuliaShow.showIO compact z.im
  let (sep, i) :=
    if i.startsWith "-" then (if compact then "-" else " - ", (i.drop 1).toString)
    else (if compact then "+" else " + ", i)
  r ++ sep ++ i ++ JuliaShow.imStar z.im ++ "im"

/-- Julia `show(::Complex)`, parenthesized as a coefficient (`(1 + 2im)v₁`). -/
instance {α : Type u} [JuliaShow α] : JuliaShow (Complex α) where
  showIO := showComplex
  needsParens _ := true
  negate z := ⟨JuliaShow.negate z.re, JuliaShow.negate z.im⟩

/-- Julia `show(io, z::Complex{Bool})` (complex.jl:215): `im` for `im`, otherwise
`Complex(true,false)`. -/
instance : JuliaShow (Complex Bool) where
  showIO _ z :=
    if !z.re && z.im then "im"
    else "Complex(" ++ toString z.re ++ "," ++ toString z.im ++ ")"
  needsParens _ := true

end JuliaBase

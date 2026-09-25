/-
Element-level classes that `StaticVectors` reductions and norms dispatch on.

Julia's `Values` functions call generic `Base` functions on their elements:
`conj` (in `dot`), `abs2`/`norm_sqr` (in `norm`), `norm(x::Number) = abs(float(x))`
(in `norm(a, p)`), and `max`/`min` (in `maximum`/`minimum`). These classes
carry exactly those element operations, with instances for the real scalar
types and for `JuliaBase.Complex`. The element semantics themselves (Julia `max`,
`isapprox`, `hypot`, …) are `JuliaBase`'s.
-/
import JuliaBase.Complex

universe u

namespace StaticVectors

open JuliaBase

/-- Julia `conj`: complex conjugation, the identity on real types. For
tensors (Grassmann) it is the reverse `~`. -/
class Conj (α : Type u) where
  /-- The conjugate. -/
  conj : α → α

export Conj (conj)

/-- Julia's `Float64`-valued size functions on a number.

* `abs2 x` is `float(abs2(x))`, i.e. `LinearAlgebra.norm_sqr` of a number
  (`re² + im²` for complex numbers, **no** `hypot`);
* `norm x` is `LinearAlgebra.norm(x::Number) = abs(float(x))` (`hypot` for
  complex numbers).

Deviation: Julia keeps `Int`/`Rational` sums exact until the final `sqrt`
and computes `Float32` norms in `Float32`; here every element is converted
to `Float` first. The results agree whenever the partial sums are exactly
representable (e.g. integer entries with `Σ x² < 2^53`). -/
class JNorm (α : Type u) where
  /-- `float(abs2(x))`. -/
  abs2 : α → Float
  /-- `abs(float(x))`. -/
  norm : α → Float

/-- Julia `max`/`min` on an element type (`maximum`/`minimum` fold with
these). For floats they propagate NaN and order `-0.0 < 0.0`. -/
class JMinMax (α : Type u) where
  /-- Julia `max`. -/
  max : α → α → α
  /-- Julia `min`. -/
  min : α → α → α

/-- Julia `isapprox` on elements, with explicit tolerances (`Float`-valued so
that one signature serves every element type). `rtol` is the resolved
default: callers pass `Base.rtoldefault` for the element type. -/
class JApprox (α : Type u) where
  /-- The default relative tolerance `Base.rtoldefault(T)` (0 for exact types). -/
  rtolDefault : Float
  /-- `isapprox(x, y; atol, rtol, nans)`. -/
  isapprox : α → α → (atol rtol : Float) → (nans : Bool) → Bool

/-! ## Real scalar instances -/

instance : Conj Float := ⟨id⟩
instance : Conj Float32 := ⟨id⟩
instance : Conj Int := ⟨id⟩
instance : Conj Nat := ⟨id⟩
instance : Conj Rat := ⟨id⟩

instance : JNorm Float := ⟨fun x => x * x, Float.abs⟩
instance : JNorm Float32 := ⟨fun x => (x * x).toFloat, fun x => x.toFloat.abs⟩
instance : JNorm Int := ⟨fun x => Float.ofInt (x * x), fun x => Float.ofNat x.natAbs⟩
instance : JNorm Nat := ⟨fun x => Float.ofNat (x * x), Float.ofNat⟩
instance : JNorm Rat := ⟨fun x => F64.ofRat (x * x), fun x => (F64.ofRat x).abs⟩

instance : JMinMax Float := ⟨F64.max, F64.min⟩
instance : JMinMax Float32 := ⟨F32.max, F32.min⟩
instance : JMinMax Int := ⟨Max.max, Min.min⟩
instance : JMinMax Nat := ⟨Max.max, Min.min⟩
instance : JMinMax Rat := ⟨fun a b => if a ≤ b then b else a, fun a b => if a ≤ b then a else b⟩

/-- Julia `isapprox(::Float64, ::Float64)`: `JuliaBase.F64.isapprox`. -/
instance : JApprox Float where
  rtolDefault := F64.rtoldefault
  isapprox x y atol rtol nans := F64.isapprox x y atol rtol nans

/-- Julia `isapprox(::Float32, ::Float32)` in `Float32` arithmetic
(`JuliaBase.F32.isapprox`), the tolerances rounded to `Float32`. This is exact for
Julia's default `rtoldefault(Float32)` and for `Float32` tolerances; a `Float64` tolerance
would make Julia compare in `Float64` instead. -/
instance : JApprox Float32 where
  rtolDefault := F32.rtoldefault.toFloat
  isapprox x y atol rtol nans := F32.isapprox x y atol.toFloat32 rtol.toFloat32 nans

/-- Julia `isapprox(::Integer, ::Integer)` (`JuliaBase.JInt.isapprox`; `nans` is
irrelevant). -/
instance : JApprox Int where
  rtolDefault := 0
  isapprox x y atol rtol _ := JInt.isapprox x y atol rtol

/-- Julia `isapprox(::Rational, ::Rational)`, the generic `Number` method
(floatfuncs.jl:222), with the norms converted to `Float64`. -/
instance : JApprox Rat where
  rtolDefault := 0
  isapprox x y atol rtol _ :=
    x == y || (F64.ofRat (x - y)).abs ≤
      F64.max atol (rtol * F64.max (F64.ofRat x).abs (F64.ofRat y).abs)

/-! ## Complex instances -/

/-- Julia `conj(z::Complex)` (complex.jl:276). -/
instance {α : Type u} [Neg α] : Conj (Complex α) := ⟨Complex.conj⟩

/-- Julia `norm_sqr`/`norm` of a complex entry: `abs2 = re² + im²` (no `hypot`) and
`norm = abs = hypot(re, im)`. -/
instance : JNorm (Complex Float) := ⟨Complex.abs2, ComplexF64.abs⟩

/-- Julia `isapprox(z::ComplexF64, w::ComplexF64)`: `JuliaBase.ComplexF64.isapprox`. -/
instance : JApprox (Complex Float) where
  rtolDefault := F64.rtoldefault
  isapprox z w atol rtol nans := ComplexF64.isapprox z w atol rtol nans

end StaticVectors

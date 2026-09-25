/-
Element-level classes that `StaticVectors` reductions and norms dispatch on.

Julia's `Values` functions call generic `Base` functions on their elements:
`conj` (in `dot`), `abs2`/`norm_sqr` (in `norm`), `norm(x::Number) = abs(float(x))`
(in `norm(a, p)`), and `max`/`min` (in `maximum`/`minimum`). These classes
carry exactly those element operations, with instances for the real scalar
types here and for `Complex` in `AbstractTensors`.
-/
import StaticVectors.Julia

universe u

namespace StaticVectors

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
instance : JNorm Rat := ⟨fun x => Julia.ratToFloat (x * x), fun x => (Julia.ratToFloat x).abs⟩

instance : JMinMax Float := ⟨Julia.max, Julia.min⟩
instance : JMinMax Float32 := ⟨Julia.max32, Julia.min32⟩
instance : JMinMax Int := ⟨Max.max, Min.min⟩
instance : JMinMax Nat := ⟨Max.max, Min.min⟩
instance : JMinMax Rat := ⟨fun a b => if a ≤ b then b else a, fun a b => if a ≤ b then a else b⟩

instance : JApprox Float where
  rtolDefault := Julia.rtolF
  isapprox x y atol rtol nans := Julia.isapprox x y atol rtol nans

instance : JApprox Float32 where
  rtolDefault := Julia.rtolF32.toFloat
  isapprox x y atol rtol nans :=
    -- Julia promotes the tolerances, and compares in `Float32` arithmetic.
    let x' := x.toFloat
    let y' := y.toFloat
    x == y ||
      (x.isFinite && y.isFinite &&
        (x - y).abs.toFloat ≤ Julia.max atol (rtol * Julia.max x'.abs y'.abs)) ||
      (nans && x.isNaN && y.isNaN)

instance : JApprox Int where
  rtolDefault := 0
  isapprox x y atol rtol _ :=
    x == y || Float.ofNat (x - y).natAbs ≤
      Julia.max atol (rtol * Julia.max (Float.ofNat x.natAbs) (Float.ofNat y.natAbs))

instance : JApprox Rat where
  rtolDefault := 0
  isapprox x y atol rtol _ :=
    x == y || (Julia.ratToFloat (x - y)).abs ≤
      Julia.max atol (rtol * Julia.max (Julia.ratToFloat x).abs (Julia.ratToFloat y).abs)

end StaticVectors

/-
Coefficient classes (DESIGN §4.1).

`Coeff α` is everything a product kernel needs from a coefficient type,
bundled so that generic kernels take **one** instance argument and specialize
cleanly (DESIGN §2 rule 3). `Analytic α` is the separate class of scalar
transcendental functions (Julia `Base.sqrt`, `exp`, `log`, …) used by the
tensor-level transcendental algorithms and by Grassmann's closed forms.

Instances: `Float`, `Float32`, `Int`, `Rat` and `Complex α` for `Coeff`;
`Float`, `Float32` and `Complex Float` for `Analytic`. `Complex` is Julia's
`Complex{T}` from `JuliaBase` (with the `ComplexF64` algorithms); its
`StaticVectors` element instances (`Conj`, `JNorm`, `JApprox`) live in
`StaticVectors.Scalar`.

`Lean.Grind.CommRing` compatibility: `Coeff` deliberately carries no laws
(`Float` satisfies none of them). Proofs about kernels (DESIGN §8, target 3)
should assume `[Coeff α] [Lean.Grind.CommRing α]` *and* coherence of the
operations, i.e. `Coeff.toAdd = CommRing.toAdd` etc.; the cleanest way is to
state such theorems for `Int`/`Rat`, whose `Coeff` instances below reuse the
core `Add`/`Mul`/`Neg`/`Sub` instances that `Lean.Grind.CommRing Int` is
built from, so the two structures agree definitionally.
-/
import JuliaBase.Complex
import StaticVectors.Packed
import StaticVectors.Scalar

universe u

namespace AbstractTensors

open StaticVectors JuliaBase

/-- Everything a kernel needs from a coefficient type (DESIGN §4.1), bundled
so generic kernels take one instance argument and specialize cleanly. -/
class Coeff (α : Type) extends Add α, Sub α, Mul α, Neg α, Inhabited α where
  /-- The additive identity (Julia `zero(T)`). -/
  zero : α
  /-- The multiplicative identity (Julia `one(T)`). -/
  one : α
  /-- Embed an integer (Julia `T(k)`). -/
  ofInt : Int → α
  /-- Embed a rational: metric factors of a `DiagonalForm`, the conformal `½`. -/
  ofRat : Rat → α
  /-- Exact zero test (Julia `iszero`; true for `-0.0`). -/
  isZero : α → Bool
  /-- Packed storage for `Values α n`. -/
  [packed : StaticVectors.Packed α]

attribute [instance_reducible, instance] Coeff.packed

/-- Julia's transcendental functions on a scalar type (`Base.sqrt`, `exp`, …).
`abs` returns the magnitude embedded back into `α` (for `Complex` it is
`hypot(re, im) + 0i`). -/
class Analytic (α : Type) where
  /-- `sqrt`. -/
  sqrt : α → α
  /-- `cbrt`. -/
  cbrt : α → α
  /-- `exp`. -/
  exp : α → α
  /-- `expm1(x) = eˣ - 1`, accurate near zero. -/
  expm1 : α → α
  /-- Natural `log`. -/
  log : α → α
  /-- `log1p(x) = log(1 + x)`, accurate near zero. -/
  log1p : α → α
  /-- `sin`. -/
  sin : α → α
  /-- `cos`. -/
  cos : α → α
  /-- `tan`. -/
  tan : α → α
  /-- `asin`. -/
  asin : α → α
  /-- `acos`. -/
  acos : α → α
  /-- `atan`. -/
  atan : α → α
  /-- Two-argument arctangent `atan(y, x)`. -/
  atan2 : α → α → α
  /-- `sinh`. -/
  sinh : α → α
  /-- `cosh`. -/
  cosh : α → α
  /-- `tanh`. -/
  tanh : α → α
  /-- `asinh`. -/
  asinh : α → α
  /-- `acosh`. -/
  acosh : α → α
  /-- `atanh`. -/
  atanh : α → α
  /-- `x ^ y`. -/
  pow : α → α → α
  /-- `abs`, embedded in `α`. -/
  abs : α → α

/-! ## `Coeff` instances -/

instance : Coeff Float where
  zero := 0
  one := 1
  ofInt := Float.ofInt
  ofRat := F64.ofRat
  isZero x := x == 0

instance : Coeff Float32 where
  zero := 0
  one := 1
  ofInt k := (Float.ofInt k).toFloat32
  ofRat r := (F64.ofRat r).toFloat32
  isZero x := x == 0

/-- Integer coefficients. `ofRat` truncates toward zero (Julia's `Int(r)` throws
`InexactError` for a non-integer `r`). -/
instance : Coeff Int where
  zero := 0
  one := 1
  ofInt := id
  ofRat r := r.num.tdiv r.den
  isZero x := x == 0

instance : Coeff Rat where
  zero := 0
  one := 1
  ofInt k := k
  ofRat := id
  isZero x := x == 0

/-- Complex coefficients over any coefficient field. -/
instance {α : Type} [Coeff α] : Coeff (Complex α) where
  default := ⟨Coeff.zero, Coeff.zero⟩
  zero := ⟨Coeff.zero, Coeff.zero⟩
  one := ⟨Coeff.one, Coeff.zero⟩
  ofInt k := ⟨Coeff.ofInt k, Coeff.zero⟩
  ofRat r := ⟨Coeff.ofRat r, Coeff.zero⟩
  isZero z := Coeff.isZero z.re && Coeff.isZero z.im

/-! ## `Analytic` instances -/

/-- `Float` with Julia's own bit-exact kernels, never the C `libm`: `exp`, `expm1`, `log`,
`log1p`, `^` (`JuliaBase.Math`), the trigonometric functions and `atan(y, x)`
(`JuliaBase.Trig`), the hyperbolic functions (`JuliaBase.Hyperbolic`) and `cbrt`
(`JuliaBase.F64.cbrt`); `sqrt` is the correctly rounded hardware square root, as in Julia.
Arguments outside a function's domain give `NaN` where Julia throws a `DomainError`. The
`Float32` instance below follows the same rule. -/
instance : Analytic Float where
  sqrt := Float.sqrt
  cbrt := F64.cbrt
  exp := F64.exp
  expm1 := F64.expm1
  log := F64.log
  log1p := F64.log1p
  sin := F64.sin
  cos := F64.cos
  tan := F64.tan
  asin := F64.asin
  acos := F64.acos
  atan := F64.atan
  atan2 := F64.atan2
  sinh := F64.sinh
  cosh := F64.cosh
  tanh := F64.tanh
  asinh := F64.asinh
  acosh := F64.acosh
  atanh := F64.atanh
  pow := F64.pow
  abs := Float.abs

/-- `Float32` with Julia's own `Float32` kernels (`JuliaBase.F32.sin`, …), bit for bit. -/
instance : Analytic Float32 where
  sqrt := Float32.sqrt
  cbrt := F32.cbrt
  exp := F32.exp
  expm1 := F32.expm1
  log := F32.log
  log1p := F32.log1p
  sin := F32.sin
  cos := F32.cos
  tan := F32.tan
  asin := F32.asin
  acos := F32.acos
  atan := F32.atan
  atan2 := F32.atan2
  sinh := F32.sinh
  cosh := F32.cosh
  tanh := F32.tanh
  asinh := F32.asinh
  acosh := F32.acosh
  atanh := F32.atanh
  pow := F32.pow
  abs := Float32.abs

/-- The principal cube root `z^(1/3)` of a `ComplexF64` (Julia has no complex `cbrt`,
a `MethodError`; port-notes/grassmann-composite.md). -/
@[inline] def complexCbrt (z : Complex Float) : Complex Float := ComplexF64.pow z ⟨1 / 3, 0⟩

/-- Complex two-argument arctangent, `-i log((x + iy)/√(x² + y²))` (Julia has no complex
`atan(y, x)`); for real arguments it is `atan(y, x)` up to rounding. -/
def complexAtan2 (y x : Complex Float) : Complex Float :=
  let w := x + (⟨0, 1⟩ : Complex Float) * y
  let l := ComplexF64.log (ComplexF64.div w (ComplexF64.sqrt (x * x + y * y)))
  ⟨l.im, -l.re⟩

/-- `Complex Float` via Julia's complex algorithms (`JuliaBase.ComplexF64`, Julia
`base/complex.jl`), plus `complexCbrt` and `complexAtan2` where Julia has no method. -/
instance : Analytic (Complex Float) where
  sqrt := ComplexF64.sqrt
  cbrt := complexCbrt
  exp := ComplexF64.exp
  expm1 := ComplexF64.expm1
  log := ComplexF64.log
  log1p := ComplexF64.log1p
  sin := ComplexF64.sin
  cos := ComplexF64.cos
  tan := ComplexF64.tan
  asin := ComplexF64.asin
  acos := ComplexF64.acos
  atan := ComplexF64.atan
  atan2 := complexAtan2
  sinh := ComplexF64.sinh
  cosh := ComplexF64.cosh
  tanh := ComplexF64.tanh
  asinh := ComplexF64.asinh
  acosh := ComplexF64.acosh
  atanh := ComplexF64.atanh
  pow := ComplexF64.pow
  abs z := ⟨ComplexF64.abs z, 0⟩

end AbstractTensors

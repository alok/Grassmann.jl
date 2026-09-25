/-
Scalar and single-blade helpers of the composite (transcendental) layer
(Grassmann.jl `src/composite.jl`; port-notes/grassmann-composite.md §3, §4.3.4).

* hoisted `Float` constants (docs/PERF.md: a decimal literal inlined into a
  specialized loop can stay a runtime `Float.ofScientific` call);
* Julia's `≈` on norms and the `isscalar` test (`src/multivectors.jl:1140`);
* Grassmann's two-argument hyperbolic arctangent `atanh(y, x)` (`C:636-705`),
  the hyperbolic twin of `atan(y, x)` used by `angle` of a hyperbolic `Couple`;
* blade squares, blade norms and single-blade products for a runtime blade
  mask. Julia evaluates `B ⟑ B` at compile time (the blade is a type
  parameter); here the blade is data, so the common signature spaces take an
  allocation-free bit path and every other space falls back to DirectSum's
  exact blade rules (`TensorBundle.terms₂`).
-/
import Grassmann.Algebra.Norms

namespace Grassmann.Composite

open DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase

/-! ## Constants -/

/-- `0.0`. -/
def f0 : Float := f64! 0.0
/-- `1.0`. -/
def f1 : Float := f64! 1.0
/-- `2.0`. -/
def f2 : Float := f64! 2.0
/-- `3.0`. -/
def f3 : Float := f64! 3.0
/-- `6.0` (the `sinh` series denominator `3!`). -/
def f6 : Float := f64! 6.0
/-- `24.0` (the `cosh` series denominator `4!`). -/
def f24 : Float := f64! 24.0
/-- `0.5`. -/
def fhalf : Float := f64! 0.5
/-- `-0.5` (the PGA closed form of `exp`, `C:145`). -/
def fmhalf : Float := -(f64! 0.5)
/-- `1e-5`, the PGA closed form's small-angle cutoff (`C:144`). -/
def pgaCut : Float := f64! 1.0e-5
/-- A quiet NaN (the value of an operation Julia rejects with an exception). -/
def nan : Float := F64.nan

/-- A natural number as a `Float` through `UInt64` (docs/PERF.md: no `Nat.toFloat` in
hot loops). -/
@[inline] def natF (k : Nat) : Float := k.toUInt64.toFloat

/-- Julia `a ≈ b` on two `Float64`s (`Base.isapprox`, `rtol = √eps`, `atol = 0`): the
series stopping test and the `isscalar` test. -/
@[inline] def approx (a b : Float) : Bool := F64.isapprox a b

/-- Julia `isscalar(t) = norm(t) ≈ norm(scalar(t))` (`src/multivectors.jl:1140`) from the
two norms: an element whose non-scalar part is below ~1.7e-4 of its scalar part counts
as a scalar. -/
@[inline] def isScalarNorms (normAll scalarPart : Float) : Bool := approx normAll scalarPart.abs

/-- `sin θ / θ` with the removable singularity filled in (`1` at `θ = 0`). Julia's closed
form of `exp` divides unguarded and returns `NaN` for a zero angle
(port-notes/grassmann-composite.md §8.3 item 2, fixed here). -/
@[inline] def sinOver (θ : Float) : Float := if θ == f0 then f1 else Float.sin θ / θ

/-- `sinh θ / θ` with the removable singularity filled in (see `sinOver`). -/
@[inline] def sinhOver (θ : Float) : Float := if θ == f0 then f1 else Float.sinh θ / θ

/-! ## Grassmann's two-argument `atanh(y, x)` (`C:636-705`) -/

/-- `π/2 + ½·PI_LO` of Julia's `atan(y, x)` template (`Base.Math.ATAN2_PI_LO(Float64)`). -/
def atanhHuge : Float := F64.pi / f2 + fhalf * f64! 1.2246467991473532e-16

/-- The high 32 bits of the IEEE pattern with the sign cleared (`Base.Math.poshighword`). -/
@[inline] def poshighword (x : Float) : UInt32 := ((x.toBits >>> 32) &&& 0x7FFFFFFF).toUInt32

/-- Grassmann's `atanh(y::Float64, x::Float64)` (`src/composite.jl:636-705`), adapted from
Julia's `atan(y, x)`: effectively `sign(y)·atanh(|y/x|)`, the sign of `x` ignored, with
the special cases of the template. Where Julia throws `DomainError` (`|y/x| > 1`, `x = 0`,
infinite `y`) this returns `NaN` (from `Float.atanh`); the `k > 60` branch returns the
template's `≈ π/2`, an artefact Julia shares (port-notes/grassmann-composite.md §4.3.4). -/
def atanh2 (y x : Float) : Float :=
  if x.isNaN || y.isNaN then nan
  else if x == f1 || x == -f1 then Float.atanh y
  else
    let m : Nat := (if F64.signbit x then 2 else 0) + (if F64.signbit y then 1 else 0)
    if y == f0 then y
    else if x == f0 then Float.atanh (F64.copysign F64.inf y)
    else if x.isInf then
      if y.isInf then y
      else if m == 0 || m == 2 then f0 else -f0
    else if y.isInf then Float.atanh y
    else
      -- `k = reinterpret(Int32, poshighword(y) - poshighword(x)) >> 20`
      let k : Int32 := (poshighword y - poshighword x).toInt32 >>> 20
      let (z, m) :=
        if k > 60 then (atanhHuge, m &&& 1)
        else if x < f0 && k < -60 then (f0, m)
        else (Float.atanh (y / x).abs, m)
      if m == 0 || m == 2 then z else -z

/-! ## Blades of a runtime mask -/

/-- Whether `V` is a plain signature space (no null generators, tangent variables or
dual/mixed structure): its blade products are signs of `e_{a xor b}` given by bit
parities (DirectSum `mulSign`). -/
@[inline] def plainSignature (V : TensorBundle) : Bool :=
  (match V.metric with | .signature _ | .euclid => true | _ => false) &&
    !V.hasinf && !V.hasorigin && V.diffvars == 0 && V.dyadmode == 0

/-- The scalar coefficient of `e_a ⟑ e_b` when that product is a scalar multiple of
`e_c` (the first scalar-valued term of DirectSum's exact product). -/
def productCoef (V : TensorBundle) (op : BinOp) (a b c : UInt64) : Float :=
  match V.terms₂ op a b with
  | .ok ts => match ts.find? (fun (t : BladeTerm) => t.bits == c && t.z == 0) with
    | some t => F64.ofRat t.coef
    | none => f0
  | .error _ => nan

/-- Julia `value(B ⟑ B)` for a blade mask `b`: the scalar a blade squares to (every
blade does, in every metric; `0` for a null blade). -/
def bladeSq (V : TensorBundle) (b : UInt64) : Float :=
  if plainSignature V then (if V.mulSign b b then -f1 else f1)
  else productCoef V .mul b b 0

/-- Julia `abs2_inv(B) = value(contraction(B, B)) = ⟨~B ⟑ B⟩₀` for a blade mask `b`
(`src/algebra.jl:473`; `+1` for Euclidean blades). -/
def bladeAbs2 (V : TensorBundle) (b : UInt64) : Float :=
  if plainSignature V then
    let s := if V.mulSign b b then -f1 else f1
    if Leibniz.parityreverse (popcount b) then -s else s
  else productCoef V .contraction b b 0

/-- `e_a ⟑ e_b` as `(coefficient, blade)` when it is a single term (a pseudoscalar
factor, a blade squared, blades of a diagonal metric); the coefficient is `0` when the
product vanishes. For a product with several terms (non-diagonal metrics) only the
first term is returned: callers use it where one term is guaranteed. -/
def bladeMul (V : TensorBundle) (a b : UInt64) : Float × UInt64 :=
  if plainSignature V then (if V.mulSign a b then -f1 else f1, a ^^^ b)
  else match V.terms₂ .mul a b with
    | .ok ts => match ts.find? (·.z == 0) with
      | some t => (F64.ofRat t.coef, t.bits)
      | none => (f0, a ^^^ b)
    | .error _ => (nan, a ^^^ b)

/-- The pseudoscalar mask of `V` (Julia `V(I)`: the non-tangent generators). -/
@[inline] def pseudoMask (V : TensorBundle) : UInt64 := V.pseudoscalar

/-- Julia `inv(I)` for the pseudoscalar `I` as its coefficient on `I`:
`(parityreverse(grade I) ? -1 : 1) / abs2_inv(I)` (`src/algebra.jl:534-535`). -/
def invPseudoCoef (V : TensorBundle) : Float :=
  let i := pseudoMask V
  let s := if Leibniz.parityreverse (popcount i) then -f1 else f1
  s / bladeAbs2 V i

/-- Julia `iszero(metric(V))` (`src/composite.jl:367`, `:442`): a `Signature` without
negative generators or the Euclidean `Int` space. A `DiagonalForm`'s `metric` is a cache
index in Julia (not a sign word), so those spaces take the general branch. -/
def zeroMetric (V : TensorBundle) : Bool :=
  match V.metric with
  | .signature s => s == 0
  | .euclid => true
  | _ => false

/-- Julia `isR301(V)` (`src/composite.jl:175-177`): the `DiagonalForm` `⟨1,1,1,0⟩` of 3D
projective geometric algebra (`S"+++0"` or `D"0,1,1,1"` do not count). -/
def isR301 (V : TensorBundle) : Bool :=
  match V.metric with
  | .diagonal d => d == #[1, 1, 1, 0] && V.n == 4 && V.diffvars == 0 && V.dyadmode == 0
  | _ => false

end Grassmann.Composite

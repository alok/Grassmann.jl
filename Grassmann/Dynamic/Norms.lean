/-
`abs2`, `norm` and `isscalar` of dynamic elements with Julia's result kinds
(AbstractTensors `src/AbstractTensors.jl:435-444`, Grassmann `src/multivectors.jl:669-695,
1140-1144`, `src/algebra.jl:473`; StaticVectors `src/linalg.jl:90-110`).

* `abs2(t) = contraction(t, t)` for a graded `t` (terms and chains; `abs2(𝟎) = 𝟎`,
  `abs2(∞) = ∞`);
* `abs2(t) = (a = (~t)⟑t; isscalar(a) ? scalar(a) : a)` for a `Spinor`, `CoSpinor` or
  `Multivector`;
* `abs2(z::Couple{V,B}) = abs2(re) + abs2(im)·abs2_inv(B)` (a scalar `Single`),
  `abs2(z::PseudoCouple{V,B}) = abs2(re)·abs2_inv(B) + abs2(im)·abs2_inv(V)`, plus
  `2⋆B·(re·im)` when `~B⟑I = ~I⟑B`;
* `norm(t) = norm(value(t))`: `abs(float(x))` for a term's value, the StaticVectors 2-norm
  `sqrt(abs2(v₁) + abs2(v₂) + ⋯)` of a container's or couple's values.

Coefficient `abs2` is `conj(x)·x` (Julia `abs2(x::Real) = x*x`); a complex coefficient's
`abs2` is real in Julia and a complex number with zero imaginary part here. Phasors are
not supported (`complexify` them first).
-/
import Grassmann.Dynamic.Products

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase

namespace TA

variable {V : TensorBundle} {α : Type} [Coeff α] [Kernels V]

/-- Julia `norm(t) = norm(value(t))` (AbstractTensors `src/AbstractTensors.jl:442`):
`abs(float(x))` of a term's value (`1` for `One` and a basis blade, `0` for `𝟎`, `Inf` for
`∞`), the StaticVectors 2-norm of a container's or couple's values. -/
def norm [JNorm α] : TA V α → Float
  | zero => 0
  | one | blade _ => 1
  | infinity => Float.inf
  | single _ x => JNorm.norm x
  | chain _ c => c.v.norm
  | spinor h | cospinor h => h.v.norm
  | multi m => m.v.norm
  | couple _ re im | pseudo _ re im => Float.sqrt (JNorm.abs2 re + JNorm.abs2 im)
  | phasor .. => panic! "TA.norm: complexify a Phasor first (Julia `complexify`)"

/-- Julia `isscalar(t) = norm(t) ≈ norm(scalar(t))` (`src/multivectors.jl:1140`), with
`Float64`'s default `isapprox` tolerance. -/
def isscalar [JNorm α] (t : TA V α) : Bool :=
  F64.isapprox (norm t) (norm (scalar t))

/-- Julia `abs2_inv(B) = abs2(B)` of a basis blade: the scalar `contraction(B, B)`. -/
@[inline] def abs2Inv (V : TensorBundle) (B : UInt64) : Rat := scalarCoef V .contraction B B

/-- `x · abs2_inv(B)` as Julia's `Number * TensorTerm{V,0}`: `x` itself for `One`,
`x·c` for `Single(c)`, `𝟎` when `c = 0`. -/
def scaleInv (c : Rat) (x : α) : TA V α :=
  if c == 0 then zero else single 0 (scaleBy c x)

/-- Julia `abs2(t)` with Julia's result kinds (see the module docstring). -/
def abs2 [Conj α] [JNorm α] (t : TA V α) : TA V α :=
  let sq := fun (x : α) => Conj.conj x * x
  match t with
  | zero => zero
  | infinity => infinity
  | couple b re im =>
    let c := abs2Inv V b
    if c == 0 then single 0 (sq re) else single 0 (sq re + scaleBy c (sq im))
  | pseudo b re im =>
    let I := pseudoBits V
    let out : TA V α := scaleInv (abs2Inv V b) (sq re) + scaleInv (abs2Inv V I) (sq im)
    let lhs : TA V Rat := mul (reverse (blade b)) (blade I)
    let rhs : TA V Rat := mul (reverse (blade I)) (blade b)
    let same := (List.range (2 ^ V.n)).all fun i =>
      lhs.coeff (fullBlade V.n i) == rhs.coeff (fullBlade V.n i)
    if !same then out
    else out + mulScalar (hodge (single b (Coeff.ofInt 2))) (re * im)
  | spinor _ | cospinor _ | multi _ =>
    let a := mul (reverse t) t
    if isscalar a then scalar a else a
  | phasor .. => panic! "TA.abs2: complexify a Phasor first (Julia `complexify`)"
  | t => contraction t t

end TA

end Grassmann

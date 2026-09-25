/-
Julia's kind predicates and the graded aliases (AbstractTensors.jl `src/AbstractTensors.jl:27-206,
366-367, 445-446, 590-592`).

* `istensor`, `ismanifold`, `isgraded`, `isterm`, `ismixed`: Julia tests `t isa TensorAlgebra`
  (… `Manifold`, `TensorGraded`, `TensorTerm`, `TensorMixed`); here they are decided by the kind
  instances a type has (`TensorKind`, found by instance resolution, `false` for anything else).
* `isscalar`, `isvector`, `isbivector`, `istrivector`, `isvolume`: `rank(t) == G || iszero(t)`
  for a graded element (`TensorZero` supplies `iszero`: every coefficient zero, from the
  element's `value`).
* `isnull(t) = iszero(t)`, `isone(t)` (`norm(t) ≈ value(scalar(t)) ≈ 1`), `norm2 a b = norm(a - b)`
  (Julia's two-argument `norm`), `isfinite` of a term.
* `Scalar`, `GradedVector`, `Bivector`, `Trivector`: the classes `TensorGraded X M V G T` at
  `G = 0, 1, 2, 3` (Julia's `const Scalar{V,T} = TensorGraded{V,0,T}`, …).
-/
import AbstractTensors.Ops
import StaticVectors.LinAlg

universe u v w

namespace AbstractTensors

open StaticVectors JuliaBase

/-! ## Graded aliases (AT:64-100) -/

/-- Julia `Scalar{V,T} = TensorGraded{V,0,T}`. -/
abbrev Scalar (X : Type u) (M : Type v) (V : M) (T : Type w) : Prop := TensorGraded X M V 0 T
/-- Julia `GradedVector{V,T} = TensorGraded{V,1,T}`. -/
abbrev GradedVector (X : Type u) (M : Type v) (V : M) (T : Type w) : Prop := TensorGraded X M V 1 T
/-- Julia `Bivector{V,T} = TensorGraded{V,2,T}`. -/
abbrev Bivector (X : Type u) (M : Type v) (V : M) (T : Type w) : Prop := TensorGraded X M V 2 T
/-- Julia `Trivector{V,T} = TensorGraded{V,3,T}`. -/
abbrev Trivector (X : Type u) (M : Type v) (V : M) (T : Type w) : Prop := TensorGraded X M V 3 T

/-! ## Type-membership predicates (AT:37-129) -/

/-- Which of Julia's abstract tensor types `X` belongs to (`X <: TensorAlgebra`, `Manifold`,
`TensorGraded`, `TensorTerm`, `TensorMixed`). Instances follow the kind classes; every other
type gets the all-`false` instance. -/
class TensorKind (X : Type u) where
  /-- `X <: TensorAlgebra` (Julia `istensor`). -/
  istensor : Bool
  /-- `X <: Manifold` (Julia `ismanifold`; graded elements are manifolds in Julia). -/
  ismanifold : Bool
  /-- `X <: TensorGraded` (Julia `isgraded`). -/
  isgraded : Bool
  /-- `X <: TensorTerm` (Julia `isterm`). -/
  isterm : Bool
  /-- `X <: TensorMixed` (Julia `ismixed`). -/
  ismixed : Bool

/-- Anything else: not a tensor (Julia's fallback `istensor(t) = false`, …). -/
instance (priority := low) instTensorKindDefault {X : Type u} : TensorKind X :=
  ⟨false, false, false, false, false⟩

/-- `X <: TensorAlgebra`. -/
instance (priority := low + 1) instTensorKindAlgebra {X : Type u} {M : Type v} {V : M} {T : Type w}
    [TensorAlgebra X M V T] : TensorKind X := ⟨true, false, false, false, false⟩

/-- `X <: TensorMixed <: TensorAlgebra`. -/
instance (priority := low + 2) instTensorKindMixed {X : Type u} {M : Type v} {V : M} {T : Type w}
    [TensorMixed X M V T] : TensorKind X := ⟨true, false, false, false, true⟩

/-- `X <: TensorGraded <: Manifold <: TensorAlgebra`. -/
instance (priority := low + 3) instTensorKindGraded {X : Type u} {M : Type v} {V : M} {G : Nat}
    {T : Type w} [TensorGraded X M V G T] : TensorKind X := ⟨true, true, true, false, false⟩

/-- `X <: TensorTerm <: TensorGraded`. -/
instance (priority := low + 4) instTensorKindTerm {X : Type u} {M : Type v} {V : M} {G : Nat}
    {T : Type w} [TensorTerm X M V G T] : TensorKind X := ⟨true, true, true, true, false⟩

section Kind

variable {X : Type u} [TensorKind X]

/-- Julia `istensor(t)`: `t isa TensorAlgebra` (AT:37). -/
def istensor (_ : X) : Bool := TensorKind.istensor X
/-- Julia `ismanifold(t)`: `t isa Manifold` (AT:51). -/
def ismanifold (_ : X) : Bool := TensorKind.ismanifold X
/-- Julia `isgraded(t)`: `t isa TensorGraded` (AT:69). -/
def isgraded (_ : X) : Bool := TensorKind.isgraded X
/-- Julia `isterm(t)`: `t isa TensorTerm` (AT:113). -/
def isterm (_ : X) : Bool := TensorKind.isterm X
/-- Julia `ismixed(t)`: `t isa TensorMixed` (AT:129). -/
def ismixed (_ : X) : Bool := TensorKind.ismixed X

end Kind

/-! ## Zero tests and grade predicates (AT:183-206, 445, 590-592) -/

/-- Julia `iszero(t)` for a tensor (`norm(t) ≈ 0`, AT:445, which holds exactly when every
coefficient is zero). -/
class TensorZero (X : Type u) where
  /-- Every coefficient is zero. -/
  isZero : X → Bool

/-- A tensor whose `value` is a `Values` vector is zero when every coefficient is. -/
instance (priority := low) instTensorZeroOfValue {X : Type u} {α : Type} {n : Nat}
    [Coeff α] [Value X (Values α n)] : TensorZero X :=
  ⟨fun t => (value t).all Coeff.isZero⟩

/-- A scalar is zero when it is (`Coeff.isZero`). -/
instance (priority := low) instTensorZeroCoeff {α : Type} [Coeff α] : TensorZero α := ⟨Coeff.isZero⟩

section Grades

variable {X : Type u} {M : Type v} {V : M} {G : Nat} {T : Type w} [TensorZero X]

/-- Julia `isscalar(t) = rank(t) == 0 || iszero(t)` (AT:194). -/
def isscalar [TensorGraded X M V G T] (t : X) : Bool := G == 0 || TensorZero.isZero t
/-- Julia `isvector(t) = rank(t) == 1 || iszero(t)` (AT:194). -/
def isvector [TensorGraded X M V G T] (t : X) : Bool := G == 1 || TensorZero.isZero t
/-- Julia `isbivector(t) = rank(t) == 2 || iszero(t)` (AT:194). -/
def isbivector [TensorGraded X M V G T] (t : X) : Bool := G == 2 || TensorZero.isZero t
/-- Julia `istrivector(t) = rank(t) == 3 || iszero(t)` (AT:194). -/
def istrivector [TensorGraded X M V G T] (t : X) : Bool := G == 3 || TensorZero.isZero t
/-- Julia `isvolume(t) = rank(t) == mdims(t) || iszero(t)` (AT:206). -/
def isvolume [TensorGraded X M V G T] [HasMDims M] (t : X) : Bool :=
  G == HasMDims.mdims V || TensorZero.isZero t

end Grades

/-- Julia `norm(t) = norm(value(t))` (AT:444) as a class, so the generic predicates below work
for any element type that provides it. -/
class TensorNorm (X : Type u) where
  /-- The Euclidean norm of the coefficients. -/
  norm : X → Float

/-- A tensor whose `value` is a `Values` vector: the norm of that vector. -/
instance (priority := low) instTensorNormOfValue {X : Type u} {α : Type} {n : Nat}
    [Coeff α] [JNorm α] [Value X (Values α n)] : TensorNorm X :=
  ⟨fun t => (value t).norm⟩

/-- Julia `isnull(n) = iszero(n)` (AT:592). -/
def isnull {X : Type u} [TensorZero X] (t : X) : Bool := TensorZero.isZero t

/-- Julia `isone(t) = norm(t) ≈ value(scalar(t)) ≈ 1` (AT:446): the scalar coefficient is `≈ 1`
(with its type's default tolerance) and the norm of the whole element is `≈` its size. -/
def isone {X : Type u} {S : Type v} {α : Type} {n : Nat} [TensorNorm X] [GradeProj X 0 S] [Coeff α]
    [Value S (Values α n)] [JNorm α] [JApprox α] (t : X) : Bool :=
  let v := value (scalar t)
  match n, v with
  | 0, _ => false
  | _ + 1, v =>
    let x := v[0]
    JApprox.isapprox x Coeff.one 0 (JApprox.rtolDefault α) false &&
      F64.isapprox (TensorNorm.norm t) (JNorm.norm x)

/-- Julia's two-argument `norm(a, b) = norm(a - b)` for graded or mixed tensors (AT:366-367). -/
def norm2 {X : Type u} [Sub X] [TensorNorm X] (a b : X) : Float := TensorNorm.norm (a - b)

/-- Julia `isfinite(b::TensorTerm) = isfinite(value(b))` (AT:117), for a term with a `Float`
coefficient. -/
def isfiniteTerm {X : Type u} {M : Type v} {V : M} {G : Nat} [TensorTerm X M V G Float]
    [Value X Float] (t : X) : Bool := F64.isfinite (value t)

end AbstractTensors

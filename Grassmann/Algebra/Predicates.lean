/-
Julia's element predicates on the typed layer, and left division `a \ b`
(AbstractTensors `src/AbstractTensors.jl:37-117, 183-206, 323, 444`; Grassmann.jl
`src/multivectors.jl:1140-1144`, `src/algebra.jl:401`).

Julia answers `istensor`, `isgraded`, `isterm` from the abstract type tree
(`TensorAlgebra ⊃ TensorGraded ⊃ TensorTerm`); here the class `ElementKind X` records the
same facts for each element type:

| type | Julia supertype | `isterm` | `isgraded` / `rank?` |
|---|---|---|---|
| `Submanifold V G`, `Single V G α` | `TensorTerm{V,G}` | `true` | `some G` |
| `Chain V G α` | `TensorGraded{V,G}` | `false` | `some G` |
| `Half V p α`, `Multivector V α`, `Couple V α`, `PseudoCouple V α` | `TensorMixed` / `AbstractSpinor` | `false` | `none` |

The part predicates follow Julia's two rules: a graded element `t` is a vector
(bivector, …) when `rank(t) == 1 || iszero(t)`, any other element when
`norm(t) ≈ norm(vector(t))` (`Float64`'s default `isapprox`); `iszero(t)` is
`norm(t) ≈ 0`, i.e. `norm(t) == 0`. The dynamic layer has the same predicates on `TA V α`
(`Grassmann/Dynamic/Ops.lean`), where the kind is a runtime value.
-/
import Grassmann.Algebra.Norms
import Grassmann.Notation

namespace Grassmann

open DirectSum StaticVectors AbstractTensors JuliaBase

/-- The place of an element type in Julia's type tree: whether it is a `TensorTerm`
(a basis blade or a `Single`) and, for a `TensorGraded` type, its grade. -/
class ElementKind (X : Type) where
  /-- Julia `X <: TensorTerm`. -/
  isterm : Bool
  /-- `some G` for Julia `X <: TensorGraded{V,G}`, `none` for a mixed element. -/
  rank? : Option Nat

section Instances

variable {V : TensorBundle} {G : Nat} {p : Bool} {α : Type} [Coeff α]

instance : ElementKind (Submanifold V G) := ⟨true, some G⟩
instance : ElementKind (Single V G α) := ⟨true, some G⟩
instance : ElementKind (Chain V G α) := ⟨false, some G⟩
instance : ElementKind (Half V p α) := ⟨false, none⟩
instance : ElementKind (Multivector V α) := ⟨false, none⟩
instance : ElementKind (Couple V α) := ⟨false, none⟩
instance : ElementKind (PseudoCouple V α) := ⟨false, none⟩

end Instances

variable {X Y Z : Type} {V : TensorBundle} {α : Type} [Coeff α]

/-- Julia `istensor(t)` (`src/AbstractTensors.jl:41`): every element type here is a
`TensorAlgebra`. -/
@[inline] def istensor [ElementKind X] (_ : X) : Bool := true

/-- Julia `isterm(t)` (`src/AbstractTensors.jl:115`): a basis blade or a `Single`. -/
@[inline] def isterm [ElementKind X] (_ : X) : Bool := ElementKind.isterm X

/-- Julia `isgraded(t)` (`src/AbstractTensors.jl:72`): a term or a `Chain`. -/
@[inline] def isgraded [ElementKind X] (_ : X) : Bool := (ElementKind.rank? X).isSome

/-- Julia `rank(t)` of a graded element; `none` for a mixed one (Julia has no method). -/
@[inline] def rank? [ElementKind X] (_ : X) : Option Nat := ElementKind.rank? X

variable [JNorm α] [DenseLayout X V α]

/-- Julia `iszero(t) = norm(t) ≈ 0` (`src/AbstractTensors.jl:443`), i.e. every coefficient
is zero. -/
@[inline] def iszero (x : X) : Bool := norm x == 0

variable [ElementKind X]

/-- `rank(t) == k || iszero(t)` for a graded element, `norm(t) ≈ norm(grade(t, k))` for a
mixed one (AbstractTensors `src/AbstractTensors.jl:183-196`, Grassmann
`src/multivectors.jl:1140-1144`). -/
def isPart (k : Nat) (x : X) : Bool :=
  match ElementKind.rank? X with
  | some g => g == k || iszero x
  | none => F64.isapprox (norm x) (gradePart x k).v.norm

/-- Julia `isscalar(t)`. -/
@[inline] def isscalar (x : X) : Bool := isPart 0 x
/-- Julia `isvector(t)`. -/
@[inline] def isvector (x : X) : Bool := isPart 1 x
/-- Julia `isbivector(t)`. -/
@[inline] def isbivector (x : X) : Bool := isPart 2 x
/-- Julia `istrivector(t)`. -/
@[inline] def istrivector (x : X) : Bool := isPart 3 x
/-- Julia `isvolume(t)` (`src/AbstractTensors.jl:206`): `rank(t) == mdims(t) || iszero(t)`
for a graded element, `norm(t) ≈ norm(volume(t))` otherwise. -/
@[inline] def isvolume (x : X) : Bool := isPart V.n x

/-- Julia `isone(t) = norm(t) ≈ value(scalar(t)) ≈ 1` (`src/AbstractTensors.jl:444`), with
`α`'s default tolerance for the last comparison. -/
def isone [JApprox α] (x : X) : Bool :=
  let s := scalarValue x
  JApprox.isapprox s Coeff.one 0 (JApprox.rtolDefault (α := α)) false &&
    F64.isapprox (norm x) (JNorm.norm s)

/-- Julia `isfinite(t)`: every coefficient is finite (Julia defines it for terms,
`isfinite(value(t))`, `src/AbstractTensors.jl:117`; containers extend it coefficientwise). -/
def isfinite (x : X) : Bool := (DenseLayout.values x).all fun c => (JNorm.norm c).isFinite

omit [DenseLayout X V α] [ElementKind X]

/-- Julia `a ∥ b = iszero(a ∧ b)` (Grassmann `src/algebra.jl:401`). -/
@[inline] def parallel [Wedge Y X Z] [DenseLayout Z V α] (a : Y) (b : X) : Bool :=
  iszero (Wedge.wedge a b : Z)

/-- `a ∥ b` between typed elements (`iszero(a ∧ b)`). -/
instance (priority := low) [Wedge Y X Z] [DenseLayout Z V α] : Parallel Y X := ⟨parallel⟩

omit [JNorm α]

/-- Julia `a \ b = inv(a) ⟑ b` (left division, AbstractTensors `src/AbstractTensors.jl:323`)
between typed elements: the typed inverse of `a` (`Chain`, `Single`, `Half`,
`Multivector`, `Couple`; `Grassmann/Algebra/Norms.lean`) times `b`. -/
instance (priority := low) [Inv X] [HMul X Y Z] : LeftDiv X Y Z := ⟨fun a b => a⁻¹ * b⟩

end Grassmann

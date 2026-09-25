/-
Vector calculus of Grassmann elements: Julia's `∇`, `Δ`, `∂`/`boundary`, `d`/`differential`,
`δ`/`codifferential`, `gradient`/`grad`, `divergence` and `curl` (Grassmann.jl
`src/Grassmann.jl:74-112`, `src/composite.jl:942-951`; Leibniz.jl `src/Leibniz.jl:107-175`;
port-notes/leibniz.md §6.1).

Julia's `∇ = Derivation(I)` is an abstract first-order derivation; a space turns it into an
element with `V(∇)` (`src/Grassmann.jl:88-97`):

* in a space without tangent variables (and for order `0`), `V(∇ᴼ) = Chain{V,1}(λ·ones(n))`,
  the vector with a `1` on every generator (`λ = 1` for `∇`, `Δ = ∇²` and every power):
  `nabla V α` here (`laplacian` is the same vector);
* in a tangent space (`tangent(V, μ, ν)`), the order-1 derivation is `Σₖ ∂ₖvₖ`, the geometric
  products of the tangent generators with the vectors (`∂₁` for every `vₖ` when `ν = 1`,
  half of the vectors of a dyadic space): `tangentNabla`, and `nablaM` chooses between the two
  as Julia does. Higher orders in a tangent space, `(∇⋅∇)^⌊O/2⌋`, have symbolic
  (`∂ₖ⊗∂ₖ`) coefficients in Julia and are not provided.

The operators are Julia's one-liners on `V(∇)`:

| Julia | here | definition |
|---|---|---|
| `∂(ω)`, `boundary` | `boundary`, prefix `∂` | `ω ⋅ V(∇)` (right contraction) |
| `d(ω)`, `differential` | `differential`, `d` | `V(∇) ∧ ω` |
| `δ(ω)`, `codifferential` | `codifferential`, `δ` | `-∂(ω)` |
| `gradient(m)`, `grad` | `gradient`, `grad` | `d(m)` |
| `divergence(m)`, `div` | `divergence` | `∂(m)` |
| `curl(m)` | `curl` | `V(∇) × m = ⋆(V(∇) ∧ m)` |
| `∂(ω::Chain{V,1,<:Chain{W,1}})` | `simplexBoundary`, `∂` | `∧(ω) ⋅ Λ(W).v1` |

The typed operators (`boundary`, `differential`, …) take any element of a space without
tangent variables and return the type of the corresponding product with a vector (a grade-`g`
chain goes to grade `g - 1` or `g + 1`, a multivector to a multivector); the multivector forms
(`boundaryM`, `differentialM`, `codifferentialM`, `curlM`) use `nablaM` and so also cover
tangent spaces.

Fixed Julia defects: `∂` of a scalar chain and `d`, `gradient`, `curl` of a top-grade chain
throw a `MethodError` in Julia (`zeros(::Expr)` in the generated product), and `δ` of an
element whose boundary is `Zero` throws (`-(::Zero)`); here they are zero.
-/
import Grassmann.Forms.Compound

namespace Grassmann.Calculus

open DirectSum DirectSum.Bits StaticVectors AbstractTensors Grassmann.Forms

variable {V W : TensorBundle} {α : Type} [Coeff α] {X Y : Type}

/-! ## `V(∇)` -/

/-- Julia `V(∇)` (and `V(Δ)`, `V(∇ᴼ)`) of a space without tangent variables
(`src/Grassmann.jl:88-89`): `Chain{V,1}(λ·ones(n))`, `λ = 1`, a `1` on every generator. -/
def nabla (V : TensorBundle) (α : Type) [Coeff α] : Chain V 1 α := ⟨Values.ofFn fun _ => Coeff.one⟩

/-- Julia `V(Δ)`, `Δ = ∇²` (`Leibniz.jl:155`), of a space without tangent variables: the same
`λ·ones` (`λ = 1² = 1`). -/
abbrev laplacian (V : TensorBundle) (α : Type) [Coeff α] : Chain V 1 α := nabla V α

/-- The unit vector `v_{k+1}` (bit `k`) as a multivector. -/
def unitMV (V : TensorBundle) (α : Type) [Coeff α] (k : Nat) : Multivector V α :=
  Multivector.ofBlade (⟨(1 : UInt64) <<< k.toUInt64⟩ : Submanifold V 1) Coeff.one

/-- The order-1 derivation `Σₖ ∂ₖvₖ` of a tangent space (Julia `V(∇)`,
`src/Grassmann.jl:90-93`): `getbasis(V, 1 << (ν = 1 ? G : k + G)) * getbasis(V, 1 << k)`
for `k < G` (`k < G/2` in a dyadic space), `G = grade(V)` the number of non-tangent
generators; the geometric products follow the space's tangent rules. -/
def tangentNabla (V : TensorBundle) (α : Type) [Coeff α] [Kernels V] : Multivector V α :=
  let G := V.grade
  let m := if V.isdyadic then G / 2 else G
  (List.range m).foldl (init := Multivector.zero) fun acc k =>
    let a := if V.diffvars == 1 then G else k + G
    acc + unitMV V α a * unitMV V α k

/-- Julia `V(∇)` of any space as a multivector: `nabla` without tangent variables,
`tangentNabla` in a tangent space. -/
def nablaM (V : TensorBundle) (α : Type) [Coeff α] [Kernels V] : Multivector V α :=
  if V.diffvars == 0 then toMultivector (nabla V α) else tangentNabla V α

/-! ## The operators (spaces without tangent variables) -/

/-- Julia `∂(ω) = ω ⋅ V(∇)` (`boundary`, `src/Grassmann.jl:110`): the right contraction with
the all-ones vector (a grade-`g` chain goes to grade `g - 1`, `Σᵢ ωᵢ` for a vector). -/
@[inline] def boundary [DenseLayout X V α] [Contraction X (Chain V 1 α) Y] (ω : X) : Y :=
  contraction ω (nabla V α)

/-- Julia `d(ω) = V(∇) ∧ ω` (`differential`, `src/Grassmann.jl:111`). -/
@[inline] def differential [DenseLayout X V α] [Wedge (Chain V 1 α) X Y] (ω : X) : Y :=
  wedge (nabla V α) ω

/-- Julia `δ(ω) = -∂(ω)` (`codifferential`, `src/Grassmann.jl:112`). -/
@[inline] def codifferential [DenseLayout X V α] [Contraction X (Chain V 1 α) Y] [Neg Y] (ω : X) : Y :=
  -(boundary ω)

/-- Julia `gradient(m::TensorAlgebra) = d(m)` (`src/composite.jl:942`; the gradients of a
simplex's barycentric coordinates are `TensorOperator.gradient`). -/
@[inline] def gradient [DenseLayout X V α] [Wedge (Chain V 1 α) X Y] (m : X) : Y := differential m

/-- Julia `grad = gradient` (`src/composite.jl:972`). -/
@[inline] def grad [DenseLayout X V α] [Wedge (Chain V 1 α) X Y] (m : X) : Y := differential m

/-- Julia `divergence(m) = ∂(m)` (`src/composite.jl:948`; `Base.div(m)` there). -/
@[inline] def divergence [DenseLayout X V α] [Contraction X (Chain V 1 α) Y] (m : X) : Y := boundary m

/-- Julia `curl(m) = V(∇) × m` (`src/composite.jl:945`), `×` = `⋆(a ∧ b)` (AT:349). -/
@[inline] def curl [DenseLayout X V α] [Cross (Chain V 1 α) X Y] (m : X) : Y := cross (nabla V α) m

/-- Julia's short name `d = differential` (`Leibniz.jl:161`). -/
@[inline] def d [DenseLayout X V α] [Wedge (Chain V 1 α) X Y] (ω : X) : Y := differential ω

/-- Julia's short name `δ = codifferential` (`Leibniz.jl:161`). -/
@[inline] def δ [DenseLayout X V α] [Contraction X (Chain V 1 α) Y] [Neg Y] (ω : X) : Y := codifferential ω

/-! ## The operators of any space (tangent spaces included), as multivectors -/

section Multivector

variable [Kernels V]

/-- Julia `∂(ω) = ω ⋅ V(∇)` with `V(∇) = nablaM V α` (tangent spaces included). -/
@[inline] def boundaryM [DenseLayout X V α] (ω : X) : Multivector V α :=
  contraction (toMultivector ω) (nablaM V α)

/-- Julia `d(ω) = V(∇) ∧ ω` with `V(∇) = nablaM V α`. -/
@[inline] def differentialM [DenseLayout X V α] (ω : X) : Multivector V α :=
  wedge (nablaM V α) (toMultivector ω)

/-- Julia `δ(ω) = -∂(ω)` with `V(∇) = nablaM V α`. -/
@[inline] def codifferentialM [DenseLayout X V α] (ω : X) : Multivector V α := -(boundaryM ω)

/-- Julia `curl(m) = V(∇) × m = ⋆(V(∇) ∧ m)` with `V(∇) = nablaM V α`. -/
@[inline] def curlM [DenseLayout X V α] (m : X) : Multivector V α := hodge (differentialM m)

end Multivector

/-! ## Simplices -/

/-- Julia `∂(ω::Chain{V,1,<:Chain{W,1}}) = ∧(ω) ⋅ Λ(W).v1` (`src/Grassmann.jl:109`): the
wedge of the vertices (homogeneous coordinates, first generator `1`) contracted with `v1`, the
oriented boundary of the simplex as a grade-`(n-1)` chain of `W`. -/
@[specialize] def simplexBoundary [Kernels W] (T : Simplex V W α) : Chain W (V.n - 1) α :=
  contraction T.wedgeAll (Chain.ofBlade (⟨1⟩ : Submanifold W 1) (Coeff.one : α))

/-! ## `∂` and `∇` -/

/-- Julia's `∂` of an element or of a simplex (`src/Grassmann.jl:109-110`). -/
class Boundary (X : Type) (Y : outParam Type) where
  /-- `∂ x`. -/
  boundary : X → Y

instance (priority := low) [DenseLayout X V α] [Contraction X (Chain V 1 α) Y] : Boundary X Y :=
  ⟨Calculus.boundary⟩

instance [Kernels W] : Boundary (Simplex V W α) (Chain W (V.n - 1) α) := ⟨simplexBoundary⟩

/-- Julia's prefix `∂` (`∂(ω)`, `∂ω`). -/
scoped prefix:max "∂" => Boundary.boundary

/-- Julia's `∇` as the element of a space without tangent variables (`V(∇)`; the space and the
coefficient type come from the context: `(∇ : Chain V 1 Float) ∧ ω`). -/
scoped notation "∇" => nabla _ _

end Grassmann.Calculus

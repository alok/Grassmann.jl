/-
Kind predicates (`istensor`, `ismanifold`, `isgraded`, `isterm`, `ismixed`) and grade
predicates (`isscalar`, `isvector`, `isbivector`, `istrivector`, `isvolume`, `isnull`,
`isone`, two-argument `norm`) of AbstractTensors on Grassmann's typed elements, against the
Julia oracle (Grassmann 0.8.46; values recorded from `istensor(Chain{ℝ^3,1}(1,2,3))`, …, see
`docs/port-notes/abstracttensors-staticvectors.md`). Compile-time checks.

Julia's Grassmann overrides `isscalar` for its mixed-grade containers (`norm(t) ≈ norm(scalar(t))`,
`Grassmann.TA.isscalar` here); the AbstractTensors predicates below are the graded ones.
-/
import Grassmann

open Grassmann hiding istensor isgraded isterm isscalar isvector isbivector istrivector isvolume isone iszero isfinite
open AbstractTensors

namespace AbstractTensorsKindTests

/-- `Chain{ℝ^3,1}(1,2,3)`. -/
def c1 : Chain ℝ3 1 Int := (Chain.ofList? [1, 2, 3]).get!
/-- `Chain{ℝ^3,2}(0,0,0)`. -/
def c2 : Chain ℝ3 2 Int := (Chain.ofList? [0, 0, 0]).get!
/-- `Chain{ℝ^3,2}(1,0,0)`. -/
def c2b : Chain ℝ3 2 Int := (Chain.ofList? [1, 0, 0]).get!
/-- `Chain{ℝ^3,3}(2)`. -/
def c3 : Chain ℝ3 3 Int := (Chain.ofList? [2]).get!
/-- `2v₁₂`. -/
def s : Single ℝ3 2 Int := ⟨3, 2⟩
/-- `1 + 0v₁` as a multivector. -/
def m : Multivector ℝ3 Int := Multivector.ofFn fun i => if i.1 == 0 then 1 else 0

-- kinds: Chain is graded (a Manifold), Single a term, Multivector/Couple mixed, Int nothing
#guard istensor c1 && ismanifold c1 && isgraded c1 && !isterm c1 && !ismixed c1
#guard istensor s && isgraded s && isterm s && !ismixed s
#guard istensor m && !isgraded m && !isterm m && ismixed m
#guard istensor (⟨0, 1, 2⟩ : Couple ℝ3 Int) && !isgraded (⟨0, 1, 2⟩ : Couple ℝ3 Int)
#guard !istensor (5 : Int) && !isgraded (5 : Int) && !isterm (5 : Int) && !ismixed (5 : Int)
#guard !istensor "v₁"

-- grades: `rank(t) == G || iszero(t)`
#guard !isscalar c1 && isvector c1 && !isbivector c1 && !istrivector c1 && !isvolume c1 && !isnull c1
#guard isscalar c2 && isvector c2 && isbivector c2 && istrivector c2 && isvolume c2 && isnull c2
#guard !isscalar c2b && !isvector c2b && isbivector c2b && !istrivector c2b && !isvolume c2b
#guard !isscalar c3 && !isvector c3 && !isbivector c3 && istrivector c3 && isvolume c3

-- graded aliases
example : GradedVector (Chain ℝ3 1 Int) TensorBundle ℝ3 Int := inferInstance
example : Bivector (Chain ℝ3 2 Int) TensorBundle ℝ3 Int := inferInstance
example : Scalar (Chain ℝ3 0 Float) TensorBundle ℝ3 Float := inferInstance

-- `isone(Chain{V,0}(1)) = true`, `isone(Chain{V,0}(2)) = false`
#guard isone ((Chain.ofList? [1.0]).get! : Chain ℝ3 0 Float)
#guard !isone ((Chain.ofList? [2.0]).get! : Chain ℝ3 0 Float)
-- `norm(c1, c1 + c1) = 3.7416573867739413`
#guard norm2 ((Chain.ofList? [1.0, 2.0, 3.0]).get! : Chain ℝ3 1 Float)
  ((Chain.ofList? [2.0, 4.0, 6.0]).get!) == 3.7416573867739413

end AbstractTensorsKindTests

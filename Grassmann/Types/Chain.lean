/-
`Chain V G α`: a homogeneous grade-`G` element (Julia `Chain{V,G,T,X}`,
`Grassmann.jl src/multivectors.jl:68-204`; port-notes/grassmann-types.md §3.3,
§4.1, §4.3).

The `binomial(n, G)` coefficients are stored in `Leibniz.indexBasis n G` order
(lexicographic in the ascending index list, *not* numeric mask order), the
Julia `bladeindex` order. `G` is a type index; `G > n` gives the empty chain
(`binomial n G = 0`), which is how `Chain V (G+H)` of a wedge beyond the top
grade is automatically zero.
-/
import Grassmann.Types.Single

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

/-- A grade-`G` element of the algebra of `V` with coefficients in `α`
(Julia `Chain{V,G,α}`); component `i` belongs to blade `(Leibniz.indexBasis V.n G)[i]`. -/
structure Chain (V : TensorBundle) (G : Nat) (α : Type) [Coeff α] where
  /-- The coefficients in Julia's `bladeindex` order. -/
  v : Values α (Leibniz.binomial V.n G)

/-- Julia `GradedVector{V,T} = Chain{V,1,T}` (`src/multivectors.jl:1210`). -/
abbrev GradedVector (V : TensorBundle) (α : Type) [Coeff α] := Chain V 1 α

/-- Julia `Bivector{V,T} = Chain{V,2,T}`. -/
abbrev Bivector (V : TensorBundle) (α : Type) [Coeff α] := Chain V 2 α

/-- Julia `Trivector{V,T} = Chain{V,3,T}`. -/
abbrev Trivector (V : TensorBundle) (α : Type) [Coeff α] := Chain V 3 α

namespace Chain

variable {V : TensorBundle} {G H : Nat} {α : Type} [Coeff α]

/-- Number of stored coefficients `binomial(n, G)` (Julia `length(t)`). -/
@[inline] def size (_ : Chain V G α) : Nat := Leibniz.binomial V.n G

/-- Build from the components (Julia `Chain{V,G}(f(i) for i in 1:C(n,G))`). -/
@[inline] def ofFn (f : Fin (Leibniz.binomial V.n G) → α) : Chain V G α := ⟨Values.ofFn f⟩

/-- Build from a list of the right length (Julia `Chain{V,G}(v::AbstractVector)`,
which throws `DimensionMismatch` otherwise). -/
def ofList? (l : List α) : Option (Chain V G α) := (Values.ofList? l).map (⟨·⟩)

/-- Build from an array of the right length. -/
def ofArray? (a : Array α) : Option (Chain V G α) := (Values.ofArray? a).map (⟨·⟩)

/-- Build from a list whose length is checked at elaboration time (Julia
`Chain{V,G}(4,5,6)`, which throws `DimensionMismatch` at run time): the proof
`l.length = binomial n G` is found by `decide` for literal spaces, e.g.
`(Chain.ofList [4, 5, 6] : Chain ℝ3 1 Int)`, or the literal `chain![4, 5, 6]`. -/
def ofList (l : List α) (h : l.length = Leibniz.binomial V.n G := by decide) : Chain V G α :=
  ⟨Values.ofFn fun i => l[i.1]'(by have := i.2; omega)⟩

/-- The zero chain (Julia `zero(Chain{V,G,T})`). -/
@[inline] def zero : Chain V G α := ⟨zeroValues _⟩

/-- Julia `one(::Chain)`: the grade-0 chain `1v`. -/
@[inline] def one : Chain V 0 α := ⟨Values.replicate Coeff.one⟩

/-- A scalar as a grade-0 chain (Julia `Chain{V,0}(x)`, printed `xv`). -/
@[inline] def scalar (x : α) : Chain V 0 α := ⟨Values.replicate x⟩

/-- The blades of grade `G` in storage order (Julia `indexbasis(n, G)`). -/
@[inline] def blades : Array UInt64 := Leibniz.indexBasis V.n G

/-- The `i`-th component (0-based; Julia `t[i+1]`). -/
@[inline] def get (c : Chain V G α) (i : Fin (Leibniz.binomial V.n G)) : α := c.v.get i

instance : GetElem (Chain V G α) Nat α (fun _ i => i < Leibniz.binomial V.n G) where
  getElem c i h := c.v.get ⟨i, h⟩

/-- The coefficient of blade `b` (Julia `t[b::Submanifold]`): the component at
`bladeindex` when `b` has grade `G`, else zero (grassmann-types.md §4.3). -/
def coeff (c : Chain V G α) (b : UInt64) : α :=
  if (Layout.chain G).contains V.n b then getD c.v (Leibniz.bladeRank V.n b) else Coeff.zero

/-- `x · e_b` as a chain: one-hot at `b` (Julia `Chain{V,G}(x, b)`,
`src/multivectors.jl:131-140`). -/
def ofBlade (b : Submanifold V G) (x : α) : Chain V G α :=
  let r := Leibniz.bladeRank V.n b.bits
  ofFn fun i => if i.1 = r then x else Coeff.zero

/-- A `Single` as a chain (Julia `Chain(v::Single)`). -/
@[inline] def ofSingle (s : Single V G α) : Chain V G α := ofBlade s.basis s.val

/-- The `i`-th term as a `Single` (Julia `t(i+1)`, `src/multivectors.jl:165-170`). -/
def term (c : Chain V G α) (i : Fin (Leibniz.binomial V.n G)) : Single V G α :=
  ⟨Leibniz.unrank V.n G i.1, c.v.get i⟩

/-- The terms `(blade, coefficient)` in storage order. -/
def terms (c : Chain V G α) : Array (UInt64 × α) :=
  let bs := Leibniz.indexBasis V.n G
  (c.v.toArray.zipIdx.map fun (x, i) => (bs[i]!, x))

/-- Reinterpret the grade along an equality (identity at runtime), e.g.
`Chain V (G - G) α` as `Chain V 0 α`. -/
@[inline] def cast (h : G = H) (c : Chain V G α) : Chain V H α := ⟨c.v.cast (by rw [h])⟩

/-- Map the coefficients (to another coefficient type). -/
@[inline] def map {β : Type} [Coeff β] (f : α → β) (c : Chain V G α) : Chain V G β := ⟨c.v.map f⟩

/-- Combine the coefficients pointwise. -/
@[inline] def zipWith (f : α → α → α) (a b : Chain V G α) : Chain V G α := ⟨Values.zipWith f a.v b.v⟩

/-- Whether every coefficient is exactly zero (Julia `iszero`). -/
@[inline] def isZero (c : Chain V G α) : Bool := c.v.all Coeff.isZero

instance : Inhabited (Chain V G α) := ⟨zero⟩

instance [BEq α] : BEq (Chain V G α) := ⟨fun a b => a.v == b.v⟩

instance [DecidableEq α] : DecidableEq (Chain V G α) := fun a b =>
  if h : a.v = b.v then isTrue (by cases a; cases b; cases h; rfl)
  else isFalse fun e => h (by cases e; rfl)

instance : AbstractTensors.TensorGraded (Chain V G α) TensorBundle V G α where

instance : AbstractTensors.Value (Chain V G α) (Values α (Leibniz.binomial V.n G)) := ⟨Chain.v⟩

/-- Julia `isapprox` of two chains of the same grade: componentwise `≈`
(`src/multivectors.jl:128`), so `0 ≈ 1e-20` is `false`. -/
def isapprox [JApprox α] (a b : Chain V G α) (atol : Float := 0)
    (rtol : Float := if atol > 0 then 0 else JApprox.rtolDefault (α := α)) : Bool :=
  Values.foldl₂ (fun acc x y => acc && JApprox.isapprox x y atol rtol false) true a.v b.v

end Chain

end Grassmann

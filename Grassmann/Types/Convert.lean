/-
Views and conversions between the element containers
(port-notes/grassmann-types.md §4.2, §4.4; DESIGN.md §4.2).

Two classes let the algebra layer treat the element types uniformly:

* `DenseLayout X V α`: every element type stores (or can produce) its
  coefficients in one of DirectSum's `Layout`s. Kernels run between any two
  layouts, so a product of *any* two element types can be evaluated without
  first densifying to a `Multivector`; the fallback result type is
  `Multivector V α`.
* `AsChain X V G α`: the homogeneous element types (`Chain`, `Single`,
  `Submanifold`) viewed as a grade-`G` chain. The static result-type rules of
  DESIGN.md §4.2 (`Chain V G ∧ Chain V H → Chain V (G+H)`, ...) are stated for
  `AsChain` operands, so they cover all three.

`toMultivector` is Julia's `Multivector(t)` for every element type.
-/
import Grassmann.Types.Couple

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

/-- An element type with a static storage layout: `values x` are the
coefficients of `x` in `layout` (DESIGN.md §5.1: the layouts the kernels read). -/
class DenseLayout (X : Type) (V : outParam TensorBundle) (α : outParam Type) [Coeff α] where
  /-- The storage layout of the dense view. -/
  layout : Layout
  /-- The coefficients in `layout`. -/
  values : X → Values α (layout.size V.n)

/-- A homogeneous element type viewed as a grade-`G` chain. -/
class AsChain (X : Type) (V : outParam TensorBundle) (G : outParam Nat) (α : outParam Type)
    [Coeff α] where
  /-- The chain with the same coefficients. -/
  toChain : X → Chain V G α

section Instances

variable {V : TensorBundle} {G : Nat} {p : Bool} {α : Type} [Coeff α]

instance : DenseLayout (Chain V G α) V α := ⟨.chain G, Chain.v⟩
instance : DenseLayout (Half V p α) V α := ⟨halfLayout p, Half.v⟩
instance : DenseLayout (Multivector V α) V α := ⟨.full, Multivector.v⟩
instance : DenseLayout (Single V G α) V α := ⟨.chain G, fun s => (Chain.ofSingle s).v⟩
instance : DenseLayout (Couple V α) V α := ⟨.full, fun z => z.toMultivector.v⟩
instance : DenseLayout (PseudoCouple V α) V α := ⟨.full, fun z => z.toMultivector.v⟩
/-- A unit blade is an `Int`-valued term (Julia `Submanifold <: TensorTerm{V,G,Int}`). -/
instance : DenseLayout (Submanifold V G) V Int := ⟨.chain G, fun b => (Chain.ofBlade b 1).v⟩

instance : AsChain (Chain V G α) V G α := ⟨id⟩
instance : AsChain (Single V G α) V G α := ⟨Chain.ofSingle⟩
instance : AsChain (Submanifold V G) V G Int := ⟨fun b => Chain.ofBlade b 1⟩

end Instances

variable {X : Type} {V : TensorBundle} {α : Type} [Coeff α]

/-- The layout of an element type's dense view. -/
@[inline] def layoutOf (X : Type) [DenseLayout X V α] : Layout := DenseLayout.layout (X := X)

/-- Julia `Multivector(t)`: the dense coefficients of any element
(`src/multivectors.jl:240-275, 561-570, 712-713`). -/
@[inline] def toMultivector [DenseLayout X V α] (x : X) : Multivector V α :=
  ⟨convertLayout V.n (layoutOf X) .full (DenseLayout.values x)⟩

/-- Julia `Spinor(t)` / `CoSpinor(t)` of any element: its part of parity `p`
(Julia throws for an element of the other parity; here that part is dropped). -/
@[inline] def toHalf [DenseLayout X V α] (x : X) (p : Bool) : Half V p α :=
  ⟨convertLayout V.n (layoutOf X) (halfLayout p) (DenseLayout.values x)⟩

/-- The grade-`g` part of any element as a chain (Julia `grade(t, g)`). -/
@[inline] def gradePart [DenseLayout X V α] (x : X) (g : Nat) : Chain V g α :=
  ⟨convertLayout V.n (layoutOf X) (.chain g) (DenseLayout.values x)⟩

namespace Multivector

variable {G : Nat} {p : Bool}

/-- Julia `Multivector(t::Chain)`: embed at `binomsum(n, G)` (`src/multivectors.jl:240-259`). -/
@[inline] def ofChain (c : Chain V G α) : Multivector V α := toMultivector c

/-- Julia `Multivector(t::Spinor)`, `Multivector(t::CoSpinor)` (`src/multivectors.jl:561-570`). -/
@[inline] def ofHalf (h : Half V p α) : Multivector V α := toMultivector h

/-- Julia `Multivector(t::Single)`. -/
@[inline] def ofSingle (s : Single V G α) : Multivector V α := toMultivector s

end Multivector

namespace Chain

variable {G : Nat}

/-- Julia `Multivector(t::Chain)`. -/
@[inline] def toMultivector (c : Chain V G α) : Multivector V α := Grassmann.toMultivector c

/-- The chain as the half of its parity. -/
@[inline] def toHalf (c : Chain V G α) : Half V (G % 2 == 1) α := Half.ofChain c

end Chain

namespace Half

variable {p : Bool}

/-- Julia `Multivector(t::Spinor)`. -/
@[inline] def toMultivector (h : Half V p α) : Multivector V α := Grassmann.toMultivector h

end Half

namespace Single

variable {G : Nat}

/-- Julia `Multivector(t::Single)`. -/
@[inline] def toMultivector (s : Single V G α) : Multivector V α := Grassmann.toMultivector s

/-- Julia `Chain(t::Single)`. -/
@[inline] def toChain (s : Single V G α) : Chain V G α := Chain.ofSingle s

end Single

/-- Julia `Multivector(b::Submanifold)`: the unit blade with an `Int` coefficient. -/
@[inline] def _root_.DirectSum.Submanifold.toMultivector {G : Nat} (b : Submanifold V G) :
    Multivector V Int := Grassmann.toMultivector b

end Grassmann

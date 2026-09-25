/-
Basis blades with a static grade (DESIGN.md §3, "Submanifolds and basis blades";
Julia `Submanifold{V,G,B}` in its basis-blade role, `DirectSum.jl
src/DirectSum.jl:252-356`).

At run time a `Submanifold V G` is one `UInt64` (a single-field structure is
unboxed); the invariant `popcount bits = G`, `bits < 2ⁿ` is maintained by the
smart constructors (`ofBits?`, `ofIndices?`, `unrank`), as DESIGN.md asks.
-/
import DirectSum.BladeAlgebra

namespace DirectSum

open Bits

/-- A unit basis blade of grade `G` in the algebra of `V` (bit `k-1` ⇔
generator `k`). -/
structure Submanifold (V : TensorBundle) (G : Nat) where
  /-- The blade mask. -/
  bits : UInt64
  deriving DecidableEq, Hashable, Repr

namespace Submanifold

variable {V : TensorBundle} {G : Nat}

/-- The blade with mask `b`, if it has grade `G` and fits in `V`. -/
def ofBits? (b : UInt64) : Option (Submanifold V G) :=
  if popcount b == G && b &&& ~~~(lowMask V.n) == 0 then some ⟨b⟩ else none

/-- The blade `e_{i₁…i_G}` from distinct 1-based indices (any order; a repeated
or out-of-range index gives `none`). The reordering sign is *not* applied:
use `TensorBundle.mul` for signed products. -/
def ofIndices? (is : List Nat) : Option (Submanifold V G) :=
  if is.eraseDups.length == is.length && is.all (fun i => 1 ≤ i && i ≤ V.n) then ofBits? (ofIndices is)
  else none

/-- The `r`-th (0-based, lex order) blade of grade `G` (Julia `indexbasis(n,G)[r+1]`). -/
def unrank (r : Nat) : Submanifold V G := ⟨Leibniz.unrank V.n G r⟩

/-- 0-based position within grade `G` (Julia `bladeindex - 1`). -/
@[inline] def rank (b : Submanifold V G) : Nat := Leibniz.bladeRank V.n b.bits

/-- 0-based position in the full multivector layout (Julia `basisindex - 1`). -/
@[inline] def basisRank (b : Submanifold V G) : Nat := Leibniz.basisRank V.n b.bits

/-- Julia `indices(b)`: ascending 1-based generator indices. -/
def indices (b : Submanifold V G) : List Nat := indicesList b.bits

/-- The unit scalar `One(V)` (Julia `Submanifold{V,0,0}`). -/
def one : Submanifold V 0 := ⟨0⟩

/-- The pseudoscalar of the non-tangent generators (Julia `V(I)`). -/
def pseudoscalar : Submanifold V (V.n - V.diffvars) := ⟨V.pseudoscalar⟩

/-- Julia's display of a basis blade (`v₁₂`, `w¹`, `∂₁v₂`, `v∞∅₁`). -/
instance : ToString (Submanifold V G) := ⟨fun b => V.bladeLabel b.bits⟩

/-- All blades of grade `G` in lex order (Julia `indexbasis(n,G)`). -/
def all : Array (Submanifold V G) := (Leibniz.indexBasis V.n G).map (⟨·⟩)

end Submanifold

end DirectSum

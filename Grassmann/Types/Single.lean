/-
Single-term elements: `Single V G α`, a scaled basis blade of static grade `G`
(Julia `Single{V,G,B,T}`, `DirectSum.jl src/DirectSum.jl:457-508`;
port-notes/grassmann-types.md §3.3, §4.1).

Julia keeps the blade `B` in the type; here, as DESIGN.md §4.2 prescribes, the
blade is a runtime `UInt64` mask and only the grade is static. The invariant
`popcount bits = G`, `bits < 2ⁿ` is maintained by the smart constructors
(`ofBits?`, `ofBlade`, `scalar`); the raw constructor is available for code that
has already established it. A zero value is allowed (`0v₁` is not `Zero`,
grassmann-types.md §3.3).

The unit blades themselves are DirectSum's `Submanifold V G`.
-/
import Grassmann.Types.Dims

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

/-- A scaled basis blade `val · e_bits` of static grade `G` (Julia `Single`). -/
structure Single (V : TensorBundle) (G : Nat) (α : Type) where
  /-- The blade mask (bit `k-1` ⇔ generator `k`); `popcount bits = G`. -/
  bits : UInt64
  /-- The coefficient (Julia `value(t)`). -/
  val : α
  deriving BEq, DecidableEq, Hashable, Repr

namespace Single

variable {V : TensorBundle} {G : Nat} {α : Type}

/-- `x · e_b` when `b` is a grade-`G` blade of `V` (Julia `Single{V}(x, b)`). -/
def ofBits? (b : UInt64) (x : α) : Option (Single V G α) :=
  if popcount b == G && b &&& ~~~(lowMask V.n) == 0 then some ⟨b, x⟩ else none

/-- `x · b` for a unit blade `b` (Julia `x * b`, `Single{V}(x, b)`). -/
@[inline] def ofBlade (b : Submanifold V G) (x : α) : Single V G α := ⟨b.bits, x⟩

/-- A scalar `x · 1` (Julia `Single{V}(x)`, printed `xv`). -/
@[inline] def scalar (x : α) : Single V 0 α := ⟨0, x⟩

/-- The unit blade (Julia `basis(t)`). -/
@[inline] def basis (s : Single V G α) : Submanifold V G := ⟨s.bits⟩

/-- Map the coefficient. -/
@[inline] def map {β : Type} (f : α → β) (s : Single V G α) : Single V G β := ⟨s.bits, f s.val⟩

instance [Inhabited α] : Inhabited (Single V G α) := ⟨⟨0, default⟩⟩

instance : AbstractTensors.TensorTerm (Single V G α) TensorBundle V G α where

end Single

/-- Julia `Single(b::Submanifold)`: a unit blade as a `Single` with coefficient `1`
(valuetype `Int`, as Julia's `Submanifold <: TensorTerm{V,G,Int}`). -/
instance {V : TensorBundle} {G : Nat} : Coe (Submanifold V G) (Single V G Int) := ⟨fun b => ⟨b.bits, 1⟩⟩

end Grassmann

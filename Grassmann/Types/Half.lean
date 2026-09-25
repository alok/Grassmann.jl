/-
`Half V odd α`: the even (`Spinor`) or odd (`CoSpinor`) half of the algebra
(Julia `Spinor{V,T,X}` / `CoSpinor{V,T,X}` = `AntiSpinor`,
`Grassmann.jl src/multivectors.jl:414-652`; port-notes/grassmann-types.md §3.3,
§4.1, §4.3).

Storage: the blades of even (odd) grade, grade-major, lexicographic within a
grade (Julia `spinindex` / `antiindex`), `2^(n-1)` coefficients (for `n = 0` the
even half is the scalar and the odd half is empty). The parity is a type index,
so products of halves have static result types (`Half p * Half q : Half (p ^^ q)`,
DESIGN.md §4.2).
-/
import Grassmann.Types.Chain

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

/-- The even (`odd = false`) or odd (`odd = true`) grades of the algebra of `V`
(Julia `Spinor` / `CoSpinor`). -/
structure Half (V : TensorBundle) (odd : Bool) (α : Type) [Coeff α] where
  /-- Coefficients in Julia's `spinindex` (even) / `antiindex` (odd) order. -/
  v : Values α (halfDim V.n odd)

/-- Julia `Spinor{V,T}`: the even subalgebra (the quaternions when `n = 3`). -/
abbrev Spinor (V : TensorBundle) (α : Type) [Coeff α] := Half V false α

/-- Julia `CoSpinor{V,T}` (alias `AntiSpinor`): the odd grades. -/
abbrev CoSpinor (V : TensorBundle) (α : Type) [Coeff α] := Half V true α

/-- Julia `AntiSpinor`, the same type as `CoSpinor`. -/
abbrev AntiSpinor (V : TensorBundle) (α : Type) [Coeff α] := Half V true α

namespace Half

variable {V : TensorBundle} {p q : Bool} {α : Type} [Coeff α]

/-- Storage layout of the half. -/
@[inline] def layout (_ : Half V p α) : Layout := halfLayout p

/-- Build from the components. -/
@[inline] def ofFn (f : Fin (halfDim V.n p) → α) : Half V p α := ⟨Values.ofFn f⟩

/-- Build from a list of the right length (Julia `Spinor{V}(v::AbstractVector)`). -/
def ofList? (l : List α) : Option (Half V p α) := (Values.ofList? l).map (⟨·⟩)

/-- Build from an array of the right length. -/
def ofArray? (a : Array α) : Option (Half V p α) := (Values.ofArray? a).map (⟨·⟩)

/-- Build from a list whose length `2ⁿ⁻¹` is checked at elaboration time (Julia
`Spinor{V}(1,2,3,4)`; the literals `spinor![…]`, `cospinor![…]`). -/
def ofList (l : List α) (h : l.length = halfDim V.n p := by decide) : Half V p α :=
  ⟨Values.ofFn fun i => l[i.1]'(by have := i.2; omega)⟩

/-- The zero half. -/
@[inline] def zero : Half V p α := ⟨zeroValues _⟩

/-- The blades stored, in order (Julia `indexeven`/`indexodd`). -/
@[inline] def blades : Array UInt64 := (halfLayout p).blades V.n

/-- The `i`-th component (0-based). -/
@[inline] def get (h : Half V p α) (i : Fin (halfDim V.n p)) : α := h.v.get i

instance : GetElem (Half V p α) Nat α (fun _ i => i < halfDim V.n p) where
  getElem h i hi := h.v.get ⟨i, hi⟩

/-- The coefficient of blade `b` (zero when `b` has the other parity). -/
def coeff (h : Half V p α) (b : UInt64) : α :=
  if (halfLayout p).contains V.n b then getD h.v ((halfLayout p).rank V.n b) else Coeff.zero

/-- The grade-`g` part as a chain (Julia `s(g)`; a zero chain when `g` has the
other parity, `src/multivectors.jl:509-514`). -/
@[inline] def grade (h : Half V p α) (g : Nat) : Chain V g α :=
  ⟨convertLayout V.n (halfLayout p) (.chain g) h.v⟩

/-- A chain of the matching parity as a half (Julia `Spinor(t::Chain)`,
`CoSpinor(t::Chain)`, `src/multivectors.jl:496-507`). -/
@[inline] def ofChain {G : Nat} (c : Chain V G α) : Half V (G % 2 == 1) α :=
  ⟨convertLayout V.n (.chain G) (halfLayout (G % 2 == 1)) c.v⟩

/-- `x · e_b` for a blade of the matching parity (zero otherwise). -/
def ofBlade {G : Nat} (b : Submanifold V G) (x : α) : Half V p α :=
  if (halfLayout p).contains V.n b.bits then
    let r := (halfLayout p).rank V.n b.bits
    ofFn fun i => if i.1 = r then x else Coeff.zero
  else zero

/-- Reinterpret the parity along an equality (identity at runtime). -/
@[inline] def cast (h : p = q) (x : Half V p α) : Half V q α := ⟨x.v.cast (by rw [h])⟩

/-- Map the coefficients. -/
@[inline] def map {β : Type} [Coeff β] (f : α → β) (h : Half V p α) : Half V p β := ⟨h.v.map f⟩

/-- Whether every coefficient is exactly zero. -/
@[inline] def isZero (h : Half V p α) : Bool := h.v.all Coeff.isZero

instance : Inhabited (Half V p α) := ⟨zero⟩

instance [BEq α] : BEq (Half V p α) := ⟨fun a b => a.v == b.v⟩

instance [DecidableEq α] : DecidableEq (Half V p α) := fun a b =>
  if h : a.v = b.v then isTrue (by cases a; cases b; cases h; rfl)
  else isFalse fun e => h (by cases e; rfl)

instance : AbstractTensors.TensorMixed (Half V p α) TensorBundle V α where

instance : AbstractTensors.Value (Half V p α) (Values α (halfDim V.n p)) := ⟨Half.v⟩

end Half

namespace Spinor

variable {V : TensorBundle} {α : Type} [Coeff α]

/-- Julia `one(::Spinor)`: the scalar `1` (`src/multivectors.jl:617-618`). -/
def one : Spinor V α := ⟨Values.ofFn fun i => if i.1 = 0 then Coeff.one else Coeff.zero⟩

/-- A scalar as a spinor. -/
def scalar (x : α) : Spinor V α := ⟨Values.ofFn fun i => if i.1 = 0 then x else Coeff.zero⟩

/-- Julia `quaternion(s, i, j, k) = Spinor{V}(Values(s, i, -j, k))`
(`src/multivectors.jl:1079-1090`): `i = v₁₂`, `j = -v₁₃`, `k = v₂₃` in `n = 3`. -/
def quaternion (s i j k : α) : Spinor V α :=
  ⟨Values.ofFn fun t => match t.1 with
    | 0 => s | 1 => i | 2 => -j | 3 => k | _ => Coeff.zero⟩

end Spinor

end Grassmann

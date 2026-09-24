/-
`Values α n`: a length-indexed, packed, immutable vector.

This is the Lean counterpart of Julia's `StaticVectors.Values{N,T}`. The
length lives in the type, so `Values Float 3` and `Values Float 4` are
different types, and the length proof is erased at runtime. Storage goes
through `Packed α`, so `Values Float n` is a bare `FloatArray` at runtime.
-/
import StaticVectors.Packed

universe u v

namespace StaticVectors

open Packed

/-- A length-`n` vector of `α`, stored packed. -/
structure Values (α : Type u) [Packed α] (n : Nat) where
  /-- Raw packed storage. -/
  data : Arr α
  /-- The storage has exactly `n` elements. -/
  size_eq : size data = n

namespace Values

variable {α : Type u} [Packed α] {n : Nat}

/-- Element access. -/
@[inline] def get (v : Values α n) (i : Fin n) : α :=
  Packed.get v.data ⟨i.1, by rw [v.size_eq]; exact i.2⟩

instance : GetElem (Values α n) Nat α (fun _ i => i < n) where
  getElem v i h := v.get ⟨i, h⟩

/-- Unchecked-by-type read used by generated kernels (literal indices). -/
@[inline] def get! [Inhabited α] (v : Values α n) (i : Nat) : α := Packed.get! v.data i

/-- Build from a function on indices. -/
@[inline] def ofFn (f : Fin n → α) : Values α n := ⟨Packed.ofFn n f, size_ofFn n f⟩

/-- Build from a list, when it has the right length. -/
def ofList? (l : List α) : Option (Values α n) :=
  if h : l.length = n then some (ofFn fun i => l[i.1]'(h ▸ i.2)) else none

/-- Build from an array, when it has the right length. -/
def ofArray? (a : Array α) : Option (Values α n) :=
  if h : a.size = n then some (ofFn fun i => a[i.1]'(h ▸ i.2)) else none

/-- Constant vector. -/
@[inline] def replicate (x : α) : Values α n := ofFn fun _ => x

/-- Replace one entry. -/
@[inline] def set (v : Values α n) (i : Fin n) (x : α) : Values α n :=
  ⟨Packed.set v.data ⟨i.1, by rw [v.size_eq]; exact i.2⟩ x, by simp [v.size_eq]⟩

/-- Convert to an ordinary `Array`. -/
def toArray (v : Values α n) : Array α := Packed.foldlFin n (fun acc i => acc.push (v.get i)) (Array.mkEmpty n)

/-- Convert to a list. -/
def toList (v : Values α n) : List α := (Packed.foldlFin n (fun acc i => v.get i :: acc) []).reverse

@[inline] def map {β : Type v} [Packed β] (f : α → β) (v : Values α n) : Values β n :=
  ofFn fun i => f (v.get i)

@[inline] def mapIdx {β : Type v} [Packed β] (f : Fin n → α → β) (v : Values α n) : Values β n :=
  ofFn fun i => f i (v.get i)

@[inline] def zipWith {β : Type v} {γ : Type u} [Packed β] [Packed γ]
    (f : α → β → γ) (v : Values α n) (w : Values β n) : Values γ n :=
  ofFn fun i => f (v.get i) (w.get i)

/-- Left fold over the entries. -/
@[inline] def foldl {β : Type v} (f : β → α → β) (init : β) (v : Values α n) : β :=
  Packed.foldlFin n (fun acc i => f acc (v.get i)) init

@[inline] def all (p : α → Bool) (v : Values α n) : Bool :=
  v.foldl (fun b x => b && p x) true

@[inline] def any (p : α → Bool) (v : Values α n) : Bool :=
  v.foldl (fun b x => b || p x) false

/-- Sum of entries. -/
@[inline] def sum [Add α] [OfNat α 0] (v : Values α n) : α := v.foldl (· + ·) 0

/-- Euclidean dot product of two value vectors. -/
@[inline] def dot [Add α] [Mul α] [OfNat α 0] (v w : Values α n) : α :=
  Packed.foldlFin n (fun acc i => acc + v.get i * w.get i) 0

/-- Append two vectors; lengths add in the type. -/
def append {m : Nat} (v : Values α n) (w : Values α m) : Values α (n + m) :=
  ofFn fun i => if h : i.1 < n then v.get ⟨i.1, h⟩ else w.get ⟨i.1 - n, by omega⟩

/-- Extract a sub-vector `[start, start + k)`. -/
def extract (v : Values α n) (start k : Nat) (h : start + k ≤ n) : Values α k :=
  ofFn fun i => v.get ⟨start + i.1, by omega⟩

/-! ## Pointwise arithmetic -/

instance [Add α] : Add (Values α n) := ⟨zipWith (· + ·)⟩
instance [Sub α] : Sub (Values α n) := ⟨zipWith (· - ·)⟩
instance [Neg α] : Neg (Values α n) := ⟨map (- ·)⟩
instance [OfNat α 0] : Zero (Values α n) := ⟨replicate 0⟩
/-- Scalar multiplication on the left. -/
instance [Mul α] : HMul α (Values α n) (Values α n) := ⟨fun a v => v.map (a * ·)⟩
/-- Scalar division on the right. -/
instance [Div α] : HDiv (Values α n) α (Values α n) := ⟨fun v a => v.map (· / a)⟩

/-! ## Equality, printing -/

instance [BEq α] : BEq (Values α n) where
  beq v w := Packed.foldlFin n (fun b i => b && v.get i == w.get i) true

/-- Two value vectors are equal when their entries are. -/
theorem ext {v w : Values α n} (h : ∀ i, v.get i = w.get i) : v = w := by
  cases v with | mk dv hv =>
  cases w with | mk dw hw =>
  have : dv = dw := Packed.ext dv dw (hv.trans hw.symm) fun i => h ⟨i.1, by rw [← hv]; exact i.2⟩
  subst this; rfl

instance [DecidableEq α] : DecidableEq (Values α n) := fun v w =>
  if h : ∀ i : Fin n, v.get i = w.get i then isTrue (ext h)
  else isFalse fun e => h fun _ => e ▸ rfl

instance [Repr α] : Repr (Values α n) where
  reprPrec v _ := "Values" ++ Std.Format.bracket "[" (Std.Format.joinSep (v.toList.map repr) ", ") "]"

instance [ToString α] : ToString (Values α n) where
  toString v := "Values(" ++ ", ".intercalate (v.toList.map toString) ++ ")"

instance [Inhabited α] : Inhabited (Values α n) := ⟨replicate default⟩

end Values

end StaticVectors

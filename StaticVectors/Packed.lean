/-
Packed storage for scalar types.

Julia's `StaticVectors.Values{N,T}` is an immutable tuple, so `Float64`
coefficients sit unboxed in registers or on the stack. In compiled Lean,
`Array Float` stores boxed floats (one heap cell per element) and costs
roughly 2× in arithmetic kernels. `FloatArray` stores raw doubles.

`Packed α` picks the flat array representation for a scalar type. `Float`
gets `FloatArray`. Every other type falls back to `Array α` through a
low-priority instance. Kernels are written once against this class, and
specializing at `Float` yields unboxed straight-line code (measured at parity
with a hand-written `FloatArray` kernel).
-/

universe u v

namespace StaticVectors

/-- Flat array storage for scalars of type `α`.

The laws are the minimum needed to track sizes in `Values`; they are proved
once per instance and erased at runtime. -/
class Packed (α : Type u) where
  /-- The packed array type. -/
  Arr : Type u
  /-- Number of stored elements. -/
  size : Arr → Nat
  /-- Checked read. -/
  get : (a : Arr) → Fin (size a) → α
  /-- An empty array with room for `n` elements. -/
  mkEmpty : Nat → Arr
  /-- Append one element. -/
  push : Arr → α → Arr
  /-- Checked write. -/
  set : (a : Arr) → Fin (size a) → α → Arr
  size_mkEmpty (n : Nat) : size (mkEmpty n) = 0
  size_push (a : Arr) (x : α) : size (push a x) = size a + 1
  size_set (a : Arr) (i : Fin (size a)) (x : α) : size (set a i x) = size a
  /-- Arrays are determined by their size and elements. -/
  ext (a b : Arr) (h : size a = size b) (hget : ∀ i : Fin (size a), get a i = get b ⟨i.1, h ▸ i.2⟩) : a = b

attribute [simp] Packed.size_mkEmpty Packed.size_push Packed.size_set

/-- Boxed fallback: any type packs into an ordinary `Array`. -/
instance (priority := low) instPackedArray {α : Type u} : Packed α where
  Arr := Array α
  size := Array.size
  get a i := a[i]
  mkEmpty := Array.mkEmpty
  push := Array.push
  set a i x := a.set i x
  size_mkEmpty _ := rfl
  size_push := by simp
  size_set := by simp
  ext a b h hget := Array.ext h fun i h₁ h₂ => hget ⟨i, h₁⟩

/-- `Float` packs unboxed into a `FloatArray`. -/
instance instPackedFloat : Packed Float where
  Arr := FloatArray
  size := FloatArray.size
  get a i := a[i]
  mkEmpty := FloatArray.emptyWithCapacity
  push := FloatArray.push
  set a i x := a.set i x
  size_mkEmpty _ := rfl
  size_push a x := by simp [FloatArray.push, FloatArray.size]
  size_set a i x := by
    simp only [FloatArray.set, FloatArray.size]
    exact Array.size_set ..
  ext a b h hget := by
    cases a with | mk a =>
    cases b with | mk b =>
    congr 1
    exact Array.ext h fun i h₁ h₂ => hget ⟨i, h₁⟩

namespace Packed

variable {α : Type u} [Packed α]

/-- Read with a default for out-of-range indices. Used by generated kernels,
whose indices are literals already known to be in range; the branch is
perfectly predicted. -/
@[inline] def get! [Inhabited α] (a : Arr α) (i : Nat) : α :=
  if h : i < size a then get a ⟨i, h⟩ else default

/-- Build a packed array from a function on `Fin n`.

Structural recursion (counting the remaining elements down) keeps this
reducible by the kernel, so `decide` works on small exact vectors. -/
@[inline] def ofFn (n : Nat) (f : Fin n → α) : Arr α :=
  go n (Nat.le_refl n) (mkEmpty n)
where
  go : (k : Nat) → k ≤ n → Arr α → Arr α
    | 0, _, acc => acc
    | k + 1, h, acc => go k (Nat.le_of_succ_le h) (push acc (f ⟨n - (k + 1), by omega⟩))

theorem size_ofFn_go (n : Nat) (f : Fin n → α) :
    ∀ (k : Nat) (h : k ≤ n) (acc : Arr α), size (ofFn.go n f k h acc) = size acc + k
  | 0, _, acc => rfl
  | k + 1, h, acc => by
    rw [ofFn.go, size_ofFn_go n f k _ _, size_push]
    omega

@[simp] theorem size_ofFn (n : Nat) (f : Fin n → α) : size (ofFn n f) = n := by
  simp [ofFn, size_ofFn_go]

/-- Structural left fold over `Fin n` (kernel-reducible, unlike well-founded folds). -/
@[inline] def foldlFin {β : Type v} (n : Nat) (f : β → Fin n → β) (init : β) : β :=
  go n (Nat.le_refl n) init
where
  go : (k : Nat) → k ≤ n → β → β
    | 0, _, acc => acc
    | k + 1, h, acc => go k (Nat.le_of_succ_le h) (f acc ⟨n - (k + 1), by omega⟩)

end Packed

end StaticVectors

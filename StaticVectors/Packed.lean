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

universe u v w

namespace StaticVectors

/-- Flat array storage for scalars of type `α`.

The laws are the minimum needed to track sizes and elements in `Values`;
they are proved once per instance and erased at runtime. -/
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
  /-- Pushing keeps the old elements. -/
  get_push_lt (a : Arr) (x : α) (i : Nat) (h : i < size a) :
    get (push a x) ⟨i, by rw [size_push]; exact Nat.lt_succ_of_lt h⟩ = get a ⟨i, h⟩
  /-- Pushing puts the new element last. -/
  get_push_size (a : Arr) (x : α) :
    get (push a x) ⟨size a, by rw [size_push]; exact Nat.lt_succ_self _⟩ = x
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
  get_push_lt a x i h := Array.getElem_push_lt h
  get_push_size _ _ := Array.getElem_push_eq
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
  get_push_lt a x i h := by
    cases a with | mk a =>
    exact Array.getElem_push_lt h
  get_push_size a x := by
    cases a with | mk a =>
    exact Array.getElem_push_eq
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
  /-- Push `f (n-k), …, f (n-1)` onto `acc`. -/
  @[specialize] go : (k : Nat) → k ≤ n → Arr α → Arr α
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

/-- Reading a pushed-onto array, by cases on the index. -/
theorem get_push (a : Arr α) (x : α) (i : Nat) (h : i < size (push a x)) :
    get (push a x) ⟨i, h⟩ = if h' : i < size a then get a ⟨i, h'⟩ else x := by
  split
  · next h' => exact get_push_lt a x i h'
  · next h' =>
    have hi : i = size a := by rw [size_push] at h; omega
    subst hi
    exact get_push_size a x

theorem get_ofFn_go (n : Nat) (f : Fin n → α) :
    ∀ (k : Nat) (hk : k ≤ n) (acc : Arr α) (_hacc : size acc = n - k) (i : Nat)
      (hi : i < size (ofFn.go n f k hk acc)),
      get (ofFn.go n f k hk acc) ⟨i, hi⟩ =
        if h : i < size acc then get acc ⟨i, h⟩
        else f ⟨i, by rw [size_ofFn_go] at hi; omega⟩
  | 0, _, acc, hacc, i, hi => by
    simp only [ofFn.go] at hi ⊢
    simp [hi]
  | k + 1, hk, acc, hacc, i, hi => by
    simp only [ofFn.go] at hi ⊢
    rw [get_ofFn_go n f k _ _ (by rw [size_push]; omega) i hi]
    by_cases h1 : i < size acc
    · have h2 : i < size (push acc (f ⟨n - (k + 1), by omega⟩)) := by rw [size_push]; omega
      rw [dite_eq_left h2, dite_eq_left h1, get_push_lt acc _ i h1]
    · rw [dite_eq_right h1]
      by_cases h2 : i < size (push acc (f ⟨n - (k + 1), by omega⟩))
      · rw [dite_eq_left h2, get_push, dite_eq_right h1]
        have : i = n - (k + 1) := by rw [size_push] at h2; omega
        subst this; rfl
      · rw [dite_eq_right h2]

/-- Elements of `ofFn`. -/
@[simp] theorem get_ofFn (n : Nat) (f : Fin n → α) (i : Fin (size (ofFn n f))) :
    get (ofFn n f) i = f ⟨i.1, by simpa using i.2⟩ := by
  have := get_ofFn_go n f n (Nat.le_refl n) (mkEmpty n) (by simp) i.1 i.2
  simp only [size_mkEmpty, Nat.not_lt_zero, dite_false] at this
  exact this

/-- Build a packed array left to right while threading a state `σ`
(a scan). Structural in `n`, like `ofFn`. -/
@[inline] def ofFnScan {σ : Type w} (n : Nat) (f : σ → Fin n → σ × α) (s : σ) : Arr α :=
  go n (Nat.le_refl n) s (mkEmpty n)
where
  /-- Emit the entries `n-k, …, n-1`, starting from state `s`. -/
  @[specialize] go : (k : Nat) → k ≤ n → σ → Arr α → Arr α
    | 0, _, _, acc => acc
    | k + 1, h, s, acc =>
      let r := f s ⟨n - (k + 1), by omega⟩
      go k (Nat.le_of_succ_le h) r.1 (push acc r.2)

theorem size_ofFnScan_go {σ : Type w} (n : Nat) (f : σ → Fin n → σ × α) :
    ∀ (k : Nat) (h : k ≤ n) (s : σ) (acc : Arr α), size (ofFnScan.go n f k h s acc) = size acc + k
  | 0, _, _, acc => rfl
  | k + 1, h, s, acc => by
    rw [ofFnScan.go, size_ofFnScan_go n f k _ _ _, size_push]
    omega

@[simp] theorem size_ofFnScan {σ : Type w} (n : Nat) (f : σ → Fin n → σ × α) (s : σ) :
    size (ofFnScan n f s) = n := by
  simp [ofFnScan, size_ofFnScan_go]

/-- Structural left fold over `Fin n` (kernel-reducible, unlike well-founded folds). -/
@[inline] def foldlFin {β : Type v} (n : Nat) (f : β → Fin n → β) (init : β) : β :=
  go n (Nat.le_refl n) init
where
  /-- Fold the indices `n-k, …, n-1` into `acc`. -/
  @[specialize] go : (k : Nat) → k ≤ n → β → β
    | 0, _, acc => acc
    | k + 1, h, acc => go k (Nat.le_of_succ_le h) (f acc ⟨n - (k + 1), by omega⟩)

/-- Structural right fold over `Fin n`: `f 0 (f 1 (… (f (n-1) init)))`. -/
@[inline] def foldrFin {β : Type v} (n : Nat) (f : Fin n → β → β) (init : β) : β :=
  go n (Nat.le_refl n) init
where
  /-- Fold the indices `k-1, …, 0` (from the right) into `acc`. -/
  @[specialize] go : (k : Nat) → k ≤ n → β → β
    | 0, _, acc => acc
    | k + 1, h, acc => go k (Nat.le_of_succ_le h) (f ⟨k, by omega⟩ acc)

end Packed

end StaticVectors

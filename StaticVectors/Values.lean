/-
`Values α n`: a length-indexed, packed, immutable vector.

This is the Lean counterpart of Julia's `StaticVectors.Values{N,T}`
(`StaticVectors.jl src/Values.jl`). The length lives in the type, so
`Values Float 3` and `Values Float 4` are different types, and the length
proof is erased at runtime. Storage goes through `Packed α`, so
`Values Float n` is a bare `FloatArray` at runtime.

Julia's mutable `Variables{N,T}` and `FixedVector{N,T}` are the same type
here: updates (`set`, `modify`) are in place when the value is unshared.
Indices are 0-based `Fin n` (Julia's `v[i]` is `v.get ⟨i-1, _⟩`).
-/
import StaticVectors.Packed

universe u v w

namespace StaticVectors

open Packed

/-- A length-`n` vector of `α`, stored packed (Julia `Values{n,α}`). -/
structure Values (α : Type u) [Packed α] (n : Nat) where
  /-- Raw packed storage. -/
  data : Arr α
  /-- The storage has exactly `n` elements. -/
  size_eq : size data = n

namespace Values

variable {α : Type u} [Packed α] {n : Nat}

/-- Element access (Julia `v[i+1]`). -/
@[inline] def get (v : Values α n) (i : Fin n) : α :=
  Packed.get v.data ⟨i.1, by rw [v.size_eq]; exact i.2⟩

instance : GetElem (Values α n) Nat α (fun _ i => i < n) where
  getElem v i h := v.get ⟨i, h⟩

/-- Unchecked-by-type read used by generated kernels (literal indices). -/
@[inline] def get! [Inhabited α] (v : Values α n) (i : Nat) : α := Packed.get! v.data i

/-- Build from a function on indices (Julia `Values{N}(f(i) for i in 1:N)`). -/
@[inline] def ofFn (f : Fin n → α) : Values α n := ⟨Packed.ofFn n f, size_ofFn n f⟩

/-- Build left to right while threading a state (a scan); `f` returns the
next state and the entry. -/
@[inline] def ofFnScan {σ : Type w} (f : σ → Fin n → σ × α) (s : σ) : Values α n :=
  ⟨Packed.ofFnScan n f s, size_ofFnScan n f s⟩

/-- Build from a list, when it has the right length (Julia
`Values{N}(a::AbstractVector)`, which throws `DimensionMismatch` otherwise). -/
def ofList? (l : List α) : Option (Values α n) :=
  if h : l.length = n then some (ofFn fun i => l[i.1]'(h ▸ i.2)) else none

/-- Build from an array, when it has the right length. -/
def ofArray? (a : Array α) : Option (Values α n) :=
  if h : a.size = n then some (ofFn fun i => a[i.1]'(h ▸ i.2)) else none

/-- Constant vector (Julia `fill(x, Values{n})`). -/
@[inline] def replicate (x : α) : Values α n := ofFn fun _ => x

/-- Replace one entry (Julia `setindex!` on `Variables`). -/
@[inline] def set (v : Values α n) (i : Fin n) (x : α) : Values α n :=
  ⟨Packed.set v.data ⟨i.1, by rw [v.size_eq]; exact i.2⟩ x, by simp [v.size_eq]⟩

/-- Update one entry in place (when unshared): Julia `v[i] = f(v[i])`. -/
@[inline] def modify (v : Values α n) (i : Fin n) (f : α → α) : Values α n :=
  v.set i (f (v.get i))

/-- Reinterpret the length along an equality; the identity at runtime. -/
@[inline] def cast {m : Nat} (h : n = m) (v : Values α n) : Values α m :=
  ⟨v.data, v.size_eq.trans h⟩

/-- Convert to an ordinary `Array`. -/
def toArray (v : Values α n) : Array α :=
  Packed.foldlFin n (fun acc i => acc.push (v.get i)) (Array.mkEmpty n)

/-- Convert to a list. -/
def toList (v : Values α n) : List α := Packed.foldrFin n (fun i acc => v.get i :: acc) []

/-! ### Elementwise loops

`map`, `zipWith` and `foldl` are direct structural loops that take the
vectors as ordinary arguments and are `@[specialize]`d on the element
function, so at `Float` they compile to unboxed `FloatArray` loops (going
through `ofFn` would call a closure and box every element). Each is proved
equal to its `ofFn`/`foldlFin` form, which carries the lemmas. -/

/-- The loop of `map`: pushes `f vᵢ` for `i = n-k, …, n-1`. -/
@[specialize] def mapLoop {β : Type v} [Packed β] (f : α → β) (v : Values α n) :
    (k : Nat) → k ≤ n → Arr β → Arr β
  | 0, _, acc => acc
  | k + 1, h, acc =>
    mapLoop f v k (Nat.le_of_succ_le h) (Packed.push acc (f (v.get ⟨n - (k + 1), by omega⟩)))

theorem mapLoop_eq {β : Type v} [Packed β] (f : α → β) (v : Values α n) :
    ∀ (k : Nat) (h : k ≤ n) (acc : Arr β),
      mapLoop f v k h acc = Packed.ofFn.go n (fun i => f (v.get i)) k h acc
  | 0, _, _ => rfl
  | k + 1, h, acc => by
    simp only [mapLoop, Packed.ofFn.go]
    exact mapLoop_eq f v k _ _

/-- Elementwise map (Julia `map(f, v)`). -/
@[inline] def map {β : Type v} [Packed β] (f : α → β) (v : Values α n) : Values β n :=
  ⟨mapLoop f v n (Nat.le_refl n) (Packed.mkEmpty n), by
    rw [mapLoop_eq]; exact size_ofFn n _⟩

theorem map_eq_ofFn {β : Type v} [Packed β] (f : α → β) (v : Values α n) :
    v.map f = ofFn fun i => f (v.get i) := by
  simp only [map, ofFn, Packed.ofFn, mapLoop_eq]

/-- Elementwise map with the index. -/
@[inline] def mapIdx {β : Type v} [Packed β] (f : Fin n → α → β) (v : Values α n) : Values β n :=
  ofFn fun i => f i (v.get i)

/-- The loop of `zipWith`. -/
@[specialize] def zipLoop {β : Type v} {γ : Type w} [Packed β] [Packed γ] (f : α → β → γ)
    (v : Values α n) (w : Values β n) : (k : Nat) → k ≤ n → Arr γ → Arr γ
  | 0, _, acc => acc
  | k + 1, h, acc =>
    zipLoop f v w k (Nat.le_of_succ_le h)
      (Packed.push acc (f (v.get ⟨n - (k + 1), by omega⟩) (w.get ⟨n - (k + 1), by omega⟩)))

theorem zipLoop_eq {β : Type v} {γ : Type w} [Packed β] [Packed γ] (f : α → β → γ)
    (v : Values α n) (w : Values β n) :
    ∀ (k : Nat) (h : k ≤ n) (acc : Arr γ),
      zipLoop f v w k h acc = Packed.ofFn.go n (fun i => f (v.get i) (w.get i)) k h acc
  | 0, _, _ => rfl
  | k + 1, h, acc => by
    simp only [zipLoop, Packed.ofFn.go]
    exact zipLoop_eq f v w k _ _

/-- Elementwise binary map (Julia `map(f, a, b)`). -/
@[inline] def zipWith {β : Type v} {γ : Type w} [Packed β] [Packed γ]
    (f : α → β → γ) (v : Values α n) (w : Values β n) : Values γ n :=
  ⟨zipLoop f v w n (Nat.le_refl n) (Packed.mkEmpty n), by
    rw [zipLoop_eq]; exact size_ofFn n _⟩

theorem zipWith_eq_ofFn {β : Type v} {γ : Type w} [Packed β] [Packed γ]
    (f : α → β → γ) (v : Values α n) (w : Values β n) :
    zipWith f v w = ofFn fun i => f (v.get i) (w.get i) := by
  simp only [zipWith, ofFn, Packed.ofFn, zipLoop_eq]

/-- Elementwise ternary map (Julia `map(f, a, b, c)`). -/
@[inline] def zipWith3 {β γ δ : Type u} [Packed β] [Packed γ] [Packed δ]
    (f : α → β → γ → δ) (a : Values α n) (b : Values β n) (c : Values γ n) : Values δ n :=
  ofFn fun i => f (a.get i) (b.get i) (c.get i)

/-- The loop of `foldl`: folds the entries `n-k, …, n-1` into `acc`. -/
@[specialize] def foldlLoop {β : Type v} (f : β → α → β) (v : Values α n) :
    (k : Nat) → k ≤ n → β → β
  | 0, _, acc => acc
  | k + 1, h, acc => foldlLoop f v k (Nat.le_of_succ_le h) (f acc (v.get ⟨n - (k + 1), by omega⟩))

theorem foldlLoop_eq {β : Type v} (f : β → α → β) (v : Values α n) :
    ∀ (k : Nat) (h : k ≤ n) (acc : β),
      foldlLoop f v k h acc = Packed.foldlFin.go n (fun acc i => f acc (v.get i)) k h acc
  | 0, _, _ => rfl
  | k + 1, h, acc => by
    simp only [foldlLoop, Packed.foldlFin.go]
    exact foldlLoop_eq f v k _ _


/-- The loop of a two-vector left fold: folds the pairs `n-k, …, n-1` into `acc`. -/
@[specialize] def foldl₂Loop {β : Type v} {γ : Type w} [Packed β] (f : γ → α → β → γ)
    (v : Values α n) (w : Values β n) : (k : Nat) → k ≤ n → γ → γ
  | 0, _, acc => acc
  | k + 1, h, acc =>
    foldl₂Loop f v w k (Nat.le_of_succ_le h)
      (f acc (v.get ⟨n - (k + 1), by omega⟩) (w.get ⟨n - (k + 1), by omega⟩))


/-! ### In-place updates, unrolled at small sizes

Julia's `Values{N,Float64}` results live in registers; here every vector result is a packed
array. The element-preserving operations (`+ -`, scalar `* /`, negation, `normalize`, `cross`)
therefore write their results into their first operand with `Packed.set`: when that operand is
unshared (an accumulator, a temporary) nothing is allocated, and otherwise the runtime copies it
once (one allocation and a `memcpy`, instead of an empty array and one out-of-line `push` per
entry). Sizes `1 … 4` are unrolled: at a literal `n` the size dispatch folds away and the
operation is straight-line code (docs/PERF.md, StaticVectors). -/

/-- Replace entry `j` of `a` by `g j aⱼ`. -/
@[inline] def upd (g : Fin n → α → α) (a : Arr α) (ha : size a = n) (j : Nat) (hj : j < n) : Arr α :=
  Packed.set a ⟨j, ha ▸ hj⟩ (g ⟨j, hj⟩ (Packed.get a ⟨j, ha ▸ hj⟩))

theorem size_upd (g : Fin n → α → α) (a : Arr α) (ha : size a = n) (j : Nat) (hj : j < n) :
    size (upd g a ha j hj) = n := by simp [upd, ha]

theorem get_upd (g : Fin n → α → α) (a : Arr α) (ha : size a = n) (j : Nat) (hj : j < n) (i : Nat)
    (hi : i < size (upd g a ha j hj)) :
    Packed.get (upd g a ha j hj) ⟨i, hi⟩ =
      if j = i then g ⟨j, hj⟩ (Packed.get a ⟨j, ha ▸ hj⟩)
      else Packed.get a ⟨i, by rw [size_upd] at hi; rw [ha]; exact hi⟩ :=
  Packed.get_set a _ _ i hi

/-- `upd` at the indices `n-k, …, n-1`, ascending. -/
@[specialize] def updLoop (g : Fin n → α → α) : (k : Nat) → k ≤ n → (a : Arr α) → size a = n → Arr α
  | 0, _, a, _ => a
  | k + 1, hk, a, ha =>
    updLoop g k (Nat.le_of_succ_le hk) (upd g a ha (n - (k + 1)) (by omega)) (size_upd ..)

theorem size_updLoop (g : Fin n → α → α) :
    ∀ (k : Nat) (hk : k ≤ n) (a : Arr α) (ha : size a = n), size (updLoop g k hk a ha) = n
  | 0, _, _, ha => ha
  | k + 1, _, _, _ => size_updLoop g k _ _ (size_upd ..)

theorem get_updLoop (g : Fin n → α → α) :
    ∀ (k : Nat) (hk : k ≤ n) (a : Arr α) (ha : size a = n) (i : Nat)
      (hi : i < size (updLoop g k hk a ha)),
      Packed.get (updLoop g k hk a ha) ⟨i, hi⟩ =
        if n - k ≤ i then g ⟨i, by rw [size_updLoop] at hi; exact hi⟩
          (Packed.get a ⟨i, by rw [size_updLoop] at hi; rw [ha]; exact hi⟩)
        else Packed.get a ⟨i, by rw [size_updLoop] at hi; rw [ha]; exact hi⟩
  | 0, _, a, ha, i, hi => by
    have : ¬ (n - 0 ≤ i) := by rw [size_updLoop] at hi; omega
    simp only [updLoop, this, ite_false]
  | k + 1, hk, a, ha, i, hi => by
    simp only [updLoop]
    rw [get_updLoop g k _ _ _ i hi, get_upd]
    by_cases h1 : n - k ≤ i
    · have h2 : n - (k + 1) ≠ i := by omega
      have h3 : n - (k + 1) ≤ i := by omega
      simp [h1, h2, h3]
    · by_cases h2 : n - (k + 1) = i
      · subst h2; simp [h1]
      · have h3 : ¬ (n - (k + 1) ≤ i) := by omega
        simp [h1, h2, h3]

/-- `upd` at every index, unrolled for `n ≤ 4`. -/
@[inline] def updAll : (n : Nat) → (g : Fin n → α → α) → (a : Arr α) → size a = n → Arr α
  | 1, g, a, ha => upd g a ha 0 (by decide)
  | 2, g, a, ha => upd g (upd g a ha 0 (by decide)) (size_upd ..) 1 (by decide)
  | 3, g, a, ha =>
    upd g (upd g (upd g a ha 0 (by decide)) (size_upd ..) 1 (by decide)) (size_upd ..) 2 (by decide)
  | 4, g, a, ha =>
    upd g (upd g (upd g (upd g a ha 0 (by decide)) (size_upd ..) 1 (by decide)) (size_upd ..) 2
      (by decide)) (size_upd ..) 3 (by decide)
  | n, g, a, ha => updLoop g n (Nat.le_refl n) a ha

theorem updAll_eq : ∀ (n : Nat) (g : Fin n → α → α) (a : Arr α) (ha : size a = n),
    updAll n g a ha = updLoop g n (Nat.le_refl n) a ha
  | 0, _, _, _ => rfl
  | 1, _, _, _ => rfl
  | 2, _, _, _ => rfl
  | 3, _, _, _ => rfl
  | 4, _, _, _ => rfl
  | _ + 5, _, _, _ => rfl

/-- `v` with every entry `vᵢ` replaced by `g i vᵢ`, written into `v`'s storage (no allocation
when `v` is unshared). -/
@[inline] def updateAll (g : Fin n → α → α) (v : Values α n) : Values α n :=
  ⟨updAll n g v.data v.size_eq, by rw [updAll_eq]; exact size_updLoop ..⟩

/-- Equal arrays have equal entries (for rewriting under the size proof). -/
theorem get_congr_arr {a b : Arr α} (h : a = b) (i : Nat) (hi : i < size a) (hi' : i < size b) :
    Packed.get a ⟨i, hi⟩ = Packed.get b ⟨i, hi'⟩ := by subst h; rfl

@[simp] theorem get_updateAll (g : Fin n → α → α) (v : Values α n) (i : Fin n) :
    (updateAll g v).get i = g i (v.get i) := by
  have hi : i.1 < size (updLoop g n (Nat.le_refl n) v.data v.size_eq) := by
    rw [size_updLoop]; exact i.2
  have h := get_congr_arr (updAll_eq n g v.data v.size_eq) i.1
    (by rw [updAll_eq]; exact hi) hi
  rw [get_updLoop] at h
  simp only [Nat.sub_self, Nat.zero_le, ite_true] at h
  exact h

/-- Elementwise map within one type (Julia `map(f, v)`), in place when `v` is unshared. -/
@[inline] def mapSelf (f : α → α) (v : Values α n) : Values α n := updateAll (fun _ x => f x) v

/-- Replace entry `j` of `a` by `f aⱼ wⱼ` (`upd` with the closure written out, so that the
compiler inlines `f` instead of lifting a closure over `w`). -/
@[inline] def zipUpd (f : α → α → α) (w : Values α n) (a : Arr α) (ha : size a = n) (j : Nat)
    (hj : j < n) : Arr α :=
  Packed.set a ⟨j, ha ▸ hj⟩ (f (Packed.get a ⟨j, ha ▸ hj⟩) (w.get ⟨j, hj⟩))

theorem size_zipUpd (f : α → α → α) (w : Values α n) (a : Arr α) (ha : size a = n) (j : Nat)
    (hj : j < n) : size (zipUpd f w a ha j hj) = n := by simp [zipUpd, ha]

/-- `zipUpd` at every index, unrolled for `n ≤ 4`; `updAll` with `g i x = f x wᵢ`. -/
@[inline] def zipAll : (n : Nat) → (f : α → α → α) → Values α n → (a : Arr α) → size a = n → Arr α
  | 1, f, w, a, ha => zipUpd f w a ha 0 (by decide)
  | 2, f, w, a, ha => zipUpd f w (zipUpd f w a ha 0 (by decide)) (size_zipUpd ..) 1 (by decide)
  | 3, f, w, a, ha =>
    zipUpd f w (zipUpd f w (zipUpd f w a ha 0 (by decide)) (size_zipUpd ..) 1 (by decide)) (size_zipUpd ..) 2
      (by decide)
  | 4, f, w, a, ha =>
    zipUpd f w (zipUpd f w (zipUpd f w (zipUpd f w a ha 0 (by decide)) (size_zipUpd ..) 1 (by decide))
      (size_zipUpd ..) 2 (by decide)) (size_zipUpd ..) 3 (by decide)
  | n, f, w, a, ha => updLoop (fun i x => f x (w.get i)) n (Nat.le_refl n) a ha

theorem zipAll_eq : ∀ (n : Nat) (f : α → α → α) (w : Values α n) (a : Arr α) (ha : size a = n),
    zipAll n f w a ha = updAll n (fun i x => f x (w.get i)) a ha
  | 0, _, _, _, _ => rfl
  | 1, _, _, _, _ => rfl
  | 2, _, _, _, _ => rfl
  | 3, _, _, _, _ => rfl
  | 4, _, _, _, _ => rfl
  | _ + 5, _, _, _, _ => rfl

/-- Replace entry `j` of `a` by `f b aⱼ` (a map with one captured value `b`, written out so the
compiler inlines `f`). -/
@[inline] def withUpd {β : Type v} (f : β → α → α) (b : β) (a : Arr α) (ha : size a = n) (j : Nat)
    (hj : j < n) : Arr α :=
  Packed.set a ⟨j, ha ▸ hj⟩ (f b (Packed.get a ⟨j, ha ▸ hj⟩))

theorem size_withUpd {β : Type v} (f : β → α → α) (b : β) (a : Arr α) (ha : size a = n) (j : Nat)
    (hj : j < n) : size (withUpd f b a ha j hj) = n := by simp [withUpd, ha]

/-- `withUpd` at every index, unrolled for `n ≤ 4`; `updAll` with `g i x = f b x`. -/
@[inline] def withAll {β : Type v} : (n : Nat) → (f : β → α → α) → β → (a : Arr α) → size a = n → Arr α
  | 1, f, b, a, ha => withUpd f b a ha 0 (by decide)
  | 2, f, b, a, ha => withUpd f b (withUpd f b a ha 0 (by decide)) (size_withUpd ..) 1 (by decide)
  | 3, f, b, a, ha =>
    withUpd f b (withUpd f b (withUpd f b a ha 0 (by decide)) (size_withUpd ..) 1 (by decide))
      (size_withUpd ..) 2 (by decide)
  | 4, f, b, a, ha =>
    withUpd f b (withUpd f b (withUpd f b (withUpd f b a ha 0 (by decide)) (size_withUpd ..) 1
      (by decide)) (size_withUpd ..) 2 (by decide)) (size_withUpd ..) 3 (by decide)
  | n, f, b, a, ha => updLoop (fun _ x => f b x) n (Nat.le_refl n) a ha

theorem withAll_eq {β : Type v} : ∀ (n : Nat) (f : β → α → α) (b : β) (a : Arr α) (ha : size a = n),
    withAll n f b a ha = updAll n (fun _ x => f b x) a ha
  | 0, _, _, _, _ => rfl
  | 1, _, _, _, _ => rfl
  | 2, _, _, _, _ => rfl
  | 3, _, _, _, _ => rfl
  | 4, _, _, _, _ => rfl
  | _ + 5, _, _, _, _ => rfl

/-- `vᵢ ↦ f b vᵢ` for one captured value `b` (scalar multiples, `normalize`), written into `v`'s
storage (in place when `v` is unshared). -/
@[inline] def mapWith {β : Type v} (f : β → α → α) (b : β) (v : Values α n) : Values α n :=
  ⟨withAll n f b v.data v.size_eq, by rw [withAll_eq, updAll_eq]; exact size_updLoop ..⟩

theorem mapWith_eq_updateAll {β : Type v} (f : β → α → α) (b : β) (v : Values α n) :
    mapWith f b v = updateAll (fun _ x => f b x) v := by
  simp only [mapWith, updateAll, withAll_eq]

@[simp] theorem get_mapWith {β : Type v} (f : β → α → α) (b : β) (v : Values α n) (i : Fin n) :
    (mapWith f b v).get i = f b (v.get i) := by
  rw [mapWith_eq_updateAll, get_updateAll]

/-- Elementwise binary map into the first operand (Julia `map(f, v, w)`), in place when `v` is
unshared. -/
@[inline] def zipSelf (f : α → α → α) (v w : Values α n) : Values α n :=
  ⟨zipAll n f w v.data v.size_eq, by rw [zipAll_eq, updAll_eq]; exact size_updLoop ..⟩

theorem zipSelf_eq_updateAll (f : α → α → α) (v w : Values α n) :
    zipSelf f v w = updateAll (fun i x => f x (w.get i)) v := by
  simp only [zipSelf, updateAll, zipAll_eq]

/-- Left fold over the entries, unrolled for `n ≤ 4` (the same left-to-right order). -/
@[inline] def foldlAll {β : Type v} : (n : Nat) → (f : β → α → β) → Values α n → β → β
  | 1, f, v, init => f init (v.get ⟨0, by decide⟩)
  | 2, f, v, init => f (f init (v.get ⟨0, by decide⟩)) (v.get ⟨1, by decide⟩)
  | 3, f, v, init => f (f (f init (v.get ⟨0, by decide⟩)) (v.get ⟨1, by decide⟩)) (v.get ⟨2, by decide⟩)
  | 4, f, v, init => f (f (f (f init (v.get ⟨0, by decide⟩)) (v.get ⟨1, by decide⟩)) (v.get ⟨2, by decide⟩)) (v.get ⟨3, by decide⟩)
  | n, f, v, init => foldlLoop f v n (Nat.le_refl n) init

theorem foldlAll_eq {β : Type v} : ∀ (n : Nat) (f : β → α → β) (v : Values α n) (init : β),
    foldlAll n f v init = foldlLoop f v n (Nat.le_refl n) init
  | 0, _, _, _ => rfl
  | 1, _, _, _ => rfl
  | 2, _, _, _ => rfl
  | 3, _, _, _ => rfl
  | 4, _, _, _ => rfl
  | _ + 5, _, _, _ => rfl

/-- Left fold over pairs of entries, unrolled for `n ≤ 4`. -/
@[inline] def foldl₂All {β : Type v} {γ : Type w} [Packed β] :
    (n : Nat) → (f : γ → α → β → γ) → Values α n → Values β n → γ → γ
  | 1, f, v, w, init => f init (v.get ⟨0, by decide⟩) (w.get ⟨0, by decide⟩)
  | 2, f, v, w, init => f (f init (v.get ⟨0, by decide⟩) (w.get ⟨0, by decide⟩)) (v.get ⟨1, by decide⟩) (w.get ⟨1, by decide⟩)
  | 3, f, v, w, init => f (f (f init (v.get ⟨0, by decide⟩) (w.get ⟨0, by decide⟩)) (v.get ⟨1, by decide⟩) (w.get ⟨1, by decide⟩)) (v.get ⟨2, by decide⟩) (w.get ⟨2, by decide⟩)
  | 4, f, v, w, init =>
    f (f (f (f init (v.get ⟨0, by decide⟩) (w.get ⟨0, by decide⟩)) (v.get ⟨1, by decide⟩) (w.get ⟨1, by decide⟩)) (v.get ⟨2, by decide⟩) (w.get ⟨2, by decide⟩)) (v.get ⟨3, by decide⟩) (w.get ⟨3, by decide⟩)
  | n, f, v, w, init => foldl₂Loop f v w n (Nat.le_refl n) init

theorem foldl₂All_eq {β : Type v} {γ : Type w} [Packed β] :
    ∀ (n : Nat) (f : γ → α → β → γ) (v : Values α n) (w : Values β n) (init : γ),
      foldl₂All n f v w init = foldl₂Loop f v w n (Nat.le_refl n) init
  | 0, _, _, _, _ => rfl
  | 1, _, _, _, _ => rfl
  | 2, _, _, _, _ => rfl
  | 3, _, _, _, _ => rfl
  | 4, _, _, _, _ => rfl
  | _ + 5, _, _, _, _ => rfl

/-- Left fold over the entries, `f (… (f init v₀) …) vₙ₋₁` (Julia `foldl(f, v; init)`),
unrolled for `n ≤ 4`. -/
@[inline] def foldl {β : Type v} (f : β → α → β) (init : β) (v : Values α n) : β :=
  foldlAll n f v init

theorem foldl_eq_foldlFin {β : Type v} (f : β → α → β) (init : β) (v : Values α n) :
    v.foldl f init = Packed.foldlFin n (fun acc i => f acc (v.get i)) init := by
  simp only [foldl, foldlAll_eq, Packed.foldlFin, foldlLoop_eq]

/-- Left fold over pairs of entries: `f (… (f init v₀ w₀) …) vₙ₋₁ wₙ₋₁`, unrolled for `n ≤ 4`. -/
@[inline] def foldl₂ {β : Type v} {γ : Type w} [Packed β] (f : γ → α → β → γ) (init : γ)
    (v : Values α n) (w : Values β n) : γ :=
  foldl₂All n f v w init

/-- Right fold over the entries, `f v₀ (… (f vₙ₋₁ init))`. -/
@[inline] def foldr {β : Type v} (f : α → β → β) (init : β) (v : Values α n) : β :=
  Packed.foldrFin n (fun i acc => f (v.get i) acc) init

/-- Left fold with the index. -/
@[inline] def foldlIdx {β : Type v} (f : β → Fin n → α → β) (init : β) (v : Values α n) : β :=
  Packed.foldlFin n (fun acc i => f acc i (v.get i)) init

/-- Julia `all(p, v)` (non-short-circuit, as Julia's `reduce(&, …)`). -/
@[inline] def all (p : α → Bool) (v : Values α n) : Bool :=
  v.foldl (fun b x => b && p x) true

/-- Julia `any(p, v)`. -/
@[inline] def any (p : α → Bool) (v : Values α n) : Bool :=
  v.foldl (fun b x => b || p x) false

/-- Append two vectors; lengths add in the type (Julia `vcat(a, b)`). -/
def append {m : Nat} (v : Values α n) (w : Values α m) : Values α (n + m) :=
  ofFn fun i => if h : i.1 < n then v.get ⟨i.1, h⟩ else w.get ⟨i.1 - n, by omega⟩

/-- Julia `vcat(a, b)`. -/
abbrev vcat {m : Nat} (v : Values α n) (w : Values α m) : Values α (n + m) := v.append w

instance {m : Nat} : HAppend (Values α n) (Values α m) (Values α (n + m)) := ⟨append⟩

/-- Extract a sub-vector `[start, start + k)`. -/
def extract (v : Values α n) (start k : Nat) (h : start + k ≤ n) : Values α k :=
  ofFn fun i => v.get ⟨start + i.1, by omega⟩

/-- Reverse the entries (Julia `reverse(v)`, `SV/abstractvector.jl:85`). -/
@[inline] def reverse (v : Values α n) : Values α n :=
  ofFn fun i => v.get ⟨n - 1 - i.1, by omega⟩

/-- Gather: `v[idx]` for a static index vector (Julia `v[idx::TupleVector{M,Int}]`,
`SV/indexing.jl:90`), giving a vector of length `m`. -/
@[inline] def gather {m : Nat} [Packed (Fin n)] (v : Values α n) (idx : Values (Fin n) m) : Values α m :=
  ofFn fun j => v.get (idx.get j)

/-- Scatter: Julia `v[idx] = w` on a copy (`SV/indexing.jl:137`); entries are
written left to right, so later duplicates win. -/
def scatter {m : Nat} [Packed (Fin n)] (v : Values α n) (idx : Values (Fin n) m) (w : Values α m) :
    Values α n :=
  Packed.foldlFin m (fun acc j => acc.set (idx.get j) (w.get j)) v

/-- The first entry of a nonempty vector. -/
@[inline] def head (v : Values α (n + 1)) : α := v.get ⟨0, by omega⟩

/-- The last entry of a nonempty vector. -/
@[inline] def last (v : Values α (n + 1)) : α := v.get ⟨n, by omega⟩

/-! ## Pointwise lemmas -/

@[simp] theorem get_ofFn (f : Fin n → α) (i : Fin n) : (ofFn f).get i = f i := by
  simp [ofFn, get]

@[simp] theorem getElem_eq_get (v : Values α n) (i : Nat) (h : i < n) : v[i] = v.get ⟨i, h⟩ := rfl

/-- Two value vectors are equal when their entries are. -/
theorem ext {v w : Values α n} (h : ∀ i, v.get i = w.get i) : v = w := by
  cases v with | mk dv hv =>
  cases w with | mk dw hw =>
  have : dv = dw := Packed.ext dv dw (hv.trans hw.symm) fun i => h ⟨i.1, by rw [← hv]; exact i.2⟩
  subst this; rfl

@[simp] theorem get_map {β : Type v} [Packed β] (f : α → β) (v : Values α n) (i : Fin n) :
    (v.map f).get i = f (v.get i) := by simp [map_eq_ofFn]

@[simp] theorem get_zipWith {β : Type v} {γ : Type w} [Packed β] [Packed γ]
    (f : α → β → γ) (v : Values α n) (w : Values β n) (i : Fin n) :
    (zipWith f v w).get i = f (v.get i) (w.get i) := by simp [zipWith_eq_ofFn]

@[simp] theorem get_replicate (x : α) (i : Fin n) : (replicate x : Values α n).get i = x := by
  simp [replicate]

@[simp] theorem get_reverse (v : Values α n) (i : Fin n) :
    v.reverse.get i = v.get ⟨n - 1 - i.1, by omega⟩ := by simp [reverse]

@[simp] theorem reverse_reverse (v : Values α n) : v.reverse.reverse = v :=
  ext fun i => by simp; congr 1; ext; simp; omega

theorem get_append_left {m : Nat} (v : Values α n) (w : Values α m) (i : Fin (n + m)) (h : i.1 < n) :
    (v.append w).get i = v.get ⟨i.1, h⟩ := by simp [append, h]

theorem get_append_right {m : Nat} (v : Values α n) (w : Values α m) (i : Fin (n + m)) (h : n ≤ i.1) :
    (v.append w).get i = w.get ⟨i.1 - n, by omega⟩ := by
  simp [append, Nat.not_lt.mpr h]

@[simp] theorem get_gather {m : Nat} [Packed (Fin n)] (v : Values α n) (idx : Values (Fin n) m)
    (j : Fin m) : (v.gather idx).get j = v.get (idx.get j) := by simp [gather]

/-! ## Pointwise arithmetic (`SV/linalg.jl`) -/

/-- Julia `a + b` (`SV/linalg.jl:14`); written into `a` (in place when `a` is unshared). -/
instance [Add α] : Add (Values α n) := ⟨zipSelf (· + ·)⟩
/-- Julia `a - b`; written into `a`. -/
instance [Sub α] : Sub (Values α n) := ⟨zipSelf (· - ·)⟩
/-- Julia `-a` (`SV/linalg.jl:9`); in place when `a` is unshared. -/
instance [Neg α] : Neg (Values α n) := ⟨mapSelf (- ·)⟩
instance [OfNat α 0] : Zero (Values α n) := ⟨replicate 0⟩
/-- Julia `s * a = map(c -> s*c, a)` (`SV/linalg.jl:31`): the scalar stays on
the left, which matters for non-commutative entries. -/
instance [Mul α] : HMul α (Values α n) (Values α n) := ⟨fun a v => mapWith (fun a x => a * x) a v⟩
/-- Julia `a * s = map(c -> c*s, a)` (`SV/linalg.jl:32`). -/
instance [Mul α] : HMul (Values α n) α (Values α n) := ⟨fun v a => mapWith (fun a x => x * a) a v⟩
/-- Julia `a / s`: true division of every entry (`SV/linalg.jl:45`). -/
instance [Div α] : HDiv (Values α n) α (Values α n) := ⟨fun v a => mapWith (fun a x => x / a) a v⟩

/-- Julia `s \ a = map(c -> s \ c, a)` (`SV/linalg.jl:46`), i.e. `c / s` for
commutative scalars. -/
@[inline] def leftDiv [Div α] (s : α) (v : Values α n) : Values α n :=
  mapWith (fun s x => x / s) s v

/-- Julia `muladd(s, a, b)` elementwise (`SV/linalg.jl:54`). Unfused here;
Julia may contract to an FMA (at most 1 ulp apart). -/
@[inline] def muladd [Mul α] [Add α] (s : α) (a b : Values α n) : Values α n :=
  zipSelf (fun x y => s * x + y) a b

@[simp] theorem get_mapSelf (f : α → α) (v : Values α n) (i : Fin n) :
    (v.mapSelf f).get i = f (v.get i) := get_updateAll _ _ _

@[simp] theorem get_zipSelf (f : α → α → α) (v w : Values α n) (i : Fin n) :
    (zipSelf f v w).get i = f (v.get i) (w.get i) := by
  rw [zipSelf_eq_updateAll, get_updateAll]

theorem mapSelf_eq_map (f : α → α) (v : Values α n) : v.mapSelf f = v.map f :=
  ext fun i => by simp

theorem zipSelf_eq_zipWith (f : α → α → α) (v w : Values α n) : zipSelf f v w = zipWith f v w :=
  ext fun i => by simp

@[simp] theorem get_add [Add α] (v w : Values α n) (i : Fin n) : (v + w).get i = v.get i + w.get i :=
  get_zipSelf _ _ _ _

@[simp] theorem get_sub [Sub α] (v w : Values α n) (i : Fin n) : (v - w).get i = v.get i - w.get i :=
  get_zipSelf _ _ _ _

@[simp] theorem get_neg [Neg α] (v : Values α n) (i : Fin n) : (-v).get i = -v.get i :=
  get_mapSelf _ _ _

@[simp] theorem get_smul [Mul α] (s : α) (v : Values α n) (i : Fin n) : (s * v).get i = s * v.get i :=
  get_mapWith _ _ _ _

/-! ## Equality, printing -/

instance [BEq α] : BEq (Values α n) where
  beq v w := Packed.foldlFin n (fun b i => b && v.get i == w.get i) true

instance [DecidableEq α] : DecidableEq (Values α n) := fun v w =>
  if h : ∀ i : Fin n, v.get i = w.get i then isTrue (ext h)
  else isFalse fun e => h fun _ => e ▸ rfl

/-- Lexicographic comparison (Julia `isless` on `AbstractVector`). -/
def compareLex [Ord α] (v w : Values α n) : Ordering :=
  Packed.foldlFin n (fun o i => o.then (compare (v.get i) (w.get i))) .eq

instance [Ord α] : Ord (Values α n) := ⟨compareLex⟩

instance [Hashable α] : Hashable (Values α n) where
  hash v := v.foldl (fun h x => mixHash h (hash x)) 7

instance [Repr α] : Repr (Values α n) where
  reprPrec v _ := "Values" ++ Std.Format.bracket "[" (Std.Format.joinSep (v.toList.map repr) ", ") "]"

/-- Julia's compact `print`/`repr` form `[e1, e2, …]` (element printing is the
element type's `toString`; Julia's shortest-round-trip float printer lives in
`JuliaBase`). -/
instance [ToString α] : ToString (Values α n) where
  toString v := "[" ++ ", ".intercalate (v.toList.map toString) ++ "]"

instance [Inhabited α] : Inhabited (Values α n) := ⟨replicate default⟩

end Values

end StaticVectors

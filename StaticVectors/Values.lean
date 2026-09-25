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

/-- Elementwise map (Julia `map(f, v)`). -/
@[inline] def map {β : Type v} [Packed β] (f : α → β) (v : Values α n) : Values β n :=
  ofFn fun i => f (v.get i)

/-- Elementwise map with the index. -/
@[inline] def mapIdx {β : Type v} [Packed β] (f : Fin n → α → β) (v : Values α n) : Values β n :=
  ofFn fun i => f i (v.get i)

/-- Elementwise binary map (Julia `map(f, a, b)`). -/
@[inline] def zipWith {β : Type v} {γ : Type w} [Packed β] [Packed γ]
    (f : α → β → γ) (v : Values α n) (w : Values β n) : Values γ n :=
  ofFn fun i => f (v.get i) (w.get i)

/-- Elementwise ternary map (Julia `map(f, a, b, c)`). -/
@[inline] def zipWith3 {β γ δ : Type u} [Packed β] [Packed γ] [Packed δ]
    (f : α → β → γ → δ) (a : Values α n) (b : Values β n) (c : Values γ n) : Values δ n :=
  ofFn fun i => f (a.get i) (b.get i) (c.get i)

/-- Left fold over the entries, `f (… (f init v₀) …) vₙ₋₁` (Julia `foldl(f, v; init)`). -/
@[inline] def foldl {β : Type v} (f : β → α → β) (init : β) (v : Values α n) : β :=
  Packed.foldlFin n (fun acc i => f acc (v.get i)) init

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
    (v.map f).get i = f (v.get i) := by simp [map]

@[simp] theorem get_zipWith {β : Type v} {γ : Type w} [Packed β] [Packed γ]
    (f : α → β → γ) (v : Values α n) (w : Values β n) (i : Fin n) :
    (zipWith f v w).get i = f (v.get i) (w.get i) := by simp [zipWith]

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

/-- Julia `a + b` (`SV/linalg.jl:14`). -/
instance [Add α] : Add (Values α n) := ⟨zipWith (· + ·)⟩
/-- Julia `a - b`. -/
instance [Sub α] : Sub (Values α n) := ⟨zipWith (· - ·)⟩
/-- Julia `-a` (`SV/linalg.jl:9`). -/
instance [Neg α] : Neg (Values α n) := ⟨map (- ·)⟩
instance [OfNat α 0] : Zero (Values α n) := ⟨replicate 0⟩
/-- Julia `s * a = map(c -> s*c, a)` (`SV/linalg.jl:31`): the scalar stays on
the left, which matters for non-commutative entries. -/
instance [Mul α] : HMul α (Values α n) (Values α n) := ⟨fun a v => v.map (a * ·)⟩
/-- Julia `a * s = map(c -> c*s, a)` (`SV/linalg.jl:32`). -/
instance [Mul α] : HMul (Values α n) α (Values α n) := ⟨fun v a => v.map (· * a)⟩
/-- Julia `a / s`: true division of every entry (`SV/linalg.jl:45`). -/
instance [Div α] : HDiv (Values α n) α (Values α n) := ⟨fun v a => v.map (· / a)⟩

/-- Julia `s \ a = map(c -> s \ c, a)` (`SV/linalg.jl:46`), i.e. `c / s` for
commutative scalars. -/
@[inline] def leftDiv [Div α] (s : α) (v : Values α n) : Values α n := v.map (· / s)

/-- Julia `muladd(s, a, b)` elementwise (`SV/linalg.jl:54`). Unfused here;
Julia may contract to an FMA (at most 1 ulp apart). -/
@[inline] def muladd [Mul α] [Add α] (s : α) (a b : Values α n) : Values α n :=
  zipWith (fun x y => s * x + y) a b

@[simp] theorem get_add [Add α] (v w : Values α n) (i : Fin n) : (v + w).get i = v.get i + w.get i :=
  get_zipWith _ _ _ _

@[simp] theorem get_sub [Sub α] (v w : Values α n) (i : Fin n) : (v - w).get i = v.get i - w.get i :=
  get_zipWith _ _ _ _

@[simp] theorem get_neg [Neg α] (v : Values α n) (i : Fin n) : (-v).get i = -v.get i :=
  get_map _ _ _

@[simp] theorem get_smul [Mul α] (s : α) (v : Values α n) (i : Fin n) : (s * v).get i = s * v.get i :=
  get_map _ _ _

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

import AbstractAnalysis.Countable

/-!
# Memoized recurrences (`SequenceArray`)

Julia's `SequenceArray{T,N,V,F}` stores computed terms in `v` and extends them
on demand with the recurrence `F(v, k)`; reading past the end *mutates* the
storage (src/AbstractAnalysis.jl:232-310). Multi-dimensional storage grows
along its **last** axis (`ElasticArray`, `resize_lastdim!`), which is how
Cartan stacks the time slices of a `TensorField` orbit.

Port decisions:
* Storage is abstracted by `LastDimStorage σ S`: storage `σ` whose last-axis
  slices have type `S`, with Julia's `extract`/`assign!` as class methods.
  Instances: `Array S` (any slice type, e.g. Cartan's fields), `FloatArray`
  (unboxed `Float` sequences) and `SlabArray` (a packed `FloatArray` of
  fixed-size slabs: Julia's `ElasticArray{Float64,N}`).
* Extension is pure and state-passing: `get` returns the value together with
  the extended sequence. Nothing global is mutated.
-/

namespace AbstractAnalysis

/-- Storage growing along its last axis (Julia `extract`/`assign!`,
src/AbstractAnalysis.jl:300-310). Indices are 1-based. -/
class LastDimStorage (σ : Type) (S : outParam Type) where
  /-- Julia `size(v)[end]`. -/
  lastDim : σ → Nat
  /-- Julia `extract(v, k)`: the `k`-th last-axis slice (1-based). -/
  extract : σ → Nat → S
  /-- Julia `assign!(v, lastDim+1, s)` after `resize_lastdim!`: append a slice. -/
  push : σ → S → σ

export LastDimStorage (lastDim extract)

instance {S : Type} [Inhabited S] : LastDimStorage (Array S) S where
  lastDim := Array.size
  extract v k := v[k - 1]!
  push := Array.push

instance : LastDimStorage FloatArray Float where
  lastDim := FloatArray.size
  extract v k := v[k - 1]!
  push := FloatArray.push

/-- Julia `ElasticArray{Float64,N}`: packed `Float` storage made of slabs of a
fixed size `slab` (the product of all but the last dimension), column-major so
appending a slab is a contiguous push. -/
structure SlabArray where
  /-- Elements of the first `slab * count` slots. -/
  data : FloatArray
  /-- Slab length (product of the leading dimensions). -/
  slab : Nat
  deriving Inhabited

namespace SlabArray

/-- Number of slabs (Julia `size(x)[end]`). -/
def count (x : SlabArray) : Nat := if x.slab = 0 then 0 else x.data.size / x.slab

/-- The `k`-th slab (1-based), copied out as a `FloatArray` (Julia `view(x, :, …, k)`). -/
def slice (x : SlabArray) (k : Nat) : FloatArray :=
  go ((k - 1) * x.slab) 0 (FloatArray.emptyWithCapacity x.slab) x.slab
where
  /-- Tail-recursive copy. -/
  go (base i : Nat) (acc : FloatArray) : Nat → FloatArray
    | 0 => acc
    | fuel + 1 => go base (i + 1) (acc.push x.data[base + i]!) fuel

/-- Append a slab (only its first `slab` entries are used). -/
def pushSlab (x : SlabArray) (s : FloatArray) : SlabArray :=
  ⟨go 0 x.data x.slab, x.slab⟩
where
  /-- Tail-recursive append. -/
  go (i : Nat) (acc : FloatArray) : Nat → FloatArray
    | 0 => acc
    | fuel + 1 => go (i + 1) (acc.push s[i]!) fuel

end SlabArray

instance : LastDimStorage SlabArray FloatArray where
  lastDim := SlabArray.count
  extract := SlabArray.slice
  push := SlabArray.pushSlab

/-- Julia `SequenceArray{T,N,V,F}`: stored terms `v` plus the recurrence
`f(v, k)` producing term `k` from the terms `1 … k-1`. -/
structure SequenceArray (σ S : Type) [LastDimStorage σ S] where
  /-- Computed terms. -/
  v : σ
  /-- Julia `counter(x)`: the recurrence `F(v, k)`. -/
  f : σ → Nat → S

namespace SequenceArray

variable {σ S : Type} [LastDimStorage σ S]

/-- Julia `length(x)` / `size(x)[end]`: number of computed terms. -/
@[inline] def length (c : SequenceArray σ S) : Nat := lastDim c.v

/-- Julia `resize!(c, n)` / `resize_lastdim!(c, n)`: extend by
`assign!(v, k, F(v, k))` for `k = m+1 … n` (src/AbstractAnalysis.jl:249-266).
Never shrinks (the port keeps memoized terms). -/
def resize (c : SequenceArray σ S) (n : Nat) : SequenceArray σ S :=
  ⟨go c.v (n - lastDim c.v), c.f⟩
where
  /-- Tail-recursive extension. -/
  go (v : σ) : Nat → σ
    | 0 => v
    | fuel + 1 => go (LastDimStorage.push v (c.f v (lastDim v + 1))) fuel

/-- Julia `c[n]` / `extract(c, n)`: extends as needed and returns the term with
the extended sequence. -/
@[inline] def get (c : SequenceArray σ S) (n : Nat) : S × SequenceArray σ S :=
  let c := if n > c.length then c.resize n else c
  (extract c.v n, c)

/-- The first `n` terms (extending as needed). -/
def take (c : SequenceArray σ S) (n : Nat) : Array S :=
  let c := c.resize n
  (List.range n).toArray.map fun i => extract c.v (i + 1)

/-- Julia `map(f, s)`: a lazy countable view `k ↦ g(s[k])` of the current
length (src/AbstractAnalysis.jl:312). Reads beyond the memo recompute from the
stored prefix. -/
def toCountable {β : Type} (c : SequenceArray σ S) (g : S → β) : CountableVector β :=
  ⟨fun k => g (c.get k).1, c.length⟩

end SequenceArray

/-- A 1-D sequence stored in a plain `Array`. -/
abbrev SequenceVector (α : Type) [Inhabited α] := SequenceArray (Array α) α

/-- Julia `accumulate_pairwise!(op, c, v)` (base/accumulate.jl), which `cumsum`
uses for rounding arithmetic: blocks below 128 elements accumulate their own
partial sum `s_` and add it to the running offset `s`, so `c[i] = v[1] + (v[2] + … + v[i])`
rather than a left fold. On exact types the two agree. -/
def accumulatePairwise {α : Type} [Inhabited α] (op : α → α → α) (v : Array α) : Array α :=
  if v.size ≤ 1 then v else (go (v.set! 0 v[0]!) v[0]! 1 (v.size - 1) v.size).1
where
  /-- Julia `_accumulate_pairwise!`: returns the updated output and the block sum. -/
  go (c : Array α) (s : α) (i1 n : Nat) : Nat → Array α × α
    | 0 => (c, s)
    | fuel + 1 =>
      if n < 128 then
        let s_ := v[i1]!
        let c := c.set! i1 (op s s_)
        (List.range (n - 1)).foldl (fun (c, s_) j =>
          let s_ := op s_ v[i1 + 1 + j]!
          (c.set! (i1 + 1 + j) (op s s_), s_)) (c, s_)
      else
        let n2 := n / 2
        let (c, s_) := go c s i1 n2 fuel
        let (c, t) := go c (op s s_) (i1 + n2) (n - n2) fuel
        (c, op s_ t)

/-- Julia `cumsum(x::CountableVector)`: eager prefix sums of the first `len`
terms via `accumulate_pairwise!` (`cumsum(view(x, :))`), extended lazily by
`u[k-1] + x(k)` (src/AbstractAnalysis.jl:283-298). -/
def CountableVector.cumsum {α : Type} [Add α] [Inhabited α] (x : CountableVector α) : SequenceVector α :=
  ⟨accumulatePairwise (· + ·) (x.slice 1 x.len), fun u k => u[k - 2]! + x.f k⟩

/-- Julia `cumprod(x::CountableVector)`. -/
def CountableVector.cumprod {α : Type} [Mul α] [Inhabited α] (x : CountableVector α) : SequenceVector α :=
  let seq : SequenceVector α := ⟨#[x.f 1], fun u k => u[k - 2]! * x.f k⟩
  if x.len = 0 then ⟨#[], seq.f⟩ else seq.resize x.len

end AbstractAnalysis

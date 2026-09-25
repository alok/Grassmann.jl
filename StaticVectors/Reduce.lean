/-
Reductions and scans over `Values` (Julia `StaticVectors.jl src/mapreduce.jl`).

Julia folds are **left folds in index order whose first step is the first
element itself** (`Base.reduce_first`), not `init ⊕ a₁`. The difference is
visible in floating point: `sum(Values(-0.0)) === -0.0`, whereas
`0.0 + -0.0 === 0.0`. Every reduction here follows that rule, and falls back
to the documented empty value (`0` for `+`, `1` for `*`) when `n = 0`.
-/
import StaticVectors.Values
import StaticVectors.Scalar

universe u v

namespace StaticVectors

namespace Values

open Packed

variable {α : Type u} [Packed α] {n : Nat}

/-- Julia `reduce(op, v)` without `init`: `op(…op(op(v₁, v₂), v₃)…, vₙ)`
(`SV/mapreduce.jl:113`), and `empty` when `n = 0` (Julia's
`mapreduce_empty`, an error for `max`/`min`). -/
@[inline] def reduce (op : α → α → α) (empty : α) (v : Values α n) : α :=
  match n, v with
  | 0, _ => empty
  | k + 1, v => Packed.foldlFin k (fun acc i => op acc (v.get i.succ)) v.head

/-- Julia `mapreduce(f, op, v)` without `init` (`SV/mapreduce.jl:113`):
the fold starts from `f(v₁)`. -/
@[inline] def mapReduce {β : Type v} (f : α → β) (op : β → β → β) (empty : β) (v : Values α n) : β :=
  match n, v with
  | 0, _ => empty
  | k + 1, v => Packed.foldlFin k (fun acc i => op acc (f (v.get i.succ))) (f v.head)

/-- Julia `mapreduce(f, op, v; init)`: `op(…op(init, f(v₁))…, f(vₙ))`. -/
@[inline] def mapFoldl {β : Type v} (f : α → β) (op : β → β → β) (init : β) (v : Values α n) : β :=
  Packed.foldlFin n (fun acc i => op acc (f (v.get i))) init

/-- Julia `sum(v)` (`SV/mapreduce.jl:242`): a left fold starting from `v₁`;
`0` when empty. No widening, as in Julia. -/
@[inline] def sum [Add α] [OfNat α 0] (v : Values α n) : α := v.reduce (· + ·) 0

/-- Julia `sum(f, v)`. -/
@[inline] def sumMap {β : Type v} [Add β] [OfNat β 0] (f : α → β) (v : Values α n) : β :=
  v.mapReduce f (· + ·) 0

/-- Julia `prod(v)` (`SV/mapreduce.jl:246`); `1` when empty. -/
@[inline] def prod [Mul α] [OfNat α 1] (v : Values α n) : α := v.reduce (· * ·) 1

/-- Julia `prod(f, v)`. -/
@[inline] def prodMap {β : Type v} [Mul β] [OfNat β 1] (f : α → β) (v : Values α n) : β :=
  v.mapReduce f (· * ·) 1

/-- Julia `maximum(v)` (`SV/mapreduce.jl:272`): a fold with Julia's `max`
(NaN-propagating, `-0.0 < 0.0` for floats). Julia throws on an empty vector;
the type `Values α (n+1)` rules that out. -/
@[inline] def maximum [JMinMax α] (v : Values α (n + 1)) : α := v.reduce JMinMax.max v.head

/-- Julia `minimum(v)` (`SV/mapreduce.jl:269`). -/
@[inline] def minimum [JMinMax α] (v : Values α (n + 1)) : α := v.reduce JMinMax.min v.head

/-- Julia `maximum(f, v)` (broken in StaticVectors, B8; fixed here). -/
@[inline] def maximumMap {β : Type v} [JMinMax β] (f : α → β) (v : Values α (n + 1)) : β :=
  v.mapReduce f JMinMax.max (f v.head)

/-- Julia `minimum(f, v)` (broken in StaticVectors, B8; fixed here). -/
@[inline] def minimumMap {β : Type v} [JMinMax β] (f : α → β) (v : Values α (n + 1)) : β :=
  v.mapReduce f JMinMax.min (f v.head)

/-- Julia `count(p, v)` (`SV/mapreduce.jl:251`). -/
@[inline] def count (p : α → Bool) (v : Values α n) : Nat :=
  v.foldl (fun c x => if p x then c + 1 else c) 0

/-- Julia `x in v` (`SV/mapreduce.jl:259`): `mapreduce(==(x), |, v; init=false)`. -/
@[inline] def contains [BEq α] (v : Values α n) (x : α) : Bool := v.any (· == x)

/-- Julia `iszero(v)` (`SV/mapreduce.jl:240`): every entry is zero (`==`, so
`-0.0` counts as zero and NaN does not). -/
@[inline] def isZero [BEq α] [OfNat α 0] (v : Values α n) : Bool := v.all (· == 0)

/-- Julia `accumulate(op, v)` (`SV/mapreduce.jl:300`): the left scan
`[v₁, op(v₁,v₂), op(op(v₁,v₂),v₃), …]`. -/
@[inline] def accumulate (op : α → α → α) (v : Values α n) : Values α n :=
  ofFnScan (σ := Option α)
    (fun s i => let y := match s with | none => v.get i | some a => op a (v.get i); (some y, y)) none

/-- Julia `accumulate(op, v; init)`: `[op(init,v₁), op(op(init,v₁),v₂), …]`. -/
@[inline] def accumulateInit {β : Type u} [Packed β] (op : β → α → β) (init : β) (v : Values α n) :
    Values β n :=
  ofFnScan (fun s i => let y := op s (v.get i); (y, y)) init

/-- Julia `cumsum(v)` (`SV/mapreduce.jl:337`). -/
@[inline] def cumsum [Add α] (v : Values α n) : Values α n := v.accumulate (· + ·)

/-- Julia `cumprod(v)` (`SV/mapreduce.jl:338`). -/
@[inline] def cumprod [Mul α] (v : Values α n) : Values α n := v.accumulate (· * ·)

/-- Julia `diff(v)` (`SV/mapreduce.jl:276`, `_diff`): `out[i] = v[i+1] - v[i]`.
`diff` of an empty vector is an error in Julia (B18); the type rules it out. -/
@[inline] def diff [Sub α] (v : Values α (n + 1)) : Values α n :=
  ofFn fun i => v.get i.succ - v.get i.castSucc

@[simp] theorem get_diff [Sub α] (v : Values α (n + 1)) (i : Fin n) :
    v.diff.get i = v.get i.succ - v.get i.castSucc := by simp [diff]

end Values

end StaticVectors

import AbstractAnalysis.Sequence

/-!
# Norms, metrics and convergence predicates

Julia's `@norm supnorm` / `@metric` macros (src/metric.jl:24-73) define, for
each norm `f`, the metric `f(a, b) = f(a - b)` on numbers and arrays, lift it
through `k => v` pairs, and fall back to `Inf` (or `0.0` for `infnorm`) on
anything else. In Lean the fallbacks become type errors, which is the point:
a `Limit` over a type without a norm does not typecheck.

* `Normed α`: Julia `norm(x)` (`abs` on numbers, the **2-norm** on arrays,
  quirk #26: `supnorm` of an array is Euclidean, not the max-norm).
* `Metric α`: the distance a `Limit` uses (Julia's `D` type parameter).
-/

namespace AbstractAnalysis

open JuliaBase

/-- Julia `LinearAlgebra.norm` on the values the analysis layer carries. -/
class Normed (α : Type) where
  /-- Julia `norm(x)`. -/
  norm : α → Float

/-- A distance: Julia's metric type parameter `D` of `Limit{T,F,D}`. -/
class Metric (α : Type) where
  /-- Julia `D(a, b)`. -/
  dist : α → α → Float

export Metric (dist)

instance (priority := low) {α : Type} [JNumber α] : Normed α := ⟨JNumber.norm⟩
instance : Normed (Complex Float) := ⟨ComplexF64.abs⟩

/-- Julia `LinearAlgebra.generic_norm2` on a list of element norms: plain
`sqrt(Σ|x|²)` unless that would overflow/underflow, else rescaled by `max|x|`. -/
def norm2Of (xs : FloatArray) : Float :=
  let n := xs.size
  let rec maxAbs (i : Nat) (m : Float) : Nat → Float
    | 0 => m
    | fuel + 1 => maxAbs (i + 1) (max m xs[i]!.abs) fuel
  let rec sumSq (i : Nat) (s : Float) (scale : Float) : Nat → Float
    | 0 => s
    | fuel + 1 => let y := xs[i]! / scale; sumSq (i + 1) (s + y * y) scale fuel
  let m := maxAbs 0 0 n
  if n == 0 || m == 0 || m.isInf then m
  else if (Float.ofNat n * m * m).isFinite && m * m != 0 then Float.sqrt (sumSq 0 0 1 n)
  else m * Float.sqrt (sumSq 0 0 m n)

instance : Normed FloatArray := ⟨norm2Of⟩
instance {α : Type} [Normed α] : Normed (Array α) :=
  ⟨fun a => norm2Of (a.foldl (fun acc x => acc.push (Normed.norm x)) (FloatArray.emptyWithCapacity a.size))⟩

/-- Julia `@metric`: `f(a, b) = f(a - b)` for any type with subtraction and a norm. -/
instance (priority := low) {α : Type} [Sub α] [Normed α] : Metric α := ⟨fun a b => Normed.norm (a - b)⟩

/-- Julia `supnorm(a - b)` for packed vectors (elementwise difference, 2-norm). -/
instance : Metric FloatArray where
  dist a b :=
    let n := min a.size b.size
    let rec diff (i : Nat) (acc : FloatArray) : Nat → FloatArray
      | 0 => acc
      | fuel + 1 => diff (i + 1) (acc.push (a[i]! - b[i]!)) fuel
    norm2Of (diff 0 (FloatArray.emptyWithCapacity n) n)

/-- Julia `supnorm(a - b)` for arrays: the 2-norm of elementwise distances. -/
instance {α : Type} [Metric α] : Metric (Array α) where
  dist a b :=
    norm2Of ((a.zip b).foldl (fun acc (x, y) => acc.push (Metric.dist x y)) (FloatArray.emptyWithCapacity a.size))

/-- Julia `supnorm(x)` (src/metric.jl:59-62). -/
@[inline] def supnorm {α : Type} [Normed α] (x : α) : Float := Normed.norm x

/-- Julia `infnorm(x)` (src/metric.jl:64-67): identical to `supnorm` wherever a
norm exists (Julia's `0.0` fallback is a type error here). -/
@[inline] def infnorm {α : Type} [Normed α] (x : α) : Float := Normed.norm x

/-- Julia `maxabs(x) = maximum(norm, x)` (the true sup-norm, src/metric.jl:69). -/
def maxabs {α : Type} [Normed α] (x : Array α) : Float :=
  match x[0]? with
  | none => 0
  | some a0 => x.foldl (fun m a => max m (Normed.norm a)) (Normed.norm a0)

/-- Julia `minabs(x) = minimum(norm, x)` (src/metric.jl:72). -/
def minabs {α : Type} [Normed α] (x : Array α) : Float :=
  match x[0]? with
  | none => 0
  | some a0 => x.foldl (fun m a => min m (Normed.norm a)) (Normed.norm a0)

/-- Julia `residuals(x, d)`: `[d(x_i, x_{i-1})]` along the last axis
(src/metric.jl:353-363). -/
def residuals {σ S : Type} [LastDimStorage σ S] (x : σ) (d : S → S → Float) : FloatArray :=
  go 2 (FloatArray.emptyWithCapacity (lastDim x - 1)) (lastDim x - 1)
where
  /-- Tail-recursive scan. -/
  go (i : Nat) (acc : FloatArray) : Nat → FloatArray
    | 0 => acc
    | fuel + 1 => go (i + 1) (acc.push (d (extract x i) (extract x (i - 1)))) fuel

/-- Julia `lipschitz(x, d, r=/)`: ratios of successive residuals
(src/metric.jl:347). -/
def lipschitz {σ S : Type} [LastDimStorage σ S] (x : σ) (d : S → S → Float)
    (r : Float → Float → Float := (· / ·)) : FloatArray :=
  residuals (residuals x d) r

/-- Julia `residualproduct(x, d)`: the distance matrix `[d(a, b) for a ∈ x, b ∈ x]`
(src/metric.jl:371-372), row-major. -/
def residualProduct {α : Type} (x : Array α) (d : α → α → Float) : Array FloatArray :=
  x.map fun a => x.foldl (fun acc b => acc.push (d a b)) (FloatArray.emptyWithCapacity x.size)

/-! ## Convergence predicates (src/metric.jl:389-437) -/

/-- Julia `isdiverging(x, d)`: true iff the successive residuals never
decrease when scanned backwards. Requires `length(x) ≥ 2` (Julia errors
otherwise; here the answer is `true`). -/
def isDiverging {α : Type} [Inhabited α] (x : Array α) (d : α → α → Float) : Bool :=
  let n := x.size
  if n < 2 then true else
  let rec go (i : Nat) (ri : Float) : Nat → Bool
    | 0 => true
    | fuel + 1 =>
      if i < 2 then true else
      let r' := d x[i - 1]! x[i - 2]!
      if ri < r' then false else go (i - 1) r' fuel
  go (n - 1) (d x[n - 1]! x[n - 2]!) n

/-- Julia `isconverging(x) = !isdiverging(x)`. -/
def isConverging {α : Type} [Inhabited α] (x : Array α) (d : α → α → Float) : Bool := !isDiverging x d

/-- Julia `iscauchy(x, d)`: the tail diameters `max_{i>n} d(x_n, x_i)` are
monotone (src/metric.jl:410-423). -/
def isCauchy {α : Type} [Inhabited α] (x : Array α) (d : α → α → Float) : Bool :=
  let N := x.size
  if N < 2 then true else
  let tailMax (n : Nat) : Float :=
    (List.range (N - n)).foldl (fun m j => max m (d x[n - 1]! x[n + j]!)) 0
  let rec go (n : Nat) (e0 : Float) : Nat → Bool
    | 0 => true
    | fuel + 1 =>
      if n = 0 then true else
      let em := tailMax n
      if e0 > em then false else go (n - 1) em fuel
  go (N - 2) (d x[N - 2]! x[N - 1]!) N

/-- Julia `isincreasing` (non-strict). -/
def isIncreasing {α : Type} [LT α] [DecidableRel (α := α) (· < ·)] [Inhabited α] (x : Array α) : Bool :=
  (List.range (x.size - 1)).all fun i => !(x[i + 1]! < x[i]!)

/-- Julia `isdecreasing` (non-strict). -/
def isDecreasing {α : Type} [LT α] [DecidableRel (α := α) (· < ·)] [Inhabited α] (x : Array α) : Bool :=
  (List.range (x.size - 1)).all fun i => !(x[i]! < x[i + 1]!)

/-- Julia `ismonotonic`. -/
def isMonotonic {α : Type} [LT α] [DecidableRel (α := α) (· < ·)] [Inhabited α] (x : Array α) : Bool :=
  isIncreasing x || isDecreasing x

/-- Julia `isbounded` as written: **inverted** (true iff every entry is
infinite, quirk #22, src/metric.jl:391-396). -/
def Julia.isBounded (x : FloatArray) : Bool := x.toList.all Float.isInf

/-- `isbounded` as intended: every entry is finite. -/
def isBounded (x : FloatArray) : Bool := x.toList.all Float.isFinite

/-! ## Suprema and infima of tails (src/metric.jl:486-544) -/

/-- Julia `supseq(x)`: suffix maxima `out[i] = max(x[i:end])`. -/
def supseq {α : Type} [Max α] (x : Array α) : Array α :=
  (x.foldr (fun a (acc : List α) => match acc with
    | [] => [a]
    | b :: _ => max a b :: acc) []).toArray

/-- Julia `infseq(x)`: suffix minima. -/
def infseq {α : Type} [Min α] (x : Array α) : Array α :=
  (x.foldr (fun a (acc : List α) => match acc with
    | [] => [a]
    | b :: _ => min a b :: acc) []).toArray

/-- Julia `countsup(x, n, k) = max(x[k], …, x[k+n])` (reads past the end of a
countable sequence, like Julia). -/
def windowMax {α : Type} [Max α] (x : Nat → α) (n k : Nat) : α :=
  (List.range n).foldl (fun m j => max m (x (k + j + 1))) (x k)

/-- Julia `countinf(x, n, k) = min(x[k], …, x[k+n])`. -/
def windowMin {α : Type} [Min α] (x : Nat → α) (n k : Nat) : α :=
  (List.range n).foldl (fun m j => min m (x (k + j + 1))) (x k)

/-- Julia `supseq(x, m)`: the lazy windowed maxima `k ↦ max(x[k..k+m])`. -/
def CountableVector.supseq {α : Type} [Max α] (x : CountableVector α) (m : Nat) : CountableVector α :=
  ⟨windowMax x.f m, x.len⟩

/-- Julia `infseq(x, m)`. -/
def CountableVector.infseq {α : Type} [Min α] (x : CountableVector α) (m : Nat) : CountableVector α :=
  ⟨windowMin x.f m, x.len⟩

/-- Julia `limsup(x::AbstractVector, m=5) = supseq(x, m)[end-m]`: the maximum of
the last `m+1` entries. -/
def limsup {α : Type} [Max α] [Inhabited α] (x : Array α) (m : Nat := 5) : α :=
  windowMax (fun i => x[i - 1]!) m (x.size - m)

/-- Julia `liminf(x::AbstractVector, m=5)`. -/
def liminf {α : Type} [Min α] [Inhabited α] (x : Array α) (m : Nat := 5) : α :=
  windowMin (fun i => x[i - 1]!) m (x.size - m)

/-- Julia `limsup(x::AbstractVector, m, n) = supseq(x, m)[n]` (src/metric.jl:543): the window
maximum at position `n` (1-based). -/
def limsupAt {α : Type} [Max α] [Inhabited α] (x : Array α) (m n : Nat) : α :=
  windowMax (fun i => x[i - 1]!) m n

/-- Julia `liminf(x::AbstractVector, m, n) = infseq(x, m)[n]` (src/metric.jl:544). -/
def liminfAt {α : Type} [Min α] [Inhabited α] (x : Array α) (m n : Nat) : α :=
  windowMin (fun i => x[i - 1]!) m n

/-! ## Finite differences (src/metric.jl:546-555) -/

/-- Julia's default step `eps()^(1/5)` for `derivative` (the value Julia's
`^(::Float64, ::Float64)` returns). -/
def derivativeStep : Float := 7.40095979741405e-4

/-- Julia `derivative(f, x, h)`: the five-point stencil
`(-f(x+2h) + 8f(x+h) - 8f(x-h) + f(x-2h)) / 12h`. -/
@[inline] def derivative (f : Float → Float) (x : Float) (h : Float := derivativeStep) : Float :=
  (-f (x + 2 * h) + 8 * f (x + h) - 8 * f (x - h) + f (x - 2 * h)) / (12 * h)

/-- Julia `derivative2(f, x, h = sqrt(sqrt(eps)))`: `(f(x+h) - 2f(x) + f(x-h)) / h²`. -/
@[inline] def derivative2 (f : Float → Float) (x : Float) (h : Float := 1.220703125e-4) : Float :=
  (f (x + h) - 2 * f x + f (x - h)) / (h * h)

end AbstractAnalysis

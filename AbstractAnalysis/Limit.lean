import AbstractAnalysis.Metric

/-!
# `Limit`: iterated maps, series and products

Julia's `Limit{T,F,D}` (src/metric.jl:77-122) records an iteration: initial
state `v0`, current state `v`, the number of states `n` (the initial one counts,
so `n = iterations + 1`), the last residual `r`, the step `f` and the metric `D`.

Julia states come in three shapes (port-notes §3.5):
1. raw values (orbits, `Limit(v0, n, F)`, `FixedCycle`);
2. `k => value` pairs (sums, products, `limit(countable)`): `Indexed V`;
3. `(k => inner) => value` pairs (arithmetic and `map` on limits): `Derived I V`.

Julia's `first`/`last` project Pair states to their value. Here that projection
is a field, `value : S → V`, so one structure covers all three shapes and the
metric always acts on values, as Julia's `@metric` Pair methods do. Cartan's
`TensorField` states are raw states with a custom `dist`.

The counting and residual conventions are Julia's exactly: they are visible in
printed goldens such as `sum(x)[1e-10]` showing `n → 100002`.
-/

namespace AbstractAnalysis

open JuliaBase

/-- Julia `k => v` state (sums, products, `limit(countable)`). -/
structure Indexed (V : Type) where
  /-- Index `k` (Julia `first(u)`). -/
  k : Nat
  /-- Value (Julia `last(u)`). -/
  val : V
  deriving Inhabited

/-- Julia `(k => inner) => v` state (arithmetic and `map` on limits). -/
structure Derived (I V : Type) where
  /-- Index `k`. -/
  k : Nat
  /-- The underlying state being advanced. -/
  inner : I
  /-- Derived value. -/
  val : V
  deriving Inhabited

/-- Julia `Limit{T,F,D}`. -/
structure Limit (S V : Type) where
  /-- Julia `initial(L)`. -/
  v0 : S
  /-- Julia `final(L)`. -/
  v : S
  /-- Julia `length(L)`: number of states. -/
  n : Nat
  /-- Julia `residual(L)`. -/
  r : Float
  /-- Julia `counter(L)`: one step. -/
  step : S → S
  /-- Julia `first`/`last` projection to values. -/
  value : S → V
  /-- Julia's metric `D`, on values. -/
  dist : V → V → Float

namespace Limit

variable {S V W T : Type}

/-- Julia `first(L)`: the initial value. -/
@[inline] def first (L : Limit S V) : V := L.value L.v0
/-- Julia `last(L)`: the current value. -/
@[inline] def last (L : Limit S V) : V := L.value L.v
/-- Julia `length(L)`. -/
@[inline] def length (L : Limit S V) : Nat := L.n
/-- Julia `residual(L)`. -/
@[inline] def residual (L : Limit S V) : Float := L.r

/-- Iterate `F` from `x` `k` times, returning `(x_{k-1}, x_k)`. -/
@[specialize] def iterPair (F : S → S) (x0 x : S) : Nat → S × S
  | 0 => (x0, x)
  | k + 1 => iterPair F x (F x) k

/-- Julia `Limit(v0, n, F, D)` (src/metric.jl:250-258): iterate `n` times and
record `n + 1` states with residual `D(x_n, x_{n-1})` (`0` when `n = 0`). -/
def iterate (v0 : S) (n : Nat) (F : S → S) (value : S → V) (dist : V → V → Float) : Limit S V :=
  let (x0, xn) := iterPair F v0 v0 n
  ⟨v0, xn, n + 1, dist (value xn) (value x0), F, value, dist⟩

/-- `Limit(v0, n, F, D)` for raw states. -/
def ofIterate (v0 : S) (n : Nat) (F : S → S) (dist : S → S → Float) : Limit S S :=
  iterate v0 n F id dist

/-- Julia `L[i]` (src/metric.jl:261-272): re-seek to state `i`, iterating from
`v0` when `i < n` and from `v` when `i > n`. -/
def seek (L : Limit S V) (i : Nat) : Limit S V :=
  if i == L.n then L else
  let (x0, xn) :=
    if i < L.n then iterPair L.step L.v0 L.v0 (i - 1)
    else iterPair L.step L.v L.v (i - L.n)
  ⟨L.v0, xn, i, L.dist (L.value xn) (L.value x0), L.step, L.value, L.dist⟩

/-- Julia `(L)(u)`: rerun the same number of steps from a new initial state. -/
def rerun (L : Limit S V) (u : S) : Limit S V := iterate u (L.n - 1) L.step L.value L.dist

/-- Default iteration cap for the open-ended loops (`limit(L, ϵ)`, `orbit`):
Julia loops forever when the tolerance is never met. -/
def maxIter : Nat := 100000000

/-- The loop of `limit(L, ϵ)` / `orbit(f, x, ϵ)`: step until the residual drops
to `ϵ`, returning `(state, previous state, count, residual, trace)`. -/
@[specialize] def untilConverged (F : S → S) (value : S → V) (dist : V → V → Float) (ϵ : Float)
    (trace : Bool) : S → S → Nat → Float → FloatArray → Nat → S × S × Nat × Float × FloatArray
  | x0, xn, n, change, out, 0 => (x0, xn, n, change, out)
  | x0, xn, n, change, out, fuel + 1 =>
    if change > ϵ then
      let xn' := F xn
      let c := dist (value xn') (value xn)
      untilConverged F value dist ϵ trace xn xn' (n + 1) c (if trace then out.push c else out) fuel
    else (x0, xn, n, change, out)

/-- Julia `limit(L, ϵ, Val(print))` (src/metric.jl:467-484). **Quirk #25,
reproduced:** the result's `v0` is the *old final state* and its length is
`old length + iterations + 1`. Also returns the residual trace. -/
def limitEpsTrace (L : Limit S V) (ϵ : Float) : Limit S V × FloatArray :=
  let x := L.v
  let (_, xn, n, change, out) := untilConverged L.step L.value L.dist ϵ true x x 1 (5 * ϵ) {} maxIter
  (⟨x, xn, n + L.n, change, L.step, L.value, L.dist⟩, out)

/-- Julia `limit(L, ϵ)` / `L[ϵ]`. -/
def limitEps (L : Limit S V) (ϵ : Float) : Limit S V :=
  let x := L.v
  let (_, xn, n, change, _) := untilConverged L.step L.value L.dist ϵ false x x 1 (5 * ϵ) {} maxIter
  ⟨x, xn, n + L.n, change, L.step, L.value, L.dist⟩

/-- Julia `collect(L)`: the values `x_1 … x_n`, re-derived by iterating from
`v0` (src/metric.jl:279-296). -/
def collect (L : Limit S V) : Array V :=
  go L.v0 (Array.mkEmpty L.n) L.n
where
  /-- Tail-recursive collection. -/
  go (s : S) (acc : Array V) : Nat → Array V
    | 0 => acc
    | k + 1 => let acc := acc.push (L.value s); if k = 0 then acc else go (L.step s) acc k

/-- Julia `collect(L)` for array-valued raw states: a `SequenceArray` whose
recurrence continues the iteration (src/metric.jl:292-296; Cartan's
`collect(::Limit{<:TensorField})`). -/
def collectSeq [Inhabited S] (L : Limit S S) : SequenceArray (Array S) S :=
  let seq : SequenceArray (Array S) S := ⟨#[L.v0], fun u k => L.step u[k - 2]!⟩
  seq.resize L.n

/-- Julia `map(f, L)` (src/metric.jl:124-137): value map with residual `Inf`;
the state tracks the underlying iteration. -/
def map (f : V → W) (L : Limit S V) (dist : W → W → Float) : Limit (Derived S W) W where
  v0 := ⟨1, L.v0, f L.first⟩
  v := ⟨L.n, L.v, f L.last⟩
  n := L.n
  r := 1.0 / 0.0
  step d := let s := L.step d.inner; ⟨d.k + 1, s, f (L.value s)⟩
  value := Derived.val
  dist := dist

/-- Julia `a ⊙ L` (src/metric.jl:159-164): advances **one step**, so the length
is `n + 1` and the residual compares the last two values. -/
def opLeft (op : T → V → V) (a : T) (L : Limit S V) : Limit (Derived S V) V :=
  let st (d : Derived S V) : Derived S V := let p := L.step d.inner; ⟨d.k + 1, p, op a (L.value p)⟩
  let vn : Derived S V := ⟨L.n, L.v, op a L.last⟩
  let vn1 := st vn
  ⟨⟨1, L.v0, op a L.first⟩, vn1, L.n + 1, L.dist vn1.val vn.val, st, Derived.val, L.dist⟩

/-- Julia `L ⊙ b` (src/metric.jl:165-170). -/
def opRight (op : V → T → V) (L : Limit S V) (b : T) : Limit (Derived S V) V :=
  let st (d : Derived S V) : Derived S V := let p := L.step d.inner; ⟨d.k + 1, p, op (L.value p) b⟩
  let vn : Derived S V := ⟨L.n, L.v, op L.last b⟩
  let vn1 := st vn
  ⟨⟨1, L.v0, op L.first b⟩, vn1, L.n + 1, L.dist vn1.val vn.val, st, Derived.val, L.dist⟩

/-- Julia `L₁ ⊙ L₂` (src/metric.jl:171-175): both advance once from their
final states and the length **resets to 2**. -/
def op₂ {S' : Type} (op : V → V → V) (a : Limit S V) (b : Limit S' V) : Limit (Derived (S × S') V) V :=
  let st (d : Derived (S × S') V) : Derived (S × S') V :=
    let p := a.step d.inner.1
    let q := b.step d.inner.2
    ⟨d.k + 1, (p, q), op (a.value p) (b.value q)⟩
  let v0 : Derived (S × S') V := ⟨1, (a.v, b.v), op a.last b.last⟩
  let vn := st v0
  ⟨v0, vn, 2, a.dist vn.val v0.val, st, Derived.val, a.dist⟩

instance [Add V] : HAdd V (Limit S V) (Limit (Derived S V) V) := ⟨opLeft (· + ·)⟩
instance [Add V] : HAdd (Limit S V) V (Limit (Derived S V) V) := ⟨opRight (· + ·)⟩
instance [Sub V] : HSub V (Limit S V) (Limit (Derived S V) V) := ⟨opLeft (· - ·)⟩
instance [Sub V] : HSub (Limit S V) V (Limit (Derived S V) V) := ⟨opRight (· - ·)⟩
instance [Mul V] : HMul V (Limit S V) (Limit (Derived S V) V) := ⟨opLeft (· * ·)⟩
instance [Mul V] : HMul (Limit S V) V (Limit (Derived S V) V) := ⟨opRight (· * ·)⟩
instance [Div V] : HDiv V (Limit S V) (Limit (Derived S V) V) := ⟨opLeft (· / ·)⟩
instance [Div V] : HDiv (Limit S V) V (Limit (Derived S V) V) := ⟨opRight (· / ·)⟩
instance {S' : Type} [Add V] : HAdd (Limit S V) (Limit S' V) (Limit (Derived (S × S') V) V) := ⟨op₂ (· + ·)⟩
instance {S' : Type} [Mul V] : HMul (Limit S V) (Limit S' V) (Limit (Derived (S × S') V) V) := ⟨op₂ (· * ·)⟩
instance {S' : Type} [Sub V] : HSub (Limit S V) (Limit S' V) (Limit (Derived (S × S') V) V) := ⟨op₂ (· - ·)⟩

/-- Julia `sum(L::Limit)` (src/metric.jl:211-216): the series of the values of
`L`, over the same number of states, measured with the default `supnorm`. -/
def sum [Add V] [Metric V] (L : Limit S V) : Limit (Derived S V) V :=
  iterate ⟨1, L.v0, L.first⟩ (L.n - 1)
    (fun d => let s := L.step d.inner; ⟨d.k + 1, s, d.val + L.value s⟩) Derived.val Metric.dist

/-- Julia `prod(L::Limit)` (src/metric.jl:217-222). -/
def prod [Mul V] [Metric V] (L : Limit S V) : Limit (Derived S V) V :=
  iterate ⟨1, L.v0, L.first⟩ (L.n - 1)
    (fun d => let s := L.step d.inner; ⟨d.k + 1, s, d.val * L.value s⟩) Derived.val Metric.dist

/-- Julia `show(io, L)` (src/metric.jl:114-122). Numbers (or `compact`) print
on one line **with a trailing newline**; other values print a header line and
then `show(last(L))` without a newline. -/
def toJulia [JuliaRepr V] (L : Limit S V) (compact : Bool := false) : String :=
  if JuliaRepr.isNumber V || compact then
    s!"{JuliaRepr.str L.last} (n → {L.n}, Δ → {F64.showString L.r})\n"
  else
    s!"Limit as n → {L.n}, Δ → {F64.showString L.r}\n{JuliaRepr.repr L.last}"

instance [JuliaRepr V] : ToString (Limit S V) := ⟨fun L => L.toJulia⟩

end Limit

/-! ## Reductions (Julia `mapreduce`) -/

/-- Julia's pairwise `mapreduce_impl` over indices `i₀ … i₁` (base/reduce.jl:252):
sequential below 1024 elements, split in half above. (`@simd` reassociation
inside a block is not modelled; goldens compare with a tolerance there.) -/
def pairwiseReduce {α : Type} (op : α → α → α) (f : Nat → α) (i₀ i₁ : Nat) : α :=
  go i₀ i₁ (i₁ - i₀ + 1)
where
  /-- Sequential left fold over `i … i₁`. -/
  seq (acc : α) (i : Nat) : Nat → α
    | 0 => acc
    | fuel + 1 => seq (op acc (f i)) (i + 1) fuel
  /-- Recursion fuelled by the range size. -/
  go (a b : Nat) : Nat → α
    | 0 => f a
    | fuel + 1 =>
      if a == b then f a
      else if b - a < 1024 then seq (op (f a) (f (a + 1))) (a + 2) (b - a - 1)
      else
        let m := a + (b - a) / 2
        op (go a m fuel) (go (m + 1) b fuel)

/-- Julia `sum(view(x, :))` for the first `len` terms (base/reduce.jl:428-448). -/
def CountableVector.jsum {α : Type} [JNumber α] (x : CountableVector α) : α :=
  if x.len = 0 then JNumber.zero else pairwiseReduce (· + ·) x.f 1 x.len

/-- Julia `prod(view(x, :))`. -/
def CountableVector.jprod {α : Type} [JNumber α] (x : CountableVector α) : α :=
  if x.len = 0 then JNumber.one else pairwiseReduce (· * ·) x.f 1 x.len

namespace CountableVector

variable {α : Type}

/-- Julia `sum(x::CountableVector)` (src/metric.jl:204-206): a `Limit` of
partial sums at `len` whose **residual is the last term** `x[end]`. -/
def sum [JNumber α] [Metric α] (x : CountableVector α) : Limit (Indexed α) α where
  v0 := ⟨1, x.f 1⟩
  v := ⟨x.len, x.jsum⟩
  n := x.len
  r := JNumber.toFloat (x.f x.len)
  step u := ⟨u.k + 1, u.val + x.f (u.k + 1)⟩
  value := Indexed.val
  dist := Metric.dist

/-- Julia `prod(x::CountableVector)` (src/metric.jl:207-210): residual
`supnorm(val, val/x[end])`. -/
def prod [JNumber α] [Metric α] (x : CountableVector α) : Limit (Indexed α) α where
  v0 := ⟨1, x.f 1⟩
  v := ⟨x.len, x.jprod⟩
  n := x.len
  r := JNumber.quotResidual x.jprod (x.f x.len)
  step u := ⟨u.k + 1, u.val * x.f (u.k + 1)⟩
  value := Indexed.val
  dist := Metric.dist

/-- Julia `limit(x::CountableFunction, n = len, d)` (src/metric.jl:453-455):
the state `n => x[n]` with residual `d(x[n], x[n-1])`. -/
def limit (x : CountableVector α) (n : Nat := x.len) (d : α → α → Float) : Limit (Indexed α) α where
  v0 := ⟨1, x.f 1⟩
  v := ⟨n, x.f n⟩
  n := n
  r := d (x.f n) (x.f (n - 1))
  step u := ⟨u.k + 1, x.f (u.k + 1)⟩
  value := Indexed.val
  dist := d

/-- Julia `limit(x::CountableVector, ϵ) = limit(limit(x, 2), ϵ)` / `x[ϵ]`. -/
def limitEps (x : CountableVector α) (ϵ : Float) (d : α → α → Float) : Limit (Indexed α) α :=
  (x.limit 2 d).limitEps ϵ

/-- Julia `dot(a, b, Σ = sum) = Σ(a * b)` (src/AbstractAnalysis.jl:115). -/
def dot [JNumber α] [Metric α] (a b : CountableVector α) : Limit (Indexed α) α := (a * b).sum

end CountableVector

/-- `n!` (Julia `factorial`, promoted to `BigInt` in Julia when `n > 20`). -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- Julia `prod(x::typeof(Naturals))` (src/AbstractAnalysis.jl:415-419): the
factorial as a limit, residual `supnorm(val/x[end], val)`. The step is Julia's
`factorial` (only meaningful for display; Julia's own step is ill-typed). -/
def prodNaturals (n : Nat) : Limit (Indexed Int) Int where
  v0 := ⟨1, 1⟩
  v := ⟨n, (factorial n : Int)⟩
  n := n
  r :=
    if n ≤ 20 then let v := Float.ofNat (factorial n); (v / Float.ofNat n - v).abs
    else -- Julia switches to `BigInt`/`BigFloat`: the residual is the rounded exact value
      IEEEFloat.ofRat Float ((factorial n : Rat) - (factorial n : Rat) / (n : Rat))
  step u := ⟨u.k + 1, u.val * ((u.k + 1 : Nat) : Int)⟩
  value := Indexed.val
  dist a b := (Float.ofInt a - Float.ofInt b).abs

/-- Julia `SequenceArray` `limit(x, n, d)` (src/metric.jl:456-460): the state
`n => x[n]`, stepping through the memoized sequence. -/
def SequenceArray.limit {σ S : Type} [LastDimStorage σ S] (x : SequenceArray σ S) (n : Nat)
    (d : S → S → Float) : Limit (Indexed S) S :=
  let x := x.resize n
  { v0 := ⟨1, extract x.v 1⟩
    v := ⟨n, extract x.v n⟩
    n := n
    r := d (extract x.v n) (extract x.v (n - 1))
    step := fun u => ⟨u.k + 1, (x.get (u.k + 1)).1⟩
    value := Indexed.val
    dist := d }

/-! ## Orbits (src/metric.jl:298-340)

Julia's metric argument defaults to `supnorm`, the `Metric` of the state type here: when `d` is
omitted it is found by instance resolution at the call site (`orbit Float.cos 1.0`), and states
without a `Metric` instance (Cartan's tensor fields) pass their own `d`. -/

/-- Julia `orbit(f, x, ϵ = 5eps(), Val(false), d = supnorm)`: iterate until
`d(x_{k+1}, x_k) ≤ ϵ`. -/
def orbit {S : Type} (f : S → S) (x : S) (ϵ : Float := 5 * 2.220446049250313e-16)
    (d : S → S → Float := by exact AbstractAnalysis.Metric.dist) : Limit S S :=
  let (_, xn, n, change, _) := Limit.untilConverged f id d ϵ false x x 1 (5 * ϵ) {} Limit.maxIter
  ⟨x, xn, n, change, f, id, d⟩

/-- Julia `orbiterror(f, x, ϵ, d = supnorm)`: the orbit plus its residual trace. -/
def orbitError {S : Type} (f : S → S) (x : S) (ϵ : Float := 5 * 2.220446049250313e-16)
    (d : S → S → Float := by exact AbstractAnalysis.Metric.dist) : Limit S S × FloatArray :=
  let (_, xn, n, change, out) := Limit.untilConverged f id d ϵ true x x 1 (5 * ϵ) {} Limit.maxIter
  (⟨x, xn, n, change, f, id, d⟩, out)

/-- Julia `orbit(f, x, k::Int, d = supnorm)`: exactly `k` steps, length `k + 1`. -/
def orbitN {S : Type} (f : S → S) (x : S) (k : Nat)
    (d : S → S → Float := by exact AbstractAnalysis.Metric.dist) : Limit S S :=
  let (x0, xn) := Limit.iterPair f x x k
  ⟨x, xn, k + 1, d xn x0, f, id, d⟩

/-- Julia `orbit(f, x, k, Val(true), d = supnorm)`: `k` steps with the residual of each. -/
def orbitNTrace {S : Type} (f : S → S) (x : S) (k : Nat)
    (d : S → S → Float := by exact AbstractAnalysis.Metric.dist) : Limit S S × FloatArray :=
  let rec go (x0 xn : S) (out : FloatArray) : Nat → S × S × FloatArray
    | 0 => (x0, xn, out)
    | j + 1 => let xn' := f xn; go xn xn' (out.push (d xn' xn)) j
  let (x0, xn, out) := go x x (FloatArray.emptyWithCapacity k) k
  (⟨x, xn, k + 1, d xn x0, f, id, d⟩, out)

/-- Julia `orbithold(f, x, n, d = supnorm)`: iterate `xₙ ↦ f(x, xₙ)` with `x` held fixed.
The step stored in the result is `f x`. -/
def orbitHold {S : Type} (f : S → S → S) (x : S) (k : Nat)
    (d : S → S → Float := by exact AbstractAnalysis.Metric.dist) : Limit S S :=
  let (x0, xn) := Limit.iterPair (f x) x x k
  ⟨x, xn, k + 1, d xn x0, f x, id, d⟩

/-- Julia `FixedCycle{F,D}`: a step function with a default iteration count
(src/metric.jl:376-387). -/
structure FixedCycle (S : Type) where
  /-- Julia `length(fc)` (default `100`). -/
  n : Nat := 100
  /-- The step. -/
  f : S → S
  /-- The metric. -/
  d : S → S → Float

namespace FixedCycle

variable {S : Type}

/-- Julia `fc[i]`: same map, new count. -/
def withLen (fc : FixedCycle S) (i : Nat) : FixedCycle S := { fc with n := i }

/-- Julia `(fc)(u, n = length(fc)) = Limit(u, n, f, D)`. -/
def run (fc : FixedCycle S) (u : S) (n : Nat := fc.n) : Limit S S := Limit.ofIterate u n fc.f fc.d

end FixedCycle

/-! ## Series and products of function families -/

/-- Julia `(s::Series)(x, Σ = sum)` (src/AbstractAnalysis.jl:209-212): with
`Ones` coefficients this is `sum(f(x))`, else `sum(c[1:len] * f(x))`. -/
def Series.eval {β α : Type} [JNumber α] [Metric α] (s : Series β α) (x : β) : Limit (Indexed α) α :=
  match s.coeffs with
  | none => (s.family.eval x).sum
  | some c => (c.withLen (min c.len s.family.len) * s.family.eval x).sum

/-- Julia `sum(f::FunctionArray) = Series(f)`. -/
def FunctionVector.series {β α : Type} (f : FunctionVector β α) : Series β α := ⟨none, f⟩

/-- Julia `(p::Product)(x, Π = prod) = Π(f(x))`. -/
def Product.eval {β α : Type} [JNumber α] [Metric α] (p : Product β α) (x : β) : Limit (Indexed α) α :=
  (p.family.eval x).prod

/-- Julia `prod(f::FunctionArray) = Product(f)`. -/
def FunctionVector.product {β α : Type} (f : FunctionVector β α) : Product β α := ⟨f⟩

end AbstractAnalysis

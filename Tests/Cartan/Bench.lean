import Cartan

/-!
Benchmarks of Cartan's field operations (compare `oracle/cartan/bench.jl`): building fields from
functions on grids, pointwise scalar functions, the flat linear operations, Grassmann products of
`Chain` fields and reductions, on a 1000×1000 grid and a 10⁶-point interval.

`run` prints `name: time` lines (best of several repetitions) and a checksum so that nothing is
optimized away.
-/

open Cartan Grassmann

namespace Tests.Cartan.Bench

/-- An opaque identity: the compiler cannot see through it, so work that depends on its result is
neither hoisted out of the timing loop nor shared between repetitions. -/
@[noinline] def blackBox {α : Type} (_salt : Nat) (x : α) : α := x

/-- Best wall time (ns) of `reps` runs of `f` (each run gets a different salt), and the last
result. -/
def timeBest {α : Type} (reps : Nat) (f : Nat → α) : IO (Nat × α) := do
  let mut best := 0
  let mut out := f reps
  for k in [0:reps] do
    let t0 ← IO.monoNanosNow
    out := f k
    let t1 ← IO.monoNanosNow
    if k == 0 || t1 - t0 < best then best := t1 - t0
  return (best, out)

/-- Format nanoseconds (one decimal). -/
def fmt (ns : Nat) : String :=
  if ns < 10000 then s!"{ns} ns"
  else if ns < 10000000 then s!"{ns / 1000}.{ns / 100 % 10} µs"
  else s!"{ns / 1000000}.{ns / 100000 % 10} ms"

/-- A `Chain ℝ3` from three coordinates. -/
@[inline] def chain3 (x y z : Float) : Chain ℝ3 1 Float := Chain.ofFn fun i =>
  if i.1 = 0 then x else if i.1 = 1 then y else z

/-- The checksum of a field: the sum of its flat data. -/
def checksum {M F : Type} [FrameBundle M] [FlatFiber F] {m : M} (t : TensorField m F) : Float :=
  JuliaBase.F64.sum t.data

/-- Run the benchmarks (`smoke`: a tiny configuration). -/
def run (smoke : Bool := false) : IO Unit := do
  let n : Nat := if smoke then 20 else 1000
  let reps := if smoke then 1 else 7
  let step := (1 : Float) / Float.ofNat (n - 1)
  let ps : ProductSpace 2 := .ofAxes #v[Axis.range 0 1 n, Axis.range 0 1 n]
  let g := GridBundle.ofSpace ps
  let line := Axis.range 0 10 (n * n)
  let report (name : String) (ns : Nat) (c : Float) : IO Unit :=
    IO.println s!"{name}: {fmt ns}  (checksum {c})"
  -- building fields
  let (ns, v) ← timeBest reps fun k =>
    ((TensorField.tabulatePoint (blackBox k g) fun x => chain3 (x.get! 0) (x.get! 1) 1).rebase? g).get!
  report s!"tabulate Chain ℝ3 on {n}×{n}" ns (checksum v)
  let (ns, w) ← timeBest reps fun k =>
    ((TensorField.tabulatePoint (blackBox k g) fun x => chain3 1 (-x.get! 1) (x.get! 0)).rebase? g).get!
  report "tabulate w" ns (checksum w)
  let (ns, a) ← timeBest reps fun k =>
    ((TensorField.tabulatePoint (blackBox k g) fun x => x.get! 0 + 2 * x.get! 1).rebase? g).get!
  report "tabulate scalar" ns (checksum a)
  let (ns, r) ← timeBest reps fun k =>
    ((TensorField.tabulate2 (blackBox k g) fun x y => chain3 x y 1).rebase? g).get!
  report "tabulate2 Chain ℝ3 (coordinates, no point)" ns (checksum r)
  let (ns, r) ← timeBest reps fun k =>
    ((TensorField.tabulate2 (blackBox k g) fun x y => x + 2 * y).rebase? g).get!
  report "tabulate2 scalar" ns (checksum r)
  let lb := GridBundle.ofAxis line
  let (ns, t) ← timeBest reps fun k => ((TensorField.ofAxis (blackBox k line)).rebase? lb).get!
  report s!"identity field of range({n * n})" ns (checksum t)
  -- scalar functions and linear operations
  let (ns, s) ← timeBest reps fun k => (blackBox k t).sin
  report "sin(t)" ns (checksum s)
  let (ns, e) ← timeBest reps fun k => (blackBox k t).exp
  report "exp(t)" ns (checksum e)
  let (ns, r) ← timeBest reps fun k => blackBox k t + s
  report "t + s" ns (checksum r)
  let (ns, r) ← timeBest reps fun k => (blackBox k s) * (2 : Float)
  report "s * 2" ns (checksum r)
  let (ns, r) ← timeBest reps fun k => blackBox k s * t
  report "s * t (field product)" ns (checksum r)
  let (ns, r) ← timeBest reps fun k => blackBox k v + w
  report "v + w (Chain)" ns (checksum r)
  let (ns, r) ← timeBest reps fun k => (2 : Float) * blackBox k v
  report "2v (Chain)" ns (checksum r)
  let (ns, r) ← timeBest reps fun k => blackBox k a * v
  report "a * v (scalar field times Chain field)" ns (checksum r)
  -- Grassmann products
  let (ns, r) ← timeBest reps fun k => blackBox k v ∧ w
  report "v ∧ w" ns (checksum r)
  let (ns, q) ← timeBest reps fun k => blackBox k v * w
  report "v * w (geometric)" ns (checksum q)
  let (ns, r) ← timeBest reps fun k => blackBox k v ⋅ w
  report "v ⋅ w" ns (checksum r)
  let (ns, r) ← timeBest reps fun k => ⋆(blackBox k v)
  report "⋆v" ns (checksum r)
  let (ns, r) ← timeBest reps fun k => (blackBox k v).norm
  report "norm(v)" ns (checksum r)
  let (ns, x) ← timeBest reps fun k => ((blackBox k a).eval2 0.3 0.7)
  report "a(0.3, 0.7) (one evaluation)" ns x
  -- reductions
  let (ns, x) ← timeBest reps fun k => (blackBox k s).sumF
  report "sum(s)" ns x
  let (ns, x) ← timeBest reps fun k => (blackBox k v).supnorm
  report "supnorm(v)" ns x
  -- a parametrized surface (Julia `torus.(TorusParameter(n, n))`)
  let T := Parameter.torus #v[n, n]
  let (ns, r) ← timeBest reps fun k => (blackBox k T).map fun p =>
    let u := p.get! 0
    let vv := p.get! 1
    let rr := 3 + Float.cos vv
    chain3 (rr * Float.cos u) (rr * Float.sin u) (Float.sin vv)
  report "torus.(TorusParameter(n,n))" ns (checksum r)
  IO.println s!"(step {step})"

end Tests.Cartan.Bench

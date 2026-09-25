import Bench.Harness.Json

/-!
# Benchmark harness

A small benchmark DSL shared by every suite of `lake exe bench`, mirrored line for line by the
Julia harness `oracle/bench/harness.jl`, so that each Lean case key `suite/case` has a Julia
twin measured by the same algorithm:

1. **Warm-up.** The body runs once untimed (first-touch allocation, thunks, caches), then once
   timed; that call's checksum is the reported `check` (skipped when the first call alone
   exceeded the case cap).
2. **Calibration.** The iteration count `k` grows ×4 until one timed batch of `k` body calls
   takes at least a tenth of the per-sample target; `k` is then scaled so that one batch takes
   about `sampleNs` (default 20 ms).
3. **Samples.** `samples` batches (default 7, fewer when a single call is slow: the whole case is
   capped near `caseNs`) are timed; each gives ns per operation = batch time / (k · ops).
   The result reports the minimum and the median.

`ops` is the number of logical operations one body call performs (for example the length of the
sweep a scalar kernel is evaluated over), so the reported unit is **ns per operation**.

**Keeping the work alive.** The body receives the iteration index; every result is folded into
a checksum (`Checksum`) that is written to a global reference after each batch and reported,
so no result is dead. Inputs that the compiler could see as closed terms must go through
`blackBox salt x`, an opaque identity whose salt is the iteration index, so that a pure
computation is neither hoisted out of the timing loop nor shared between iterations.

**Filters.** A case runs when its key `suite/case` contains one of the `--filter` substrings
(or when there are none). Setup work that only a case needs belongs in `benchWith`'s setup
action, which is skipped for filtered-out cases.
-/

namespace Bench

universe u v

open JuliaBase

/-- Harness options (command line: `lake exe bench --help`). -/
structure Config where
  /-- Tiny sizes and a single short sample per case (CI smoke test). -/
  smoke : Bool := false
  /-- Target duration of one timed batch, in ns. -/
  sampleNs : Nat := 20000000
  /-- Number of timed batches per case. -/
  samples : Nat := 7
  /-- Soft cap on the total timed duration of one case, in ns. -/
  caseNs : Nat := 1500000000
  /-- Substrings of `suite/case` keys to run (empty: everything). -/
  filters : Array String := #[]
  /-- Print only the result lines. -/
  quiet : Bool := false
  deriving Inhabited

/-- One measured case. Times are ns per operation. -/
structure Result where
  /-- Suite name (the first half of the key). -/
  suite : String
  /-- Case name (the second half of the key). -/
  name : String
  /-- Size description, for display (`n=10000`). -/
  param : String
  /-- Operations per body call. -/
  ops : Nat
  /-- Body calls per timed batch. -/
  iters : Nat
  /-- Timed batches. -/
  samples : Nat
  /-- Fastest batch, ns per operation. -/
  minNs : Float
  /-- Median batch, ns per operation. -/
  medianNs : Float
  /-- Slowest batch, ns per operation. -/
  maxNs : Float
  /-- The checksum of one body result (comparable with the Julia twin when both compute
  the same quantity; `NaN` when meaningless). -/
  check : Float
  deriving Inhabited

/-- `suite/case`. -/
def Result.key (r : Result) : String := r.suite ++ "/" ++ r.name

/-- Mutable state of a run. -/
structure Ctx where
  /-- Options. -/
  cfg : Config
  /-- The suite being run. -/
  suite : String
  /-- Results so far. -/
  results : IO.Ref (Array Result)

/-- The benchmark monad: suites are `BenchM Unit` programs that call `bench`. -/
abbrev BenchM := ReaderT Ctx IO

/-- Whether this run uses smoke-test sizes. -/
def smoke : BenchM Bool := return (← read).cfg.smoke

/-- `full` normally, `small` under `--smoke`. -/
def size (full small : Nat) : BenchM Nat := return if (← smoke) then small else full

/-- Print unless `--quiet`. -/
def note (msg : String) : BenchM Unit := do
  unless (← read).cfg.quiet do IO.println msg

/-! ## Sinks -/

/-- A cheap scalar summary of a result, folded into the checksum so that the result is live.
Lean and Julia instances agree where the notion is shared (a float is itself, an integer its
value, a collection or string its length). -/
class Checksum (α : Type u) where
  /-- The summary. -/
  check : α → Float

instance : Checksum Float := ⟨id⟩
instance : Checksum Float32 := ⟨Float32.toFloat⟩
instance : Checksum Nat := ⟨fun n => if n < 2 ^ 64 then n.toUInt64.toFloat else Float.ofNat n⟩
instance : Checksum Int := ⟨fun n => if n.natAbs < 2 ^ 63 then n.toInt64.toFloat else Float.ofInt n⟩
instance : Checksum UInt64 := ⟨UInt64.toFloat⟩
instance : Checksum UInt32 := ⟨UInt32.toFloat⟩
instance : Checksum Bool := ⟨fun b => if b then 1 else 0⟩
instance : Checksum Unit := ⟨fun _ => 0⟩
instance : Checksum String := ⟨fun s => s.length.toUInt64.toFloat⟩
instance : Checksum FloatArray := ⟨fun a => a.size.toUInt64.toFloat⟩
instance : Checksum ByteArray := ⟨fun a => a.size.toUInt64.toFloat⟩
instance {α : Type u} : Checksum (Array α) := ⟨fun a => a.size.toUInt64.toFloat⟩
instance {α : Type u} : Checksum (List α) := ⟨fun a => a.length.toUInt64.toFloat⟩
instance {α : Type u} {β : Type v} [Checksum α] [Checksum β] : Checksum (α × β) :=
  ⟨fun (a, b) => Checksum.check a + Checksum.check b⟩
instance {α : Type u} [Checksum α] : Checksum (Option α) := ⟨fun o => o.elim 0 Checksum.check⟩

/-- Implementation of `blackBox`: the result depends on `salt` through a branch the compiler
cannot decide (`ptrAddrUnsafe` is an external call; a `Nat` is never at address 0, so the
first branch is never taken). -/
@[noinline] unsafe def blackBoxImpl {α : Type u} (salt : Nat) (x : α) : α :=
  if ptrAddrUnsafe salt == 0 then unsafeCast salt else x

/-- An opaque identity whose result depends on the salt (the iteration index), so a computation
on it can neither be extracted as a closed term, hoisted out of the timing loop, nor shared
between iterations.

A plain `@[noinline] def blackBox (_salt : Nat) (x : α) := x` does **not** work: the compiler's
arity reduction drops the unused salt (`blackBox._redArg x`), after which `f (blackBox s 10)`
is a closed term computed once at initialization, and a body `fun s => …` that no longer uses
`s` is itself extracted. -/
@[implemented_by blackBoxImpl] def blackBox {α : Type u} (_salt : Nat) (x : α) : α := x

/-- The global sink: every batch's checksum lands here. -/
initialize sinkRef : IO.Ref Float ← IO.mkRef 0

/-! ## Deterministic inputs -/

/-- One SplitMix64 step (as `Tests/Util/Random.lean` and the Julia harness): `(value, state)`. -/
@[inline] def splitmix64 (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (z ^^^ (z >>> 31), s)

/-- `2⁻⁵³`. -/
def twoPowNeg53 : Float := Float.ofBits 0x3CA0000000000000

/-- `n` floats uniform in `[lo, hi)` from SplitMix64 seeded with `seed` (53-bit mantissas); the
same sequence as `randfloats` in `oracle/bench/harness.jl`. -/
def randFloats (n : Nat) (seed : UInt64) (lo : Float := 0) (hi : Float := 1) : FloatArray :=
  go n seed (FloatArray.emptyWithCapacity n)
where
  /-- Tail-recursive fill. -/
  go : Nat → UInt64 → FloatArray → FloatArray
    | 0, _, acc => acc
    | k + 1, s, acc =>
      let (z, s) := splitmix64 s
      go k s (acc.push (lo + (hi - lo) * ((z >>> 11).toFloat * twoPowNeg53)))

/-- `n` raw SplitMix64 outputs. -/
def randWords (n : Nat) (seed : UInt64) : Array UInt64 :=
  go n seed (Array.mkEmpty n)
where
  /-- Tail-recursive fill. -/
  go : Nat → UInt64 → Array UInt64 → Array UInt64
    | 0, _, acc => acc
    | k + 1, s, acc => let (z, s) := splitmix64 s; go k s (acc.push z)

/-! ## Timing -/

/-- `k` body calls for iteration indices `i, i+1, …`, their checksums summed. Structural
recursion in `IO`, so the calls are sequenced and never inlined into the caller. -/
@[specialize] def runBatch {α : Type} [Checksum α] (body : Nat → α) : (k i : Nat) → Float → IO Float
  | 0, _, acc => pure acc
  | k + 1, i, acc => do
    let r := body i
    runBatch body k (i + 1) (acc + Checksum.check r)

/-- Time one batch of `k` calls starting at index `i`: `(ns, checksum)`. -/
@[specialize] def timeBatch {α : Type} [Checksum α] (body : Nat → α) (k i : Nat) : IO (Nat × Float) := do
  let t0 ← IO.monoNanosNow
  let c ← runBatch body k i 0
  sinkRef.set c
  let t1 ← IO.monoNanosNow
  return (t1 - t0, c)

/-- Median of a non-empty array. -/
def median (xs : Array Float) : Float :=
  let s := xs.qsort (· < ·)
  if s.isEmpty then 0 else
  if s.size % 2 == 1 then s[s.size / 2]! else (s[s.size / 2 - 1]! + s[s.size / 2]!) / 2

/-- Human-readable time per operation. -/
def fmtNs (ns : Float) : String :=
  if ns < 1000 then F64.showCompact ns ++ " ns"
  else if ns < 1e6 then F64.showCompact (ns / 1e3) ++ " µs"
  else if ns < 1e9 then F64.showCompact (ns / 1e6) ++ " ms"
  else F64.showCompact (ns / 1e9) ++ " s"

/-- Pad on the right to width `w`. -/
def padRight (s : String) (w : Nat) : String := s ++ String.ofList (List.replicate (w - s.length) ' ')

/-- Whether the key `suite/name` passes the filters. -/
def selected (cfg : Config) (key : String) : Bool :=
  cfg.filters.isEmpty || cfg.filters.any fun f => (key.splitOn f).length > 1

/-- The shared measurement algorithm (module docstring). `timeK k i` times `k` calls starting at
iteration index `i` and returns `(ns, checksum)`. -/
def measureWith (name param : String) (ops : Nat) (timeK : Nat → Nat → IO (Nat × Float)) :
    BenchM Unit := do
  let ctx ← read
  let cfg := ctx.cfg
  let ops := max ops 1
  -- warm-up: one untimed call, then one timed call whose checksum is the reported check
  -- (skipped when the first call alone exceeded the case cap)
  let (t1, c1) ← timeK 1 0
  let (tw, check) ← if t1 > cfg.caseNs then pure (t1, c1) else timeK 1 0
  -- calibration: grow k until a batch takes ≥ sampleNs / 10
  let mut k := 1
  let mut t := tw
  let mut i := 1
  if tw < cfg.sampleNs / 10 then
    for _ in [0:40] do
      let (tk, _) ← timeK k i
      i := i + k
      t := tk
      if tk ≥ cfg.sampleNs / 10 || k ≥ (1 <<< 40) then break
      k := k * 4
  -- scale k so that a batch lasts about sampleNs
  let perCall := (max t 1).toFloat / k.toFloat
  let kk := max 1 (cfg.sampleNs.toFloat / perCall).ceil.toUInt64.toNat
  let batch := perCall * kk.toFloat
  let nsamp := if cfg.smoke then 1 else
    max 1 (min cfg.samples (cfg.caseNs.toFloat / max batch 1).floor.toUInt64.toNat)
  let mut per : Array Float := #[]
  for _ in [0:nsamp] do
    let (ts, _) ← timeK kk i
    i := i + kk
    per := per.push (ts.toFloat / (kk.toFloat * ops.toFloat))
  let r : Result := {
    suite := ctx.suite, name, param, ops, iters := kk, samples := nsamp
    minNs := per.foldl min per[0]!, medianNs := median per, maxNs := per.foldl max per[0]!
    check }
  ctx.results.modify (·.push r)
  IO.println s!"  {padRight r.key 44} {padRight param 16} median {padRight (fmtNs r.medianNs) 12} min {padRight (fmtNs r.minNs) 12} ({kk}×{nsamp})"

/-- Benchmark a case: `body i` is one call (`ops` operations) at iteration index `i`. -/
def bench {α : Type} [Checksum α] (name : String) (body : Nat → α) (ops : Nat := 1)
    (param : String := "") : BenchM Unit := do
  let ctx ← read
  unless selected ctx.cfg (ctx.suite ++ "/" ++ name) do return
  measureWith name param ops (timeBatch body)

/-- Benchmark a case whose inputs come from `setup` (run only if the case is selected, not
timed). -/
def benchWith {β α : Type} [Checksum α] (name : String) (setup : IO β) (body : β → Nat → α)
    (ops : Nat := 1) (param : String := "") : BenchM Unit := do
  let ctx ← read
  unless selected ctx.cfg (ctx.suite ++ "/" ++ name) do return
  let inp ← setup
  measureWith name param ops (timeBatch (body inp))

/-- Time `k` calls of an `IO` action. -/
def timeBatchIO {α : Type} [Checksum α] (act : Nat → IO α) (k i : Nat) : IO (Nat × Float) := do
  let t0 ← IO.monoNanosNow
  let mut c := 0.0
  for j in [0:k] do
    c := c + Checksum.check (← act (i + j))
  sinkRef.set c
  let t1 ← IO.monoNanosNow
  return (t1 - t0, c)

/-- Benchmark an `IO` action (cases that spawn tasks or need effects); `act i` is one call. -/
def benchIO {α : Type} [Checksum α] (name : String) (act : Nat → IO α) (ops : Nat := 1)
    (param : String := "") : BenchM Unit := do
  let ctx ← read
  unless selected ctx.cfg (ctx.suite ++ "/" ++ name) do return
  measureWith name param ops (timeBatchIO act)

/-! ## Suites and output -/

/-- A named suite. -/
structure Suite where
  /-- Suite name: the first half of every key it produces. -/
  name : String
  /-- The cases. -/
  run : BenchM Unit

/-- Adapters from the shapes a suite entry point may have. -/
class IntoSuite (α : Type) where
  /-- Wrap as a suite called `name`. -/
  into : String → α → Suite

instance : IntoSuite (BenchM Unit) := ⟨fun n r => ⟨n, r⟩⟩
instance : IntoSuite (Suite) := ⟨fun _ s => s⟩
/-- A legacy entry point `run (smoke : Bool) : IO Unit` prints its own lines and records nothing. -/
instance : IntoSuite (Bool → IO Unit) := ⟨fun n r => ⟨n, do r (← smoke)⟩⟩
instance : IntoSuite (IO Unit) := ⟨fun n r => ⟨n, liftM (m := IO) r⟩⟩

/-- Run suites, returning every result. -/
def runSuites (cfg : Config) (suites : List Suite) : IO (Array Result) := do
  let results ← IO.mkRef #[]
  for s in suites do
    unless cfg.quiet do IO.println s!"== {s.name}"
    s.run { cfg, suite := s.name, results }
  results.get

/-- The results as a JSON document, one result per line (schema in `docs/perf/README.md`). -/
def toJson (cfg : Config) (rs : Array Result) : String :=
  let res := rs.toList.map fun r => Json.render <| .obj #[
    ("key", .str r.key), ("suite", .str r.suite), ("case", .str r.name), ("param", .str r.param),
    ("ops", .nat r.ops), ("iters", .nat r.iters), ("samples", .nat r.samples),
    ("min_ns", .num r.minNs), ("median_ns", .num r.medianNs), ("max_ns", .num r.maxNs),
    ("check", .num r.check)]
  "{\"lang\": \"lean\", \"smoke\": " ++ Json.render (.bool cfg.smoke) ++
    ", \"sample_ns\": " ++ toString cfg.sampleNs ++ ", \"samples\": " ++ toString cfg.samples ++
    ",\n \"results\": [\n  " ++ ",\n  ".intercalate res ++ "\n]}\n"

end Bench

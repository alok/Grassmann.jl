import Grassmann
import Grassmann.Kernel.Generated
import Tests.Util.Random

/-!
# Product benchmarks of the generated kernels (DESIGN.md §5.2, docs/PERF.md)

For `ℝ3`, `STA`, `PGA3` and `CGA3` at `Float`: `Multivector*Multivector`,
`Spinor*Spinor`, the rotor sandwich of a vector (`R*v*~R`, `v ⊘ R`, `R >>> v`),
`Chain1∧Chain1`, `Chain2*Chain1`, the reverse and the Hodge complement of a
multivector and the Hodge complement of a vector. Each is timed as ns per call
over `N` calls on a ring of `K = 1024` random operands (inputs vary per call,
so nothing is loop-invariant), each result's coefficients summed into the
accumulator (so every output is computed), best of 7 runs after a warm-up: the
loop of `oracle/bench/grassmann_bench.jl`, which times the same operations in
Julia. The reference kernels (the interpreted plans every space had before code
generation) are timed on two products for comparison.

The call sites are ordinary typed expressions (`a * b`, `v ⊘ R`, ...) at concrete
types: their `Kernels` dispatch folds at compile time to the generated kernels,
specialized at `Float`.
-/

namespace Bench.Grassmann

open _root_.Grassmann DirectSum StaticVectors Grassmann.Kernel

/-- Ring size of the operand arrays (a power of two). -/
def ringSize : Nat := 1024

/-- Sum of the coefficients (keeps every output of a product live): a `USize` loop over the
packed storage (`FloatArray.foldl`). -/
@[inline] def total {n : Nat} (v : Values Float n) : Float := v.data.foldl (· + ·) 0

/-- `Σ f(xs[i & m], ys[(7i + 3) & m])` over `k` calls from `i`, `m = K - 1` (tail-recursive,
unboxed accumulator, `USize` indices, no default values). -/
@[specialize] def loop2 {X Y : Type} (f : X → Y → Float) (xs : Array X) (ys : Array Y) :
    Nat → USize → Float → Float
  | 0, _, acc => acc
  | k + 1, i, acc =>
    let m : USize := 1023
    let a := (i &&& m).toNat
    let b := ((7 * i + 3) &&& m).toNat
    if h : a < xs.size ∧ b < ys.size then
      loop2 f xs ys k (i + 1) (acc + f xs[a] ys[b])
    else acc

/-- `Σ f(xs[i & m])` over `k` calls from `i`. -/
@[specialize] def loop1 {X : Type} (f : X → Float) (xs : Array X) : Nat → USize → Float → Float
  | 0, _, acc => acc
  | k + 1, i, acc =>
    let m : USize := 1023
    let a := (i &&& m).toNat
    if h : a < xs.size then loop1 f xs k (i + 1) (acc + f xs[a]) else acc

/-- `f` applied `k` times to `x`: the result of each call is the (exclusive) operand of the
next, so kernels that write into their operand work in place. -/
@[specialize] def iterate {X : Type} (f : X → X) (x : X) : Nat → X
  | 0 => x
  | k + 1 => iterate f (f x) k

/-- Time one run of `run k salt` (ns per call) and return its checksum. -/
@[noinline] def measure (run : Nat → USize → Float) (k : Nat) (salt : USize) : IO (Float × Float) := do
  let t0 ← IO.monoNanosNow
  let s ← IO.lazyPure fun _ => run k salt
  let t1 ← IO.monoNanosNow
  return ((t1 - t0).toFloat / k.toUInt64.toFloat, s)

/-- Warm up, then print the best of `reps` runs of `k` calls. -/
def timed (name : String) (k reps : Nat) (run : Nat → USize → Float) : IO Float := do
  let _ ← measure run (k / 10 + 1) 0
  let mut best := 1.0e30
  let mut sum := 0.0
  for r in [0:reps] do
    let (t, s) ← measure run k r.toUSize
    best := min best t
    sum := s
  let name := name.pushn ' ' (26 - name.length)
  IO.println s!"  {name} {JuliaBase.F64.showCompact best} ns/op   (checksum {JuliaBase.F64.showCompact sum})"
  return best

/-- `n` random values in `[-1, 1)`. -/
def randVals (n : Nat) : Tests.Gen (Values Float n) := do
  let xs ← Tests.Gen.array n (Tests.Gen.floatIn (-1) 1)
  return Values.ofFn fun i => xs[i.1]!

/-- `ringSize` random values of a container. -/
def ring {X : Type} (n : Nat) (mk : Values Float n → X) : Tests.Gen (Array X) := do
  let mut out := #[]
  for _ in [0:ringSize] do out := out.push (mk (← randVals n))
  return out

/-- The benchmarks of one space. Specialized at every call on the `Kernels V` instance, so
each space's typed operations compile to its generated kernels. -/
@[inline] def space (label : String) (V : TensorBundle) [Kernels V] [SandwichKernels V] (N reps : Nat) (seed : Nat) :
    IO (List (String × Float)) := do
  let n := V.n
  let ((M, S, U, C), _) := (do
      return (← ring (2 ^ n) (Multivector.mk (V := V)), ← ring (Layout.even.size n) (Half.mk (V := V) (odd := false)),
        ← ring (Layout.size n (.chain 1)) (Chain.mk (V := V) (G := 1)),
        ← ring (Layout.size n (.chain 2)) (Chain.mk (V := V) (G := 2))) : Tests.Gen _)
    |> (StateT.run · (Tests.Rng.ofSeed seed))
  IO.println s!"== {label}  {V}"
  let mvN := if n ≥ 5 then N / 10 else N
  let mut out := []
  -- the harness alone: the coefficient sum of an operand, and of a fresh copy of it (one
  -- allocation, copy and free of a result: the floor of every Lean operation here)
  out := ("sum of an operand", ← timed "sum of an operand" N reps fun k i =>
    loop1 (fun (a : Multivector V Float) => total a.v) M k i 0) :: out
  out := ("copy of an operand", ← timed "copy of an operand" N reps fun k i =>
    loop1 (fun (a : Multivector V Float) =>
      (a.v.data.set! 0 (a.v.data.get! 1)).foldl (· + ·) 0) M k i 0) :: out
  out := ("Multivector*Multivector", ← timed "Multivector*Multivector" mvN reps fun k i =>
    loop2 (fun (a b : Multivector V Float) => total (a * b).v) M M k i 0) :: out
  out := ("Spinor*Spinor", ← timed "Spinor*Spinor" N reps fun k i =>
    loop2 (fun (s t : Spinor V Float) => total (s * t : Spinor V Float).v) S S k i 0) :: out
  out := ("R*v*~R", ← timed "R*v*~R" N reps fun k i =>
    loop2 (fun (R : Spinor V Float) (v : Chain V 1 Float) => total (R * v * ~R : CoSpinor V Float).v) S U k i 0) :: out
  out := ("v ⊘ R", ← timed "v ⊘ R" N reps fun k i =>
    loop2 (fun (R : Spinor V Float) (v : Chain V 1 Float) => total (v ⊘ R : Chain V 1 Float).v) S U k i 0) :: out
  out := ("R >>> v", ← timed "R >>> v" N reps fun k i =>
    loop2 (fun (R : Spinor V Float) (v : Chain V 1 Float) => total (R >>> v : Chain V 1 Float).v) S U k i 0) :: out
  out := ("Chain1∧Chain1", ← timed "Chain1∧Chain1" N reps fun k i =>
    loop2 (fun (a b : Chain V 1 Float) => total (a ∧ b : Chain V 2 Float).v) U U k i 0) :: out
  out := ("Chain2*Chain1", ← timed "Chain2*Chain1" N reps fun k i =>
    loop2 (fun (c : Chain V 2 Float) (u : Chain V 1 Float) => total (c * u : CoSpinor V Float).v) C U k i 0) :: out
  out := ("reverse Multivector", ← timed "reverse Multivector" N reps fun k i =>
    loop1 (fun (a : Multivector V Float) => total (~a).v) M k i 0) :: out
  out := ("reverse in place (m := ~m)", ← timed "reverse in place (m := ~m)" N reps fun k i =>
    let m := M[i.toNat % ringSize]!
    total (iterate (fun (a : Multivector V Float) => ~a) m k).v) :: out
  out := ("hodge Multivector", ← timed "hodge Multivector" N reps fun k i =>
    loop1 (fun (a : Multivector V Float) => total (⋆a : Multivector V Float).v) M k i 0) :: out
  out := ("hodge Chain1", ← timed "hodge Chain1" N reps fun k i =>
    loop1 (fun (u : Chain V 1 Float) => total (⋆u : Chain V (V.n - 1) Float).v) U k i 0) :: out
  -- the reference kernels (interpreted plans) on the same operands
  out := ("ref Multivector*Multivector", ← timed "ref Multivector*Multivector" (mvN / 10 + 1) reps fun k i =>
    loop2 (fun (a b : Multivector V Float) => total (refBin V .mul .full .full .full a.v b.v)) M M k i 0) :: out
  out := ("ref Spinor*Spinor", ← timed "ref Spinor*Spinor" (N / 10 + 1) reps fun k i =>
    loop2 (fun (s t : Spinor V Float) => total (refBin V .mul .even .even .even s.v t.v)) S S k i 0) :: out
  return out.reverse

/-- Run the suite; `smoke` uses few iterations. The environment variable
`GRASSMANN_BENCH_SPACES` (e.g. `ℝ3,CGA3`) restricts the spaces, `GRASSMANN_BENCH_N` sets the
number of calls per operation. -/
def run (smoke : Bool) : IO Unit := do
  let only := (← IO.getEnv "GRASSMANN_BENCH_SPACES").map (·.splitOn ",")
  let N := match (← IO.getEnv "GRASSMANN_BENCH_N").bind String.toNat? with
    | some k => k
    | none => if smoke then 10000 else 10000000
  let reps := if smoke then 1 else 7
  let want := fun (l : String) => only.all (·.contains l)
  IO.println s!"Grassmann products at Float ({N} calls per operation, ns/op, best of {reps})"
  if want "ℝ3" then discard <| space "ℝ3" ℝ3 N reps 1
  if want "STA" then discard <| space "STA" STA N reps 2
  if want "PGA3" then discard <| space "PGA3" PGA3 N reps 3
  if want "CGA3" then discard <| space "CGA3" CGA3 N reps 4

end Bench.Grassmann

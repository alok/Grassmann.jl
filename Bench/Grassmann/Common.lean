import Bench.Harness
import Grassmann

/-!
# Shared pieces of the `grassmann` suite

Every case of the suite has the same shape, mirrored by its Julia twin
(`oracle/bench/grassmann.jl`): one body call applies an operation to the `K = 1024`
operands of a ring (binary operations pair `xs[i]` with `ys[(7i + 3) mod K]`), sums every
coefficient of every result into a `Float` accumulator (so every output is computed and
live), and counts as `K` operations. The operands are built from `Bench.randFloats`
(SplitMix64, uniform in `[-1, 1)`), the same numbers in the same storage order as the Julia
twin, so the checksums agree.
-/

namespace Bench.Grassmann

open _root_.Grassmann DirectSum StaticVectors Bench

/-- Ring size of the operand arrays (a power of two). -/
def ringSize : Nat := 1024

/-- Sum of the coefficients (keeps every output of a result live): a `USize` loop over the
packed storage (`FloatArray.foldl`). -/
@[inline] def total {n : Nat} (v : Values Float n) : Float := v.data.foldl (· + ·) 0

/-- `ringSize` elements built from `ringSize · d` random floats in `[-1, 1)` (element `i` takes
the floats `i·d, …, i·d + d - 1`, Julia's `vals[(i-1)d+1 : i·d]`). -/
def ringOf {X : Type} (d : Nat) (seed : UInt64) (mk : Values Float d → X) : Array X :=
  let xs := randFloats (d * ringSize) seed (-1) 1
  (Array.range ringSize).map fun i => mk (Values.ofFn fun j => xs[i * d + j.1]!)

/-- `Σ f(xs[i], ys[(7i + 3) & (K-1)])` over `i < K` (tail-recursive, unboxed accumulator,
`USize` indices). -/
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

/-- `Σ f(xs[i])` over `i < K`. -/
@[specialize] def loop1 {X : Type} (f : X → Float) (xs : Array X) : Nat → USize → Float → Float
  | 0, _, acc => acc
  | k + 1, i, acc =>
    let m : USize := 1023
    let a := (i &&& m).toNat
    if h : a < xs.size then loop1 f xs k (i + 1) (acc + f xs[a]) else acc

/-- `f` applied `k` times to `x`: each call's result is the (exclusive) operand of the next,
so kernels that write into their operand work in place. -/
@[specialize] def iterate {X : Type} (f : X → X) (x : X) : Nat → X
  | 0 => x
  | k + 1 => iterate f (f x) k

/-- A binary case: `K` calls of `f` on the rings `xs`, `ys` per body call. -/
@[inline] def case2 {X Y : Type} (name : String) (f : X → Y → Float) (xs : Array X) (ys : Array Y)
    (param : String := "") : BenchM Unit :=
  bench name (ops := ringSize) (param := param) fun s => loop2 f (blackBox s xs) ys ringSize 0 0

/-- A unary case: `K` calls of `f` on the ring `xs` per body call. -/
@[inline] def case1 {X : Type} (name : String) (f : X → Float) (xs : Array X) (param : String := "") :
    BenchM Unit :=
  bench name (ops := ringSize) (param := param) fun s => loop1 f (blackBox s xs) ringSize 0 0

end Bench.Grassmann

import Bench.Harness
import Grassmann

/-!
# `dynamic`: the dynamic (Julia-exact) element layer `Grassmann.TA`

Julia twin: `oracle/bench/dynamic.jl`, the same operations on Grassmann.jl elements stored in a
`Vector{Any}` (so Julia dispatches on the runtime type, as the dynamic layer does on its kind).
Operands are rings of 1024 random elements of `ℝ3` (`Submanifold(3)`) with `Float64`
coefficients from `randFloats`; each body sweeps the ring (`ops = 1024` pairs, the second
operand at index `7k + 3`) and sums every result's stored coefficients (the checksum), so the
work is identical in both languages.

* `mul_multi`, `mul_chain1`, `wedge_chain1`, `mul_single`, `add_multi`, `reverse_multi`: the
  operator instances (`*`, `∧`, `+`, `~`), which in `ℝ3` take the generated kernels
  (`Grassmann.Dynamic.Fast`, `DynKernels ℝ3`);
* `*_loops`: the same through Julia's loops (`TA.mul`, `TA.wedge`, `TA.add`, `TA.reverse`),
  what every space without `DynKernels` runs (Lean only).
-/

namespace Bench.Dynamic

open _root_.Grassmann DirectSum StaticVectors Bench

/-- Ring size. -/
def ringSize : Nat := 1024

/-- Elements of a container layout from consecutive random floats in `[-1, 1)`. -/
def randTAs (l : Layout) (seed : UInt64) : Array (TA ℝ3 Float) :=
  let w := l.size 3
  let xs := randFloats (ringSize * w) seed (-1) 1
  (Array.range ringSize).map fun k =>
    TA.ofLayout (V := ℝ3) l (Values.ofFn fun i => xs.get! (k * w + i.1))

/-- Random `Single`s on the blades `1 + (w mod 7)` (never the scalar). -/
def randSingles (seed : UInt64) : Array (TA ℝ3 Float) :=
  let xs := randFloats ringSize seed (-1) 1
  let bs := randWords ringSize (seed + 1)
  (Array.range ringSize).map fun k => .single ((1 : UInt64) + bs[k]! % 7) (xs.get! k)

/-- The sum of a result's stored coefficients (Julia `sum(value(x))`). -/
def taSum (x : TA ℝ3 Float) : Float :=
  match x with
  | .zero => 0
  | .one | .blade _ => 1
  | .single _ v => v
  | .couple _ re im | .pseudo _ re im => re + im
  | .chain _ c => c.v.data.foldl (· + ·) 0
  | .spinor h | .cospinor h => h.v.data.foldl (· + ·) 0
  | .multi m => m.v.data.foldl (· + ·) 0
  | _ => 0

/-- `Σ taSum (f xs[k] ys[7k+3])` over `k` calls (tail-recursive, `USize` indices). -/
@[specialize] def sweep2 (f : TA ℝ3 Float → TA ℝ3 Float → TA ℝ3 Float) (xs ys : Array (TA ℝ3 Float)) :
    Nat → USize → Float → Float
  | 0, _, acc => acc
  | k + 1, i, acc =>
    let m : USize := 1023
    let a := (i &&& m).toNat
    let b := ((7 * i + 3) &&& m).toNat
    if h : a < xs.size ∧ b < ys.size then sweep2 f xs ys k (i + 1) (acc + taSum (f xs[a] ys[b]))
    else acc

/-- `Σ taSum (f xs[k])` over `k` calls. -/
@[specialize] def sweep1 (f : TA ℝ3 Float → TA ℝ3 Float) (xs : Array (TA ℝ3 Float)) :
    Nat → USize → Float → Float
  | 0, _, acc => acc
  | k + 1, i, acc =>
    let m : USize := 1023
    let a := (i &&& m).toNat
    if h : a < xs.size then sweep1 f xs k (i + 1) (acc + taSum (f xs[a])) else acc

/-- The suite. -/
def suite : Suite := ⟨"dynamic", do
  let ms := randTAs .full 101
  let ns := randTAs .full 102
  let cs := randTAs (.chain 1) 103
  let ds := randTAs (.chain 1) 104
  let ss := randSingles 105
  let ts := randSingles 107
  let n := ringSize
  bench "mul_multi_R3" (ops := n) fun s => sweep2 (· * ·) (blackBox s ms) ns n 0 0
  bench "mul_multi_R3_loops" (ops := n) fun s => sweep2 TA.mul (blackBox s ms) ns n 0 0
  bench "mul_chain1_R3" (ops := n) fun s => sweep2 (· * ·) (blackBox s cs) ds n 0 0
  bench "mul_chain1_R3_loops" (ops := n) fun s => sweep2 TA.mul (blackBox s cs) ds n 0 0
  bench "wedge_chain1_R3" (ops := n) fun s => sweep2 (· ∧ ·) (blackBox s cs) ds n 0 0
  bench "wedge_chain1_R3_loops" (ops := n) fun s => sweep2 TA.wedge (blackBox s cs) ds n 0 0
  bench "mul_single_R3" (ops := n) fun s => sweep2 (· * ·) (blackBox s ss) ts n 0 0
  bench "add_multi_R3" (ops := n) fun s => sweep2 (· + ·) (blackBox s ms) ns n 0 0
  bench "add_multi_R3_loops" (ops := n) fun s => sweep2 TA.add (blackBox s ms) ns n 0 0
  bench "reverse_multi_R3" (ops := n) fun s => sweep1 (~·) (blackBox s ms) n 0 0
  bench "reverse_multi_R3_loops" (ops := n) fun s => sweep1 TA.reverse (blackBox s ms) n 0 0⟩

end Bench.Dynamic

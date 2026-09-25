import Bench.Harness
import DirectSum

/-!
# `directsum`: blade operations, index tables, product plans

Julia twin: `oracle/bench/directsum.jl` (Grassmann 0.8 / DirectSum / Leibniz). Blade-level
operations are what Grassmann's generated product code evaluates at compile time and what the
Lean fallback kernels and code generator evaluate at elaboration/plan time.

* `parity_R8`: the reordering-and-metric sign `parity(8, s, a, b)` of all 256² blade pairs
  (Julia: the cached `Grassmann.parity`).
* `blade_mul_R5`, `blade_mul_CGA3`: the geometric product of every pair of the 32 basis blades
  (Julia: `a * b` on `Submanifold`s taken from a vector, i.e. dynamically dispatched; `CGA3`
  takes the Gram/Chevalley path of `paritygeometric`).
* `plan_mul_R5`: the multiply-accumulate plan of `Multivector × Multivector` (Julia: the same
  loop over basis pairs recording `(i, j, basisindex(r), sign)`); `plan_mul_CGA3` is Lean-only.
* `index_tables_n10`: building Leibniz's `indexbasis`/`bladeindex` tables for `n = 10`
  (Julia: the `_calc` functions its caches call); `basis_index_n10`: cached lookups.
* `blade_show_R10`: the ASCII labels (`v10`, `v12345678910`) of all 1024 blades of `ℝ10`
  (Julia: `string` of the names `Λ(V).b`).
-/

namespace Bench.DirectSum

open _root_.DirectSum Leibniz Bench

/-- A scalar summary of a blade result: `±1` for a signed blade, `0` for zero, else the number
of nonzero terms (the Julia twin computes the same from Julia's result type). -/
def weight : BladeResult → Float
  | .zero => 0
  | .blade _ => 1
  | .single c _ => if c < 0 then -1 else if c > 0 then 1 else 0
  | .sum t => (t.filter (·.2 != 0)).size.toUInt64.toFloat
  | .nested _ r => weight r

/-- `∑ weight (V.mul a b)` over all pairs of `bs`. -/
def mulAll (V : TensorBundle) (bs : Array UInt64) : Float :=
  bs.foldl (fun acc a => bs.foldl (fun acc b => acc + weight (V.mul a b)) acc) 0

/-- Number of pairs `a, b < 2^n` with `parityjoin s a b`. -/
def parityCount (s : UInt64) (n : Nat) : Nat :=
  go 0 0 (n * n)
where
  /-- Flat loop over `k = a·n + b`. -/
  go (k acc : Nat) : Nat → Nat
    | 0 => acc
    | f + 1 =>
      let a := (k / n).toUInt64
      let b := (k % n).toUInt64
      go (k + 1) (if parityjoin s a b then acc + 1 else acc) f

/-- `∑ basisIndex n b` over all `b < 2^n` (a counted loop, as the Julia twin's `for b in
0:(1<<n)-1`). -/
def sumBasisIndex (n : Nat) : Nat :=
  go 0 0 (1 <<< n)
where
  /-- Tail-recursive loop over the masks. -/
  go (b : UInt64) (acc : Nat) : Nat → Nat
    | 0 => acc
    | k + 1 => go (b + 1) (acc + basisIndex n b) k

/-- Total bytes of the ASCII labels (`v12`, Julia's names `Λ(V).b`) of every blade. -/
def labelBytes (V : TensorBundle) (bs : Array UInt64) : Nat :=
  bs.foldl (fun acc b => acc + (V.bladeLabel b (label := true)).utf8ByteSize) 0

/-- The suite. -/
def suite : Suite := ⟨"directsum", do
  bench "parity_R8" (ops := 65536) (param := "256²") fun s => parityCount (blackBox s 1) 256
  let b5 := indexBasisAll 5
  bench "blade_mul_R5" (ops := 1024) (param := "32²") fun s =>
    mulAll (blackBox s (TensorBundle.sig 5)) b5
  bench "blade_mul_CGA3" (ops := 1024) (param := "32²") fun s => mulAll (blackBox s CGA3) b5
  bench "plan_mul_R5" (ops := 1024) (param := "32²") fun s =>
    ((blackBox s (TensorBundle.sig 5)).plan₂ .mul .full .full .full).toOption.map (·.size)
  bench "plan_mul_CGA3" (ops := 1024) (param := "32²") fun s =>
    ((blackBox s CGA3).plan₂ .mul .full .full .full).toOption.map (·.size)
  bench "index_tables_n10" (param := "n=10") fun s =>
    let t := IndexTables.build (blackBox s 10)
    t.basis.size + t.rank.size
  bench "basis_index_n10" (ops := 1024) (param := "n=10") fun s => sumBasisIndex (blackBox s 10)
  let b10 := indexBasisAll 10
  bench "blade_show_R10" (ops := 1024) (param := "n=10") fun s =>
    labelBytes (blackBox s (TensorBundle.sig 10)) b10⟩

end Bench.DirectSum

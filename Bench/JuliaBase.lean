import Bench.Harness
import JuliaBase

/-!
# `juliabase`: Julia `Base` semantics

Julia twin: `oracle/bench/juliabase.jl`. Inputs come from SplitMix64 on both sides (identical
values), so every check (total printed length, sums) agrees exactly when the semantics do.

* `show_float`, `show_float_compact`: Julia's Ryu shortest printing (`string(x)`, the compact
  `IOContext`) of 1000 doubles with random mantissas and magnitudes `2^-32 … 2^31` (both the
  plain and the exponent layouts), ns per number.
* `parse_float`: `parse(Float64, s)` of those printed strings.
* `sum_f64`: `sum(::Vector{Float64})` (pairwise, SIMD in Julia), ns per element.
* `range_collect`, `colon_collect`, `range_getindex`: `TwicePrecision` ranges, ns per element.
* `round_digits`: `round(x, digits = 3)`.
* `complex_*`: `ComplexF64` division, `sqrt`, `exp`, `log`.
-/

namespace Bench.JuliaBase

open _root_.JuliaBase Bench

/-- A double with a random mantissa and sign and an exponent in `-32 … 31`, from one word. -/
@[inline] def wordFloat (w : UInt64) : Float :=
  Float.ofBits ((w &&& (0x800FFFFFFFFFFFFF : UInt64)) ||| (((991 : UInt64) + ((w >>> 52) &&& 63)) <<< 52))

/-- `∑ f xs[i]`. -/
@[specialize] def sumMap (f : Float → Float) (xs : FloatArray) : Float :=
  go 0 0
where
  /-- Tail-recursive loop. -/
  go (i : Nat) (acc : Float) : Float :=
    if h : i < xs.size then go (i + 1) (acc + f xs[i]) else acc
  termination_by xs.size - i

/-- `∑ bytes (f xs[i])`: total printed length. -/
@[specialize] def totalBytes (f : Float → String) (xs : FloatArray) : Nat :=
  go 0 0
where
  /-- Tail-recursive loop. -/
  go (i acc : Nat) : Nat :=
    if h : i < xs.size then go (i + 1) (acc + (f xs[i]).utf8ByteSize) else acc
  termination_by xs.size - i

/-- `∑ parse s`. -/
def sumParse (ss : Array String) : Float :=
  ss.foldl (fun acc s => acc + F64.parse s) 0

/-- `∑ (re + im) (f zs[i])` over complex numbers stored as `(re, im)` pairs. -/
@[specialize] def sumComplex (f : Complex Float → Complex Float) (zs : FloatArray) : Float :=
  go 0 0
where
  /-- Tail-recursive loop. -/
  go (i : Nat) (acc : Float) : Float :=
    if h : i + 1 < zs.size then
      let w := f ⟨zs[i], zs[i + 1]⟩
      go (i + 2) (acc + (w.re + w.im))
    else acc
  termination_by zs.size - i

/-- `∑ (re + im) (zs[i] / ws[i])`. -/
def sumDiv (zs : FloatArray) : Float :=
  go 0 0
where
  /-- Tail-recursive loop over consecutive pairs `z, w`. -/
  go (i : Nat) (acc : Float) : Float :=
    if h : i + 3 < zs.size then
      let q := ComplexF64.div ⟨zs[i], zs[i + 1]⟩ ⟨zs[i + 2], zs[i + 3]⟩
      go (i + 4) (acc + (q.re + q.im))
    else acc
  termination_by zs.size - i

/-- `∑ r[i]` for `i = 1 … len`. -/
def sumRange (r : StepRangeLen) : Float :=
  go 1 r.len 0
where
  /-- Tail-recursive loop. -/
  go (i : Int) : Nat → Float → Float
    | 0, acc => acc
    | k + 1, acc => go (i + 1) k (acc + r.get i)

/-- `round(x, digits = 3)`. -/
def round3 (x : Float) : Float := F64.roundDigits x 3

/-- The suite. -/
def suite : Suite := ⟨"juliabase", do
  let m := 1000
  let xs : FloatArray := ⟨(randWords m 0x5EED).map wordFloat⟩
  let pm := s!"n={m}"
  bench "show_float" (ops := m) (param := pm) fun s => totalBytes F64.showString (blackBox s xs)
  bench "show_float_compact" (ops := m) (param := pm) fun s => totalBytes F64.showCompact (blackBox s xs)
  let strs := xs.toList.toArray.map F64.showString
  bench "parse_float" (ops := m) (param := pm) fun s => sumParse (blackBox s strs)
  let n ← size 100000 1000
  let ys := randFloats n 0xB0B (-1) 1
  bench "sum_f64" (ops := n) (param := s!"n={n}") fun s => F64.sum (blackBox s ys)
  let r := 10000
  let pr := s!"n={r}"
  bench "range_collect" (ops := r) (param := pr) fun s => (range 0.0 1.0 (blackBox s r)).toFloatArray
  bench "colon_collect" (ops := r) (param := pr) fun s => (colon (blackBox s 0.1) 0.1 1000.0).toFloatArray
  let rr := range 0.0 1.0 r
  bench "range_getindex" (ops := r) (param := pr) fun s => sumRange (blackBox s rr)
  let us := randFloats m 0xF00D (-1000) 1000
  bench "round_digits" (ops := m) (param := pm) fun s => sumMap round3 (blackBox s us)
  let zs := randFloats (2 * m) 0xC0FFEE (-10) 10
  bench "complex_div" (ops := m / 2) (param := pm) fun s => sumDiv (blackBox s zs)
  bench "complex_sqrt" (ops := m) (param := pm) fun s => sumComplex ComplexF64.sqrt (blackBox s zs)
  bench "complex_exp" (ops := m) (param := pm) fun s => sumComplex ComplexF64.exp (blackBox s zs)
  bench "complex_log" (ops := m) (param := pm) fun s => sumComplex ComplexF64.log (blackBox s zs)⟩

end Bench.JuliaBase

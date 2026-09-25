import JuliaBase.FloatLit

/-!
# Julia `sum(::Vector{Float64})`, bit for bit

Julia sums a `Vector{Float64}` pairwise (`base/reduce.jl:252-277, 428-448`): fewer than 16
elements left to right; otherwise the index range is halved until the blocks have at most
1024 elements, and each block runs an `@simd` loop that LLVM vectorizes. The vectorized
accumulator layout fixes the rounding, so the port replays it.

**Platform assumption.** The layout is the one LLVM chooses on the oracle machine, Apple
aarch64 (NEON, 128-bit vectors): 2 `Float64` lanes × 4 interleaved accumulators, i.e. groups
of 8 elements. On x86-64 (AVX2: 4 lanes, or AVX-512: 8) Julia's `sum` of the same vector can
differ in the last bits, and `F64.sum` agrees with aarch64 Julia only.
-/

namespace JuliaBase

namespace F64

/-- One `mapreduce_impl` block `a[i0..i1]` (0-based, inclusive, `i1 ≥ i0 + 1`) of Julia's
`sum(::Vector{Float64})` as LLVM vectorizes it on aarch64: `v = a[i0] + a[i0+1]`, then the
`@simd` loop over the rest with **2 lanes × 4 unrolled accumulators** (the start value `v` in
lane 0 of the first, `-0.0` elsewhere), the accumulators combined vectorwise, then the two
lanes, then the scalar tail added in order. -/
def sumBlock (a : FloatArray) (i0 i1 : Nat) : Float :=
  let v := a[i0]! + a[i0 + 1]!
  let r0 := i0 + 2
  let m := i1 + 1 - r0
  let nvec := m / 8 * 8
  let s := if nvec == 0 then v else vec 0 v (-f64! 0.0) (-f64! 0.0) (-f64! 0.0) (-f64! 0.0) (-f64! 0.0) (-f64! 0.0) (-f64! 0.0) (nvec / 8)
  tail (r0 + nvec) s (m - nvec)
where
  /-- The vector loop over groups of 8. -/
  vec (j : Nat) (a00 a01 a10 a11 a20 a21 a30 a31 : Float) : Nat → Float
    | 0 =>
      let b0 := ((a00 + a10) + a20) + a30
      let b1 := ((a01 + a11) + a21) + a31
      b0 + b1
    | k + 1 =>
      let b := i0 + 2 + 8 * j
      vec (j + 1) (a00 + a[b]!) (a01 + a[b + 1]!) (a10 + a[b + 2]!) (a11 + a[b + 3]!)
        (a20 + a[b + 4]!) (a21 + a[b + 5]!) (a30 + a[b + 6]!) (a31 + a[b + 7]!) k
  /-- Scalar remainder. -/
  tail (i : Nat) (s : Float) : Nat → Float
    | 0 => s
    | k + 1 => tail (i + 1) (s + a[i]!) k

/-- Julia `sum(v::Vector{Float64})`, bit for bit on aarch64 (base/reduce.jl:252-277,
428-448): `0.0` when empty, fewer than 16 elements added left to right, otherwise halved
(`imid = i0 + (i1 - i0) >> 1`) until blocks are shorter than `pairwise_blocksize = 1024`,
each block summed by `sumBlock`. -/
def sum (a : FloatArray) : Float :=
  let n := a.size
  if n == 0 then f64! 0.0
  else if n == 1 then a[0]!
  else if n < 16 then seq 2 (a[0]! + a[1]!) (n - 2)
  else impl 0 (n - 1) n
where
  /-- Left-to-right accumulation. -/
  seq (i : Nat) (s : Float) : Nat → Float
    | 0 => s
    | k + 1 => seq (i + 1) (s + a[i]!) k
  /-- Pairwise recursion (fuelled by the length). -/
  impl (i0 i1 : Nat) : Nat → Float
    | 0 => sumBlock a i0 i1
    | fuel + 1 =>
      if i0 == i1 then a[i0]!
      else if i1 - i0 < 1024 then sumBlock a i0 i1
      else
        let imid := i0 + (i1 - i0) / 2
        impl i0 imid fuel + impl (imid + 1) i1 fuel

end F64

end JuliaBase

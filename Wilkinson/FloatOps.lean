/-!
# Julia's `sum(::Vector{Float64})`, bit for bit

`sum(::Vector{Float64})`, whose pairwise blocking and SIMD accumulator layout fix the
rounding of `simpson`'s sums. (Julia's powers, `exp`/`log` and the `TwicePrecision` range
arithmetic are in `JuliaBase`.)
-/

namespace Wilkinson

/-- One `mapreduce_impl` block of Julia's `sum(::Vector{Float64})` as LLVM
vectorises it on aarch64: `a[i0] + a[i0+1]`, then the `@simd` loop runs with
**2 lanes × 4 unrolled accumulators** (the start value in lane 0 of the first),
the accumulators are combined vectorwise, then the two lanes, then the scalar
tail is added in order. -/
def simdBlock (a : FloatArray) (i0 i1 : Nat) : Float :=
  let v := a[i0]! + a[i0 + 1]!
  let r0 := i0 + 2
  let m := i1 + 1 - r0
  let nvec := m / 8 * 8
  let s := if nvec == 0 then v else vec 0 v (-0.0) (-0.0) (-0.0) (-0.0) (-0.0) (-0.0) (-0.0) (nvec / 8)
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

/-- Julia `sum(v::Vector{Float64})`, bit for bit (base/reduce.jl:252-277, 428-448):
fewer than 16 elements are added left to right; otherwise the range is halved
until blocks are shorter than 1024, and each block is summed by `simdBlock`.
Checked against Julia 1.13 on thousands of random vectors (identical bits). -/
def juliaSum (a : FloatArray) : Float :=
  let n := a.size
  if n == 0 then 0.0
  else if n == 1 then a[0]!
  else if n < 16 then seq 2 (a[0]! + a[1]!) (n - 2)
  else impl 0 (n - 1) n
where
  /-- Left-to-right accumulation. -/
  seq (i : Nat) (s : Float) : Nat → Float
    | 0 => s
    | k + 1 => seq (i + 1) (s + a[i]!) k
  /-- Pairwise recursion. -/
  impl (i0 i1 : Nat) : Nat → Float
    | 0 => simdBlock a i0 i1
    | fuel + 1 =>
      if i0 == i1 then a[i0]!
      else if i1 - i0 < 1024 then simdBlock a i0 i1
      else
        let imid := i0 + (i1 - i0) / 2
        impl i0 imid fuel + impl (imid + 1) i1 fuel

end Wilkinson

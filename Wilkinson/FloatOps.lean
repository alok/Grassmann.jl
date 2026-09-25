/-!
# Julia's floating-point kernels, bit for bit

Wilkinson's error bounds are only as meaningful as the arithmetic that
produces them, so the port reproduces the exact kernels Julia runs (the
Dekker `TwicePrecision` arithmetic of `base/twiceprecision.jl` is
`JuliaBase.TwicePrecision`; what `JuliaBase` lacks lives here):

* `Base.Math.two_mul` (an `fma`, as Julia uses on FMA hardware);
* the compensated power-by-squaring `pow_body(::Float64, ::Integer)` from
  `base/special/pow.jl`, which is what `x^9` evaluates to in Julia (and why
  it is more accurate than repeated multiplication);
* `power_by_squaring` (`base/intfuncs.jl`) and the `Float32` power;
* `literal_pow`, the lowering of `x^k` for a literal `k`;
* `sum(::Vector{Float64})`, whose pairwise blocking and SIMD accumulator
  layout fix the rounding of `simpson`'s sums.

`two_mul` is a true `fma` (Julia calls `fma` explicitly), while `muladd`
inside `pow_body` is unfused, both as measured on the machine the goldens come
from (Apple aarch64, Julia 1.13).
-/

namespace Wilkinson

/-- Julia `Base.Math.two_mul(x, y) = (x*y, fma(x, y, -x*y))`: `hi + lo = x·y`
exactly (barring overflow). -/
@[inline] def twoMul (x y : Float) : Float × Float :=
  let xy := x * y
  (xy, Float.fma x y (-xy))

/-- Julia `muladd(x, y, z)` as compiled inside `pow_body`: LLVM leaves it
**unfused** there (`x*y + z`, two roundings). Measured against Julia 1.13 on
20000 random `(x, n)`: the unfused final `muladd` reproduces every result, the
fused one misses 22%. -/
@[inline] def muladd (x y z : Float) : Float := x * y + z

/-- Julia `^(x::Float64, n::Integer)`'s compensated power by squaring,
`pow_body(x::Float64, n::Integer)` (base/special/pow.jl): an extended-precision
square-and-multiply whose final `muladd` folds in the accumulated low parts. -/
def powBody (x : Float) (n : Int) : Float :=
  if n = 3 then x * x * x
  else if n < 0 then
    let rx := 1 / x
    if n = -2 then rx * rx
    else
      let xnlo := if x.isFinite then -(Float.fma x rx (-1.0)) * rx else -0.0
      loop rx xnlo 1.0 0.0 n.natAbs (n.natAbs + 1)
  else loop x (-0.0) 1.0 0.0 n.toNat (n.toNat + 1)
where
  /-- The squaring loop, fuelled by the exponent. -/
  loop (x xnlo y ynlo : Float) (n : Nat) : Nat → Float
    | 0 => x * y
    | fuel + 1 =>
      if n > 1 then
        let (y, ynlo) :=
          if n % 2 = 1 then
            let err := muladd y xnlo (x * ynlo)
            let (y', ynlo') := twoMul x y
            (y', ynlo' + err)
          else (y, ynlo)
        let err := x * 2 * xnlo
        let (x', xnlo') := twoMul x x
        loop x' (xnlo' + err) y ynlo (n / 2) fuel
      else
        let err := muladd y xnlo (x * ynlo)
        if x.isFinite && err.isFinite then muladd x y err else x * y

/-- Julia `x ^ n` for `x::Float64`, `n::Integer` (base/special/pow.jl:58-75).
Exponents outside `[-2^12, 3·2^13]` use Julia's `log`/`exp` path, approximated
here by the C library `pow`. -/
def powInt (x : Float) (n : Int) : Float :=
  if n = 0 then 1.0
  else if -4096 ≤ n ∧ n ≤ 24576 then powBody x n
  else Float.pow x (Float.ofInt n)

/-- Julia `power_by_squaring(x, p)` for `x::Float64`, `p ≥ 1` (base/intfuncs.jl:394):
the squaring order Julia uses, which fixes the rounding. -/
def powerBySquaring (x : Float) (p : Nat) : Float :=
  if p = 0 then 1.0
  else if p = 1 then x
  else if p = 2 then x * x
  else
    let t := trailingZeros p + 1
    let p := p >>> t
    -- `square_is_useful`: the first squaring reuses `x_squared_`
    let x := if t - 1 > 0 then squareTimes (x * x) (t - 2) else x
    outer x x p (p + 1)
where
  /-- Number of trailing zero bits. -/
  trailingZeros (p : Nat) : Nat := go p 0 64
  /-- Fuelled scan. -/
  go (p acc : Nat) : Nat → Nat
    | 0 => acc
    | fuel + 1 => if p % 2 = 0 && p != 0 then go (p / 2) (acc + 1) fuel else acc
  /-- Square `k` times. -/
  squareTimes (x : Float) : Nat → Float
    | 0 => x
    | k + 1 => squareTimes (x * x) k
  /-- `while p > 0`: square `t` times, multiply into `y`. -/
  outer (x y : Float) (p : Nat) : Nat → Float
    | 0 => y
    | fuel + 1 =>
      if p > 0 then
        let t := trailingZeros p + 1
        let x := squareTimes x t
        outer x (y * x) (p >>> t) fuel
      else y

/-- Julia `x ^ n` for `x::Float32` (base/special/pow.jl:80-88, 108-113): `-2` and
`3` are special-cased, other small exponents square in `Float64` and round once. -/
def powInt32 (x : Float32) (n : Int) : Float32 :=
  if n = 0 then 1.0
  else if n = -2 then let i := 1 / x; i * i
  else if n = 3 then x * x * x
  else if n < 0 then (powerBySquaring (1 / x.toFloat) n.natAbs).toFloat32
  else (powerBySquaring x.toFloat n.toNat).toFloat32

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

/-- Julia `literal_pow(^, x, Val(k))` for `Float64` (base/intfuncs.jl:465-475):
`x^2 = x*x`, `x^3 = x*x*x`, `x^-1 = inv(x)`, otherwise `x^k`. -/
def literalPow (x : Float) (k : Int) : Float :=
  match k with
  | 0 => 1.0
  | 1 => x
  | 2 => x * x
  | 3 => x * x * x
  | -1 => 1 / x
  | _ => powInt x k

/-- Julia `literal_pow` for `Float32`. -/
def literalPow32 (x : Float32) (k : Int) : Float32 :=
  match k with
  | 0 => 1.0
  | 1 => x
  | 2 => x * x
  | 3 => x * x * x
  | -1 => 1 / x
  | _ => powInt32 x k

end Wilkinson

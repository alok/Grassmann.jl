import JuliaBase.IEEE

/-!
# `BigFloat p`: MPFR-style binary floating point

Julia's `BigFloat` (MPFR, default precision 256) is Wilkinson's reference
arithmetic: the "exact" curve of a `PolynomialComparison` is an evaluation in
`BigFloat`. The port implements the same model directly on Lean's GMP-backed
`Nat`: a value is `±m · 2^e` with an exactly `p`-bit mantissa, and every
operation computes the exact result and rounds once, to nearest with ties to
even, exactly as MPFR does. The precision is a **type index**, so
`BigFloat 256` and `BigFloat 53` cannot be mixed by accident, at no runtime
cost. The exponent range is unbounded (MPFR's is ±2^62), so nothing overflows.

`log` is computed to `p + 64` fixed-point bits (atanh series) before rounding:
absolutely accurate to far below an ulp of every `Float64` Wilkinson later
derives from it, though not guaranteed correctly rounded at 256 bits when
the result is tiny.
-/

namespace Wilkinson

open JuliaBase

/-- `±m · 2^e` with `2^(p-1) ≤ m < 2^p` (Julia `BigFloat` with `precision = p`). -/
inductive BigFloat (p : Nat) where
  /-- Signed zero. -/
  | zero (neg : Bool)
  /-- Finite nonzero value `±m · 2^e`. -/
  | finite (neg : Bool) (m : Nat) (e : Int)
  /-- Signed infinity. -/
  | inf (neg : Bool)
  /-- Not a number. -/
  | nan
  deriving Inhabited, BEq, Repr, DecidableEq

namespace BigFloat

variable {p : Nat}

/-- Bit length of a natural (`0` for `0`). -/
@[inline] def bitLength (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-- Round the value `±(m + δ) · 2^e` (`0 ≤ δ < 1`, `sticky ↔ δ > 0`) to `p` bits,
nearest-even. Callers with an inexact tail supply at least `p + 2` bits of `m`;
with `≤ p` bits the value `m · 2^e` is represented as is. -/
def round (p : Nat) (neg : Bool) (m : Nat) (e : Int) (sticky : Bool := false) : BigFloat p :=
  if m = 0 then .zero neg else
  let b := bitLength m
  if b ≤ p then
    .finite neg (m <<< (p - b)) (e - (p - b : Nat))
  else
    let s := b - p
    let q := m >>> s
    let rem := m % (2 ^ s)
    let half := 2 ^ (s - 1)
    let up := rem > half || (rem == half && (sticky || q % 2 == 1))
    let q := if up then q + 1 else q
    if q == 2 ^ p then .finite neg (2 ^ (p - 1)) (e + s + 1) else .finite neg q (e + s)

/-- Exact conversion from a `Float` (every `Float64` is representable when `p ≥ 53`). -/
def ofFloat (p : Nat) (x : Float) : BigFloat p :=
  if x.isNaN then .nan
  else if x.isInf then .inf (x < 0)
  else match IEEEFloat.decode x with
    | none => .zero (IEEEFloat.signBit x)
    | some (s, m, e) => round p s m e

/-- Exact conversion from a `Float32`. -/
def ofFloat32 (p : Nat) (x : Float32) : BigFloat p := ofFloat p x.toFloat

/-- Conversion from an integer (rounded when it needs more than `p` bits). -/
def ofInt (p : Nat) (n : Int) : BigFloat p := round p (n < 0) n.natAbs 0

/-- Round a rational: `num / den` with enough quotient bits and a sticky bit. -/
def ofRat (p : Nat) (q : Rat) : BigFloat p :=
  if q.num = 0 then .zero false else
  let n := q.num.natAbs
  let d := q.den
  -- scale so the quotient has at least p + 2 bits
  let k := p + 2 + bitLength d - bitLength n + 1
  let num := n <<< k
  round p (q.num < 0) (num / d) (-(k : Int)) (num % d != 0)

/-- Negation. -/
def neg : BigFloat p → BigFloat p
  | .zero s => .zero (!s)
  | .finite s m e => .finite (!s) m e
  | .inf s => .inf (!s)
  | .nan => .nan

/-- Absolute value. -/
def abs : BigFloat p → BigFloat p
  | .zero _ => .zero false
  | .finite _ m e => .finite false m e
  | .inf _ => .inf false
  | .nan => .nan

/-- Exact signed integer mantissa at a common exponent. -/
@[inline] def signedAt (neg : Bool) (m : Nat) (shift : Nat) : Int :=
  let v : Int := (m <<< shift : Nat)
  if neg then -v else v

/-- Correctly rounded addition. -/
def add : BigFloat p → BigFloat p → BigFloat p
  | .nan, _ | _, .nan => .nan
  | .inf a, .inf b => if a == b then .inf a else .nan
  | .inf a, _ => .inf a
  | _, .inf b => .inf b
  | .zero a, .zero b => .zero (a && b)
  | .zero _, y => y
  | x, .zero _ => x
  | .finite sa ma ea, .finite sb mb eb =>
    let e := min ea eb
    let s := signedAt sa ma (ea - e).toNat + signedAt sb mb (eb - e).toNat
    if s = 0 then .zero false else round p (s < 0) s.natAbs e

/-- Correctly rounded subtraction. -/
def sub (x y : BigFloat p) : BigFloat p := add x (neg y)

/-- Correctly rounded multiplication. -/
def mul : BigFloat p → BigFloat p → BigFloat p
  | .nan, _ | _, .nan => .nan
  | .inf _, .zero _ | .zero _, .inf _ => .nan
  | .inf a, .inf b => .inf (a != b)
  | .inf a, .finite b .. | .finite b .., .inf a => .inf (a != b)
  | .zero a, .zero b => .zero (a != b)
  | .zero a, .finite b .. | .finite b .., .zero a => .zero (a != b)
  | .finite sa ma ea, .finite sb mb eb => round p (sa != sb) (ma * mb) (ea + eb)

/-- Correctly rounded division. -/
def div : BigFloat p → BigFloat p → BigFloat p
  | .nan, _ | _, .nan => .nan
  | .inf _, .inf _ => .nan
  | .zero _, .zero _ => .nan
  | .inf a, .zero b | .inf a, .finite b .. => .inf (a != b)
  | .zero a, .inf b | .finite a .., .inf b => .zero (a != b)
  | .zero a, .finite b .. => .zero (a != b)
  | .finite a .., .zero b => .inf (a != b)
  | .finite sa ma ea, .finite sb mb eb =>
    let k := p + 2 + bitLength mb
    let num := ma <<< k
    round p (sa != sb) (num / mb) (ea - eb - k) (num % mb != 0)

/-- Julia `x ^ n` for `x::BigFloat`, `n::Integer` (MPFR `mpfr_pow_si`, correctly
rounded): the exact power, rounded once. -/
def powInt (x : BigFloat p) (n : Int) : BigFloat p :=
  if n = 0 then round p false 1 0 else
  match x with
  | .nan => .nan
  | .zero s => if n > 0 then .zero (s && n % 2 == 1) else .inf (s && n % 2 == 1)
  | .inf s => if n > 0 then .inf (s && n % 2 == 1) else .zero (s && n % 2 == 1)
  | .finite s m e =>
    let neg := s && n % 2 == 1
    if n > 0 then round p neg (m ^ n.toNat) (e * n)
    else
      -- `2^(-e|n|) / m^|n|`, one rounding (enough quotient bits plus a sticky bit)
      let d := m ^ n.natAbs
      let k := p + 2 + bitLength d
      let num := 1 <<< k
      round p neg (num / d) (-(e * n.natAbs) - k) (num % d != 0)

/-- Julia `Float64(x::BigFloat)` (round to nearest). -/
def toFloat : BigFloat p → Float
  | .zero s => if s then -0.0 else 0.0
  | .finite s m e => IEEEFloat.ofDyadic Float s m e
  | .inf s => if s then -1.0 / 0.0 else 1.0 / 0.0
  | .nan => 0.0 / 0.0

/-- Julia `Float32(x::BigFloat)`. -/
def toFloat32 : BigFloat p → Float32
  | .zero s => if s then -0.0 else 0.0
  | .finite s m e => IEEEFloat.ofDyadic Float32 s m e
  | .inf s => if s then -1.0 / 0.0 else 1.0 / 0.0
  | .nan => 0.0 / 0.0

/-- Exact rational value of a finite `BigFloat`. -/
def toRat? : BigFloat p → Option Rat
  | .zero _ => some 0
  | .finite s m e =>
    let q : Rat := if e ≥ 0 then ((m * 2 ^ e.toNat : Nat) : Rat) else (m : Rat) / ((2 ^ (-e).toNat : Nat) : Rat)
    some (if s then -q else q)
  | _ => none

/-- Sign test. -/
def isNeg : BigFloat p → Bool
  | .zero s | .finite s .. | .inf s => s
  | .nan => false

/-- `atanh(z)`-series sum `Σ z^(2k+1)/(2k+1)` in `W`-bit fixed point, for
`z = Z / 2^W < 1/3`. -/
def atanhFixed (W Z : Nat) : Nat :=
  go Z 0 0 (W + 4)
where
  /-- Terms until they vanish. -/
  go (zp acc k : Nat) : Nat → Nat
    | 0 => acc
    | fuel + 1 =>
      if zp = 0 then acc
      else go ((((zp * Z) >>> W) * Z) >>> W) (acc + zp / (2 * k + 1)) (k + 1) fuel

/-- `ln 2` in `W`-bit fixed point, via `2 atanh(1/3)`. -/
def ln2Fixed (W : Nat) : Nat := 2 * atanhFixed W ((1 <<< W) / 3)

/-- `ln 2` at the working precision of `BigFloat 256`, computed once. -/
def ln2Fixed320 : Nat := ln2Fixed 320

/-- Julia `log(x::BigFloat)`: `log x = 2 atanh((t-1)/(t+1)) + (e + p - 1) ln 2`
with `x = t · 2^(e+p-1)`, `t ∈ [1, 2)`, evaluated in `p + 64`-bit fixed point
and rounded to `p` bits. `log 0 = -Inf`, `log(x < 0) = NaN`. -/
def log (x : BigFloat p) : BigFloat p :=
  match x with
  | .nan => .nan
  | .inf true => .nan
  | .inf false => .inf false
  | .zero _ => .inf true
  | .finite true .. => .nan
  | .finite false m e =>
    let W := p + 64
    let h := 2 ^ (p - 1)
    let Z := ((m - h) <<< W) / (m + h)
    let lnT : Int := 2 * atanhFixed W Z
    let l2 : Int := if W == 320 then ln2Fixed320 else ln2Fixed W
    let L : Int := lnT + (e + (p - 1 : Nat)) * l2
    if L = 0 then .zero false else round p (L < 0) L.natAbs (-(W : Int)) true

instance : Add (BigFloat p) := ⟨add⟩
instance : Sub (BigFloat p) := ⟨sub⟩
instance : Mul (BigFloat p) := ⟨mul⟩
instance : Div (BigFloat p) := ⟨div⟩
instance : Neg (BigFloat p) := ⟨neg⟩

end BigFloat

/-- Julia's default `BigFloat` (`precision(BigFloat) == 256`). -/
abbrev Big := BigFloat 256

end Wilkinson

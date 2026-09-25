/-
Ryu shortest round-trip digits, ported from Julia's `base/ryu/shortest.jl`
(`reduce_shortest`) and `base/ryu/utils.jl` (tables and `mulshift`).

`reduceShortest64 x` returns `(b, e10)` with `|x| = b · 10^e10` where `b` has the fewest
decimal digits that still parse back to `x` (Julia's tie-breaking rules included). With
`maxsignif := some 999_999` it reproduces Julia's `:compact => true` reduction to at most
six significant digits.

The port keeps Julia's integer widths: `UInt64` for Float64 (the 128-bit products are
split into two `UInt64` halves, as the C Ryu does) and `UInt32` for Float32. It also
keeps one Julia quirk: in the `e2 ≥ 0` branch, `((v % UInt32) - 5 * div(v, 5)) == 0`
is evaluated in wrapping `UInt64` arithmetic, which is never zero for normal Float64
inputs (C Ryu computes `v mod 5` there). Matching it is required for bit-exactness.

The power-of-5 tables are closed terms computed from `Nat` arithmetic when the module
is initialized, exactly as Julia computes them from `BigInt` (utils.jl:228-272).
-/

namespace JuliaBase.Ryu

/-- Julia `Ryu.log10pow2(e)` = `⌊log10(2^e)⌋` for `0 ≤ e < 1651` (utils.jl:35). -/
@[inline] def log10pow2 (e : Nat) : Nat := (e * 78913) >>> 18

/-- Julia `Ryu.log10pow5(e)` = `⌊log10(5^e)⌋` for `0 ≤ e < 2621` (utils.jl:43). -/
@[inline] def log10pow5 (e : Nat) : Nat := (e * 732923) >>> 20

/-- Julia `Ryu.pow5bits(e)` = `e == 0 ? 1 : ⌈log2(5^e)⌉` (utils.jl:50). -/
@[inline] def pow5bits (e : Nat) : Nat := ((e * 1217359) >>> 19) + 1

/-- Julia `Ryu.decimallength(v)` (utils.jl:95-113): number of decimal digits of `v ≥ 1`
(and `1` for `v = 0`). -/
def decimalLength (v : UInt64) : Nat :=
  if v ≥ 10000000000000000 then 17
  else if v ≥ 1000000000000000 then 16
  else if v ≥ 100000000000000 then 15
  else if v ≥ 10000000000000 then 14
  else if v ≥ 1000000000000 then 13
  else if v ≥ 100000000000 then 12
  else if v ≥ 10000000000 then 11
  else if v ≥ 1000000000 then 10
  else if v ≥ 100000000 then 9
  else if v ≥ 10000000 then 8
  else if v ≥ 1000000 then 7
  else if v ≥ 100000 then 6
  else if v ≥ 10000 then 5
  else if v ≥ 1000 then 4
  else if v ≥ 100 then 3
  else if v ≥ 10 then 2
  else 1

/-! ## Tables (utils.jl:228-272) -/

/-- Julia `pow5invsplit(T, i)` = `⌊2^(⌊log2 5^i⌋ + bitcount) / 5^i⌋ + 1`. -/
def pow5InvSplitNat (bitcount i : Nat) : Nat :=
  let p := 5 ^ i
  (1 <<< (Nat.log2 p + bitcount)) / p + 1

/-- Julia `pow5split(T, i)` = `5^i >> (ndigits(5^i, base=2) - bitcount)`, where a negative
shift is a left shift. -/
def pow5SplitNat (bitcount i : Nat) : Nat :=
  let p := 5 ^ i
  let nd := Nat.log2 p + 1
  if nd ≥ bitcount then p >>> (nd - bitcount) else p <<< (bitcount - nd)

/-- `n` table entries of a 128-bit table, stored as interleaved `(lo, hi)` `UInt64` halves. -/
def table128 (f : Nat → Nat) (n : Nat) : Array UInt64 := Id.run do
  let mut out : Array UInt64 := Array.mkEmpty (2 * n)
  for i in [0:n] do
    let v := f i
    out := (out.push v.toUInt64).push (v >>> 64).toUInt64
  return out

/-- `n` table entries of a 64-bit table. -/
def table64 (f : Nat → Nat) (n : Nat) : Array UInt64 := Id.run do
  let mut out : Array UInt64 := Array.mkEmpty n
  for i in [0:n] do
    out := out.push (f i).toUInt64
  return out

/-- `pow5invsplit_table_Float64`: `i ∈ [0, 291]` (`log10pow2(1023 - 53 - 1) = 291`),
`pow5_inv_bitcount(Float64) = 122`. -/
def pow5InvSplit64 : Array UInt64 := table128 (pow5InvSplitNat 122) 292

/-- `pow5split_table_Float64`: `i ∈ [0, 325]`, `pow5_bitcount(Float64) = 121`. -/
def pow5Split64 : Array UInt64 := table128 (pow5SplitNat 121) 326

/-- `pow5invsplit_table_Float32`: `i ∈ [0, 30]`, `pow5_inv_bitcount(Float32) = 59`. -/
def pow5InvSplit32 : Array UInt64 := table64 (pow5InvSplitNat 59) 31

/-- `pow5split_table_Float32`: `i ∈ [0, 47]`, `pow5_bitcount(Float32) = 61`. -/
def pow5Split32 : Array UInt64 := table64 (pow5SplitNat 61) 48

/-! ## Wide multiplication -/

/-- High 64 bits of the 128-bit product `a * b` (Julia `umul256` style split, utils.jl:195). -/
@[inline] def umulHi (a b : UInt64) : UInt64 :=
  let aLo := a &&& 0xFFFFFFFF
  let aHi := a >>> 32
  let bLo := b &&& 0xFFFFFFFF
  let bHi := b >>> 32
  let b00 := aLo * bLo
  let b01 := aLo * bHi
  let b10 := aHi * bLo
  let b11 := aHi * bHi
  let mid1 := b10 + (b00 >>> 32)
  let mid2 := b01 + (mid1 &&& 0xFFFFFFFF)
  b11 + (mid1 >>> 32) + (mid2 >>> 32)

/-- Julia `Ryu.mulshift(m::UInt64, mul::UInt128, j)` (utils.jl:62) =
`((m * mul) >> j) % UInt64` for `j ≥ 64`, with `mul = lo + hi·2^64`. -/
@[inline] def mulShift64 (m lo hi : UInt64) (j : Nat) : UInt64 :=
  let h0 := umulHi m lo
  let pLo := m * hi
  let pHi := umulHi m hi
  let sLo := pLo + h0
  let sHi := pHi + (if sLo < pLo then 1 else 0)
  let s := j - 64
  if s == 0 then sLo
  else if s < 64 then (sHi <<< (64 - s).toUInt64) ||| (sLo >>> s.toUInt64)
  else if s < 128 then sHi >>> (s - 64).toUInt64
  else 0

/-- `mulshift` against entry `i` of a Float64 table. -/
@[inline] def mulShiftTab64 (tab : Array UInt64) (m : UInt64) (i j : Nat) : UInt64 :=
  mulShift64 m tab[2 * i]! tab[2 * i + 1]! j

/-- Julia `Ryu.mulshift(m::UInt32, mul::UInt64, j)` = `((m * mul) >> j) % UInt32`, `j ≥ 32`. -/
@[inline] def mulShift32 (m : UInt64) (mul : UInt64) (j : Nat) : UInt64 :=
  let t := ((m * (mul &&& 0xFFFFFFFF)) >>> 32) + m * (mul >>> 32)
  let s := j - 32
  (if s < 64 then t >>> s.toUInt64 else 0) &&& 0xFFFFFFFF

/-! ## Digit reduction (shortest.jl:120-247) -/

/-- The decimal `digits · 10^exp10`. -/
structure Decimal where
  /-- the significand digits, as an integer without trailing zeros (except `0` itself) -/
  digits : UInt64
  /-- the decimal exponent -/
  exp10 : Int
  deriving Repr, BEq, Inhabited

@[inline] private def b2u (b : Bool) : UInt64 := if b then 1 else 0

/-- "remove trailing zeros" loop (shortest.jl:219-229, 237-246). -/
def stripZeros : Nat → UInt64 → Int → Decimal
  | 0, b, e => ⟨b, e⟩
  | fuel + 1, b, e => if b % 10 != 0 then ⟨b, e⟩ else stripZeros fuel (b / 10) (e + 1)

/-- "reduce to max significant digits" loop (shortest.jl:204-229): drop digits while
`b > maxsignif`, tracking round-half-even through `ballZero`, then round and strip. -/
def maxSignifLoop (maxs : UInt64) : Nat → UInt64 → Int → Bool → Bool → Decimal
  | 0, b, e, roundup, _ => stripZeros 24 (b + b2u roundup) e
  | fuel + 1, b, e, roundup, ballZero =>
    if b ≤ maxs then stripZeros 24 (b + b2u roundup) e
    else
      let bd := b / 10
      let bm := b % 10
      let roundup := if ballZero && bd % 2 == 0 then bm > 5 else bm ≥ 5
      maxSignifLoop maxs fuel bd (e + 1) roundup (ballZero && bm == 0)

/-- Tail of the general path (shortest.jl:204-233): optional max-significant-digit
reduction, then the final rounding. -/
@[inline] def finish (maxsignif : Option UInt64) (b : UInt64) (e10 : Int) (roundup ballZero : Bool) :
    Decimal :=
  match maxsignif with
  | some maxs => if b > maxs then maxSignifLoop maxs 24 b e10 roundup ballZero else ⟨b + b2u roundup, e10⟩
  | none => ⟨b + b2u roundup, e10⟩

/-- Specialized common case (shortest.jl:170-202): no exact trailing zeros to track. -/
def fastLoop (maxsignif : Option UInt64) : Nat → UInt64 → UInt64 → UInt64 → Int → Bool → Decimal
  | 0, a, b, _, e10, roundup => finish maxsignif b e10 (b == a || roundup) false
  | fuel + 1, a, b, c, e10, roundup =>
    let cd := c / 10
    let ad := a / 10
    if cd ≤ ad then finish maxsignif b e10 (b == a || roundup) false
    else fastLoop maxsignif fuel ad (b / 10) cd (e10 + 1) (b % 10 ≥ 5)

/-- Entry of the specialized case: one step of 100, then single digits. -/
@[inline] def fastPath (maxsignif : Option UInt64) (a b c : UInt64) (e10 : Int) (bLast : UInt64) :
    Decimal :=
  let roundup := bLast ≥ 5
  let cd100 := c / 100
  let ad100 := a / 100
  if cd100 > ad100 then
    fastLoop maxsignif 24 ad100 (b / 100) cd100 (e10 + 2) (b % 100 ≥ 50)
  else fastLoop maxsignif 24 a b c e10 roundup

/-- After the slow loops: the round-half-even fixup and the rounding decision
(shortest.jl:163-168). -/
@[inline] def slowFinish (maxsignif : Option UInt64) (mfEven : Bool) (a b : UInt64) (e10 : Int)
    (aAll bAll : Bool) (bLast : UInt64) : Decimal :=
  let bLast := if bAll && bLast == 5 && b % 2 == 0 then 4 else bLast
  let roundup := (b == a && (!mfEven || !aAll)) || bLast ≥ 5
  finish maxsignif b e10 roundup bAll

/-- Second slow loop (shortest.jl:143-162): while `a`'s last digit is zero (or `b` is still at
least `maxsignif`), drop digits. -/
def slowLoopA (maxsignif : Option UInt64) (mfEven : Bool) :
    Nat → UInt64 → UInt64 → UInt64 → Int → Bool → Bool → UInt64 → Decimal
  | 0, a, b, _, e10, aAll, bAll, bLast => slowFinish maxsignif mfEven a b e10 aAll bAll bLast
  | fuel + 1, a, b, c, e10, aAll, bAll, bLast =>
    let ad := a / 10
    let am := a % 10
    let stop := am != 0 && (match maxsignif with | none => true | some m => b < m)
    if stop then slowFinish maxsignif mfEven a b e10 aAll bAll bLast
    else
      slowLoopA maxsignif mfEven fuel ad (b / 10) (c / 10) (e10 + 1) aAll (bAll && bLast == 0) (b % 10)

/-- First slow loop (shortest.jl:125-142): exact trailing-zero tracking while `c/10 > a/10`. -/
def slowLoop (maxsignif : Option UInt64) (mfEven : Bool) :
    Nat → UInt64 → UInt64 → UInt64 → Int → Bool → Bool → UInt64 → Decimal
  | 0, a, b, c, e10, aAll, bAll, bLast =>
    if aAll then slowLoopA maxsignif mfEven 24 a b c e10 aAll bAll bLast
    else slowFinish maxsignif mfEven a b e10 aAll bAll bLast
  | fuel + 1, a, b, c, e10, aAll, bAll, bLast =>
    let cd := c / 10
    let ad := a / 10
    if cd ≤ ad then
      if aAll then slowLoopA maxsignif mfEven 24 a b c e10 aAll bAll bLast
      else slowFinish maxsignif mfEven a b e10 aAll bAll bLast
    else
      slowLoop maxsignif mfEven fuel ad (b / 10) cd (e10 + 1) (aAll && a % 10 == 0)
        (bAll && bLast == 0) (b % 10)

/-- Step 4 dispatch (shortest.jl:120): slow path when an exact trailing-zero flag is set. -/
@[inline] def step4 (maxsignif : Option UInt64) (mfEven : Bool) (a b c : UInt64) (e10 : Int)
    (aAll bAll : Bool) (bLast : UInt64) : Decimal :=
  if aAll || bAll then slowLoop maxsignif mfEven 24 a b c e10 aAll bAll bLast
  else fastPath maxsignif a b c e10 bLast

/-- Integer shortcut (shortest.jl:234-257): `x` is an integer below `2^53`. -/
@[inline] def integerPath (maxsignif : Option UInt64) (b : UInt64) : Decimal :=
  match maxsignif with
  | some maxs => if b > maxs then maxSignifLoop maxs 24 b 0 false true else stripZeros 24 b 0
  | none => stripZeros 24 b 0

/-- Julia `Ryu.reduce_shortest(x::Float64, maxsignif)` (shortest.jl:8-259) for finite,
nonzero `x`: `|x| = digits · 10^exp10` with the shortest round-trip `digits`. With
`maxsignif = some 999_999`, the Julia `compact` variant (at most 6 significant digits). -/
def reduceShortest64 (x : Float) (maxsignif : Option UInt64 := none) : Decimal :=
  let uf := x.toBits
  let m := uf &&& 0x000FFFFFFFFFFFFF
  let e := ((uf >>> 52) &&& 0x7FF).toNat
  let mf := 0x0010000000000000 ||| m
  let ef : Int := (e : Int) - 1075
  let isInt := ef ≤ 0 && ef ≥ -52 && (mf &&& ((1 <<< (-ef).toNat.toUInt64) - 1)) == 0
  if ef > 0 || ef < -52 || !isInt then
    -- subnormal fix-up
    let (mf, ef) := if e == 0 then (m, (-1074 : Int)) else (mf, ef)
    let e2 := ef - 2
    let mfEven := mf % 2 == 0
    let v := 4 * mf
    let w := v + 2
    let uShiftHalf := m == 0 && e > 1
    let u := v - 2 + b2u uShiftHalf
    if e2 ≥ 0 then
      let e2n := e2.toNat
      let q := log10pow2 e2n - (if e2n > 3 then 1 else 0)
      let k := 122 + pow5bits q - 1
      let i := q + k - e2n
      let a := mulShiftTab64 pow5InvSplit64 u q i
      let b := mulShiftTab64 pow5InvSplit64 v q i
      let c := mulShiftTab64 pow5InvSplit64 w q i
      if q ≤ 21 then
        let p5 : UInt64 := 5 ^ q
        -- Julia: `(v % UInt32) - 5 * div(v, 5)` promotes to wrapping UInt64 arithmetic
        if (v &&& 0xFFFFFFFF) - 5 * (v / 5) == 0 then
          step4 maxsignif mfEven a b c q false (v % p5 == 0) 0
        else if mfEven then
          step4 maxsignif mfEven a b c q (u % p5 == 0) false 0
        else
          step4 maxsignif mfEven a b (c - b2u (w % p5 == 0)) q false false 0
      else step4 maxsignif mfEven a b c q false false 0
    else
      let ne2 := (-e2).toNat
      let q := log10pow5 ne2 - (if ne2 > 1 then 1 else 0)
      let e10 : Int := (q : Int) + e2
      let i := ne2 - q
      let k : Int := (pow5bits i : Int) - 121
      let j := ((q : Int) - k).toNat
      let a := mulShiftTab64 pow5Split64 u i j
      let b := mulShiftTab64 pow5Split64 v i j
      let c := mulShiftTab64 pow5Split64 w i j
      if q ≤ 1 then
        if mfEven then step4 maxsignif mfEven a b c e10 (!uShiftHalf) true 0
        else step4 maxsignif mfEven a b (c - 1) e10 false true 0
      else if q < 63 then
        step4 maxsignif mfEven a b c e10 false (v &&& ((1 <<< q.toUInt64) - 1) == 0) 0
      else step4 maxsignif mfEven a b c e10 false false 0
  else
    integerPath maxsignif (mf >>> (-ef).toNat.toUInt64)

/-- Julia `Ryu.reduce_shortest(x::Float32, maxsignif)` (shortest.jl:8-259, `T == Float32`
branches) for finite, nonzero `x`. Values are held in `UInt64` but every Julia `UInt32`
operation that could wrap is truncated explicitly. -/
def reduceShortest32 (x : Float32) (maxsignif : Option UInt64 := none) : Decimal :=
  let uf := x.toBits.toUInt64
  let m := uf &&& 0x007FFFFF
  let e := ((uf >>> 23) &&& 0xFF).toNat
  let mf := 0x00800000 ||| m
  let ef : Int := (e : Int) - 150
  let isInt := ef ≤ 0 && ef ≥ -23 && (mf &&& ((1 <<< (-ef).toNat.toUInt64) - 1)) == 0
  if ef > 0 || ef < -23 || !isInt then
    let (mf, ef) := if e == 0 then (m, (-149 : Int)) else (mf, ef)
    let e2 := ef - 2
    let mfEven := mf % 2 == 0
    let v := 4 * mf
    let w := v + 2
    let uShiftHalf := m == 0 && e > 1
    let u := v - 2 + b2u uShiftHalf
    let u32 (t : UInt64) : UInt64 := t &&& 0xFFFFFFFF
    if e2 ≥ 0 then
      let e2n := e2.toNat
      let q := log10pow2 e2n
      let k := 59 + pow5bits q - 1
      let i := q + k - e2n
      let mul := pow5InvSplit32[q]!
      let a := mulShift32 u mul i
      let b := mulShift32 v mul i
      let c := mulShift32 w mul i
      let bLast : UInt64 :=
        if q != 0 && u32 (c - 1) / 10 ≤ a / 10 then
          let l := 59 + pow5bits (q - 1) - 1
          mulShift32 v pow5InvSplit32[q - 1]! (q - 1 + l - e2n) % 10
        else 0
      if q ≤ 9 then
        let p5 : UInt64 := 5 ^ q
        if v % 5 == 0 then
          step4 maxsignif mfEven a b c q false (v % p5 == 0) bLast
        else if mfEven then
          step4 maxsignif mfEven a b c q (u % p5 == 0) false bLast
        else
          step4 maxsignif mfEven a b (u32 (c - b2u (w % p5 == 0))) q false false bLast
      else step4 maxsignif mfEven a b c q false false bLast
    else
      let ne2 := (-e2).toNat
      let q := log10pow5 ne2
      let e10 : Int := (q : Int) + e2
      let i := ne2 - q
      let k : Int := (pow5bits i : Int) - 61
      let j := ((q : Int) - k).toNat
      let mul := pow5Split32[i]!
      let a := mulShift32 u mul j
      let b := mulShift32 v mul j
      let c := mulShift32 w mul j
      let bLast : UInt64 :=
        if q != 0 && u32 (c - 1) / 10 ≤ a / 10 then
          let j' := ((q : Int) - 1 - ((pow5bits (i + 1) : Int) - 61)).toNat
          mulShift32 v pow5Split32[i + 1]! j' % 10
        else 0
      if q ≤ 1 then
        if mfEven then step4 maxsignif mfEven a b c e10 (!uShiftHalf) true bLast
        else step4 maxsignif mfEven a b (u32 (c - 1)) e10 false true bLast
      else if q < 31 then
        step4 maxsignif mfEven a b c e10 false (v &&& ((1 <<< (q - 1).toUInt64) - 1) == 0) bLast
      else step4 maxsignif mfEven a b c e10 false false bLast
  else
    integerPath maxsignif (mf >>> (-ef).toNat.toUInt64)

end JuliaBase.Ryu

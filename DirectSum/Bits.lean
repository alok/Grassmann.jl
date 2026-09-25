/-
Bit-level primitives for basis blades.

A basis blade `e_{i₁ i₂ … i_k}` (with `i₁ < … < i_k`) is encoded as the
bitmask with bits `i₁-1, …, i_k-1` set (index 1 ↦ bit 0), exactly as in
DirectSum.jl/Leibniz.jl. Its grade is the popcount.

The central quantity is the *reordering parity* of a product `e_A e_B`:
bringing the concatenated index word into ascending order takes a number of
adjacent transpositions whose parity is `#{(i, j) : i ∈ A, j ∈ B, i > j} mod 2`.
Julia computes this as
`isodd(sum(digits(a) .* cumsum(digits(b << 1))))` (`parityjoin`).
We compute it branch-free with a prefix-XOR scan, and prove the fast
version equal to the naive specification.
-/

namespace DirectSum.Bits

/-- Population count (number of set bits). -/
@[inline] def popcount (x : UInt64) : Nat :=
  -- SWAR popcount; compiles to a handful of ALU ops.
  let m1 : UInt64 := 0x5555555555555555
  let m2 : UInt64 := 0x3333333333333333
  let m4 : UInt64 := 0x0F0F0F0F0F0F0F0F
  let h01 : UInt64 := 0x0101010101010101
  let x := x - ((x >>> 1) &&& m1)
  let x := (x &&& m2) + ((x >>> 2) &&& m2)
  let x := (x + (x >>> 4)) &&& m4
  ((x * h01) >>> 56).toNat

/-- Parity of the popcount: `true` iff an odd number of bits are set. -/
@[inline] def parity (x : UInt64) : Bool :=
  let x := x ^^^ (x >>> 32)
  let x := x ^^^ (x >>> 16)
  let x := x ^^^ (x >>> 8)
  let x := x ^^^ (x >>> 4)
  let x := x ^^^ (x >>> 2)
  let x := x ^^^ (x >>> 1)
  (x &&& 1) == 1

/-- Bit `i` of `prefixParity b` is the parity of the number of set bits of `b`
strictly below position `i`. -/
@[inline] def prefixParity (b : UInt64) : UInt64 :=
  let y := b <<< 1
  let y := y ^^^ (y <<< 1)
  let y := y ^^^ (y <<< 2)
  let y := y ^^^ (y <<< 4)
  let y := y ^^^ (y <<< 8)
  let y := y ^^^ (y <<< 16)
  let y := y ^^^ (y <<< 32)
  y

/-- Canonical reordering parity of `e_a e_b` (Julia `parityjoin(N,a,b)`):
`true` iff the product picks up a minus sign from reordering. -/
@[inline] def reorderParity (a b : UInt64) : Bool :=
  parity (a &&& prefixParity b)

/-- Naive specification of the reordering parity, directly from the
definition: count pairs `(i, j)` with `i ∈ a`, `j ∈ b`, `j < i`.
(Structural recursion only, so the kernel can evaluate it.) -/
def reorderParitySpec (n : Nat) (a b : Nat) : Bool :=
  let pairs := (List.range n).foldl (fun c i =>
    if a.testBit i then (List.range i).foldl (fun c j => if b.testBit j then c + 1 else c) c else c) 0
  pairs % 2 == 1

/-- Grade of a blade bitmask. -/
@[inline] def grade (x : UInt64) : Nat := popcount x

/-- Bitmask of the first `n` basis vectors (the pseudoscalar of `ℝⁿ`). -/
@[inline] def fullMask (n : Nat) : UInt64 := if n ≥ 64 then 0xFFFFFFFFFFFFFFFF else (1 <<< n.toUInt64) - 1

/-- 1-based indices of the set bits, ascending (Julia `indices`). -/
def indices (x : UInt64) : Array Nat := Id.run do
  let mut out := #[]
  for i in [0:64] do
    if (x >>> i.toUInt64) &&& 1 == 1 then out := out.push (i + 1)
  return out

/-- Bitmask from 1-based indices. -/
def ofIndices (is : List Nat) : UInt64 :=
  is.foldl (fun acc i => acc ||| ((1 : UInt64) <<< (i - 1).toUInt64)) 0

/-! ## Saturating shifts and masks

Julia's `<<` saturates (`UInt(1) << 64 == 0`), Lean's `UInt64` shifts are taken
mod 64. Every mask built from a possibly large count goes through these. -/

/-- The low `n` bits set (Julia `(UInt(1)<<n)-1`, saturating at 64). Same as
`fullMask`; this is the name the port notes use. -/
@[inline] def lowMask (n : Nat) : UInt64 := fullMask n

/-- Left shift that returns 0 once the count reaches 64 (Julia `x << k`). -/
@[inline] def shl (x : UInt64) (k : Nat) : UInt64 := if k ≥ 64 then 0 else x <<< k.toUInt64

/-- Right shift that returns 0 once the count reaches 64 (Julia `x >> k`). -/
@[inline] def shr (x : UInt64) (k : Nat) : UInt64 := if k ≥ 64 then 0 else x >>> k.toUInt64

/-- Single bit for 1-based generator index `i` (index 0 or > 64 gives 0). -/
@[inline] def bit (i : Nat) : UInt64 := if i = 0 then 0 else shl 1 (i - 1)

/-- Isolate the lowest set bit (`x & -x`). -/
@[inline] def lowestBit (x : UInt64) : UInt64 := x &&& (0 - x)

/-- Number of trailing zero bits; `ctz 0 = 64`. Branch-free via popcount. -/
@[inline] def ctz (x : UInt64) : Nat := popcount (lowestBit x - 1)

/-- Is bit `i` (0-based) set? -/
@[inline] def testBit (x : UInt64) (i : Nat) : Bool := (shr x i &&& 1) == 1

/-- Sum of the 1-based positions of the set bits (Julia `sum(indices(b))`).
Computed with six masked popcounts: position `k` (0-based) contributes
`k + 1`, and `k = Σⱼ 2ʲ·bitⱼ(k)`. -/
@[inline] def sumIndices (b : UInt64) : Nat :=
  popcount b + popcount (b &&& 0xAAAAAAAAAAAAAAAA)
    + 2 * popcount (b &&& 0xCCCCCCCCCCCCCCCC) + 4 * popcount (b &&& 0xF0F0F0F0F0F0F0F0)
    + 8 * popcount (b &&& 0xFF00FF00FF00FF00) + 16 * popcount (b &&& 0xFFFF0000FFFF0000)
    + 32 * popcount (b &&& 0xFFFFFFFF00000000)

/-- 1-based indices of the set bits, ascending, as a `List` (structural, fuel 64). -/
def indicesList (x : UInt64) : List Nat := go x 1 64
where
  /-- Scan the low bit of `x`, which sits at 1-based position `i`. -/
  go (x : UInt64) (i : Nat) : Nat → List Nat
    | 0 => []
    | fuel + 1 => if x == 0 then [] else
        if x &&& 1 == 1 then i :: go (x >>> 1) (i + 1) fuel else go (x >>> 1) (i + 1) fuel

/-- Parallel bit extract (x86 `pext`): gather the bits of `b` found at the set
positions of `s` into the low bits, in order. This is Leibniz `lowerbits_calc`
(`Leibniz.jl src/utilities.jl:256`) without its cache defect. -/
def pext (b s : UInt64) : UInt64 := go s 0 0 64
where
  /-- `s` = remaining selector bits, `j` = next output position. -/
  go (s j acc : UInt64) : Nat → UInt64
    | 0 => acc
    | fuel + 1 => if s == 0 then acc else
        let low := lowestBit s
        let acc := if b &&& low != 0 then acc ||| ((1 : UInt64) <<< j) else acc
        go (s &&& (s - 1)) (j + 1) acc fuel

/-- Parallel bit deposit (x86 `pdep`): local bit `j` of `b` goes to the `j`-th
set position of `s` (Leibniz `expandbits`, `Leibniz.jl src/utilities.jl:279`). -/
def pdep (b s : UInt64) : UInt64 := go s 0 0 64
where
  /-- `s` = remaining target positions, `j` = next source bit of `b`. -/
  go (s j acc : UInt64) : Nat → UInt64
    | 0 => acc
    | fuel + 1 => if s == 0 then acc else
        let low := lowestBit s
        let acc := if (b >>> j) &&& 1 == 1 then acc ||| low else acc
        go (s &&& (s - 1)) (j + 1) acc fuel

/-- Julia `flipsign(N,S) = (2^N-1) & ~S` (`DirectSum.jl src/generic.jl:141`):
negate every metric bit of an `N`-generator signature. -/
@[inline] def flipsign (n : Nat) (s : UInt64) : UInt64 := lowMask n &&& ~~~s

/-- Julia `dual(V,B,M)` on masks (`DirectSum.jl src/generic.jl:144`): swap the
two halves of a dyadic mask of rank `r` (`M = r/2`). -/
@[inline] def dualSwap (r : Nat) (b : UInt64) : UInt64 :=
  let m := r / 2
  (shl b m &&& lowMask r) ||| shr b m

/-! ## Compile-time checks

`decide` runs these in the kernel, so they act as unit tests enforced by the
type checker. -/

example : popcount 0 = 0 := by decide
example : popcount 0b1011 = 3 := by decide
example : popcount 0xFFFFFFFFFFFFFFFF = 64 := by decide
example : parity 0b1011 = true := by decide
example : ctz 0b1000 = 3 ∧ ctz 1 = 0 ∧ ctz 0 = 64 := by decide
example : sumIndices 0b1011 = 7 ∧ sumIndices 0 = 0 := by decide
example : sumIndices 0x8000000000000000 = 64 := by decide
example : indicesList 0b1011 = [1, 2, 4] := by decide
-- Oracle (port-notes/directsum.md §4.3): expandbits(5,0b10110,0b101) = 0x12,
-- pext of 0b10100 through 0b10110 = 0x6 (Julia's buggy lowerbits gives 0x3).
example : pdep 0b101 0b10110 = 0x12 := by decide
example : pext 0b10100 0b10110 = 0x6 := by decide
example : pext 0b1001 0b1011 = 0x5 := by decide
example : flipsign 3 0b010 = 0b101 := by decide
example : dualSwap 6 0b000101 = 0x28 := by decide
-- e₂ e₁ = -e₁ e₂ ; e₁ e₂ = +e₁₂
example : reorderParity 0b10 0b01 = true := by decide
example : reorderParity 0b01 0b10 = false := by decide
-- e₂₃ e₁ : moving e₁ left past e₃ and e₂ → even
example : reorderParity 0b110 0b001 = false := by decide
-- e₃ e₁₂ : e₁ and e₂ both pass e₃ → even
example : reorderParity 0b100 0b011 = false := by decide
-- e₂ e₁₃ : e₁ passes e₂ → odd
example : reorderParity 0b010 0b101 = true := by decide

/-- The fast reordering parity agrees with the specification on every pair of
blades in dimension ≤ 5 (1024 pairs), checked by the kernel. -/
theorem reorderParity_eq_spec_4 :
    ∀ a b : Fin 16, reorderParity a.1.toUInt64 b.1.toUInt64 = reorderParitySpec 4 a.1 b.1 := by
  decide +kernel

end DirectSum.Bits

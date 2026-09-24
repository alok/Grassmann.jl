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

/-! ## Compile-time checks

`decide` runs these in the kernel, so they act as unit tests enforced by the
type checker. -/

example : popcount 0 = 0 := by decide
example : popcount 0b1011 = 3 := by decide
example : popcount 0xFFFFFFFFFFFFFFFF = 64 := by decide
example : parity 0b1011 = true := by decide
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

/-
Space-independent sign rules from Leibniz.jl `src/generic.jl`: grade-involution
parities, the complement mask, and the raw complement parities.

`true` always means "the component is negated".
-/
import DirectSum.Bits

namespace Leibniz

open DirectSum.Bits

/-! ## Grade-involution parities (`Leibniz.jl src/generic.jl:139-142`) -/

/-- Julia `parityreverse(G) = isodd((G-1)G/2)`: the reverse `~` negates grades
`G ≡ 2, 3 (mod 4)`. -/
@[inline] def parityreverse (g : Nat) : Bool := g % 4 ≥ 2

/-- Julia `parityinvolute(G) = isodd(G)`. -/
@[inline] def parityinvolute (g : Nat) : Bool := g % 2 == 1

/-- Julia `parityclifford(G) = parityreverse(G) ⊻ parityinvolute(G)`: grades
`≡ 1, 2 (mod 4)`. -/
@[inline] def parityclifford (g : Nat) : Bool := parityreverse g != parityinvolute g

/-- Julia `parityconj = parityreverse` (so `conj ≡ reverse ≡ ~`). -/
@[inline] def parityconj (g : Nat) : Bool := parityreverse g

/-- `parityreverse` agrees with Julia's defining formula `isodd((G-1)G/2)`. -/
theorem parityreverse_spec : ∀ g < 128, parityreverse g = ((g * (g - 1) / 2) % 2 == 1) := by
  decide +kernel

/-! ## Splitting masks -/

/-- Julia `indexsplit(B, N) = [1 << (k-1) for k ∈ indices(B, N)]`: the single-generator masks
of `b`, ascending. -/
def indexsplit (b : UInt64) : Array UInt64 := go b #[] 64
where
  /-- Peel the lowest set bit. -/
  go (x : UInt64) (acc : Array UInt64) : Nat → Array UInt64
    | 0 => acc
    | fuel + 1 => if x == 0 then acc else go (x &&& (x - 1)) (acc.push (lowestBit x)) fuel

example : indexsplit 0b101101 = #[1, 4, 8, 32] := by decide

/-! ## Complement mask (`Leibniz.jl src/generic.jl:233-237`) -/

/-- Julia `complement(N,B,D=0,P=0)`: flip every ordinary (non-tangent, non-null)
bit of the `N`-generator mask `B`; the `D` tangent bits of `B` are copied. With
`P = 2` (conformal: both `∞` and `∅`) the null pair is copied and then toggled
together iff it holds zero or two of them. `P = 1` behaves like `P = 0`. -/
def complement (n : Nat) (b : UInt64) (d : Nat := 0) (p : Nat := 0) : UInt64 :=
  let up : UInt64 := shl 1 (if p == 1 then 0 else p) - 1
  let nd := n - d
  let c := ((~~~b) &&& (up ^^^ lowMask nd)) ||| (b &&& (up ^^^ shl (lowMask d) nd))
  if popcount (c &&& up) != 1 then c ^^^ up else c

-- Oracle (port-notes/directsum.md §6.4).
example : complement 3 1 = 0x6 ∧ complement 3 2 = 0x5 := by decide
example : complement 5 1 0 2 = 0x1d ∧ complement 5 2 0 2 = 0x1e ∧ complement 5 3 0 2 = 0x1c := by
  decide
example : complement 5 4 0 2 = 0x1b ∧ complement 5 0 0 2 = 0x1f := by decide
example : complement 4 1 1 0 = 0x6 ∧ complement 4 9 1 0 = 0xe := by decide

/-- Without a null pair, `complement` is an involution on the low `n` bits. -/
theorem complement_involutive_le6 :
    ∀ n < 7, ∀ b < 2 ^ n, complement n (complement n b.toUInt64) = b.toUInt64 := by
  decide +kernel

/-! ## Raw complement parities (`Leibniz.jl src/generic.jl:202-214`)

`s` is the sum of the blade's 1-based indices, `g` its grade, `n` the dimension. -/

/-- Julia `parityright(V::Int,B::Int,G,N) = isodd(B + G(G+1)/2)`: the sign of the
permutation `(S, Sᶜ)`, so that `e_S ∧ !e_S = I`. -/
@[inline] def parityrightRaw (s g : Nat) : Bool := (s + (g + 1) * g / 2) % 2 == 1

/-- Julia `parityleft = (isodd(G) && iseven(N)) ⊻ parityright`. -/
@[inline] def parityleftRaw (s g n : Nat) : Bool :=
  (g % 2 == 1 && n % 2 == 0) != parityrightRaw s g

/-- Julia `parityrighthodge(V::Int,…) = isodd(V) ⊻ parityright` with `V` the number
of negative-metric generators in the blade. -/
@[inline] def parityrighthodgeRaw (neg s g : Nat) : Bool := (neg % 2 == 1) != parityrightRaw s g

/-- Julia `paritylefthodge = (isodd(G) && iseven(N)) ⊻ parityrighthodge`. -/
@[inline] def paritylefthodgeRaw (neg s g n : Nat) : Bool :=
  (g % 2 == 1 && n % 2 == 0) != parityrighthodgeRaw neg s g

/-- Oracle rows (leibniz.md §4.4, `N = 4`, masks `0..15`). -/
example : (List.range 16).map (fun b => parityrightRaw (sumIndices b.toUInt64) (popcount b.toUInt64))
    = [false, false, true, false, false, true, false, false,
       true, false, true, true, false, false, true, false] := by decide
example : (List.range 16).map (fun b => parityleftRaw (sumIndices b.toUInt64) (popcount b.toUInt64) 4)
    = [false, true, false, false, true, true, false, true,
       false, false, true, false, false, true, false, false] := by decide
example : (List.range 16).map
      (fun b => parityrighthodgeRaw (popcount (1 &&& b.toUInt64)) (sumIndices b.toUInt64)
        (popcount b.toUInt64))
    = [false, true, true, true, false, false, false, true,
       true, true, true, false, false, true, true, true] := by decide

end Leibniz

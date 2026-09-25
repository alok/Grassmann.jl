/-
PrimitiveBits: fixed-width bit vectors with 1-based bit indexing.

Julia source: `PrimitiveBits.jl src/PrimitiveBits.jl` (PB). `Declare(b)` (PB:6-36) is
evaluated for `b ∈ [8,16,32,64,128]` (PB:38-40) and generates a `primitive type
PrimitiveBits$b` that reinterprets `UInt$b`, with `getindex` (bit `i-1`, LSB = index 1),
range/colon indexing, construction from integers and Bool vectors, and printing LSB-first.

Lean design: one structure `Bits w` indexed by the width `w` (a zero-cost type index)
over `BitVec w`; Julia's five widths are abbreviations. Indexing `b[i]` demands a proof
`1 ≤ i ∧ i ≤ w`, discharged automatically for literals, so Julia's silent out-of-range
`true` (quirk, PB:14-17) becomes a type error. The quirk itself is kept as
`Bits.Julia.getindex` for oracle parity. Julia's broken `iterate` (PB:23-27, references an
undefined `r`) is replaced by the intended LSB-first iteration.
-/

namespace PrimitiveBits

universe u v

/-- Julia `PrimitiveBits{w}`: a `w`-bit word whose bits are addressed `1..w`, index 1
being the least significant bit (PB:9-17). The width is a type index. -/
structure Bits (w : Nat) where
  /-- The underlying bit vector (Julia: the raw bits of the primitive type). -/
  toBitVec : BitVec w
  deriving DecidableEq

/-- Julia `PrimitiveBits8`. -/
abbrev PrimitiveBits8 := Bits 8
/-- Julia `PrimitiveBits16`. -/
abbrev PrimitiveBits16 := Bits 16
/-- Julia `PrimitiveBits32`. -/
abbrev PrimitiveBits32 := Bits 32
/-- Julia `PrimitiveBits64`. -/
abbrev PrimitiveBits64 := Bits 64
/-- Julia `PrimitiveBits128`. -/
abbrev PrimitiveBits128 := Bits 128

namespace Bits

variable {w : Nat}

/-! ## Construction and conversion (PB:12-13, 28-31) -/

/-- Reinterpret a bit vector (Julia `PrimitiveBits$b(b::UInt$b)`, PB:12). -/
@[inline] def ofBitVec (v : BitVec w) : Bits w := ⟨v⟩

/-- The value as a natural number (Julia `UInt$b(b)`, PB:13). -/
@[inline] def toNat (b : Bits w) : Nat := b.toBitVec.toNat

/-- Truncating constructor: `n mod 2^w`. -/
@[inline] def ofNatMod (w : Nat) (n : Nat) : Bits w := ⟨BitVec.ofNat w n⟩

/-- Julia `PrimitiveBits$b(b::Integer) = PrimitiveBits$b(convert(UInt$b, b))` (PB:28):
throws `InexactError` when `n` is negative or does not fit in `w` bits. -/
def ofInt? (w : Nat) (n : Int) : Except String (Bits w) :=
  if n < 0 then .error s!"InexactError: convert(UInt{w}, {n})"
  else if n.toNat < 2 ^ w then .ok (ofNatMod w n.toNat)
  else .error s!"InexactError: convert(UInt{w}, {n})"

/-- `ofInt?` restricted to naturals. -/
@[inline] def ofNat? (w : Nat) (n : Nat) : Except String (Bits w) := ofInt? w n

/-- `PrimitiveBits8(b::UInt8)` (PB:12). -/
@[inline] def ofUInt8 (x : UInt8) : Bits 8 := ⟨x.toBitVec⟩
/-- `UInt8(b::PrimitiveBits8)` (PB:13). -/
@[inline] def toUInt8 (b : Bits 8) : UInt8 := ⟨b.toBitVec⟩
/-- `PrimitiveBits16(b::UInt16)` (PB:12). -/
@[inline] def ofUInt16 (x : UInt16) : Bits 16 := ⟨x.toBitVec⟩
/-- `UInt16(b::PrimitiveBits16)` (PB:13). -/
@[inline] def toUInt16 (b : Bits 16) : UInt16 := ⟨b.toBitVec⟩
/-- `PrimitiveBits32(b::UInt32)` (PB:12). -/
@[inline] def ofUInt32 (x : UInt32) : Bits 32 := ⟨x.toBitVec⟩
/-- `UInt32(b::PrimitiveBits32)` (PB:13). -/
@[inline] def toUInt32 (b : Bits 32) : UInt32 := ⟨b.toBitVec⟩
/-- `PrimitiveBits64(b::UInt64)` (PB:12). -/
@[inline] def ofUInt64 (x : UInt64) : Bits 64 := ⟨x.toBitVec⟩
/-- `UInt64(b::PrimitiveBits64)` (PB:13). -/
@[inline] def toUInt64 (b : Bits 64) : UInt64 := ⟨b.toBitVec⟩

/-- Total constructor from exactly `w` Bools, element 0 being bit index 1 (LSB).
This is the statically-sized form of Julia's `PrimitiveBits$b(::Vector{Bool})`. -/
def ofVector (v : Vector Bool w) : Bits w :=
  ⟨(BitVec.ofBoolListLE v.toList).cast (by simp)⟩

/-- Julia `PrimitiveBits$b(b::Union{BitVector,Vector{Bool}})` (PB:29-31):
`parse(UInt$b, join(reverse bits), base=2)`. Element 1 is the LSB. Errors exactly as
Julia's `parse`: an empty vector is an `ArgumentError`; a value `≥ 2^w` is an
`OverflowError` (leading `false`s beyond the width are accepted). -/
def ofBools (v : Array Bool) : Except String (Bits w) :=
  if v.isEmpty then .error "ArgumentError: input string is empty or only contains whitespace"
  else
    let n := v.foldr (fun b acc => 2 * acc + if b then 1 else 0) 0
    if n < 2 ^ w then .ok (ofNatMod w n)
    else .error s!"OverflowError: overflow parsing \"{String.ofList (v.toList.reverse.map fun b => if b then '1' else '0')}\""

/-! ## Indexing (PB:14-22) -/

/-- Julia `firstindex(::PrimitiveBits$b) = 1` (PB:20). -/
@[inline] def firstIndex (_ : Bits w) : Nat := 1
/-- Julia `lastindex(::PrimitiveBits$b) = b` (PB:21). -/
@[inline] def lastIndex (_ : Bits w) : Nat := w
/-- Julia `length(::PrimitiveBits$b) = b` (PB:22). -/
@[inline] def length (_ : Bits w) : Nat := w

/-- Bit `i` (1-based, LSB = 1) for an in-range index (PB:14-17). -/
@[inline] def get (b : Bits w) (i : Nat) (_ : 1 ≤ i ∧ i ≤ w) : Bool :=
  b.toBitVec.getLsbD (i - 1)

/-- `b[i]` with `1 ≤ i ≤ w` checked statically. -/
instance : GetElem (Bits w) Nat Bool (fun _ i => 1 ≤ i ∧ i ≤ w) where
  getElem b i h := b.get i h

/-- Optional indexing: `none` out of range (the clean replacement for Julia's quirk). -/
@[inline] def get? (b : Bits w) (i : Nat) : Option Bool :=
  if h : 1 ≤ i ∧ i ≤ w then some (b.get i h) else none

/-- All bits LSB-first: Julia `b[:]` (PB:19) and the intended `collect(b)`. -/
def toList (b : Bits w) : List Bool :=
  (List.range w).map b.toBitVec.getLsbD

/-- All bits LSB-first as an array. -/
@[inline] def toArray (b : Bits w) : Array Bool := b.toList.toArray

/-- Iteration over the bits LSB-first (the intended semantics of Julia's broken
`iterate`, PB:23-27). -/
instance {m : Type u → Type v} [Monad m] : ForIn m (Bits w) Bool where
  forIn b init f := forIn b.toList init f

namespace Julia

/-- Julia `getindex(b, i::Integer)` verbatim (PB:14-17):
`d = one(U) << (i-1); (d & U(b)) == d`. A shift by a negative amount or by `≥ w`
yields `d = 0`, so **every out-of-range index returns `true`** (quirk). -/
def getindex {w : Nat} (b : Bits w) (i : Int) : Bool :=
  if 1 ≤ i ∧ i ≤ w then b.toBitVec.getLsbD (i - 1).toNat else true

/-- Julia `getindex(b, r::UnitRange)` (PB:18): elementwise `getindex`, quirk included. -/
def getRange {w : Nat} (b : Bits w) (lo hi : Int) : Array Bool :=
  ((List.range (hi - lo + 1).toNat).map fun k => getindex b (lo + Int.ofNat k)).toArray

end Julia

/-! ## Printing (PB:32-33) -/

/-- Julia `print(io, b)`: `'['`, the bits LSB-first as `0`/`1`, `']'` (PB:32). -/
protected def toString (b : Bits w) : String :=
  "[" ++ String.ofList (b.toList.map fun x => if x then '1' else '0') ++ "]"

instance : ToString (Bits w) := ⟨Bits.toString⟩
/-- `show == print` in Julia (PB:33). -/
instance : Repr (Bits w) := ⟨fun b _ => Bits.toString b⟩

/-! ## Laws -/

@[simp] theorem getElem_eq (b : Bits w) (i : Nat) (h : 1 ≤ i ∧ i ≤ w) :
    b[i] = b.toBitVec.getLsbD (i - 1) := rfl

/-- Bit extensionality: two words with the same bits at every index are equal. -/
theorem ext {a b : Bits w} (h : ∀ (i : Nat) (hi : 1 ≤ i ∧ i ≤ w), a[i] = b[i]) : a = b := by
  cases a with | mk a => cases b with | mk b =>
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have := h (j + 1) (by omega)
  simpa using this

/-- Indexing the vector constructor reads the vector back (1-based). -/
theorem getElem_ofVector (v : Vector Bool w) (i : Nat) (h : 1 ≤ i ∧ i ≤ w) :
    (ofVector v)[i] = v[i - 1]'(by omega) := by
  simp [ofVector, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    Vector.getElem?_eq_getElem (show i - 1 < w by omega)]

/-- Indexing the truncating constructor reads the binary digits of `n`. -/
theorem getElem_ofNatMod (n i : Nat) (h : 1 ≤ i ∧ i ≤ w) :
    (ofNatMod w n)[i] = n.testBit (i - 1) := by
  simp [ofNatMod, BitVec.getLsbD_ofNat]
  omega

/-- The Julia indexer agrees with the checked indexer in range. -/
theorem julia_getindex_eq (b : Bits w) (i : Nat) (h : 1 ≤ i ∧ i ≤ w) :
    Julia.getindex b i = b[i] := by
  simp only [Julia.getindex, getElem_eq]
  split
  · congr 1; omega
  · omega

/-- The Julia indexer is `true` out of range (quirk PB:14-17, made a theorem). -/
theorem julia_getindex_out_of_range (b : Bits w) (i : Int) (h : i < 1 ∨ w < i) :
    Julia.getindex b i = true := by
  simp only [Julia.getindex]
  split
  · omega
  · rfl

@[simp] theorem toUInt8_ofUInt8 (x : UInt8) : toUInt8 (ofUInt8 x) = x := rfl
@[simp] theorem ofUInt8_toUInt8 (b : Bits 8) : ofUInt8 (toUInt8 b) = b := rfl
@[simp] theorem toUInt16_ofUInt16 (x : UInt16) : toUInt16 (ofUInt16 x) = x := rfl
@[simp] theorem ofUInt16_toUInt16 (b : Bits 16) : ofUInt16 (toUInt16 b) = b := rfl
@[simp] theorem toUInt32_ofUInt32 (x : UInt32) : toUInt32 (ofUInt32 x) = x := rfl
@[simp] theorem ofUInt32_toUInt32 (b : Bits 32) : ofUInt32 (toUInt32 b) = b := rfl
@[simp] theorem toUInt64_ofUInt64 (x : UInt64) : toUInt64 (ofUInt64 x) = x := rfl
@[simp] theorem ofUInt64_toUInt64 (b : Bits 64) : ofUInt64 (toUInt64 b) = b := rfl

@[simp] theorem length_toList (b : Bits w) : b.toList.length = w := by
  simp [toList]

end Bits

end PrimitiveBits

/-!
# Packed-array helpers

Size-tracked builders for the `FloatArray`/`ByteArray` rasters Fatou produces, and the
little-endian `UInt16` encoding of iteration counts (the layout of the oracle's
`*.iter.u16` dumps, two bytes per pixel).
-/

namespace Fatou

/-- A fresh `ByteArray` is empty whatever its capacity. -/
@[simp] theorem size_byteEmpty (n : Nat) : (ByteArray.emptyWithCapacity n).size = 0 := rfl

/-- A fresh `FloatArray` is empty whatever its capacity. -/
@[simp] theorem size_floatEmpty (n : Nat) : (FloatArray.emptyWithCapacity n).size = 0 := rfl

/-- Pushing onto a `FloatArray` adds one element. -/
theorem FloatArray.size_push (a : FloatArray) (x : Float) : (a.push x).size = a.size + 1 := by
  cases a; simp [FloatArray.push, FloatArray.size]

/-- The `FloatArray` `[f 0, f 1, …, f (n-1)]`, filled by a tail-recursive loop. -/
@[inline] def floatArrayOfFn (n : Nat) (f : Nat → Float) : FloatArray :=
  go n 0 (FloatArray.emptyWithCapacity n)
where
  /-- push `f i, f (i+1), …` (`k` of them) -/
  go : Nat → Nat → FloatArray → FloatArray
    | 0, _, acc => acc
    | k + 1, i, acc => go k (i + 1) (acc.push (f i))

/-- The fill loop of `floatArrayOfFn` pushes exactly `k` elements. -/
theorem floatArrayOfFn.size_go (f : Nat → Float) (k i : Nat) (acc : FloatArray) :
    (floatArrayOfFn.go f k i acc).size = acc.size + k := by
  induction k generalizing i acc with
  | zero => rfl
  | succ k ih => simp [floatArrayOfFn.go, ih, FloatArray.size_push]; omega

/-- `floatArrayOfFn n f` has `n` elements. -/
@[simp] theorem size_floatArrayOfFn (n : Nat) (f : Nat → Float) :
    (floatArrayOfFn n f).size = n := by
  simp [floatArrayOfFn, floatArrayOfFn.size_go]

/-- Append `src[i:]` to `dst`, one element at a time (Lean core has no `FloatArray.append`).
Reads with the inline `get!` (`src[i]!` compiles to an out-of-line bounds-check closure). -/
def appendFloats (dst src : FloatArray) : FloatArray :=
  go src.size 0 dst
where
  /-- push `src[i], src[i+1], …` (`k` of them) -/
  go : Nat → Nat → FloatArray → FloatArray
    | 0, _, acc => acc
    | k + 1, i, acc => go k (i + 1) (acc.push (src.get! i))

/-- The copy loop of `appendFloats` pushes exactly `k` elements. -/
theorem appendFloats.size_go (src : FloatArray) (k i : Nat) (acc : FloatArray) :
    (appendFloats.go src k i acc).size = acc.size + k := by
  induction k generalizing i acc with
  | zero => rfl
  | succ k ih => simp [appendFloats.go, ih, FloatArray.size_push]; omega

/-- Appending adds the sizes. -/
@[simp] theorem size_appendFloats (dst src : FloatArray) :
    (appendFloats dst src).size = dst.size + src.size := by
  simp [appendFloats, appendFloats.size_go]

/-- `set!` keeps the size of a `FloatArray`. -/
@[simp] theorem FloatArray.size_set! (a : FloatArray) (i : Nat) (x : Float) :
    (a.set! i x).size = a.size := by
  cases a; simp [FloatArray.set!, FloatArray.size]

/-- `n` zeros, as a `FloatArray` to be overwritten in place. -/
def zerosF (n : Nat) : FloatArray :=
  go n (FloatArray.emptyWithCapacity n)
where
  /-- push `k` zeros -/
  go : Nat → FloatArray → FloatArray
    | 0, acc => acc
    | k + 1, acc => go k (acc.push 0)

theorem zerosF.size_go (k : Nat) (acc : FloatArray) : (zerosF.go k acc).size = acc.size + k := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih => simp [zerosF.go, ih, FloatArray.size_push]; omega

@[simp] theorem size_zerosF (n : Nat) : (zerosF n).size = n := by
  simp [zerosF, zerosF.size_go]

/-- `n` zero bytes: one byte, doubled by `++` (a `memcpy` each) and cut to size. -/
def zerosB (n : Nat) : ByteArray :=
  (go n (ByteArray.mk #[0])).extract 0 n
where
  /-- double `acc` until it holds at least `n` bytes (`fuel` doublings at most) -/
  go : Nat → ByteArray → ByteArray
    | 0, acc => acc
    | fuel + 1, acc => if acc.size ≥ n then acc else go fuel (acc ++ acc)

theorem zerosB.size_go (n fuel : Nat) (acc : ByteArray) (h : 0 < acc.size) (hf : n ≤ acc.size * 2 ^ fuel) :
    n ≤ (zerosB.go n fuel acc).size := by
  induction fuel generalizing acc with
  | zero => simpa [zerosB.go] using hf
  | succ fuel ih =>
    simp only [zerosB.go]
    split
    · omega
    · apply ih
      · simp [ByteArray.size_append]; omega
      · simp only [ByteArray.size_append, Nat.pow_succ] at hf ⊢
        rw [← Nat.mul_assoc, Nat.mul_two] at hf; rw [Nat.add_mul]; exact hf

@[simp] theorem size_zerosB (n : Nat) : (zerosB n).size = n := by
  have h : n ≤ (zerosB.go n n (ByteArray.mk #[0])).size :=
    zerosB.size_go n n _ (by decide) (by
      have : ({ data := #[0] } : ByteArray).size = 1 := rfl
      rw [this, Nat.one_mul]; exact Nat.le_of_lt Nat.lt_two_pow_self)
  simp only [zerosB, ByteArray.size_extract]
  omega

/-- Write a `UInt16` in little-endian byte order at element index `i` (bytes `2i`, `2i+1`). -/
@[inline] def setU16 (a : ByteArray) (i : Nat) (v : UInt16) : ByteArray :=
  (a.set! (2 * i) v.toUInt8).set! (2 * i + 1) (v >>> 8).toUInt8

@[simp] theorem size_setU16 (a : ByteArray) (i : Nat) (v : UInt16) : (setU16 a i v).size = a.size := by
  simp [setU16]

/-- Append a `UInt16` in little-endian byte order. -/
@[inline] def pushU16 (a : ByteArray) (v : UInt16) : ByteArray :=
  (a.push v.toUInt8).push (v >>> 8).toUInt8

/-- A `UInt16` takes two bytes. -/
@[simp] theorem size_pushU16 (a : ByteArray) (v : UInt16) : (pushU16 a v).size = a.size + 2 := by
  simp [pushU16, ByteArray.size_push]

/-- Read the little-endian `UInt16` at element index `i` (bytes `2i`, `2i+1`). -/
@[inline] def getU16 (a : ByteArray) (i : Nat) : UInt16 :=
  a[2 * i]!.toUInt16 ||| (a[2 * i + 1]!.toUInt16 <<< 8)

/-- Every 16-bit value survives the little-endian round trip. -/
theorem u16_roundtrip (v : UInt16) : v.toUInt8.toUInt16 ||| ((v >>> 8).toUInt8.toUInt16 <<< 8) = v := by
  apply UInt16.eq_of_toBitVec_eq
  simp only [UInt16.toBitVec_or, UInt16.toBitVec_shiftLeft, UInt8.toBitVec_toUInt16,
    UInt16.toBitVec_toUInt8, UInt16.toBitVec_shiftRight]
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_setWidth]
  by_cases h : i < 8
  · simp [h, BitVec.getLsbD_eq_getElem hi]
  · have h1 : i - 8 < 8 := by omega
    have h2 : 8 + (i - 8) = i := by omega
    simp [h, h1, h2, BitVec.getLsbD_eq_getElem hi]

/-- Lexicographic index `j*cols + k` of pixel `(j, k)` is in range. -/
theorem index_lt {rows cols j k : Nat} (hj : j < rows) (hk : k < cols) :
    j * cols + k < rows * cols := by
  have : (j + 1) * cols ≤ rows * cols := Nat.mul_le_mul_right _ hj
  rw [Nat.succ_mul] at this
  omega

end Fatou

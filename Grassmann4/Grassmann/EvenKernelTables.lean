/-
  Grassmann/EvenKernelTables.lean - Cached kernels for packed even multivectors

  This production module owns the dimension- and signature-specific lookup
  tables shared by `MV` and the deprecated `EvenMV` backend.  Keeping these
  tables independent of `EvenMV` prevents the primary runtime from importing
  that backend and its proof-oriented dependencies.
-/
import Grassmann.SignTablesCore

namespace Grassmann

/-! ## Packed-even kernel tables -/

namespace EvenKernelTables

/-- Boolean test for an even-grade blade mask. -/
@[inline]
private def isEvenMask (mask : Nat) : Bool :=
  popcount mask % 2 == 0

/-- Array of even blade masks in increasing bitmask order. -/
private def evenMasksCompute (n : Nat) : Array Nat :=
  (Array.range (2 ^ n)).filter isEvenMask

/-- Map a full blade mask to its packed-even index.

The entry for an odd mask is deliberately unspecified and currently zero. -/
private def evenIndexMapCompute (n : Nat) : Array Nat :=
  let sizeFull := 2 ^ n
  let masks := evenMasksCompute n
  (Array.range masks.size).foldl (init := Array.replicate sizeFull 0) fun acc i =>
    acc.set! (masks.getD i 0) i

/-! ### Cached enumeration for small dimensions -/

private def evenMasks2 : Array Nat := evenMasksCompute 2
private def evenMasks3 : Array Nat := evenMasksCompute 3
private def evenMasks4 : Array Nat := evenMasksCompute 4
private def evenMasks5 : Array Nat := evenMasksCompute 5

private def evenIndexMap2 : Array Nat := evenIndexMapCompute 2
private def evenIndexMap3 : Array Nat := evenIndexMapCompute 3
private def evenIndexMap4 : Array Nat := evenIndexMapCompute 4
private def evenIndexMap5 : Array Nat := evenIndexMapCompute 5

private def evenPackedIdx2 : Array Nat := Array.range (2 ^ (2 - 1))
private def evenPackedIdx3 : Array Nat := Array.range (2 ^ (3 - 1))
private def evenPackedIdx4 : Array Nat := Array.range (2 ^ (4 - 1))
private def evenPackedIdx5 : Array Nat := Array.range (2 ^ (5 - 1))

private def fullIdx2 : Array Nat := Array.range (2 ^ 2)
private def fullIdx3 : Array Nat := Array.range (2 ^ 3)
private def fullIdx4 : Array Nat := Array.range (2 ^ 4)
private def fullIdx5 : Array Nat := Array.range (2 ^ 5)

@[inline]
def evenMasksCached (n : Nat) : Array Nat :=
  match n with
  | 2 => evenMasks2
  | 3 => evenMasks3
  | 4 => evenMasks4
  | 5 => evenMasks5
  | _ => evenMasksCompute n

@[inline]
def evenIndexMapCached (n : Nat) : Array Nat :=
  match n with
  | 2 => evenIndexMap2
  | 3 => evenIndexMap3
  | 4 => evenIndexMap4
  | 5 => evenIndexMap5
  | _ => evenIndexMapCompute n

/-- Cached packed index range `0 .. 2^(n-1)-1` for small dimensions. -/
@[inline]
def evenPackedIdxCached (n : Nat) : Array Nat :=
  match n with
  | 2 => evenPackedIdx2
  | 3 => evenPackedIdx3
  | 4 => evenPackedIdx4
  | 5 => evenPackedIdx5
  | _ => Array.range (2 ^ (n - 1))

/-- Cached full index range `0 .. 2^n-1` for small dimensions. -/
@[inline]
def fullIdxCached (n : Nat) : Array Nat :=
  match n with
  | 2 => fullIdx2
  | 3 => fullIdx3
  | 4 => fullIdx4
  | 5 => fullIdx5
  | _ => Array.range (2 ^ n)

/-! ### Even x even multiplication tables -/

/-- Packed output index for every packed-even input pair. -/
private def evenMulIdxCompute (n : Nat) : Array Nat :=
  let sizeEven := 2 ^ (n - 1)
  let masks := evenMasksCompute n
  let map := evenIndexMapCompute n
  Array.ofFn (n := sizeEven * sizeEven) fun idx =>
    let i := idx / sizeEven
    let j := idx % sizeEven
    map.getD ((masks.getD i 0) ^^^ (masks.getD j 0)) 0

def evenMulIdx2 : Array Nat := evenMulIdxCompute 2
def evenMulIdx3 : Array Nat := evenMulIdxCompute 3
def evenMulIdx4 : Array Nat := evenMulIdxCompute 4
def evenMulIdx5 : Array Nat := evenMulIdxCompute 5

@[inline]
def evenMulIdxCached (n : Nat) : Array Nat :=
  match n with
  | 2 => evenMulIdx2
  | 3 => evenMulIdx3
  | 4 => evenMulIdx4
  | 5 => evenMulIdx5
  | _ => #[]

/-- Product sign for every packed-even input pair. -/
private def evenMulSignFromTable {n : Nat} (table : SignTable n) : Array Int8 :=
  let sizeEven := 2 ^ (n - 1)
  let masks := evenMasksCached n
  Array.ofFn (n := sizeEven * sizeEven) fun idx =>
    let i := idx / sizeEven
    let j := idx % sizeEven
    table.lookup (masks.getD i 0) (masks.getD j 0)

def evenMulSignR2 : Array Int8 := evenMulSignFromTable R2SignTable
def evenMulSignR3 : Array Int8 := evenMulSignFromTable R3SignTable
def evenMulSignR4 : Array Int8 := evenMulSignFromTable R4SignTable
def evenMulSignSTA : Array Int8 := evenMulSignFromTable STASignTable
def evenMulSignPGA3 : Array Int8 := evenMulSignFromTable PGA3SignTable
def evenMulSignCGA3 : Array Int8 := evenMulSignFromTable CGA3SignTable

/-- Cached even-product sign table for a canonical signature. -/
@[inline]
def evenMulSignCached {n : Nat} (s : Signature n) : Option (Array Int8) :=
  match n with
  | 2 => if s == R2 then some evenMulSignR2 else none
  | 3 => if s == R3 then some evenMulSignR3 else none
  | 4 =>
      if s == R4 then some evenMulSignR4
      else if s == STA then some evenMulSignSTA
      else if s == PGA3 then some evenMulSignPGA3
      else none
  | 5 => if s == CGA3 then some evenMulSignCGA3 else none
  | _ => none

/-! ### Even x full and full x even tables -/

private def evenLeftMulIdxCompute (n : Nat) : Array Nat :=
  let sizeEven := 2 ^ (n - 1)
  let sizeFull := 2 ^ n
  let masks := evenMasksCompute n
  Array.ofFn (n := sizeEven * sizeFull) fun idx =>
    let i := idx / sizeFull
    let j := idx % sizeFull
    (masks.getD i 0) ^^^ j

private def evenLeftMulIdx2 : Array Nat := evenLeftMulIdxCompute 2
private def evenLeftMulIdx3 : Array Nat := evenLeftMulIdxCompute 3
private def evenLeftMulIdx4 : Array Nat := evenLeftMulIdxCompute 4
private def evenLeftMulIdx5 : Array Nat := evenLeftMulIdxCompute 5

@[inline]
def evenLeftMulIdxCached (n : Nat) : Array Nat :=
  match n with
  | 2 => evenLeftMulIdx2
  | 3 => evenLeftMulIdx3
  | 4 => evenLeftMulIdx4
  | 5 => evenLeftMulIdx5
  | _ => #[]

private def evenRightMulIdxCompute (n : Nat) : Array Nat :=
  let sizeEven := 2 ^ (n - 1)
  let sizeFull := 2 ^ n
  let masks := evenMasksCompute n
  Array.ofFn (n := sizeFull * sizeEven) fun idx =>
    let i := idx / sizeEven
    let j := idx % sizeEven
    i ^^^ (masks.getD j 0)

private def evenRightMulIdx2 : Array Nat := evenRightMulIdxCompute 2
private def evenRightMulIdx3 : Array Nat := evenRightMulIdxCompute 3
private def evenRightMulIdx4 : Array Nat := evenRightMulIdxCompute 4
private def evenRightMulIdx5 : Array Nat := evenRightMulIdxCompute 5

@[inline]
def evenRightMulIdxCached (n : Nat) : Array Nat :=
  match n with
  | 2 => evenRightMulIdx2
  | 3 => evenRightMulIdx3
  | 4 => evenRightMulIdx4
  | 5 => evenRightMulIdx5
  | _ => #[]

private def evenLeftMulSignFromTable {n : Nat} (table : SignTable n) : Array Int8 :=
  let sizeEven := 2 ^ (n - 1)
  let sizeFull := 2 ^ n
  let masks := evenMasksCached n
  Array.ofFn (n := sizeEven * sizeFull) fun idx =>
    let i := idx / sizeFull
    let j := idx % sizeFull
    table.lookup (masks.getD i 0) j

private def evenRightMulSignFromTable {n : Nat} (table : SignTable n) : Array Int8 :=
  let sizeEven := 2 ^ (n - 1)
  let sizeFull := 2 ^ n
  let masks := evenMasksCached n
  Array.ofFn (n := sizeFull * sizeEven) fun idx =>
    let i := idx / sizeEven
    let j := idx % sizeEven
    table.lookup i (masks.getD j 0)

private def evenLeftMulSignR2 : Array Int8 := evenLeftMulSignFromTable R2SignTable
private def evenLeftMulSignR3 : Array Int8 := evenLeftMulSignFromTable R3SignTable
private def evenLeftMulSignR4 : Array Int8 := evenLeftMulSignFromTable R4SignTable
private def evenLeftMulSignSTA : Array Int8 := evenLeftMulSignFromTable STASignTable
private def evenLeftMulSignPGA3 : Array Int8 := evenLeftMulSignFromTable PGA3SignTable
private def evenLeftMulSignCGA3 : Array Int8 := evenLeftMulSignFromTable CGA3SignTable

private def evenRightMulSignR2 : Array Int8 := evenRightMulSignFromTable R2SignTable
private def evenRightMulSignR3 : Array Int8 := evenRightMulSignFromTable R3SignTable
private def evenRightMulSignR4 : Array Int8 := evenRightMulSignFromTable R4SignTable
private def evenRightMulSignSTA : Array Int8 := evenRightMulSignFromTable STASignTable
private def evenRightMulSignPGA3 : Array Int8 := evenRightMulSignFromTable PGA3SignTable
private def evenRightMulSignCGA3 : Array Int8 := evenRightMulSignFromTable CGA3SignTable

/-- Cached sign table for left multiplication by a packed-even value. -/
@[inline]
def evenLeftMulSignCached {n : Nat} (s : Signature n) : Option (Array Int8) :=
  match n with
  | 2 => if s == R2 then some evenLeftMulSignR2 else none
  | 3 => if s == R3 then some evenLeftMulSignR3 else none
  | 4 =>
      if s == R4 then some evenLeftMulSignR4
      else if s == STA then some evenLeftMulSignSTA
      else if s == PGA3 then some evenLeftMulSignPGA3
      else none
  | 5 => if s == CGA3 then some evenLeftMulSignCGA3 else none
  | _ => none

/-- Cached sign table for right multiplication by a packed-even value. -/
@[inline]
def evenRightMulSignCached {n : Nat} (s : Signature n) : Option (Array Int8) :=
  match n with
  | 2 => if s == R2 then some evenRightMulSignR2 else none
  | 3 => if s == R3 then some evenRightMulSignR3 else none
  | 4 =>
      if s == R4 then some evenRightMulSignR4
      else if s == STA then some evenRightMulSignSTA
      else if s == PGA3 then some evenRightMulSignPGA3
      else none
  | 5 => if s == CGA3 then some evenRightMulSignCGA3 else none
  | _ => none

/-! ### Output-major right-product tables -/

private def evenRightOutLeftIdxCompute (n : Nat) : Array Nat :=
  let sizeEven := 2 ^ (n - 1)
  let sizeFull := 2 ^ n
  let masks := evenMasksCompute n
  Array.ofFn (n := sizeFull * sizeEven) fun idx =>
    let k := idx / sizeEven
    let j := idx % sizeEven
    k ^^^ (masks.getD j 0)

private def evenRightOutLeftIdx2 : Array Nat := evenRightOutLeftIdxCompute 2
private def evenRightOutLeftIdx3 : Array Nat := evenRightOutLeftIdxCompute 3
private def evenRightOutLeftIdx4 : Array Nat := evenRightOutLeftIdxCompute 4
private def evenRightOutLeftIdx5 : Array Nat := evenRightOutLeftIdxCompute 5

@[inline]
def evenRightOutLeftIdxCached (n : Nat) : Array Nat :=
  match n with
  | 2 => evenRightOutLeftIdx2
  | 3 => evenRightOutLeftIdx3
  | 4 => evenRightOutLeftIdx4
  | 5 => evenRightOutLeftIdx5
  | _ => #[]

private def evenRightOutSignFromTable {n : Nat} (table : SignTable n) : Array Int8 :=
  let sizeEven := 2 ^ (n - 1)
  let sizeFull := 2 ^ n
  let masks := evenMasksCached n
  Array.ofFn (n := sizeFull * sizeEven) fun idx =>
    let k := idx / sizeEven
    let j := idx % sizeEven
    let mask := masks.getD j 0
    table.lookup (k ^^^ mask) mask

private def evenRightOutSignR2 : Array Int8 := evenRightOutSignFromTable R2SignTable
private def evenRightOutSignR3 : Array Int8 := evenRightOutSignFromTable R3SignTable
private def evenRightOutSignR4 : Array Int8 := evenRightOutSignFromTable R4SignTable
private def evenRightOutSignSTA : Array Int8 := evenRightOutSignFromTable STASignTable
private def evenRightOutSignPGA3 : Array Int8 := evenRightOutSignFromTable PGA3SignTable
private def evenRightOutSignCGA3 : Array Int8 := evenRightOutSignFromTable CGA3SignTable

/-- Cached output-major sign table for restricted right products. -/
@[inline]
def evenRightOutSignCached {n : Nat} (s : Signature n) : Option (Array Int8) :=
  match n with
  | 2 => if s == R2 then some evenRightOutSignR2 else none
  | 3 => if s == R3 then some evenRightOutSignR3 else none
  | 4 =>
      if s == R4 then some evenRightOutSignR4
      else if s == STA then some evenRightOutSignSTA
      else if s == PGA3 then some evenRightOutSignPGA3
      else none
  | 5 => if s == CGA3 then some evenRightOutSignCGA3 else none
  | _ => none

end EvenKernelTables

/-! ## Compatibility namespace

`EvenMV.Kernel` was the original public location of these tables.  Exporting
the production declarations here preserves source compatibility without
maintaining a second set of arrays. -/

namespace EvenMV.Kernel

export EvenKernelTables (
  evenMasksCached
  evenIndexMapCached
  evenPackedIdxCached
  fullIdxCached
  evenMulIdx2
  evenMulIdx3
  evenMulIdx4
  evenMulIdx5
  evenMulIdxCached
  evenMulSignR2
  evenMulSignR3
  evenMulSignR4
  evenMulSignSTA
  evenMulSignPGA3
  evenMulSignCGA3
  evenLeftMulIdxCached
  evenRightMulIdxCached
  evenRightOutLeftIdxCached)

/-- Compatibility forwarding wrapper for the historical unused `sig` binder. -/
@[inline]
def evenMulSignCached {n : Nat} {sig : Signature n} (s : Signature n) : Option (Array Int8) :=
  let _ := sig
  EvenKernelTables.evenMulSignCached s

/-- Compatibility forwarding wrapper for the historical unused `sig` binder. -/
@[inline]
def evenLeftMulSignCached {n : Nat} {sig : Signature n}
    (s : Signature n) : Option (Array Int8) :=
  let _ := sig
  EvenKernelTables.evenLeftMulSignCached s

/-- Compatibility forwarding wrapper for the historical unused `sig` binder. -/
@[inline]
def evenRightMulSignCached {n : Nat} {sig : Signature n}
    (s : Signature n) : Option (Array Int8) :=
  let _ := sig
  EvenKernelTables.evenRightMulSignCached s

/-- Compatibility forwarding wrapper for the historical unused `sig` binder. -/
@[inline]
def evenRightOutSignCached {n : Nat} {sig : Signature n}
    (s : Signature n) : Option (Array Int8) :=
  let _ := sig
  EvenKernelTables.evenRightOutSignCached s

end EvenMV.Kernel

end Grassmann

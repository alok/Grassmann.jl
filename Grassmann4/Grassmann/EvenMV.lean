/-
  Grassmann/EvenMV.lean - Packed even-grade multivectors (spinors/rotors)

  Motivation:
  - Even elements (grades 0,2,4,...) form the Spin/Pin even subalgebra.
  - Rotors and spinors live here and are performance hot paths.
  - Storing only even blades cuts memory and work in half (2^(n-1) coeffs).

  Design:
  - `EvenMV sig F` stores coefficients only for even-grade basis blades.
  - Enumeration of even blades is by increasing bitmask order.
  - Proof obligations about parity/indices are left as `sorry_proof` for now.
-/
import Grassmann.Multivector
import Grassmann.Parity
import Grassmann.Proof
import Grassmann.BladeIndex
import Grassmann.GradeSet
import Grassmann.SignTables
import Mathlib.Algebra.Group.Nat.Even

open Grassmann.Proof

namespace Grassmann

variable {n : ℕ} {sig : Signature n} {F : Type*} [Ring F]

/-- Packed even multivector: coefficients for even-grade blades only. -/
structure EvenMV (sig : Signature n) (F : Type*) where
  /-- Coefficients indexed over the 2^(n-1) even blades. -/
  coeffs : Fin (2 ^ (n - 1)) → F

namespace EvenMV

/-- Zero even multivector. -/
@[inline] def zero : EvenMV sig F := ⟨fun _ => 0⟩

/-- Scalar even multivector (only grade 0). -/
@[inline] def scalar (x : F) : EvenMV sig F :=
  ⟨fun i => if i.val = 0 then x else 0⟩

/-- Unit scalar (identity rotor). -/
@[inline] def one : EvenMV sig F := scalar 1

/-- Scalar part (packed index 0). -/
@[inline] def scalarPart (e : EvenMV sig F) : F :=
  e.coeffs ⟨0, Nat.two_pow_pos (n - 1)⟩

instance : Zero (EvenMV sig F) := ⟨zero⟩
instance : One (EvenMV sig F) := ⟨one⟩

/-- Componentwise addition. -/
@[inline] def add (a b : EvenMV sig F) : EvenMV sig F :=
  ⟨fun i => a.coeffs i + b.coeffs i⟩

/-- Componentwise subtraction. -/
@[inline] def sub (a b : EvenMV sig F) : EvenMV sig F :=
  ⟨fun i => a.coeffs i - b.coeffs i⟩

/-- Negation. -/
@[inline] def neg (a : EvenMV sig F) : EvenMV sig F :=
  ⟨fun i => -a.coeffs i⟩

/-- Scalar multiplication. -/
@[inline] def smul (x : F) (a : EvenMV sig F) : EvenMV sig F :=
  ⟨fun i => x * a.coeffs i⟩

instance : Add (EvenMV sig F) := ⟨add⟩
instance : Sub (EvenMV sig F) := ⟨sub⟩
instance : Neg (EvenMV sig F) := ⟨neg⟩
instance : SMul F (EvenMV sig F) := ⟨smul⟩

/-! ### Kernel tables

This namespace contains the precomputed index/sign kernels used by the fast
even-only algorithms. It is factored out so other backends (e.g. `DataArray`)
can reuse the same tables without duplicating logic.
-/

namespace Kernel

/-- Boolean test for even grade (runtime cheap). -/
private def isEvenGrade (n : ℕ) (m : Nat) : Bool :=
  decide (Even (grade (BitVec.ofNat n m)))

/-- List of all even blade bitmasks in increasing order. -/
private def evenMaskList (n : ℕ) : List Nat :=
  (List.range (2 ^ n)).filter fun m => isEvenGrade n m

/-- Array of even blade masks for O(1) access (computed). -/
private def evenMasksCompute (n : ℕ) : Array Nat :=
  (evenMaskList n).toArray

/-- Map full blade bitmask → packed even index (computed).
    For odd masks, the value is arbitrary (0). -/
private def evenIndexMapCompute (n : ℕ) : Array Nat :=
  let sizeFull := 2 ^ n
  let masks := evenMasksCompute n
  let init := Array.replicate sizeFull 0
  (List.finRange masks.size).foldl (init := init) fun acc i =>
    let mask := masks.getD i.val 0
    acc.set! mask i.val

/-! #### Cached enumeration for small n -/

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

@[inline] def evenMasksCached (n : ℕ) : Array Nat :=
  match n with
  | 2 => evenMasks2
  | 3 => evenMasks3
  | 4 => evenMasks4
  | 5 => evenMasks5
  | _ => evenMasksCompute n

@[inline] def evenIndexMapCached (n : ℕ) : Array Nat :=
  match n with
  | 2 => evenIndexMap2
  | 3 => evenIndexMap3
  | 4 => evenIndexMap4
  | 5 => evenIndexMap5
  | _ => evenIndexMapCompute n

/-- Cached packed index range `0..2^(n-1)-1` for small `n` (avoids allocating per product). -/
@[inline] def evenPackedIdxCached (n : ℕ) : Array Nat :=
  match n with
  | 2 => evenPackedIdx2
  | 3 => evenPackedIdx3
  | 4 => evenPackedIdx4
  | 5 => evenPackedIdx5
  | _ => Array.range (2 ^ (n - 1))

/-- Cached full index range `0..2^n-1` for small `n`. -/
@[inline] def fullIdxCached (n : ℕ) : Array Nat :=
  match n with
  | 2 => fullIdx2
  | 3 => fullIdx3
  | 4 => fullIdx4
  | 5 => fullIdx5
  | _ => Array.range (2 ^ n)

/-! #### Cached even×even kernel tables (n=2..5) -/

/-- For each packed even pair `(i,j)`, precompute the packed output index `k`.
    This depends only on `n` (not on signature). -/
private def evenMulIdxCompute (n : ℕ) : Array Nat :=
  let sizeEven := 2 ^ (n - 1)
  let masks := evenMasksCompute n
  let map := evenIndexMapCompute n
  Array.ofFn (n := sizeEven * sizeEven) fun idx =>
    let i := idx / sizeEven
    let j := idx % sizeEven
    let mi := masks.getD i 0
    let mj := masks.getD j 0
    map.getD (mi ^^^ mj) 0

private def evenMulIdx2 : Array Nat := evenMulIdxCompute 2
private def evenMulIdx3 : Array Nat := evenMulIdxCompute 3
private def evenMulIdx4 : Array Nat := evenMulIdxCompute 4
private def evenMulIdx5 : Array Nat := evenMulIdxCompute 5

@[inline] def evenMulIdxCached (n : ℕ) : Array Nat :=
  match n with
  | 2 => evenMulIdx2
  | 3 => evenMulIdx3
  | 4 => evenMulIdx4
  | 5 => evenMulIdx5
  | _ => #[]

/-- For each packed even pair `(i,j)`, precompute the sign in `{-1,0,1}`.
    This depends on the signature (via its precomputed `SignTable`). -/
private def evenMulSignFromTable {n : ℕ} (table : SignTable n) : Array Int8 :=
  let sizeEven := 2 ^ (n - 1)
  let masks := evenMasksCached n
  Array.ofFn (n := sizeEven * sizeEven) fun idx =>
    let i := idx / sizeEven
    let j := idx % sizeEven
    let mi := masks.getD i 0
    let mj := masks.getD j 0
    table.lookup mi mj

private def evenMulSignR2 : Array Int8 := evenMulSignFromTable R2SignTable
private def evenMulSignR3 : Array Int8 := evenMulSignFromTable R3SignTable
private def evenMulSignR4 : Array Int8 := evenMulSignFromTable R4SignTable
private def evenMulSignSTA : Array Int8 := evenMulSignFromTable STASignTable
private def evenMulSignPGA3 : Array Int8 := evenMulSignFromTable PGA3SignTable
private def evenMulSignCGA3 : Array Int8 := evenMulSignFromTable CGA3SignTable

/-- Cached even×even sign table restricted to even blades, for canonical signatures. -/
@[inline] def evenMulSignCached (s : Signature n) : Option (Array Int8) :=
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

/-! #### Cached even×full kernels (left/right multiply) -/

/-- For each even packed index `i` and full index `j`, precompute the full output index `k`.
    Depends only on `n`. Layout: `k[(i*sizeFull)+j]`. -/
private def evenLeftMulIdxCompute (n : ℕ) : Array Nat :=
  let sizeEven := 2 ^ (n - 1)
  let sizeFull := 2 ^ n
  let masks := evenMasksCompute n
  Array.ofFn (n := sizeEven * sizeFull) fun idx =>
    let i := idx / sizeFull
    let j := idx % sizeFull
    let mi := masks.getD i 0
    mi ^^^ j

private def evenLeftMulIdx2 : Array Nat := evenLeftMulIdxCompute 2
private def evenLeftMulIdx3 : Array Nat := evenLeftMulIdxCompute 3
private def evenLeftMulIdx4 : Array Nat := evenLeftMulIdxCompute 4
private def evenLeftMulIdx5 : Array Nat := evenLeftMulIdxCompute 5

@[inline] def evenLeftMulIdxCached (n : ℕ) : Array Nat :=
  match n with
  | 2 => evenLeftMulIdx2
  | 3 => evenLeftMulIdx3
  | 4 => evenLeftMulIdx4
  | 5 => evenLeftMulIdx5
  | _ => #[]

/-- For each full index `i` and packed even index `j`, precompute the full output index `k`.
    Depends only on `n`. Layout: `k[(i*sizeEven)+j]`. -/
private def evenRightMulIdxCompute (n : ℕ) : Array Nat :=
  let sizeEven := 2 ^ (n - 1)
  let sizeFull := 2 ^ n
  let masks := evenMasksCompute n
  Array.ofFn (n := sizeFull * sizeEven) fun idx =>
    let i := idx / sizeEven
    let j := idx % sizeEven
    let mj := masks.getD j 0
    i ^^^ mj

private def evenRightMulIdx2 : Array Nat := evenRightMulIdxCompute 2
private def evenRightMulIdx3 : Array Nat := evenRightMulIdxCompute 3
private def evenRightMulIdx4 : Array Nat := evenRightMulIdxCompute 4
private def evenRightMulIdx5 : Array Nat := evenRightMulIdxCompute 5

@[inline] def evenRightMulIdxCached (n : ℕ) : Array Nat :=
  match n with
  | 2 => evenRightMulIdx2
  | 3 => evenRightMulIdx3
  | 4 => evenRightMulIdx4
  | 5 => evenRightMulIdx5
  | _ => #[]

/-- For each even packed index `i` and full index `j`, precompute the sign in `{-1,0,1}`.
    Depends on the signature's `SignTable`. Layout: `sign[(i*sizeFull)+j]`. -/
private def evenLeftMulSignFromTable {n : ℕ} (table : SignTable n) : Array Int8 :=
  let sizeEven := 2 ^ (n - 1)
  let sizeFull := 2 ^ n
  let masks := evenMasksCached n
  Array.ofFn (n := sizeEven * sizeFull) fun idx =>
    let i := idx / sizeFull
    let j := idx % sizeFull
    let mi := masks.getD i 0
    table.lookup mi j

/-- For each full index `i` and even packed index `j`, precompute the sign in `{-1,0,1}`.
    Depends on the signature's `SignTable`. Layout: `sign[(i*sizeEven)+j]`. -/
private def evenRightMulSignFromTable {n : ℕ} (table : SignTable n) : Array Int8 :=
  let sizeEven := 2 ^ (n - 1)
  let sizeFull := 2 ^ n
  let masks := evenMasksCached n
  Array.ofFn (n := sizeFull * sizeEven) fun idx =>
    let i := idx / sizeEven
    let j := idx % sizeEven
    let mj := masks.getD j 0
    table.lookup i mj

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

/-- Cached even×full sign table restricted to left even blades, for canonical signatures. -/
@[inline] def evenLeftMulSignCached (s : Signature n) : Option (Array Int8) :=
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

/-- Cached full×even sign table restricted to right even blades, for canonical signatures. -/
@[inline] def evenRightMulSignCached (s : Signature n) : Option (Array Int8) :=
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

/-! #### Cached kernels for `RightAtIndices`

When computing only a restricted set of *output* indices (e.g. a PGA point/plane/line
transform where we know the output grade), it is profitable to loop over
`outIdx × even` and invert the XOR mapping.

For very small outputs (grade-1/grade-3 in `n=4`) the per‑pair overhead of
computing `i := k ^^^ mask(j)` and then indexing `signs[(i*sizeEven)+j]` starts to
matter, so we cache:
- the inverted left index `i[(k*sizeEven)+j]`
- the sign in the same layout `signOut[(k*sizeEven)+j]` for canonical signatures
  (so the inner loop is just a couple of array loads + mul/add).
-/

/-- For each output index `k` and packed even index `j`, precompute the left index
    `i = k ^^^ mask(j)`. Depends only on `n`.

    Layout: `i[(k*sizeEven)+j]`. -/
private def evenRightOutLeftIdxCompute (n : ℕ) : Array Nat :=
  let sizeEven := 2 ^ (n - 1)
  let sizeFull := 2 ^ n
  let masks := evenMasksCompute n
  Array.ofFn (n := sizeFull * sizeEven) fun idx =>
    let k := idx / sizeEven
    let j := idx % sizeEven
    let mj := masks.getD j 0
    k ^^^ mj

private def evenRightOutLeftIdx2 : Array Nat := evenRightOutLeftIdxCompute 2
private def evenRightOutLeftIdx3 : Array Nat := evenRightOutLeftIdxCompute 3
private def evenRightOutLeftIdx4 : Array Nat := evenRightOutLeftIdxCompute 4
private def evenRightOutLeftIdx5 : Array Nat := evenRightOutLeftIdxCompute 5

@[inline] def evenRightOutLeftIdxCached (n : ℕ) : Array Nat :=
  match n with
  | 2 => evenRightOutLeftIdx2
  | 3 => evenRightOutLeftIdx3
  | 4 => evenRightOutLeftIdx4
  | 5 => evenRightOutLeftIdx5
  | _ => #[]

/-- For each output index `k` and packed even index `j`, precompute the sign for the
    contribution coming from `i = k ^^^ mask(j)`.

    Layout: `sign[(k*sizeEven)+j]`. -/
private def evenRightOutSignFromTable {n : ℕ} (table : SignTable n) : Array Int8 :=
  let sizeEven := 2 ^ (n - 1)
  let sizeFull := 2 ^ n
  let masks := evenMasksCached n
  Array.ofFn (n := sizeFull * sizeEven) fun idx =>
    let k := idx / sizeEven
    let j := idx % sizeEven
    let mj := masks.getD j 0
    let i := k ^^^ mj
    table.lookup i mj

private def evenRightOutSignR2 : Array Int8 := evenRightOutSignFromTable R2SignTable
private def evenRightOutSignR3 : Array Int8 := evenRightOutSignFromTable R3SignTable
private def evenRightOutSignR4 : Array Int8 := evenRightOutSignFromTable R4SignTable
private def evenRightOutSignSTA : Array Int8 := evenRightOutSignFromTable STASignTable
private def evenRightOutSignPGA3 : Array Int8 := evenRightOutSignFromTable PGA3SignTable
private def evenRightOutSignCGA3 : Array Int8 := evenRightOutSignFromTable CGA3SignTable

/-- Cached `RightAtIndices` sign table in output-major layout for canonical signatures. -/
@[inline] def evenRightOutSignCached (s : Signature n) : Option (Array Int8) :=
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

/-- Packed index → full blade mask. -/
@[inline]
private def packedToMask (i : Fin (2 ^ (n - 1))) : Nat :=
  (evenMasksCached n).getD i.val 0

/-- Full mask → packed index (assumes mask is even). -/
@[inline]
private def maskToPacked (m : Nat) : Fin (2 ^ (n - 1)) :=
  let k := (evenIndexMapCached n).getD m 0
  ⟨k, by sorry_proof⟩

end Kernel

open Kernel

/-! ### Conversions -/

/-- Convert packed even multivector to dense multivector. -/
def toMultivector (e : EvenMV sig F) : Multivector sig F :=
  let masks := evenMasksCached n
  let map := evenIndexMapCached n
  ⟨fun i =>
    let m := i.val
    if grade (BitVec.ofNat n m) % 2 = 0 then
      let k := map.getD m 0
      e.coeffs ⟨k, by sorry_proof⟩
    else 0⟩

/-- Pack the even part of a dense multivector. -/
def ofMultivectorEven (m : Multivector sig F) : EvenMV sig F :=
  let masks := evenMasksCached n
  ⟨fun i =>
    let mask := masks.getD i.val 0
    m.coeffs ⟨mask, by sorry_proof⟩⟩

/-! ### Involutions on packed storage -/

/-- Reverse (dagger) on even multivectors. Preserves parity. -/
def reverse (e : EvenMV sig F) : EvenMV sig F :=
  let masks := evenMasksCached n
  ⟨fun i =>
    let mask := masks.getD i.val 0
    let g := grade (BitVec.ofNat n mask)
    if (g * (g - 1) / 2) % 2 = 0 then e.coeffs i else -e.coeffs i⟩

postfix:max "†ᵉ" => EvenMV.reverse

/-! ### Packed products -/

/-- Even × even geometric product in packed space.
    Complexity: O(4^(n-1)). Result stays even, so we write directly to packed output. -/
@[specialize]
def geometricProduct (a b : EvenMV sig F) : EvenMV sig F :=
  let sizeEven := 2 ^ (n - 1)
  let idxEven := evenPackedIdxCached n
  match evenMulSignCached (sig := sig) (n := n) sig with
  | some signs =>
      -- Fast kernel: (packed_i, packed_j) ↦ (packed_k, sign) is precomputed.
      let mulIdx := evenMulIdxCached n
      let resultArray : Array F := Id.run do
        let mut out : Array F := Array.replicate sizeEven (0 : F)
        for i in idxEven do
          let ai := a.coeffs ⟨i, by sorry_proof⟩
          let base := i * sizeEven
          for j in idxEven do
            let sign := signs.getD (base + j) 0
            if sign != 0 then
              let k := mulIdx.getD (base + j) 0
              let bj := b.coeffs ⟨j, by sorry_proof⟩
              let coeff := ai * bj
              let contrib := if sign < 0 then -coeff else coeff
              let old := out.getD k 0
              out := out.set! k (old + contrib)
        return out
      ⟨fun k => resultArray.getD k.val 0⟩
  | none =>
      -- Generic fallback: use full sign table when available; else compute signs on the fly.
      let masks := evenMasksCached n
      let map := evenIndexMapCached n
      let table? : Option (SignTable n) := Grassmann.cachedSignTable (n := n) sig
      let resultArray : Array F := Id.run do
        let mut out : Array F := Array.replicate sizeEven (0 : F)
        match table? with
        | some table =>
            for i in idxEven do
              let mi := masks.getD i 0
              let ai := a.coeffs ⟨i, by sorry_proof⟩
              for j in idxEven do
                let mj := masks.getD j 0
                let sign := table.lookup mi mj
                if sign != 0 then
                  let resMask := mi ^^^ mj
                  let k := map.getD resMask 0
                  let bj := b.coeffs ⟨j, by sorry_proof⟩
                  let coeff := ai * bj
                  let contrib := if sign < 0 then -coeff else coeff
                  let old := out.getD k 0
                  out := out.set! k (old + contrib)
        | none =>
            for i in idxEven do
              let mi := masks.getD i 0
              let bi : Blade sig := ⟨BitVec.ofNat n mi⟩
              let ai := a.coeffs ⟨i, by sorry_proof⟩
              for j in idxEven do
                let mj := masks.getD j 0
                let bj : Blade sig := ⟨BitVec.ofNat n mj⟩
                let sign := geometricSign sig bi bj
                if sign != 0 then
                  let resMask := mi ^^^ mj
                  let k := map.getD resMask 0
                  let bjCoeff := b.coeffs ⟨j, by sorry_proof⟩
                  let coeff := ai * bjCoeff
                  let contrib := if sign < 0 then -coeff else coeff
                  let old := out.getD k 0
                  out := out.set! k (old + contrib)
        return out
      ⟨fun k => resultArray.getD k.val 0⟩

instance : Mul (EvenMV sig F) := ⟨geometricProduct⟩

/-- Left multiply dense multivector by packed even element. -/
@[specialize]
def geometricProductLeft (a : EvenMV sig F) (b : Multivector sig F) :
    Multivector sig F :=
  let sizeFull := 2 ^ n
  let idxEven := evenPackedIdxCached n
  let idxAll := fullIdxCached n
  let resultArray : Array F :=
    match evenLeftMulSignCached (sig := sig) (n := n) sig with
    | some signs =>
        -- Fast kernel for canonical signatures.
        let mulIdx := evenLeftMulIdxCached n
        Id.run do
          let mut out : Array F := Array.replicate sizeFull (0 : F)
          for i in idxEven do
            let ai := a.coeffs ⟨i, by sorry_proof⟩
            let base := i * sizeFull
            for j in idxAll do
              let sign := signs.getD (base + j) 0
              if sign != 0 then
                let resIdx := mulIdx.getD (base + j) 0
                let bj := b.coeffs ⟨j, by sorry_proof⟩
                let coeff := ai * bj
                let contrib := if sign < 0 then -coeff else coeff
                let old := out.getD resIdx 0
                out := out.set! resIdx (old + contrib)
          return out
    | none =>
        -- Generic fallback: use full sign table when available; else compute signs on the fly.
        let masks := evenMasksCached n
        let table? : Option (SignTable n) := Grassmann.cachedSignTable (n := n) sig
        Id.run do
          let mut out : Array F := Array.replicate sizeFull (0 : F)
          match table? with
          | some table =>
              for i in idxEven do
                let mi := masks.getD i 0
                let ai := a.coeffs ⟨i, by sorry_proof⟩
                for j in idxAll do
                  let sign := table.lookup mi j
                  if sign != 0 then
                    let resIdx := mi ^^^ j
                    let bj := b.coeffs ⟨j, by sorry_proof⟩
                    let coeff := ai * bj
                    let contrib := if sign < 0 then -coeff else coeff
                    let old := out.getD resIdx 0
                    out := out.set! resIdx (old + contrib)
          | none =>
              for i in idxEven do
                let mi := masks.getD i 0
                let bi : Blade sig := ⟨BitVec.ofNat n mi⟩
                let ai := a.coeffs ⟨i, by sorry_proof⟩
                for j in idxAll do
                  let bj : Blade sig := ⟨BitVec.ofNat n j⟩
                  let sign := geometricSign sig bi bj
                  if sign != 0 then
                    let resIdx := mi ^^^ j
                    let bjCoeff := b.coeffs ⟨j, by sorry_proof⟩
                    let coeff := ai * bjCoeff
                    let contrib := if sign < 0 then -coeff else coeff
                    let old := out.getD resIdx 0
                    out := out.set! resIdx (old + contrib)
          return out
  ⟨fun k => resultArray.getD k.val 0⟩

/-- Right multiply dense multivector by packed even element. -/
@[specialize]
def geometricProductRight (a : Multivector sig F) (b : EvenMV sig F) :
    Multivector sig F :=
  let sizeFull := 2 ^ n
  let idxEven := evenPackedIdxCached n
  let idxAll := fullIdxCached n
  let resultArray : Array F :=
    match evenRightMulSignCached (sig := sig) (n := n) sig with
    | some signs =>
        -- Fast kernel for canonical signatures.
        let mulIdx := evenRightMulIdxCached n
        let sizeEven := 2 ^ (n - 1)
        Id.run do
          let mut out : Array F := Array.replicate sizeFull (0 : F)
          for i in idxAll do
            let ai := a.coeffs ⟨i, by sorry_proof⟩
            let base := i * sizeEven
            for j in idxEven do
              let sign := signs.getD (base + j) 0
              if sign != 0 then
                let resIdx := mulIdx.getD (base + j) 0
                let bj := b.coeffs ⟨j, by sorry_proof⟩
                let coeff := ai * bj
                let contrib := if sign < 0 then -coeff else coeff
                let old := out.getD resIdx 0
                out := out.set! resIdx (old + contrib)
          return out
    | none =>
        -- Generic fallback: use full sign table when available; else compute signs on the fly.
        let masks := evenMasksCached n
        let table? : Option (SignTable n) := Grassmann.cachedSignTable (n := n) sig
        Id.run do
          let mut out : Array F := Array.replicate sizeFull (0 : F)
          match table? with
          | some table =>
              for i in idxAll do
                let ai := a.coeffs ⟨i, by sorry_proof⟩
                for j in idxEven do
                  let mj := masks.getD j 0
                  let sign := table.lookup i mj
                  if sign != 0 then
                    let resIdx := i ^^^ mj
                    let bj := b.coeffs ⟨j, by sorry_proof⟩
                    let coeff := ai * bj
                    let contrib := if sign < 0 then -coeff else coeff
                    let old := out.getD resIdx 0
                    out := out.set! resIdx (old + contrib)
          | none =>
              for i in idxAll do
                let bi : Blade sig := ⟨BitVec.ofNat n i⟩
                let ai := a.coeffs ⟨i, by sorry_proof⟩
                for j in idxEven do
                  let mj := masks.getD j 0
                  let bj : Blade sig := ⟨BitVec.ofNat n mj⟩
                  let sign := geometricSign sig bi bj
                  if sign != 0 then
                    let resIdx := i ^^^ mj
                    let bjCoeff := b.coeffs ⟨j, by sorry_proof⟩
                    let coeff := ai * bjCoeff
                    let contrib := if sign < 0 then -coeff else coeff
                    let old := out.getD resIdx 0
                    out := out.set! resIdx (old + contrib)
          return out
  ⟨fun k => resultArray.getD k.val 0⟩

/-- Sandwich product with packed even rotor: R * x * R†. -/
@[inline]
def sandwich (R : EvenMV sig F) (x : Multivector sig F) : Multivector sig F :=
  let Rrev := R†ᵉ
  let Rx := geometricProductLeft R x
  geometricProductRight Rx Rrev

/-! ### Sparse sandwich specializations -/

/-- Left multiply dense multivector by packed even element,
    iterating only over the provided right indices. -/
@[specialize]
def geometricProductLeftSparse (a : EvenMV sig F) (b : Multivector sig F)
    (bIdx : Array (Fin (2 ^ n))) : Multivector sig F :=
  let sizeFull := 2 ^ n
  let idxEven := evenPackedIdxCached n
  let resultArray : Array F :=
    match evenLeftMulSignCached (sig := sig) (n := n) sig with
    | some signs =>
        -- Fast kernel for canonical signatures.
        let mulIdx := evenLeftMulIdxCached n
        Id.run do
          let mut out : Array F := Array.replicate sizeFull (0 : F)
          for i in idxEven do
            let ai := a.coeffs ⟨i, by sorry_proof⟩
            let base := i * sizeFull
            for j in bIdx do
              let jv := j.val
              let sign := signs.getD (base + jv) 0
              if sign != 0 then
                let resIdx := mulIdx.getD (base + jv) 0
                let bj := b.coeffs j
                let coeff := ai * bj
                let contrib := if sign < 0 then -coeff else coeff
                let old := out.getD resIdx 0
                out := out.set! resIdx (old + contrib)
          return out
    | none =>
        -- Generic fallback: use full sign table when available; else compute signs on the fly.
        let masks := evenMasksCached n
        let table? : Option (SignTable n) := Grassmann.cachedSignTable (n := n) sig
        Id.run do
          let mut out : Array F := Array.replicate sizeFull (0 : F)
          match table? with
          | some table =>
              for i in idxEven do
                let mi := masks.getD i 0
                let ai := a.coeffs ⟨i, by sorry_proof⟩
                for j in bIdx do
                  let sign := table.lookup mi j.val
                  if sign != 0 then
                    let resIdx := mi ^^^ j.val
                    let bj := b.coeffs j
                    let coeff := ai * bj
                    let contrib := if sign < 0 then -coeff else coeff
                    let old := out.getD resIdx 0
                    out := out.set! resIdx (old + contrib)
          | none =>
              for i in idxEven do
                let mi := masks.getD i 0
                let bi : Blade sig := ⟨BitVec.ofNat n mi⟩
                let ai := a.coeffs ⟨i, by sorry_proof⟩
                for j in bIdx do
                  let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
                  let sign := geometricSign sig bi bj
                  if sign != 0 then
                    let resIdx := mi ^^^ j.val
                    let bjCoeff := b.coeffs j
                    let coeff := ai * bjCoeff
                    let contrib := if sign < 0 then -coeff else coeff
                    let old := out.getD resIdx 0
                    out := out.set! resIdx (old + contrib)
          return out
  ⟨fun k => resultArray.getD k.val 0⟩

/-- Right multiply dense multivector by packed even element,
    iterating only over the provided left indices. -/
@[specialize]
def geometricProductRightSparse (a : Multivector sig F) (aIdx : Array (Fin (2 ^ n)))
    (b : EvenMV sig F) : Multivector sig F :=
  let sizeFull := 2 ^ n
  let idxEven := evenPackedIdxCached n
  let resultArray : Array F :=
    match evenRightMulSignCached (sig := sig) (n := n) sig with
    | some signs =>
        -- Fast kernel for canonical signatures.
        let mulIdx := evenRightMulIdxCached n
        let sizeEven := 2 ^ (n - 1)
        Id.run do
          let mut out : Array F := Array.replicate sizeFull (0 : F)
          for i in aIdx do
            let ai := a.coeffs i
            let base := i.val * sizeEven
            for j in idxEven do
              let sign := signs.getD (base + j) 0
              if sign != 0 then
                let resIdx := mulIdx.getD (base + j) 0
                let bj := b.coeffs ⟨j, by sorry_proof⟩
                let coeff := ai * bj
                let contrib := if sign < 0 then -coeff else coeff
                let old := out.getD resIdx 0
                out := out.set! resIdx (old + contrib)
          return out
    | none =>
        -- Generic fallback: use full sign table when available; else compute signs on the fly.
        let masks := evenMasksCached n
        let table? : Option (SignTable n) := Grassmann.cachedSignTable (n := n) sig
        Id.run do
          let mut out : Array F := Array.replicate sizeFull (0 : F)
          match table? with
          | some table =>
              for i in aIdx do
                let ai := a.coeffs i
                for j in idxEven do
                  let mj := masks.getD j 0
                  let sign := table.lookup i.val mj
                  if sign != 0 then
                    let resIdx := i.val ^^^ mj
                    let bj := b.coeffs ⟨j, by sorry_proof⟩
                    let coeff := ai * bj
                    let contrib := if sign < 0 then -coeff else coeff
                    let old := out.getD resIdx 0
                    out := out.set! resIdx (old + contrib)
          | none =>
              for i in aIdx do
                let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
                let ai := a.coeffs i
                for j in idxEven do
                  let mj := masks.getD j 0
                  let bj : Blade sig := ⟨BitVec.ofNat n mj⟩
                  let sign := geometricSign sig bi bj
                  if sign != 0 then
                    let resIdx := i.val ^^^ mj
                    let bjCoeff := b.coeffs ⟨j, by sorry_proof⟩
                    let coeff := ai * bjCoeff
                    let contrib := if sign < 0 then -coeff else coeff
                    let old := out.getD resIdx 0
                    out := out.set! resIdx (old + contrib)
          return out
  ⟨fun k => resultArray.getD k.val 0⟩

/-- Right-multiply by a packed even element, computing only the requested output indices.

    This is useful when the *consumer* only needs a restricted-grade output
    (e.g. motors acting on PGA points, where we only care about the grade-3 part).

    The returned multivector has all non-requested coefficients set to zero. -/
@[specialize]
def geometricProductRightAtIndices (a : Multivector sig F) (b : EvenMV sig F)
    (outIdx : Array (Fin (2 ^ n))) : Multivector sig F :=
  let sizeFull := 2 ^ n
  let sizeEven := 2 ^ (n - 1)
  let idxEven := evenPackedIdxCached n
  let masks := evenMasksCached n
  let resultArray : Array F :=
    match evenRightMulSignCached (sig := sig) (n := n) sig with
    | some signs =>
        -- Fast kernel for canonical signatures.
        match evenRightOutSignCached (sig := sig) (n := n) sig with
        | some outSigns =>
            let invIdx := evenRightOutLeftIdxCached n
            Id.run do
              let mut out : Array F := Array.replicate sizeFull (0 : F)
              for k in outIdx do
                let base := k.val * sizeEven
                let mut acc : F := 0
                for j in idxEven do
                  let sign := outSigns.getD (base + j) 0
                  if sign != 0 then
                    let i := invIdx.getD (base + j) 0
                    let ai := a.coeffs ⟨i, by sorry_proof⟩
                    let bj := b.coeffs ⟨j, by sorry_proof⟩
                    let coeff := ai * bj
                    let contrib := if sign < 0 then -coeff else coeff
                    acc := acc + contrib
                out := out.set! k.val acc
              return out
        | none =>
            -- Fall back to the generic output-major computation when no cached kernel exists.
            Id.run do
              let mut out : Array F := Array.replicate sizeFull (0 : F)
              for k in outIdx do
                let mut acc : F := 0
                for j in idxEven do
                  let mj := masks.getD j 0
                  let i := k.val ^^^ mj
                  let sign := signs.getD (i * sizeEven + j) 0
                  if sign != 0 then
                    let ai := a.coeffs ⟨i, by sorry_proof⟩
                    let bj := b.coeffs ⟨j, by sorry_proof⟩
                    let coeff := ai * bj
                    let contrib := if sign < 0 then -coeff else coeff
                    acc := acc + contrib
                out := out.set! k.val acc
              return out
    | none =>
        -- Generic fallback: use full sign table when available; else compute signs on the fly.
        let table? : Option (SignTable n) := Grassmann.cachedSignTable (n := n) sig
        Id.run do
          let mut out : Array F := Array.replicate sizeFull (0 : F)
          match table? with
          | some table =>
              for k in outIdx do
                let mut acc : F := 0
                for j in idxEven do
                  let mj := masks.getD j 0
                  let i := k.val ^^^ mj
                  let sign := table.lookup i mj
                  if sign != 0 then
                    let ai := a.coeffs ⟨i, by sorry_proof⟩
                    let bj := b.coeffs ⟨j, by sorry_proof⟩
                    let coeff := ai * bj
                    let contrib := if sign < 0 then -coeff else coeff
                    acc := acc + contrib
                out := out.set! k.val acc
          | none =>
              for k in outIdx do
                let mut acc : F := 0
                for j in idxEven do
                  let mj := masks.getD j 0
                  let i := k.val ^^^ mj
                  let bi : Blade sig := ⟨BitVec.ofNat n i⟩
                  let bj : Blade sig := ⟨BitVec.ofNat n mj⟩
                  let sign := geometricSign sig bi bj
                  if sign != 0 then
                    let ai := a.coeffs ⟨i, by sorry_proof⟩
                    let bjCoeff := b.coeffs ⟨j, by sorry_proof⟩
                    let coeff := ai * bjCoeff
                    let contrib := if sign < 0 then -coeff else coeff
                    acc := acc + contrib
                out := out.set! k.val acc
          return out
  ⟨fun k => resultArray.getD k.val 0⟩

/-- Faster sandwich product specialized by grade sets.

    This is the generalization of `sandwichVectorFast`: you provide an *upper bound*
    on the grades present in `x` (`xGs`) and in the intermediate product `R * x`
    (`midGs`), and we use cached grade-set index tables to iterate only over those
    blades.

    Correctness assumes `x` actually respects `xGs` (and `R*x` respects `midGs`).
    For arbitrary multivectors, use `sandwich`. -/
@[inline]
def sandwichGradeSetFast (R : EvenMV sig F) (x : Multivector sig F)
    (xGs midGs : GradeSet) : Multivector sig F :=
  let Rrev := R†ᵉ
  let xIdx : Array (Fin (2 ^ n)) := gradeSetIndicesFastArray n xGs
  let midIdx : Array (Fin (2 ^ n)) := gradeSetIndicesFastArray n midGs
  let Rx := geometricProductLeftSparse R x xIdx
  geometricProductRightSparse Rx midIdx Rrev

/-- Sandwich product specialized by grade sets, computing only the requested output grades.

    This keeps the *work* of the second multiplication proportional to the number of
    requested output blades, instead of iterating all `midGs × even` pairs.

    This is a big win for cases like PGA points/planes where the output grade is known. -/
@[inline]
def sandwichGradeSetFastOut (R : EvenMV sig F) (x : Multivector sig F)
    (xGs midGs outGs : GradeSet) : Multivector sig F :=
  let Rrev := R†ᵉ
  let xIdx : Array (Fin (2 ^ n)) := gradeSetIndicesFastArray n xGs
  let outIdx : Array (Fin (2 ^ n)) := gradeSetIndicesFastArray n outGs
  let Rx := geometricProductLeftSparse R x xIdx
  -- We currently don't need `midGs` at runtime because `Rx` is already sparse-by-construction,
  -- but we keep it in the API so call sites document the expected intermediate grades.
  let _ := midGs
  geometricProductRightAtIndices (sig := sig) (n := n) (F := F) Rx Rrev outIdx

/-- Faster sandwich product specialized for vectors.
    Uses grade-set indices: `even × vector` gives odd, then `odd × even` gives odd.

    This matches the sparse-pair counts of `R3Fast.sandwichFast`, but works for any `n`.
    Correctness assumes `x` is actually a vector (only grade 1 coefficients). -/
@[inline]
def sandwichVectorFast (R : EvenMV sig F) (x : Multivector sig F) : Multivector sig F :=
  sandwichGradeSetFast (sig := sig) (n := n) (F := F) R x GradeSet.vector (GradeSet.odd n)

/-- Even faster sandwich product specialized for *rotating vectors*.

    This computes only the grade‑1 output of `R * x * R†`.

    Assumes:
    - `x` is a vector (grade 1)
    - `R` is a *versor* (rotor/motor), so the sandwich preserves grade.

    For arbitrary even elements (that may introduce a pseudoscalar part), use
    `sandwichVectorFast`. -/
@[inline]
def sandwichVectorGrade1Fast (R : EvenMV sig F) (x : Multivector sig F) : Multivector sig F :=
  sandwichGradeSetFastOut (sig := sig) (n := n) (F := F)
    R x GradeSet.vector (GradeSet.odd n) GradeSet.vector

end EvenMV

end Grassmann

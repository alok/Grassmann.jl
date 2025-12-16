/-
  Grassmann/EvenMVDA.lean - Packed even multivectors backed by `DataArray` (Float)

  This is the numerics backend for rotors/motors/spinors in small algebras
  (R3/PGA3/CGA3) where we care about:
  - contiguous coefficient storage
  - minimizing closure allocation (vs `Fin → F`)
  - enabling destructive `set!` updates when buffers are exclusive

  It reuses the same precomputed kernel tables as `EvenMV` via `EvenMV.Kernel`.
-/
import Grassmann.DataArray
import Grassmann.MultivectorDA
import Grassmann.EvenMV
import Grassmann.BladeIndex
import Grassmann.GradeSet
import Grassmann.Proof

open Grassmann.Proof

namespace Grassmann

variable {n : ℕ} {sig : Signature n}

/-- Packed even multivector over `Float` with coefficients stored in a `DataArray`.

Invariant (by convention): `coeffs.size = 2^(n-1)`. -/
structure EvenMVDA (sig : Signature n) where
  coeffs : DataArray

namespace EvenMVDA

@[inline] private def sizeEven (n : Nat) : Nat := 2 ^ (n - 1)
@[inline] private def sizeFull (n : Nat) : Nat := 2 ^ n

/-! ### Constructors -/

@[inline] def zero : EvenMVDA sig :=
  ⟨DataArray.zeros (sizeEven n)⟩

@[inline] def scalar (x : Float) : EvenMVDA sig :=
  ⟨(DataArray.zeros (sizeEven n)).set! 0 x⟩

@[inline] def one : EvenMVDA sig := scalar 1.0

@[inline] def scalarPart (e : EvenMVDA sig) : Float :=
  e.coeffs.get! 0

instance : Zero (EvenMVDA sig) := ⟨zero⟩
instance : One (EvenMVDA sig) := ⟨one⟩

/-! ### Conversions -/

/-- Convert to the proof-friendly packed representation (`Fin → Float`). -/
@[inline] def toEvenMV (e : EvenMVDA sig) : EvenMV sig Float :=
  ⟨fun i => e.coeffs.get! i.val⟩

/-- Convert from the proof-friendly packed representation. -/
@[inline] def ofEvenMV (e : EvenMV sig Float) : EvenMVDA sig :=
  let arr : Array Float := Array.ofFn (n := 2 ^ (n - 1)) fun i => e.coeffs i
  ⟨DataArray.ofArray arr⟩

/-- Pack the even part of a dense multivector (`Multivector`). -/
@[inline] def ofMultivectorEven (m : Multivector sig Float) : EvenMVDA sig :=
  let masks := EvenMV.Kernel.evenMasksCached n
  let arr : Array Float := Array.ofFn (n := 2 ^ (n - 1)) fun i =>
    let mask := masks.getD i.val 0
    m.coeffs ⟨mask, by sorry_proof⟩
  ⟨DataArray.ofArray arr⟩

/-- Pack the even part of a dense `DataArray` multivector. -/
@[inline] def ofMultivectorDAEven (m : MultivectorDA sig) : EvenMVDA sig :=
  let masks := EvenMV.Kernel.evenMasksCached n
  let arr : Array Float := Array.ofFn (n := 2 ^ (n - 1)) fun i =>
    let mask := masks.getD i.val 0
    m.coeffs.get! mask
  ⟨DataArray.ofArray arr⟩

/-- Convert to a dense `DataArray` multivector (odd coefficients are zero). -/
def toMultivectorDA (e : EvenMVDA sig) : MultivectorDA sig := Id.run do
  let masks := EvenMV.Kernel.evenMasksCached n
  let idxEven := EvenMV.Kernel.evenPackedIdxCached n
  let mut out : DataArray := DataArray.zeros (sizeFull n)
  for i in idxEven do
    let mask := masks.getD i 0
    out := out.set! mask (e.coeffs.get! i)
  return ⟨out⟩

/-- Convert to the dense proof-friendly multivector (`Fin → Float`). -/
@[inline] def toMultivector (e : EvenMVDA sig) : Multivector sig Float :=
  e.toMultivectorDA.toMultivector

instance : Coe (EvenMVDA sig) (Multivector sig Float) := ⟨toMultivector⟩

/-! ### Involutions -/

/-- Reverse (dagger) on packed storage. -/
def reverse (e : EvenMVDA sig) : EvenMVDA sig := Id.run do
  let masks := EvenMV.Kernel.evenMasksCached n
  let idxEven := EvenMV.Kernel.evenPackedIdxCached n
  let mut out : DataArray := DataArray.zeros (sizeEven n)
  for i in idxEven do
    let mask := masks.getD i 0
    let g := grade (BitVec.ofNat n mask)
    let c := e.coeffs.get! i
    let c' := if (g * (g - 1) / 2) % 2 = 0 then c else -c
    out := out.set! i c'
  return ⟨out⟩

postfix:max "†ᵈ" => EvenMVDA.reverse

/-! ### Packed products (Float/DataArray backend) -/

/-- Even × even geometric product in packed space. -/
def geometricProduct (a b : EvenMVDA sig) : EvenMVDA sig := Id.run do
  let idxEven := EvenMV.Kernel.evenPackedIdxCached n
  match EvenMV.Kernel.evenMulSignCached (sig := sig) (n := n) sig with
  | some signs =>
      let mulIdx := EvenMV.Kernel.evenMulIdxCached n
      let mut out : DataArray := DataArray.zeros (sizeEven n)
      for i in idxEven do
        let ai := a.coeffs.get! i
        let base := i * (sizeEven n)
        for j in idxEven do
          let sign := signs.getD (base + j) 0
          if sign != 0 then
            let k := mulIdx.getD (base + j) 0
            let bj := b.coeffs.get! j
            let coeff := ai * bj
            let contrib := if sign < 0 then -coeff else coeff
            let old := out.get! k
            out := out.set! k (old + contrib)
      return ⟨out⟩
  | none =>
      -- Fallback: use the full sign table when cached; otherwise compute signs on the fly.
      let masks := EvenMV.Kernel.evenMasksCached n
      let map := EvenMV.Kernel.evenIndexMapCached n
      let table? : Option (SignTable n) := Grassmann.cachedSignTable (n := n) sig
      let mut out : DataArray := DataArray.zeros (sizeEven n)
      match table? with
      | some table =>
          for i in idxEven do
            let mi := masks.getD i 0
            let ai := a.coeffs.get! i
            for j in idxEven do
              let mj := masks.getD j 0
              let sign := table.lookup mi mj
              if sign != 0 then
                let resMask := mi ^^^ mj
                let k := map.getD resMask 0
                let bj := b.coeffs.get! j
                let coeff := ai * bj
                let contrib := if sign < 0 then -coeff else coeff
                let old := out.get! k
                out := out.set! k (old + contrib)
      | none =>
          for i in idxEven do
            let mi := masks.getD i 0
            let bi : Blade sig := ⟨BitVec.ofNat n mi⟩
            let ai := a.coeffs.get! i
            for j in idxEven do
              let mj := masks.getD j 0
              let bjBlade : Blade sig := ⟨BitVec.ofNat n mj⟩
              let sign := geometricSign sig bi bjBlade
              if sign != 0 then
                let resMask := mi ^^^ mj
                let k := map.getD resMask 0
                let bj := b.coeffs.get! j
                let coeff := ai * bj
                let contrib := if sign < 0 then -coeff else coeff
                let old := out.get! k
                out := out.set! k (old + contrib)
      return ⟨out⟩

instance : Mul (EvenMVDA sig) := ⟨geometricProduct⟩

/-! ### Dense products (even × full) -/

/-- Left multiply a dense `DataArray` multivector by a packed even element. -/
def geometricProductLeftSparse (a : EvenMVDA sig) (b : MultivectorDA sig)
    (bIdx : Array (Fin (2 ^ n))) : MultivectorDA sig := Id.run do
  let idxEven := EvenMV.Kernel.evenPackedIdxCached n
  let mut out : DataArray := DataArray.zeros (sizeFull n)
  match EvenMV.Kernel.evenLeftMulSignCached (sig := sig) (n := n) sig with
  | some signs =>
      let mulIdx := EvenMV.Kernel.evenLeftMulIdxCached n
      for i in idxEven do
        let ai := a.coeffs.get! i
        let base := i * (sizeFull n)
        for j in bIdx do
          let jv := j.val
          let sign := signs.getD (base + jv) 0
          if sign != 0 then
            let resIdx := mulIdx.getD (base + jv) 0
            let bj := b.coeffs.get! jv
            let coeff := ai * bj
            let contrib := if sign < 0 then -coeff else coeff
            let old := out.get! resIdx
            out := out.set! resIdx (old + contrib)
      return ⟨out⟩
  | none =>
      let masks := EvenMV.Kernel.evenMasksCached n
      let table? : Option (SignTable n) := Grassmann.cachedSignTable (n := n) sig
      match table? with
      | some table =>
          for i in idxEven do
            let mi := masks.getD i 0
            let ai := a.coeffs.get! i
            for j in bIdx do
              let sign := table.lookup mi j.val
              if sign != 0 then
                let resIdx := mi ^^^ j.val
                let bj := b.coeffs.get! j.val
                let coeff := ai * bj
                let contrib := if sign < 0 then -coeff else coeff
                let old := out.get! resIdx
                out := out.set! resIdx (old + contrib)
      | none =>
          for i in idxEven do
            let mi := masks.getD i 0
            let bi : Blade sig := ⟨BitVec.ofNat n mi⟩
            let ai := a.coeffs.get! i
            for j in bIdx do
              let bjBlade : Blade sig := ⟨BitVec.ofNat n j.val⟩
              let sign := geometricSign sig bi bjBlade
              if sign != 0 then
                let resIdx := mi ^^^ j.val
                let bj := b.coeffs.get! j.val
                let coeff := ai * bj
                let contrib := if sign < 0 then -coeff else coeff
                let old := out.get! resIdx
                out := out.set! resIdx (old + contrib)
      return ⟨out⟩

/-- Right multiply a dense `DataArray` multivector by a packed even element,
    computing only the requested output indices (others are zero). -/
def geometricProductRightAtIndices (a : MultivectorDA sig) (b : EvenMVDA sig)
    (outIdx : Array (Fin (2 ^ n))) : MultivectorDA sig := Id.run do
  let sizeEven := 2 ^ (n - 1)
  let idxEven := EvenMV.Kernel.evenPackedIdxCached n
  let masks := EvenMV.Kernel.evenMasksCached n
  let mut out : DataArray := DataArray.zeros (sizeFull n)
  match EvenMV.Kernel.evenRightMulSignCached (sig := sig) (n := n) sig with
  | some signs =>
      match EvenMV.Kernel.evenRightOutSignCached (sig := sig) (n := n) sig with
      | some outSigns =>
          let invIdx := EvenMV.Kernel.evenRightOutLeftIdxCached n
          for k in outIdx do
            let base := k.val * sizeEven
            let mut acc : Float := 0.0
            for j in idxEven do
              let sign := outSigns.getD (base + j) 0
              if sign != 0 then
                let i := invIdx.getD (base + j) 0
                let ai := a.coeffs.get! i
                let bj := b.coeffs.get! j
                let coeff := ai * bj
                let contrib := if sign < 0 then -coeff else coeff
                acc := acc + contrib
            out := out.set! k.val acc
          return ⟨out⟩
      | none =>
          for k in outIdx do
            let mut acc : Float := 0.0
            for j in idxEven do
              let mj := masks.getD j 0
              let i := k.val ^^^ mj
              let sign := signs.getD (i * sizeEven + j) 0
              if sign != 0 then
                let ai := a.coeffs.get! i
                let bj := b.coeffs.get! j
                let coeff := ai * bj
                let contrib := if sign < 0 then -coeff else coeff
                acc := acc + contrib
            out := out.set! k.val acc
          return ⟨out⟩
  | none =>
      let table? : Option (SignTable n) := Grassmann.cachedSignTable (n := n) sig
      match table? with
      | some table =>
          for k in outIdx do
            let mut acc : Float := 0.0
            for j in idxEven do
              let mj := masks.getD j 0
              let i := k.val ^^^ mj
              let sign := table.lookup i mj
              if sign != 0 then
                let ai := a.coeffs.get! i
                let bj := b.coeffs.get! j
                let coeff := ai * bj
                let contrib := if sign < 0 then -coeff else coeff
                acc := acc + contrib
            out := out.set! k.val acc
          return ⟨out⟩
      | none =>
          for k in outIdx do
            let mut acc : Float := 0.0
            for j in idxEven do
              let mj := masks.getD j 0
              let i := k.val ^^^ mj
              let bi : Blade sig := ⟨BitVec.ofNat n i⟩
              let bjBlade : Blade sig := ⟨BitVec.ofNat n mj⟩
              let sign := geometricSign sig bi bjBlade
              if sign != 0 then
                let ai := a.coeffs.get! i
                let bj := b.coeffs.get! j
                let coeff := ai * bj
                let contrib := if sign < 0 then -coeff else coeff
                acc := acc + contrib
            out := out.set! k.val acc
          return ⟨out⟩

/-! ### Sandwich products -/

/-- Fast sandwich specialized by grade sets (full output). -/
@[inline]
def sandwichGradeSetFast (R : EvenMVDA sig) (x : MultivectorDA sig)
    (xGs midGs : GradeSet) : MultivectorDA sig :=
  let Rrev := R†ᵈ
  let xIdx : Array (Fin (2 ^ n)) := gradeSetIndicesFastArray n xGs
  let midIdx : Array (Fin (2 ^ n)) := gradeSetIndicesFastArray n midGs
  let Rx := geometricProductLeftSparse (sig := sig) (n := n) R x xIdx
  -- No output restriction here; compute full then sparsify by the index list.
  let full := (EvenMVDA.geometricProductRightAtIndices (sig := sig) (n := n) (a := Rx) (b := Rrev)
    (outIdx := Array.ofFn (n := 2 ^ n) fun i => i))
  -- Keep only the grade-set upper bound (others are already 0 by construction for small midGs).
  let _ := midIdx
  full

/-- Fast sandwich specialized by grade sets, computing only requested output grades. -/
@[inline]
def sandwichGradeSetFastOut (R : EvenMVDA sig) (x : MultivectorDA sig)
    (xGs midGs outGs : GradeSet) : MultivectorDA sig :=
  let Rrev := R†ᵈ
  let xIdx : Array (Fin (2 ^ n)) := gradeSetIndicesFastArray n xGs
  let outIdx : Array (Fin (2 ^ n)) := gradeSetIndicesFastArray n outGs
  let Rx := geometricProductLeftSparse (sig := sig) (n := n) R x xIdx
  let _ := midGs
  geometricProductRightAtIndices (sig := sig) (n := n) Rx Rrev outIdx

/-- Fast sandwich specialized for vectors (computes only grade‑1 output). -/
@[inline]
def sandwichVectorFast (R : EvenMVDA sig) (x : MultivectorDA sig) : MultivectorDA sig :=
  sandwichGradeSetFastOut (sig := sig) (n := n) R x GradeSet.vector (GradeSet.odd n) GradeSet.vector

end EvenMVDA

end Grassmann

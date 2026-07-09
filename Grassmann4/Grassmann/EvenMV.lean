/-
  Grassmann/EvenMV.lean - Packed even-grade multivectors (spinors/rotors)

  Motivation:
  - Even elements (grades 0,2,4,...) form the Spin/Pin even subalgebra.
  - Rotors and spinors live here and are performance hot paths.
  - Storing only even blades cuts memory and work in half (2^(n-1) coeffs).

  Design:
  - `EvenMV sig F` stores coefficients only for even-grade basis blades.
  - Enumeration of even blades is by increasing bitmask order.
  - Cached Nat index tables are read through bounds-checked coefficient helpers.
-/
import Grassmann.Multivector
import Grassmann.Parity
import Grassmann.Proof
import Grassmann.BladeIndex
import Grassmann.GradeSet
import Grassmann.SignTables
import Grassmann.EvenKernelTables

open Grassmann.Proof

namespace Grassmann

variable {n : ℕ} {sig : Signature n} {F : Type*} [Ring F]

/-- Packed even multivector: coefficients for even-grade blades only.

**DEPRECATED**: Use `MV sig .even` from `Grassmann.MV` instead. The unified MV type
provides a cleaner API with automatic grade tracking. -/
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

/-! Shared packed-even lookup tables live in the production table module. -/

open EvenKernelTables

@[inline] private def packedCoeffD (e : EvenMV sig F) (i : Nat) : F :=
  if h : i < 2 ^ (n - 1) then
    e.coeffs ⟨i, h⟩
  else
    0

@[inline] private def denseCoeffD (m : Multivector sig F) (i : Nat) : F :=
  if h : i < 2 ^ n then
    m.coeffs ⟨i, h⟩
  else
    0

/-! ### Conversions -/

/-- Convert packed even multivector to dense multivector. -/
def toMultivector (e : EvenMV sig F) : Multivector sig F :=
  let map := evenIndexMapCached n
  ⟨fun i =>
    let m := i.val
    if grade (BitVec.ofNat n m) % 2 = 0 then
      let k := map.getD m 0
      packedCoeffD e k
    else 0⟩

/-- Pack the even part of a dense multivector. -/
def ofMultivectorEven (m : Multivector sig F) : EvenMV sig F :=
  let masks := evenMasksCached n
  ⟨fun i =>
    let mask := masks.getD i.val 0
    denseCoeffD m mask⟩

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
  match evenMulSignCached (n := n) sig with
  | some signs =>
      -- Fast kernel: (packed_i, packed_j) ↦ (packed_k, sign) is precomputed.
      let mulIdx := evenMulIdxCached n
      let resultArray : Array F := Id.run do
        let mut out : Array F := Array.replicate sizeEven (0 : F)
        for i in idxEven do
          let ai := packedCoeffD a i
          let base := i * sizeEven
          for j in idxEven do
            let sign := signs.getD (base + j) 0
            if sign != 0 then
              let k := mulIdx.getD (base + j) 0
              let bj := packedCoeffD b j
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
              let ai := packedCoeffD a i
              for j in idxEven do
                let mj := masks.getD j 0
                let sign := table.lookup mi mj
                if sign != 0 then
                  let resMask := mi ^^^ mj
                  let k := map.getD resMask 0
                  let bj := packedCoeffD b j
                  let coeff := ai * bj
                  let contrib := if sign < 0 then -coeff else coeff
                  let old := out.getD k 0
                  out := out.set! k (old + contrib)
        | none =>
            for i in idxEven do
              let mi := masks.getD i 0
              let bi : Blade sig := ⟨BitVec.ofNat n mi⟩
              let ai := packedCoeffD a i
              for j in idxEven do
                let mj := masks.getD j 0
                let bj : Blade sig := ⟨BitVec.ofNat n mj⟩
                let sign := geometricSign sig bi bj
                if sign != 0 then
                  let resMask := mi ^^^ mj
                  let k := map.getD resMask 0
                  let bjCoeff := packedCoeffD b j
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
    match evenLeftMulSignCached (n := n) sig with
    | some signs =>
        -- Fast kernel for canonical signatures.
        let mulIdx := evenLeftMulIdxCached n
        Id.run do
          let mut out : Array F := Array.replicate sizeFull (0 : F)
          for i in idxEven do
            let ai := packedCoeffD a i
            let base := i * sizeFull
            for j in idxAll do
              let sign := signs.getD (base + j) 0
              if sign != 0 then
                let resIdx := mulIdx.getD (base + j) 0
                let bj := denseCoeffD b j
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
                let ai := packedCoeffD a i
                for j in idxAll do
                  let sign := table.lookup mi j
                  if sign != 0 then
                    let resIdx := mi ^^^ j
                    let bj := denseCoeffD b j
                    let coeff := ai * bj
                    let contrib := if sign < 0 then -coeff else coeff
                    let old := out.getD resIdx 0
                    out := out.set! resIdx (old + contrib)
          | none =>
              for i in idxEven do
                let mi := masks.getD i 0
                let bi : Blade sig := ⟨BitVec.ofNat n mi⟩
                let ai := packedCoeffD a i
                for j in idxAll do
                  let bj : Blade sig := ⟨BitVec.ofNat n j⟩
                  let sign := geometricSign sig bi bj
                  if sign != 0 then
                    let resIdx := mi ^^^ j
                    let bjCoeff := denseCoeffD b j
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
    match evenRightMulSignCached (n := n) sig with
    | some signs =>
        -- Fast kernel for canonical signatures.
        let mulIdx := evenRightMulIdxCached n
        let sizeEven := 2 ^ (n - 1)
        Id.run do
          let mut out : Array F := Array.replicate sizeFull (0 : F)
          for i in idxAll do
            let ai := denseCoeffD a i
            let base := i * sizeEven
            for j in idxEven do
              let sign := signs.getD (base + j) 0
              if sign != 0 then
                let resIdx := mulIdx.getD (base + j) 0
                let bj := packedCoeffD b j
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
                let ai := denseCoeffD a i
                for j in idxEven do
                  let mj := masks.getD j 0
                  let sign := table.lookup i mj
                  if sign != 0 then
                    let resIdx := i ^^^ mj
                    let bj := packedCoeffD b j
                    let coeff := ai * bj
                    let contrib := if sign < 0 then -coeff else coeff
                    let old := out.getD resIdx 0
                    out := out.set! resIdx (old + contrib)
          | none =>
              for i in idxAll do
                let bi : Blade sig := ⟨BitVec.ofNat n i⟩
                let ai := denseCoeffD a i
                for j in idxEven do
                  let mj := masks.getD j 0
                  let bj : Blade sig := ⟨BitVec.ofNat n mj⟩
                  let sign := geometricSign sig bi bj
                  if sign != 0 then
                    let resIdx := i ^^^ mj
                    let bjCoeff := packedCoeffD b j
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
    match evenLeftMulSignCached (n := n) sig with
    | some signs =>
        -- Fast kernel for canonical signatures.
        let mulIdx := evenLeftMulIdxCached n
        Id.run do
          let mut out : Array F := Array.replicate sizeFull (0 : F)
          for i in idxEven do
            let ai := packedCoeffD a i
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
                let ai := packedCoeffD a i
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
                let ai := packedCoeffD a i
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
    match evenRightMulSignCached (n := n) sig with
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
                let bj := packedCoeffD b j
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
                    let bj := packedCoeffD b j
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
                    let bjCoeff := packedCoeffD b j
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
    match evenRightMulSignCached (n := n) sig with
    | some signs =>
        -- Fast kernel for canonical signatures.
        match evenRightOutSignCached (n := n) sig with
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
                    let ai := denseCoeffD a i
                    let bj := packedCoeffD b j
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
                    let ai := denseCoeffD a i
                    let bj := packedCoeffD b j
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
                    let ai := denseCoeffD a i
                    let bj := packedCoeffD b j
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
                    let ai := denseCoeffD a i
                    let bjCoeff := packedCoeffD b j
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

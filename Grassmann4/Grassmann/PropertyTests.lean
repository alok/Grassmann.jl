/-
  Grassmann/PropertyTests.lean - Property-based testing with Plausible

  This module provides random generators and property tests for verifying
  algebraic identities in Clifford/Grassmann algebras.

  Usage:
    #eval runPropertyTests
    #test ∀ a b : R3Mv, a + b = b + a
-/
import Plausible
import Grassmann.SparseMultivector
import Grassmann.NativeVector
import Grassmann.Products
import Grassmann.Manifold
import Grassmann.LinearAlgebra
import Grassmann.StaticOpt
import Grassmann.MV
import Grassmann.PGA
import Grassmann.CGA
import Grassmann.RotorExp
import Grassmann.JuliaExamples
import Grassmann.BladeIndex
import Grassmann.SignTables
import Grassmann.Repr

namespace Grassmann.PropertyTests

open Grassmann
open Plausible

/-! ## Custom Generators for Multivectors -/

/-- Generate a random Float in [-scale, scale] using Nat and conversion -/
def genFloat (scale : Float := 10.0) : Gen Float := do
  let size ← Gen.getSize
  let maxVal := max 1 (size * 100)  -- Range for integer part
  let nSub ← Gen.choose Nat 0 (2 * maxVal) (by omega)
  let n := nSub.val  -- Extract value from subtype
  -- Convert to Float in [-scale, scale]
  let normalized := (n.toFloat / maxVal.toFloat) - 1.0  -- Range [-1, 1]
  return normalized * scale

/-- Generate a small Float for numerical stability -/
def genSmallFloat : Gen Float := genFloat 5.0

/-- Generate a random sparse coefficient list for a multivector -/
def genSparseCoeffs (maxIdx : Nat) (maxTerms : Nat := 4) : Gen (List (Nat × Float)) := do
  let numTerms ← Gen.choose Nat 0 maxTerms (by omega)
  let mut terms : List (Nat × Float) := []
  for _ in [0:numTerms] do
    let idx ← Gen.choose Nat 0 maxIdx (by omega)
    let coeff ← genSmallFloat
    if coeff.abs > 0.001 then
      terms := (idx.val, coeff) :: terms
  return terms.reverse

/-! ## Multivector Generators -/

/-- Wrapper for R3 multivectors for Plausible testing -/
structure R3Mv where
  mv : MultivectorS R3 Float
  deriving Repr

/-- Create R3Mv from coefficient list -/
def R3Mv.ofList (coeffs : List (Nat × Float)) : R3Mv :=
  ⟨MultivectorS.ofList coeffs⟩

/-- Generator for R3 multivectors (2³ = 8 basis elements) -/
instance : Arbitrary R3Mv where
  arbitrary := do
    let coeffs ← genSparseCoeffs 7 4
    return R3Mv.ofList coeffs

/-- Shrink R3 multivectors by removing terms -/
instance : Shrinkable R3Mv where
  shrink mv :=
    let terms := mv.mv.toList
    -- Try removing each term
    terms.mapIdx fun i _ =>
      R3Mv.ofList (terms.eraseIdx i)

/-- Wrapper for CGA3 multivectors -/
structure CGA3Mv where
  mv : MultivectorS CGA3 Float
  deriving Repr

/-- Wrapper for PGA3 multivectors. -/
structure PGA3Mv where
  mv : MultivectorS PGA3 Float
  deriving Repr

/-- Create CGA3Mv from coefficient list -/
def CGA3Mv.ofList (coeffs : List (Nat × Float)) : CGA3Mv :=
  ⟨MultivectorS.ofList coeffs⟩

/-- Create PGA3Mv from coefficient list. -/
def PGA3Mv.ofList (coeffs : List (Nat × Float)) : PGA3Mv :=
  ⟨MultivectorS.ofList coeffs⟩

/-- Generator for PGA3 multivectors (2⁴ = 16 basis elements). -/
instance : Arbitrary PGA3Mv where
  arbitrary := do
    let coeffs ← genSparseCoeffs 15 4
    return PGA3Mv.ofList coeffs

instance : Shrinkable PGA3Mv where
  shrink mv :=
    let terms := mv.mv.toList
    terms.mapIdx fun i _ =>
      PGA3Mv.ofList (terms.eraseIdx i)

/-- Generator for CGA3 multivectors (2⁵ = 32 basis elements) -/
instance : Arbitrary CGA3Mv where
  arbitrary := do
    let coeffs ← genSparseCoeffs 31 3  -- Fewer terms for larger algebra
    return CGA3Mv.ofList coeffs

instance : Shrinkable CGA3Mv where
  shrink mv :=
    let terms := mv.mv.toList
    terms.mapIdx fun i _ =>
      CGA3Mv.ofList (terms.eraseIdx i)

/-! ## Approximate Equality for Floating Point -/

/-- Check if two Floats are approximately equal -/
def approxEq (a b : Float) (tol : Float := 1e-9) : Bool :=
  (a - b).abs < tol

/-- Check if two multivectors are approximately equal -/
def mvApproxEq {n : Nat} {sig : Signature n} (a b : MultivectorS sig Float)
    (tol : Float := 1e-9) : Bool :=
  let aList := a.toList
  let bList := b.toList
  -- Check all coefficients up to the maximum index in either list
  let maxA := aList.map Prod.fst |>.foldl max 0
  let maxB := bList.map Prod.fst |>.foldl max 0
  let maxIdx := max maxA maxB
  (List.range (maxIdx + 1)).all fun i =>
    approxEq (a.coeff i) (b.coeff i) tol

instance : BEq R3Mv where
  beq a b := mvApproxEq a.mv b.mv

instance : BEq PGA3Mv where
  beq a b := mvApproxEq a.mv b.mv

instance : BEq CGA3Mv where
  beq a b := mvApproxEq a.mv b.mv

/-! ## Dense Reference Multivectors for MV Parity Tests -/

/-- Wrapper for dense R3 multivectors used as the reference for packed `MV`. -/
structure R3DenseMv where
  mv : Multivector R3 Float

/-- Wrapper for dense PGA3 multivectors used as the reference for packed `MV`. -/
structure PGA3DenseMv where
  mv : Multivector PGA3 Float

/-- Wrapper for dense CGA3 multivectors used as the reference for packed `MV`. -/
structure CGA3DenseMv where
  mv : Multivector CGA3 Float

/-- Build a dense R3 multivector by summing duplicate blade entries. -/
def R3DenseMv.ofList (coeffs : List (Nat × Float)) : R3DenseMv :=
  ⟨⟨fun i =>
    coeffs.foldl (init := 0.0) fun acc (idx, coeff) =>
      if idx == i.val then acc + coeff else acc⟩⟩

/-- Build a dense PGA3 multivector by summing duplicate blade entries. -/
def PGA3DenseMv.ofList (coeffs : List (Nat × Float)) : PGA3DenseMv :=
  ⟨⟨fun i =>
    coeffs.foldl (init := 0.0) fun acc (idx, coeff) =>
      if idx == i.val then acc + coeff else acc⟩⟩

/-- Build a dense CGA3 multivector by summing duplicate blade entries. -/
def CGA3DenseMv.ofList (coeffs : List (Nat × Float)) : CGA3DenseMv :=
  ⟨⟨fun i =>
    coeffs.foldl (init := 0.0) fun acc (idx, coeff) =>
      if idx == i.val then acc + coeff else acc⟩⟩

/-- Generator for dense R3 multivectors. -/
def genR3DenseMv : Gen R3DenseMv := do
  let coeffs ← genSparseCoeffs 7 6
  return R3DenseMv.ofList coeffs

/-- Generator for dense PGA3 multivectors. -/
def genPGA3DenseMv : Gen PGA3DenseMv := do
  let coeffs ← genSparseCoeffs 15 5
  return PGA3DenseMv.ofList coeffs

/-- Generator for dense CGA3 multivectors. -/
def genCGA3DenseMv : Gen CGA3DenseMv := do
  let coeffs ← genSparseCoeffs 31 5
  return CGA3DenseMv.ofList coeffs

/-- Compare dense multivectors coefficient-wise. -/
def denseMvApproxEq {n : Nat} {sig : Signature n} (a b : Multivector sig Float)
    (tol : Float := 1e-9) : Bool :=
  (List.finRange (2 ^ n)).all fun i =>
    approxEq (a.coeffs i) (b.coeffs i) tol

/-- Convert sparse multivectors to the dense reference representation. -/
def sparseToDenseRef {n : Nat} {sig : Signature n} (m : MultivectorS sig Float) :
    Multivector sig Float :=
  ⟨fun i => m.coeff i.val⟩

/-- Compare sparse results against dense reference results coefficient-wise. -/
def sparseMatchesDense {n : Nat} {sig : Signature n} (sparse : MultivectorS sig Float)
    (dense : Multivector sig Float) (tol : Float := 1e-9) : Bool :=
  denseMvApproxEq (sparseToDenseRef sparse) dense tol

/-- Dense oracle for the Hestenes inner product: keep grade `|r - s|` from each
homogeneous grade-`r`/grade-`s` product. -/
def denseInnerProductRef {n : Nat} {sig : Signature n}
    (a b : Multivector sig Float) : Multivector sig Float :=
  (List.range (n + 1)).foldl (init := (0 : Multivector sig Float)) fun acc r =>
    (List.range (n + 1)).foldl (init := acc) fun acc' s =>
      let targetGrade := if r >= s then r - s else s - r
      acc' + (((a.gradeProject r) * (b.gradeProject s)).gradeProject targetGrade)

/-- Public dense → sparse → dense conversion preserves dense coefficients. -/
def denseSparseRoundtripMatches {n : Nat} {sig : Signature n} (dense : Multivector sig Float)
    (tol : Float := 1e-9) : Bool :=
  denseMvApproxEq (sparseToDense (denseToSparse dense)) dense tol

/-- Public sparse → dense → sparse conversion preserves sparse coefficients. -/
def sparseDenseRoundtripMatches {n : Nat} {sig : Signature n} (sparse : MultivectorS sig Float)
    (tol : Float := 1e-9) : Bool :=
  mvApproxEq (denseToSparse (sparseToDense sparse)) sparse tol

/-- Dense reference with all grades above `maxGrade` discarded. -/
def truncateDenseToGrade {n : Nat} {sig : Signature n} (maxGrade : Nat)
    (dense : Multivector sig Float) : Multivector sig Float :=
  ⟨fun i =>
    if grade (BitVec.ofNat n i.val) ≤ maxGrade then dense.coeffs i else 0.0⟩

/-- Convert a dense reference multivector to a truncated representation. -/
def truncatedOfDense {n : Nat} {sig : Signature n} {maxGrade : Nat}
    (dense : Multivector sig Float) : TruncatedMV sig maxGrade Float :=
  TruncatedMV.ofSparse (denseToSparse dense)

/-- Dense view of a truncated multivector, using public coefficient access. -/
def truncatedToDenseRef {n : Nat} {sig : Signature n} {maxGrade : Nat}
    (truncated : TruncatedMV sig maxGrade Float) : Multivector sig Float :=
  ⟨fun i => truncated.coeff i.val⟩

/-- Compare a truncated result against a dense reference after applying truncation. -/
def truncatedMatchesDense {n : Nat} {sig : Signature n} {maxGrade : Nat}
    (truncated : TruncatedMV sig maxGrade Float) (dense : Multivector sig Float)
    (tol : Float := 1e-9) : Bool :=
  denseMvApproxEq (truncatedToDenseRef truncated) (truncateDenseToGrade maxGrade dense) tol

/-- Compare a packed `MV` result against its dense reference. -/
def packedMatchesDense {n : Nat} {sig : Signature n} {p : Parity}
    (packed : MV sig p) (dense : Multivector sig Float) (tol : Float := 1e-9) : Bool :=
  denseMvApproxEq (MV.toMultivector packed) dense tol

/-- Compare two packed `MV` values through the dense reference view. -/
def packedApproxEq {n : Nat} {sig : Signature n} {p : Parity}
    (a b : MV sig p) (tol : Float := 1e-9) : Bool :=
  denseMvApproxEq (MV.toMultivector a) (MV.toMultivector b) tol

/-- Dense reference for a user-facing `MV.setCoeff` write.

Packed `MV` storage ignores masks outside the selected parity, while its dense view
has zero coefficients at those masks. This reference mirrors that public behavior
without depending on the packed array layout.
-/
def denseAfterPackedSetCoeff {n : Nat} {sig : Signature n} (p : Parity)
    (base : Multivector sig Float) (mask : Nat) (value : Float) :
    Multivector sig Float :=
  ⟨fun i =>
    if mask < 2 ^ n && Parity.containsMask p mask && i.val == mask then
      value
    else if Parity.containsMask p i.val then
      base.coeffs i
    else
      0.0⟩

/-- Dense reference for the public `MV.ofPairs` constructor.

`MV.ofPairs` is implemented as repeated public `setCoeff` writes, so duplicate
masks are overwrites, out-of-range masks are ignored, and parity-packed storage
keeps only masks admitted by the selected parity.
-/
def denseAfterPackedOfPairs {n : Nat} {sig : Signature n} (p : Parity)
    (pairs : List (Nat × Float)) : Multivector sig Float :=
  pairs.foldl (init := (0 : Multivector sig Float)) fun acc (mask, value) =>
    if mask < 2 ^ n && Parity.containsMask p mask then
      acc.setCoeff ⟨BitVec.ofNat n mask⟩ value
    else
      acc

/-- Compare `MV.ofPairs` against the dense public-behavior reference. -/
def packedOfPairsMatchesDense {n : Nat} (sig : Signature n) (p : Parity)
    (pairs : List (Nat × Float)) (tol : Float := 1e-9) : Bool :=
  packedMatchesDense (MV.ofPairs sig p pairs)
    (denseAfterPackedOfPairs (sig := sig) p pairs) tol

/-- Packed norm-squared computation agrees with dense references for full and
parity-packed inputs. -/
def packedNormSqMatchesDense {n : Nat} {sig : Signature n}
    (a : Multivector sig Float) (tol : Float := 1e-6) : Bool :=
  let denseEven := a.evenPart
  let denseOdd := a.oddPart
  let full : MV sig .full := MV.ofMultivector a .full
  let even : MV sig .even := MV.ofMultivector denseEven .even
  let odd : MV sig .odd := MV.ofMultivector denseOdd .odd
  approxEq ((full * MV.rev full).scalarPart) a.normSq tol &&
    approxEq ((even * MV.rev even).scalarPart) denseEven.normSq tol &&
    approxEq ((odd * MV.rev odd).scalarPart) denseOdd.normSq tol

/-- Packed reverse norm-squared computation agrees with dense references for full
and parity-packed inputs. -/
def packedNormSqRevMatchesDense {n : Nat} {sig : Signature n}
    (a : Multivector sig Float) (tol : Float := 1e-6) : Bool :=
  let denseEven := a.evenPart
  let denseOdd := a.oddPart
  let full : MV sig .full := MV.ofMultivector a .full
  let even : MV sig .even := MV.ofMultivector denseEven .even
  let odd : MV sig .odd := MV.ofMultivector denseOdd .odd
  approxEq ((MV.rev full * full).scalarPart) a.normSqRev tol &&
    approxEq ((MV.rev even * even).scalarPart) denseEven.normSqRev tol &&
    approxEq ((MV.rev odd * odd).scalarPart) denseOdd.normSqRev tol

/-- Packed scalar-product computation agrees with dense references for full and
parity-packed inputs. -/
def packedScalarProductMatchesDense {n : Nat} {sig : Signature n}
    (a b : Multivector sig Float) (tol : Float := 1e-6) : Bool :=
  let denseAEven := a.evenPart
  let denseAOdd := a.oddPart
  let denseBEven := b.evenPart
  let denseBOdd := b.oddPart
  let fullA : MV sig .full := MV.ofMultivector a .full
  let fullB : MV sig .full := MV.ofMultivector b .full
  let evenA : MV sig .even := MV.ofMultivector denseAEven .even
  let oddA : MV sig .odd := MV.ofMultivector denseAOdd .odd
  let evenB : MV sig .even := MV.ofMultivector denseBEven .even
  let oddB : MV sig .odd := MV.ofMultivector denseBOdd .odd
  approxEq ((MV.rev fullA * fullB).scalarPart) (a.scalarProduct b) tol &&
    approxEq ((MV.rev evenA * evenB).scalarPart)
      (denseAEven.scalarProduct denseBEven) tol &&
    approxEq ((MV.rev evenA * oddB).scalarPart)
      (denseAEven.scalarProduct denseBOdd) tol &&
    approxEq ((MV.rev oddA * evenB).scalarPart)
      (denseAOdd.scalarProduct denseBEven) tol &&
    approxEq ((MV.rev oddA * oddB).scalarPart)
      (denseAOdd.scalarProduct denseBOdd) tol

/-- Packed wedge agrees with dense wedge for full and parity-packed inputs. -/
def packedWedgeMatchesDense {n : Nat} {sig : Signature n} (a b : Multivector sig Float)
    (tol : Float := 1e-6) : Bool :=
  let denseAEven := a.evenPart
  let denseAOdd := a.oddPart
  let denseBEven := b.evenPart
  let denseBOdd := b.oddPart
  let fullA : MV sig .full := MV.ofMultivector a .full
  let fullB : MV sig .full := MV.ofMultivector b .full
  let evenA : MV sig .even := MV.ofMultivector denseAEven .even
  let oddA : MV sig .odd := MV.ofMultivector denseAOdd .odd
  let evenB : MV sig .even := MV.ofMultivector denseBEven .even
  let oddB : MV sig .odd := MV.ofMultivector denseBOdd .odd
  packedMatchesDense (MV.wedge fullA fullB) (a ⋀ᵐ b) tol &&
    packedMatchesDense (MV.wedge evenA evenB) (denseAEven ⋀ᵐ denseBEven) tol &&
    packedMatchesDense (MV.wedge evenA oddB) (denseAEven ⋀ᵐ denseBOdd) tol &&
    packedMatchesDense (MV.wedge oddA evenB) (denseAOdd ⋀ᵐ denseBEven) tol &&
    packedMatchesDense (MV.wedge oddA oddB) (denseAOdd ⋀ᵐ denseBOdd) tol

/-- Packed left contraction agrees with dense left contraction for full and parity-packed inputs. -/
def packedLeftContractMatchesDense {n : Nat} {sig : Signature n}
    (a b : Multivector sig Float) (tol : Float := 1e-6) : Bool :=
  let denseAEven := a.evenPart
  let denseAOdd := a.oddPart
  let denseBEven := b.evenPart
  let denseBOdd := b.oddPart
  let fullA : MV sig .full := MV.ofMultivector a .full
  let fullB : MV sig .full := MV.ofMultivector b .full
  let evenA : MV sig .even := MV.ofMultivector denseAEven .even
  let oddA : MV sig .odd := MV.ofMultivector denseAOdd .odd
  let evenB : MV sig .even := MV.ofMultivector denseBEven .even
  let oddB : MV sig .odd := MV.ofMultivector denseBOdd .odd
  packedMatchesDense (MV.leftContract fullA fullB) (a ⌋ᵐ b) tol &&
    packedMatchesDense (MV.leftContract evenA evenB) (denseAEven ⌋ᵐ denseBEven) tol &&
    packedMatchesDense (MV.leftContract evenA oddB) (denseAEven ⌋ᵐ denseBOdd) tol &&
    packedMatchesDense (MV.leftContract oddA evenB) (denseAOdd ⌋ᵐ denseBEven) tol &&
    packedMatchesDense (MV.leftContract oddA oddB) (denseAOdd ⌋ᵐ denseBOdd) tol

/-- Packed right contraction agrees with dense right contraction for full and
parity-packed inputs. -/
def packedRightContractMatchesDense {n : Nat} {sig : Signature n}
    (a b : Multivector sig Float) (tol : Float := 1e-6) : Bool :=
  let denseAEven := a.evenPart
  let denseAOdd := a.oddPart
  let denseBEven := b.evenPart
  let denseBOdd := b.oddPart
  let fullA : MV sig .full := MV.ofMultivector a .full
  let fullB : MV sig .full := MV.ofMultivector b .full
  let evenA : MV sig .even := MV.ofMultivector denseAEven .even
  let oddA : MV sig .odd := MV.ofMultivector denseAOdd .odd
  let evenB : MV sig .even := MV.ofMultivector denseBEven .even
  let oddB : MV sig .odd := MV.ofMultivector denseBOdd .odd
  packedMatchesDense (MV.rightContract fullA fullB) (a ⌊ᵐ b) tol &&
    packedMatchesDense (MV.rightContract evenA evenB) (denseAEven ⌊ᵐ denseBEven) tol &&
    packedMatchesDense (MV.rightContract evenA oddB) (denseAEven ⌊ᵐ denseBOdd) tol &&
    packedMatchesDense (MV.rightContract oddA evenB) (denseAOdd ⌊ᵐ denseBEven) tol &&
    packedMatchesDense (MV.rightContract oddA oddB) (denseAOdd ⌊ᵐ denseBOdd) tol

/-- Full packed `MV` dual and derived products agree with dense references. -/
def packedFullDerivedProductsMatchDense {n : Nat} {sig : Signature n}
    (a b : Multivector sig Float) (tol : Float := 1e-6) : Bool :=
  let fullA : MV sig .full := MV.ofMultivector a .full
  let fullB : MV sig .full := MV.ofMultivector b .full
  packedMatchesDense (MV.hodgeDual fullA) (⋆ᵐa) tol &&
    packedMatchesDense (MV.regressiveProduct fullA fullB) (a ⋁ᵐ b) tol &&
    packedMatchesDense (MV.fatDot fullA fullB) (a ⋅ᵐ b) tol &&
    packedMatchesDense (MV.commutator fullA fullB) (Multivector.commutator a b) tol &&
    packedMatchesDense (MV.antiCommutator fullA fullB) (Multivector.antiCommutator a b) tol

/-! ## Native Vector Reference Tests -/

/-- Convert a dense reference multivector to the native-vector baseline. -/
def nativeOfDense {n : Nat} {sig : Signature n} (m : Multivector sig Float) : NativeMV sig :=
  ⟨Vector.ofFn fun i => m.coeffs i⟩

/-- Compare a native-vector result against its dense reference coefficient-wise. -/
def nativeMatchesDense {n : Nat} {sig : Signature n} (native : NativeMV sig)
    (dense : Multivector sig Float) (tol : Float := 1e-9) : Bool :=
  (List.finRange (2 ^ n)).all fun i =>
    approxEq (native.coeff i.val) (dense.coeffs i) tol

/-- Dense reference for the public native-vector `ofPairs` constructor.

Native storage accepts all in-range masks and implements duplicate entries as
overwrites through repeated public `setCoeff` writes.
-/
def denseAfterNativeOfPairs {n : Nat} {sig : Signature n}
    (pairs : List (Nat × Float)) : Multivector sig Float :=
  pairs.foldl (init := (0 : Multivector sig Float)) fun acc (mask, value) =>
    if mask < 2 ^ n then
      acc.setCoeff ⟨BitVec.ofNat n mask⟩ value
    else
      acc

/-- Compare native-vector `ofPairs` against the dense public-behavior reference. -/
def nativeOfPairsMatchesDense {n : Nat} (sig : Signature n)
    (pairs : List (Nat × Float)) (tol : Float := 1e-9) : Bool :=
  nativeMatchesDense (NativeMV.ofPairs sig pairs)
    (denseAfterNativeOfPairs (sig := sig) pairs) tol

/-- Native-vector `GAlgebra` operations agree with dense references. -/
def nativeGAlgebraOpsMatchDense {n : Nat} {sig : Signature n}
    (a b : Multivector sig Float) (k : Nat) (scale : Float)
    (tol : Float := 1e-6) : Bool :=
  let inst := (inferInstance : GAlgebra sig (NativeMV sig) Float)
  let nativeA := nativeOfDense a
  let nativeB := nativeOfDense b
  let basisOk :=
    (List.finRange n).all fun i =>
      nativeMatchesDense (inst.basisVector i) (Multivector.basis i) tol
  let bladeOk :=
    (List.range (2 ^ n)).all fun mask =>
      nativeMatchesDense
        (inst.blade (BitVec.ofNat n mask))
        (Multivector.ofBlade ⟨BitVec.ofNat n mask⟩ : Multivector sig Float)
        tol
  nativeMatchesDense inst.zero Multivector.zero tol &&
    nativeMatchesDense inst.one Multivector.one tol &&
    nativeMatchesDense (inst.scalar scale) (Multivector.scalar scale) tol &&
    basisOk &&
    bladeOk &&
    nativeMatchesDense (inst.add nativeA nativeB) (a + b) tol &&
    nativeMatchesDense (inst.neg nativeA) (-a) tol &&
    nativeMatchesDense (inst.smul scale nativeA) (a.smul scale) tol &&
    nativeMatchesDense (inst.mul nativeA nativeB) (a * b) tol &&
    nativeMatchesDense (inst.wedge nativeA nativeB) (a ⋀ᵐ b) tol &&
    nativeMatchesDense (inst.leftContract nativeA nativeB) (a ⌋ᵐ b) tol &&
    nativeMatchesDense (inst.rightContract nativeA nativeB) (a ⌊ᵐ b) tol &&
    nativeMatchesDense (inst.reverse nativeA) a.reverse tol &&
    nativeMatchesDense (inst.involute nativeA) a.involute tol &&
    nativeMatchesDense (inst.conjugate nativeA) a.conjugate tol &&
    nativeMatchesDense (inst.gradeProject nativeA k) (a.gradeProject k) tol &&
    approxEq (inst.scalarPart nativeA) a.scalarPart tol

/-- Native-vector round-trip preserves all dense coefficients. -/
def prop_native_full_roundtrip : Gen Bool := do
  let a ← genR3DenseMv
  return nativeMatchesDense (nativeOfDense a.mv) a.mv

/-- Native-vector `ofPairs` handles duplicate and out-of-range masks. -/
def prop_native_ofPairs_dense : Bool :=
  let pairs : List (Nat × Float) :=
    [(0, 1.25), (1, -2.0), (3, 4.0), (8, 9.0), (1, 2.5), (6, -1.0)]
  nativeOfPairsMatchesDense R3 pairs

/-- Native-vector grade projection agrees with dense grade projection. -/
def prop_native_grade_projection_dense : Gen Bool := do
  let a ← genR3DenseMv
  let k ← Gen.choose Nat 0 3 (by omega)
  let native := nativeOfDense a.mv
  return nativeMatchesDense (native.gradeProject k.val) (a.mv.gradeProject k.val)

/-- Native-vector even and odd projections agree with dense projections. -/
def prop_native_parity_projection_dense : Gen Bool := do
  let a ← genR3DenseMv
  let native := nativeOfDense a.mv
  return nativeMatchesDense native.evenPart a.mv.evenPart &&
    nativeMatchesDense native.oddPart a.mv.oddPart

/-- Native-vector geometric multiplication agrees with dense multiplication. -/
def prop_native_mul_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  let nativeA := nativeOfDense a.mv
  let nativeB := nativeOfDense b.mv
  return nativeMatchesDense (nativeA * nativeB) (a.mv * b.mv) (tol := 1e-6)

/-- Native-vector wedge product agrees with dense wedge product. -/
def prop_native_wedge_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  return nativeMatchesDense (NativeMV.wedge (nativeOfDense a.mv) (nativeOfDense b.mv))
    (a.mv ⋀ᵐ b.mv) (tol := 1e-6)

/-- Native-vector reverse agrees with dense reverse. -/
def prop_native_reverse_dense : Gen Bool := do
  let a ← genR3DenseMv
  return nativeMatchesDense (nativeOfDense a.mv).reverse a.mv.reverse

/-- Native-vector scalar extraction agrees with dense scalar extraction. -/
def prop_native_scalar_part_dense : Gen Bool := do
  let a ← genR3DenseMv
  return approxEq (nativeOfDense a.mv).scalarPart a.mv.scalarPart

/-- Native-vector grade involution and Clifford conjugate agree with dense involutions. -/
def prop_native_involutions_dense : Gen Bool := do
  let a ← genR3DenseMv
  let native := nativeOfDense a.mv
  return nativeMatchesDense native.involute a.mv.involute &&
    nativeMatchesDense native.conjugate a.mv.conjugate

/-- Native-vector left contraction agrees with dense left contraction. -/
def prop_native_left_contract_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  return nativeMatchesDense ((nativeOfDense a.mv) ⌋ᵥ (nativeOfDense b.mv))
    (a.mv ⌋ᵐ b.mv) (tol := 1e-6)

/-- Native-vector right contraction agrees with dense right contraction. -/
def prop_native_right_contract_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  return nativeMatchesDense ((nativeOfDense a.mv) ⌊ᵥ (nativeOfDense b.mv))
    (a.mv ⌊ᵐ b.mv) (tol := 1e-6)

/-- Native-vector Hodge dual agrees with dense Hodge dual. -/
def prop_native_hodge_dual_dense : Gen Bool := do
  let a ← genR3DenseMv
  return nativeMatchesDense (⋆ᵥ(nativeOfDense a.mv)) (⋆ᵐa.mv) (tol := 1e-6)

/-- Native-vector regressive product agrees with dense regressive product. -/
def prop_native_regressive_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  return nativeMatchesDense ((nativeOfDense a.mv) ⋁ᵥ (nativeOfDense b.mv))
    (a.mv ⋁ᵐ b.mv) (tol := 1e-6)

/-- R3 native-vector `GAlgebra` operations agree with dense references. -/
def prop_native_galgebra_ops_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  let k ← Gen.choose Nat 0 3 (by omega)
  let scale ← genSmallFloat
  return nativeGAlgebraOpsMatchDense (sig := R3) a.mv b.mv k.val scale

/-- Native-vector `GAlgebra` instance dispatch agrees with direct dense sandwiching. -/
def prop_native_galgebra_sandwich_dense : Gen Bool := do
  let r ← genR3DenseMv
  let x ← genR3DenseMv
  let nativeR := nativeOfDense r.mv
  let nativeX := nativeOfDense x.mv
  let generic :=
    Grassmann.sandwich (sig := R3) (M := NativeMV R3) (F := Float) nativeR nativeX
  return nativeMatchesDense generic (r.mv.sandwich x.mv) (tol := 1e-6)

/-- Native-vector `GAlgebra` normSq agrees with dense normSq. -/
def prop_native_galgebra_normSq_dense : Gen Bool := do
  let a ← genR3DenseMv
  let native := nativeOfDense a.mv
  return approxEq
    (Grassmann.normSq (sig := R3) (M := NativeMV R3) (F := Float) native)
    a.mv.normSq (tol := 1e-6)

/-! ## PGA3 Native Vector Reference Tests -/

/-- PGA3 native-vector round-trip preserves all dense coefficients. -/
def prop_native_pga3_full_roundtrip : Gen Bool := do
  let a ← genPGA3DenseMv
  return nativeMatchesDense (nativeOfDense a.mv) a.mv

/-- PGA3 native-vector `ofPairs` matches dense public constructor behavior. -/
def prop_native_pga3_ofPairs_dense : Bool :=
  let pairs : List (Nat × Float) :=
    [(0, 1.0), (1, 2.0), (3, 3.5), (5, -4.0), (8, 6.0), (16, 9.0),
      (3, -1.5)]
  nativeOfPairsMatchesDense PGA3 pairs

/-- PGA3 native-vector grade projection agrees with dense grade projection. -/
def prop_native_pga3_grade_projection_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let k ← Gen.choose Nat 0 4 (by omega)
  let native := nativeOfDense a.mv
  return nativeMatchesDense (native.gradeProject k.val) (a.mv.gradeProject k.val)

/-- PGA3 native-vector even and odd projections agree with dense projections. -/
def prop_native_pga3_parity_projection_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let native := nativeOfDense a.mv
  return nativeMatchesDense native.evenPart a.mv.evenPart &&
    nativeMatchesDense native.oddPart a.mv.oddPart

/-- PGA3 native-vector geometric multiplication agrees with dense multiplication. -/
def prop_native_pga3_mul_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  let nativeA := nativeOfDense a.mv
  let nativeB := nativeOfDense b.mv
  return nativeMatchesDense (nativeA * nativeB) (a.mv * b.mv) (tol := 1e-6)

/-- PGA3 native-vector wedge product agrees with dense wedge product. -/
def prop_native_pga3_wedge_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  return nativeMatchesDense (NativeMV.wedge (nativeOfDense a.mv) (nativeOfDense b.mv))
    (a.mv ⋀ᵐ b.mv) (tol := 1e-6)

/-- PGA3 native-vector reverse agrees with dense reverse. -/
def prop_native_pga3_reverse_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  return nativeMatchesDense (nativeOfDense a.mv).reverse a.mv.reverse

/-- PGA3 native-vector scalar extraction agrees with dense scalar extraction. -/
def prop_native_pga3_scalar_part_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  return approxEq (nativeOfDense a.mv).scalarPart a.mv.scalarPart

/-- PGA3 native-vector grade involution and Clifford conjugate agree with dense involutions. -/
def prop_native_pga3_involutions_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let native := nativeOfDense a.mv
  return nativeMatchesDense native.involute a.mv.involute &&
    nativeMatchesDense native.conjugate a.mv.conjugate

/-- PGA3 native-vector left contraction agrees with dense left contraction. -/
def prop_native_pga3_left_contract_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  return nativeMatchesDense ((nativeOfDense a.mv) ⌋ᵥ (nativeOfDense b.mv))
    (a.mv ⌋ᵐ b.mv) (tol := 1e-6)

/-- PGA3 native-vector right contraction agrees with dense right contraction. -/
def prop_native_pga3_right_contract_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  return nativeMatchesDense ((nativeOfDense a.mv) ⌊ᵥ (nativeOfDense b.mv))
    (a.mv ⌊ᵐ b.mv) (tol := 1e-6)

/-- PGA3 native-vector Hodge dual agrees with dense Hodge dual. -/
def prop_native_pga3_hodge_dual_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  return nativeMatchesDense (⋆ᵥ(nativeOfDense a.mv)) (⋆ᵐa.mv) (tol := 1e-6)

/-- PGA3 native-vector regressive product agrees with dense regressive product. -/
def prop_native_pga3_regressive_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  return nativeMatchesDense ((nativeOfDense a.mv) ⋁ᵥ (nativeOfDense b.mv))
    (a.mv ⋁ᵐ b.mv) (tol := 1e-6)

/-- PGA3 native-vector `GAlgebra` operations agree with dense references. -/
def prop_native_pga3_galgebra_ops_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  let k ← Gen.choose Nat 0 4 (by omega)
  let scale ← genSmallFloat
  return nativeGAlgebraOpsMatchDense (sig := PGA3) a.mv b.mv k.val scale

/-- PGA3 native-vector `GAlgebra` instance dispatch agrees with direct dense sandwiching. -/
def prop_native_pga3_galgebra_sandwich_dense : Gen Bool := do
  let r ← genPGA3DenseMv
  let x ← genPGA3DenseMv
  let nativeR := nativeOfDense r.mv
  let nativeX := nativeOfDense x.mv
  let generic :=
    Grassmann.sandwich (sig := PGA3) (M := NativeMV PGA3) (F := Float) nativeR nativeX
  return nativeMatchesDense generic (r.mv.sandwich x.mv) (tol := 1e-6)

/-- PGA3 native-vector `GAlgebra` normSq agrees with dense normSq. -/
def prop_native_pga3_galgebra_normSq_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let native := nativeOfDense a.mv
  return approxEq
    (Grassmann.normSq (sig := PGA3) (M := NativeMV PGA3) (F := Float) native)
    a.mv.normSq (tol := 1e-6)

/-! ## CGA3 Native Vector Reference Tests -/

/-- CGA3 native-vector round-trip preserves all dense coefficients. -/
def prop_native_cga3_full_roundtrip : Gen Bool := do
  let a ← genCGA3DenseMv
  return nativeMatchesDense (nativeOfDense a.mv) a.mv

/-- CGA3 native-vector `ofPairs` matches dense public constructor behavior. -/
def prop_native_cga3_ofPairs_dense : Bool :=
  let pairs : List (Nat × Float) :=
    [(0, -0.5), (1, 1.0), (3, -2.0), (7, 4.0), (18, 5.0), (31, -6.0),
      (32, 7.0), (18, -8.0)]
  nativeOfPairsMatchesDense CGA3 pairs

/-- CGA3 native-vector grade projection agrees with dense grade projection. -/
def prop_native_cga3_grade_projection_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let k ← Gen.choose Nat 0 5 (by omega)
  let native := nativeOfDense a.mv
  return nativeMatchesDense (native.gradeProject k.val) (a.mv.gradeProject k.val)

/-- CGA3 native-vector even and odd projections agree with dense projections. -/
def prop_native_cga3_parity_projection_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let native := nativeOfDense a.mv
  return nativeMatchesDense native.evenPart a.mv.evenPart &&
    nativeMatchesDense native.oddPart a.mv.oddPart

/-- CGA3 native-vector geometric multiplication agrees with dense multiplication. -/
def prop_native_cga3_mul_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  let nativeA := nativeOfDense a.mv
  let nativeB := nativeOfDense b.mv
  return nativeMatchesDense (nativeA * nativeB) (a.mv * b.mv) (tol := 1e-6)

/-- CGA3 native-vector wedge product agrees with dense wedge product. -/
def prop_native_cga3_wedge_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  return nativeMatchesDense (NativeMV.wedge (nativeOfDense a.mv) (nativeOfDense b.mv))
    (a.mv ⋀ᵐ b.mv) (tol := 1e-6)

/-- CGA3 native-vector reverse agrees with dense reverse. -/
def prop_native_cga3_reverse_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  return nativeMatchesDense (nativeOfDense a.mv).reverse a.mv.reverse

/-- CGA3 native-vector scalar extraction agrees with dense scalar extraction. -/
def prop_native_cga3_scalar_part_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  return approxEq (nativeOfDense a.mv).scalarPart a.mv.scalarPart

/-- CGA3 native-vector grade involution and Clifford conjugate agree with dense involutions. -/
def prop_native_cga3_involutions_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let native := nativeOfDense a.mv
  return nativeMatchesDense native.involute a.mv.involute &&
    nativeMatchesDense native.conjugate a.mv.conjugate

/-- CGA3 native-vector left contraction agrees with dense left contraction. -/
def prop_native_cga3_left_contract_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  return nativeMatchesDense ((nativeOfDense a.mv) ⌋ᵥ (nativeOfDense b.mv))
    (a.mv ⌋ᵐ b.mv) (tol := 1e-6)

/-- CGA3 native-vector right contraction agrees with dense right contraction. -/
def prop_native_cga3_right_contract_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  return nativeMatchesDense ((nativeOfDense a.mv) ⌊ᵥ (nativeOfDense b.mv))
    (a.mv ⌊ᵐ b.mv) (tol := 1e-6)

/-- CGA3 native-vector Hodge dual agrees with dense Hodge dual. -/
def prop_native_cga3_hodge_dual_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  return nativeMatchesDense (⋆ᵥ(nativeOfDense a.mv)) (⋆ᵐa.mv) (tol := 1e-6)

/-- CGA3 native-vector regressive product agrees with dense regressive product. -/
def prop_native_cga3_regressive_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  return nativeMatchesDense ((nativeOfDense a.mv) ⋁ᵥ (nativeOfDense b.mv))
    (a.mv ⋁ᵐ b.mv) (tol := 1e-6)

/-- CGA3 native-vector `GAlgebra` operations agree with dense references. -/
def prop_native_cga3_galgebra_ops_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  let k ← Gen.choose Nat 0 5 (by omega)
  let scale ← genSmallFloat
  return nativeGAlgebraOpsMatchDense (sig := CGA3) a.mv b.mv k.val scale

/-- CGA3 native-vector `GAlgebra` instance dispatch agrees with direct dense sandwiching. -/
def prop_native_cga3_galgebra_sandwich_dense : Gen Bool := do
  let r ← genCGA3DenseMv
  let x ← genCGA3DenseMv
  let nativeR := nativeOfDense r.mv
  let nativeX := nativeOfDense x.mv
  let generic :=
    Grassmann.sandwich (sig := CGA3) (M := NativeMV CGA3) (F := Float) nativeR nativeX
  return nativeMatchesDense generic (r.mv.sandwich x.mv) (tol := 1e-6)

/-- CGA3 native-vector `GAlgebra` normSq agrees with dense normSq. -/
def prop_native_cga3_galgebra_normSq_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let native := nativeOfDense a.mv
  return approxEq
    (Grassmann.normSq (sig := CGA3) (M := NativeMV CGA3) (F := Float) native)
    a.mv.normSq (tol := 1e-6)

/-! ## Sign Table Reference Tests -/

/-- R3 precomputed sign-table multiplication agrees with generic dense multiplication. -/
def prop_sign_table_r3_mul_generic : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  return denseMvApproxEq (mulR3 a.mv b.mv) (Multivector.geometricProduct a.mv b.mv)
    (tol := 1e-6)

/-- PGA3 precomputed sign-table multiplication agrees with generic dense multiplication. -/
def prop_sign_table_pga3_mul_generic : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  return denseMvApproxEq (mulPGA3 a.mv b.mv) (Multivector.geometricProduct a.mv b.mv)
    (tol := 1e-6)

/-- CGA3 precomputed sign-table multiplication agrees with generic dense multiplication. -/
def prop_sign_table_cga3_mul_generic : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  return denseMvApproxEq (mulCGA3 a.mv b.mv) (Multivector.geometricProduct a.mv b.mv)
    (tol := 1e-6)

/-! ## Packed MV Reference Tests -/

/-- Packed `MV` index tables agree with generic parity filtering and round-trip all
valid blade masks. This covers both cached dimensions and generic fallback paths. -/
def packedLayoutInvariant (n : Nat) (p : Parity) : Bool :=
  let idx := MV.indices n p
  let expected := MV.computeIndices n p
  let packedIndicesRoundtrip :=
    (List.range idx.size).all fun pi =>
      let mask := MV.unpackIdx n p pi
      mask == idx.getD pi 0 &&
        decide (mask < 2 ^ n) &&
        Parity.containsMask p mask &&
        MV.packIdx n p mask == pi &&
        MV.computePackIdx n p mask == pi
  let validMasksRoundtrip :=
    (List.range (2 ^ n)).all fun mask =>
      if Parity.containsMask p mask then
        let pi := MV.packIdx n p mask
        decide (pi < idx.size) &&
          MV.unpackIdx n p pi == mask &&
          pi == MV.computePackIdx n p mask
      else true
  idx == expected &&
    idx.size == storageSize n p &&
    packedIndicesRoundtrip &&
    validMasksRoundtrip

/-- Packed `MV` layout maps are internally consistent for cached and fallback dimensions. -/
def prop_mv_layout_invariants : Bool :=
  [1, 2, 3, 4, 5, 6].all fun n =>
    [.full, .even, .odd].all fun p =>
      packedLayoutInvariant n p

/-- Full packed `MV` round-trip preserves all dense coefficients. -/
def prop_mv_full_roundtrip : Gen Bool := do
  let a ← genR3DenseMv
  let packed : MV R3 .full := MV.ofMultivector a.mv .full
  return packedMatchesDense packed a.mv

/-- Even and odd packed projections match dense even/odd projection. -/
def prop_mv_parity_projection : Gen Bool := do
  let a ← genR3DenseMv
  let evenPacked : MV R3 .even := MV.ofMultivector a.mv .even
  let oddPacked : MV R3 .odd := MV.ofMultivector a.mv .odd
  return packedMatchesDense evenPacked a.mv.evenPart &&
    packedMatchesDense oddPacked a.mv.oddPart

/-- Packed `MV` grade projection agrees with dense grade projection. -/
def prop_mv_grade_projection_dense : Gen Bool := do
  let a ← genR3DenseMv
  let k ← Gen.choose Nat 0 3 (by omega)
  let denseEven := a.mv.evenPart
  let denseOdd := a.mv.oddPart
  let full : MV R3 .full := MV.ofMultivector a.mv .full
  let even : MV R3 .even := MV.ofMultivector denseEven .even
  let odd : MV R3 .odd := MV.ofMultivector denseOdd .odd
  return packedMatchesDense (MV.gradeProject full k.val) (a.mv.gradeProject k.val) &&
    packedMatchesDense (MV.gradeProject even k.val) (denseEven.gradeProject k.val) &&
    packedMatchesDense (MV.gradeProject odd k.val) (denseOdd.gradeProject k.val)

/-- Packed `MV.scalarPart` agrees with dense scalar extraction across storage tags. -/
def prop_mv_scalar_part_dense : Gen Bool := do
  let a ← genR3DenseMv
  let denseEven := a.mv.evenPart
  let denseOdd := a.mv.oddPart
  let full : MV R3 .full := MV.ofMultivector a.mv .full
  let even : MV R3 .even := MV.ofMultivector denseEven .even
  let odd : MV R3 .odd := MV.ofMultivector denseOdd .odd
  return approxEq full.scalarPart a.mv.scalarPart &&
    approxEq even.scalarPart denseEven.scalarPart &&
    approxEq odd.scalarPart denseOdd.scalarPart

/-- Packed norm-squared agrees with dense references across storage tags. -/
def prop_mv_normSq_dense : Gen Bool := do
  let a ← genR3DenseMv
  return packedNormSqMatchesDense a.mv

/-- Packed reverse norm-squared agrees with dense references across storage tags. -/
def prop_mv_normSqRev_dense : Gen Bool := do
  let a ← genR3DenseMv
  return packedNormSqRevMatchesDense a.mv

/-- Packed scalar product agrees with dense references across storage tags. -/
def prop_mv_scalar_product_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  return packedScalarProductMatchesDense a.mv b.mv

/-- Full packed `MV` linear operations agree with dense references. -/
def prop_mv_full_linear_ops_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  let packedA : MV R3 .full := MV.ofMultivector a.mv .full
  let packedB : MV R3 .full := MV.ofMultivector b.mv .full
  let scale : Float := 2.5
  return packedMatchesDense (packedA + packedB) (a.mv + b.mv) &&
    packedMatchesDense (-packedA) (-a.mv) &&
    packedMatchesDense (scale * packedA) (a.mv.smul scale)

/-- Even packed `MV` linear operations agree with dense references. -/
def prop_mv_even_linear_ops_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  let denseA := a.mv.evenPart
  let denseB := b.mv.evenPart
  let packedA : MV R3 .even := MV.ofMultivector denseA .even
  let packedB : MV R3 .even := MV.ofMultivector denseB .even
  let scale : Float := -3.0
  return packedMatchesDense (packedA + packedB) (denseA + denseB) &&
    packedMatchesDense (-packedA) (-denseA) &&
    packedMatchesDense (scale * packedA) (denseA.smul scale)

/-- Odd packed `MV` linear operations agree with dense references. -/
def prop_mv_odd_linear_ops_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  let denseA := a.mv.oddPart
  let denseB := b.mv.oddPart
  let packedA : MV R3 .odd := MV.ofMultivector denseA .odd
  let packedB : MV R3 .odd := MV.ofMultivector denseB .odd
  let scale : Float := 0.25
  return packedMatchesDense (packedA + packedB) (denseA + denseB) &&
    packedMatchesDense (-packedA) (-denseA) &&
    packedMatchesDense (scale * packedA) (denseA.smul scale)

/-- Full packed `MV` projectors agree with dense even/odd projection. -/
def prop_mv_full_projectors_dense : Gen Bool := do
  let a ← genR3DenseMv
  let packed : MV R3 .full := MV.ofMultivector a.mv .full
  return packedMatchesDense (MV.evenPart packed) a.mv.evenPart &&
    packedMatchesDense (MV.oddPart packed) a.mv.oddPart

/-- Packed even/odd widening into full storage agrees with dense references. -/
def prop_mv_widen_dense : Gen Bool := do
  let a ← genR3DenseMv
  let evenPacked : MV R3 .even := MV.ofMultivector a.mv.evenPart .even
  let oddPacked : MV R3 .odd := MV.ofMultivector a.mv.oddPart .odd
  let evenFull : MV R3 .full := evenPacked
  let oddFull : MV R3 .full := oddPacked
  return packedMatchesDense evenFull a.mv.evenPart &&
    packedMatchesDense oddFull a.mv.oddPart

/-- Packed `MV` user-facing coefficient access respects the parity tag. -/
def prop_mv_parity_guard_coeff : Bool :=
  let evenScalar := MV.scalar R3 7.0
  let oddVector := (MV.zero R3 .odd).setCoeff 1 2.0
  approxEq (evenScalar.coeff 0) 7.0 &&
  approxEq (evenScalar.coeff 1) 0.0 &&
  approxEq (oddVector.coeff 1) 2.0 &&
  approxEq (oddVector.coeff 0) 0.0 &&
  approxEq (oddVector.coeff 8) 0.0

/-- Packed `MV` user-facing coefficient writes ignore masks outside their parity. -/
def prop_mv_parity_guard_setCoeff : Bool :=
  let evenZero : MV R3 .even := MV.zero R3 .even
  let evenValid := evenZero.setCoeff 3 4.0
  let evenInvalid := evenValid.setCoeff 1 9.0
  let oddValid := (MV.zero R3 .odd).setCoeff 1 2.0
  let oddInvalid := oddValid.setCoeff 0 9.0
  approxEq (evenValid.coeff 3) 4.0 &&
  approxEq (evenInvalid.coeff 3) 4.0 &&
  approxEq (evenInvalid.coeff 1) 0.0 &&
  approxEq (oddInvalid.coeff 1) 2.0 &&
  approxEq (oddInvalid.coeff 0) 0.0

/-- Packed `MV.setCoeff` agrees with the dense reference for full/even/odd storage. -/
def prop_mv_setCoeff_dense : Gen Bool := do
  let a ← genR3DenseMv
  let maskSub ← Gen.choose Nat 0 8 (by omega)
  let value ← genSmallFloat
  let mask := maskSub.val
  let full : MV R3 .full := MV.ofMultivector a.mv .full
  let even : MV R3 .even := MV.ofMultivector a.mv.evenPart .even
  let odd : MV R3 .odd := MV.ofMultivector a.mv.oddPart .odd
  return packedMatchesDense (full.setCoeff mask value)
      (denseAfterPackedSetCoeff .full a.mv mask value) &&
    packedMatchesDense (even.setCoeff mask value)
      (denseAfterPackedSetCoeff .even a.mv mask value) &&
    packedMatchesDense (odd.setCoeff mask value)
      (denseAfterPackedSetCoeff .odd a.mv mask value)

/-- Packed `MV.ofPairs` handles duplicate, out-of-range, and parity-filtered masks. -/
def prop_mv_ofPairs_dense : Bool :=
  let pairs : List (Nat × Float) :=
    [(0, 1.25), (1, -2.0), (3, 4.0), (8, 9.0), (1, 2.5), (6, -1.0)]
  packedOfPairsMatchesDense R3 .full pairs &&
    packedOfPairsMatchesDense R3 .even pairs &&
    packedOfPairsMatchesDense R3 .odd pairs

/-- Packed full multiplication agrees with dense multiplication. -/
def prop_mv_full_mul_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  let packedA : MV R3 .full := MV.ofMultivector a.mv .full
  let packedB : MV R3 .full := MV.ofMultivector b.mv .full
  return packedMatchesDense (packedA * packedB) (a.mv * b.mv) (tol := 1e-6)

/-- Packed even × even multiplication agrees with dense multiplication. -/
def prop_mv_even_mul_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  let denseA := a.mv.evenPart
  let denseB := b.mv.evenPart
  let packedA : MV R3 .even := MV.ofMultivector denseA .even
  let packedB : MV R3 .even := MV.ofMultivector denseB .even
  return packedMatchesDense (packedA * packedB) (denseA * denseB) (tol := 1e-6)

/-- Packed even × odd multiplication agrees with dense multiplication. -/
def prop_mv_even_odd_mul_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  let denseA := a.mv.evenPart
  let denseB := b.mv.oddPart
  let packedA : MV R3 .even := MV.ofMultivector denseA .even
  let packedB : MV R3 .odd := MV.ofMultivector denseB .odd
  return packedMatchesDense (packedA * packedB) (denseA * denseB) (tol := 1e-6)

/-- Packed odd × even multiplication agrees with dense multiplication. -/
def prop_mv_odd_even_mul_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  let denseA := a.mv.oddPart
  let denseB := b.mv.evenPart
  let packedA : MV R3 .odd := MV.ofMultivector denseA .odd
  let packedB : MV R3 .even := MV.ofMultivector denseB .even
  return packedMatchesDense (packedA * packedB) (denseA * denseB) (tol := 1e-6)

/-- Packed odd × odd multiplication agrees with dense multiplication. -/
def prop_mv_odd_mul_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  let denseA := a.mv.oddPart
  let denseB := b.mv.oddPart
  let packedA : MV R3 .odd := MV.ofMultivector denseA .odd
  let packedB : MV R3 .odd := MV.ofMultivector denseB .odd
  return packedMatchesDense (packedA * packedB) (denseA * denseB) (tol := 1e-6)

/-- Packed wedge agrees with dense wedge across full/even/odd storage. -/
def prop_mv_wedge_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  return packedWedgeMatchesDense a.mv b.mv

/-- Packed left contraction agrees with dense left contraction across full/even/odd storage. -/
def prop_mv_left_contract_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  return packedLeftContractMatchesDense a.mv b.mv

/-- Packed right contraction agrees with dense right contraction across full/even/odd storage. -/
def prop_mv_right_contract_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  return packedRightContractMatchesDense a.mv b.mv

/-- Full packed derived products agree with dense references. -/
def prop_mv_full_derived_products_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  return packedFullDerivedProductsMatchDense a.mv b.mv

/-- Packed reverse agrees with dense reverse. -/
def prop_mv_reverse_dense : Gen Bool := do
  let a ← genR3DenseMv
  let denseEven := a.mv.evenPart
  let denseOdd := a.mv.oddPart
  let full : MV R3 .full := MV.ofMultivector a.mv .full
  let even : MV R3 .even := MV.ofMultivector denseEven .even
  let odd : MV R3 .odd := MV.ofMultivector denseOdd .odd
  return packedMatchesDense (MV.rev full) a.mv.reverse &&
    packedMatchesDense (MV.rev even) denseEven.reverse &&
    packedMatchesDense (MV.rev odd) denseOdd.reverse

/-- Packed involute and Clifford conjugate agree with dense involutions. -/
def prop_mv_involutions_dense : Gen Bool := do
  let a ← genR3DenseMv
  let denseEven := a.mv.evenPart
  let denseOdd := a.mv.oddPart
  let full : MV R3 .full := MV.ofMultivector a.mv .full
  let even : MV R3 .even := MV.ofMultivector denseEven .even
  let odd : MV R3 .odd := MV.ofMultivector denseOdd .odd
  return packedMatchesDense (MV.involute full) a.mv.involute &&
    packedMatchesDense (MV.conjugate full) a.mv.conjugate &&
    packedMatchesDense (MV.involute even) denseEven.involute &&
    packedMatchesDense (MV.conjugate even) denseEven.conjugate &&
    packedMatchesDense (MV.involute odd) denseOdd.involute &&
    packedMatchesDense (MV.conjugate odd) denseOdd.conjugate

/-- Packed sandwich product agrees with dense sandwich product for even versors. -/
def prop_mv_sandwich_dense : Gen Bool := do
  let r ← genR3DenseMv
  let x ← genR3DenseMv
  let denseR := r.mv.evenPart
  let denseX := x.mv.oddPart
  let packedR : MV R3 .even := MV.ofMultivector denseR .even
  let packedX : MV R3 .odd := MV.ofMultivector denseX .odd
  return packedMatchesDense (mvSandwich packedR packedX) (denseR.sandwich denseX) (tol := 1e-6)

/-- Full packed `MV` agrees with dense references through the polymorphic `GAlgebra` API. -/
def packedGAlgebraOpsMatchDense {n : Nat} {sig : Signature n}
    (a b : Multivector sig Float) (k : Nat) (scale : Float)
    (tol : Float := 1e-6) : Bool :=
  let inst := (inferInstance : GAlgebra sig (MV sig .full) Float)
  let packedA : MV sig .full := MV.ofMultivector a .full
  let packedB : MV sig .full := MV.ofMultivector b .full
  let basisOk :=
    (List.finRange n).all fun i =>
      packedMatchesDense (inst.basisVector i) (Multivector.basis i) tol
  let bladeOk :=
    (List.range (2 ^ n)).all fun mask =>
      packedMatchesDense
        (inst.blade (BitVec.ofNat n mask))
        (Multivector.ofBlade ⟨BitVec.ofNat n mask⟩ : Multivector sig Float)
        tol
  packedMatchesDense inst.zero Multivector.zero tol &&
    packedMatchesDense inst.one Multivector.one tol &&
    packedMatchesDense (inst.scalar scale) (Multivector.scalar scale) tol &&
    basisOk &&
    bladeOk &&
    packedMatchesDense (inst.add packedA packedB) (a + b) tol &&
    packedMatchesDense (inst.neg packedA) (-a) tol &&
    packedMatchesDense (inst.smul scale packedA) (a.smul scale) tol &&
    packedMatchesDense (inst.mul packedA packedB) (a * b) tol &&
    packedMatchesDense (inst.wedge packedA packedB) (a ⋀ᵐ b) tol &&
    packedMatchesDense (inst.leftContract packedA packedB) (a ⌋ᵐ b) tol &&
    packedMatchesDense (inst.rightContract packedA packedB) (a ⌊ᵐ b) tol &&
    packedMatchesDense (inst.reverse packedA) a.reverse tol &&
    packedMatchesDense (inst.involute packedA) a.involute tol &&
    packedMatchesDense (inst.conjugate packedA) a.conjugate tol &&
    packedMatchesDense (inst.gradeProject packedA k) (a.gradeProject k) tol &&
    approxEq (inst.scalarPart packedA) a.scalarPart tol

/-- Packed full `MV` agrees with dense references for generic normalization and
inverse helpers. A large scalar offset keeps the generated multivector away from
zero-norm and negative-norm cases in degenerate or indefinite signatures. -/
def packedGAlgebraUnitHelpersMatchDense {n : Nat} {sig : Signature n}
    (a : Multivector sig Float) (scalarBias : Float := 100.0)
    (tol : Float := 1e-6) : Bool :=
  let dense := a + (Multivector.scalar scalarBias : Multivector sig Float)
  let packed : MV sig .full := MV.ofMultivector dense .full
  let normalized :=
    Grassmann.unitNormalizeFloat (sig := sig) (M := MV sig .full) packed
  let inverse :=
    Grassmann.versorInverseFloat (sig := sig) (M := MV sig .full) packed
  packedMatchesDense normalized dense.normalize tol &&
    packedMatchesDense inverse dense.inv tol

/-- R3 full packed `MV` `GAlgebra` operations agree with dense references. -/
def prop_mv_galgebra_ops_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  let k ← Gen.choose Nat 0 3 (by omega)
  let scale ← genSmallFloat
  return packedGAlgebraOpsMatchDense (sig := R3) a.mv b.mv k.val scale

/-- Packed full `MV` `GAlgebra` dispatch agrees with dense sandwiching. -/
def prop_mv_galgebra_sandwich_dense : Gen Bool := do
  let r ← genR3DenseMv
  let x ← genR3DenseMv
  let packedR : MV R3 .full := MV.ofMultivector r.mv .full
  let packedX : MV R3 .full := MV.ofMultivector x.mv .full
  let generic :=
    Grassmann.sandwich (sig := R3) (M := MV R3 .full) (F := Float) packedR packedX
  return packedMatchesDense generic (r.mv.sandwich x.mv) (tol := 1e-6)

/-- Packed full `MV` `GAlgebra` normSq agrees with dense normSq. -/
def prop_mv_galgebra_normSq_dense : Gen Bool := do
  let a ← genR3DenseMv
  let packed : MV R3 .full := MV.ofMultivector a.mv .full
  return approxEq
    (Grassmann.normSq (sig := R3) (M := MV R3 .full) (F := Float) packed)
    a.mv.normSq (tol := 1e-6)

/-- Packed full `MV` generic normalization/inverse helpers agree with dense references. -/
def prop_mv_galgebra_unit_helpers_dense : Gen Bool := do
  let a ← genR3DenseMv
  return packedGAlgebraUnitHelpersMatchDense (sig := R3) a.mv

/-! ## Packed MV Dispatch Equivalence Tests -/

/-- R3 direct-dispatch multiplication and typeclass multiplication agree. -/
def prop_mv_r3_dispatch_mul_equivalence : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  let fullA : MV R3 .full := MV.ofMultivector a.mv .full
  let fullB : MV R3 .full := MV.ofMultivector b.mv .full
  let evenA : MV R3 .even := MV.ofMultivector a.mv.evenPart .even
  let evenB : MV R3 .even := MV.ofMultivector b.mv.evenPart .even
  let oddA : MV R3 .odd := MV.ofMultivector a.mv.oddPart .odd
  let oddB : MV R3 .odd := MV.ofMultivector b.mv.oddPart .odd
  return packedApproxEq (MV.mulDirect fullA fullB) (MV.mulTC fullA fullB) (tol := 1e-6) &&
    packedApproxEq (MV.mulDirect evenA evenB) (MV.mulTC evenA evenB) (tol := 1e-6) &&
    packedApproxEq (MV.mulDirect evenA oddB) (MV.mulTC evenA oddB) (tol := 1e-6) &&
    packedApproxEq (MV.mulDirect oddA evenB) (MV.mulTC oddA evenB) (tol := 1e-6) &&
    packedApproxEq (MV.mulDirect oddA oddB) (MV.mulTC oddA oddB) (tol := 1e-6)

/-- PGA3 direct-dispatch multiplication and typeclass multiplication agree. -/
def prop_mv_pga3_dispatch_mul_equivalence : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  let fullA : MV PGA3 .full := MV.ofMultivector a.mv .full
  let fullB : MV PGA3 .full := MV.ofMultivector b.mv .full
  let evenA : MV PGA3 .even := MV.ofMultivector a.mv.evenPart .even
  let evenB : MV PGA3 .even := MV.ofMultivector b.mv.evenPart .even
  let oddA : MV PGA3 .odd := MV.ofMultivector a.mv.oddPart .odd
  let oddB : MV PGA3 .odd := MV.ofMultivector b.mv.oddPart .odd
  return packedApproxEq (MV.mulDirect fullA fullB) (MV.mulTC fullA fullB) (tol := 1e-6) &&
    packedApproxEq (MV.mulDirect evenA evenB) (MV.mulTC evenA evenB) (tol := 1e-6) &&
    packedApproxEq (MV.mulDirect evenA oddB) (MV.mulTC evenA oddB) (tol := 1e-6) &&
    packedApproxEq (MV.mulDirect oddA evenB) (MV.mulTC oddA evenB) (tol := 1e-6) &&
    packedApproxEq (MV.mulDirect oddA oddB) (MV.mulTC oddA oddB) (tol := 1e-6)

/-- CGA3 direct-dispatch multiplication and typeclass multiplication agree. -/
def prop_mv_cga3_dispatch_mul_equivalence : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  let fullA : MV CGA3 .full := MV.ofMultivector a.mv .full
  let fullB : MV CGA3 .full := MV.ofMultivector b.mv .full
  let evenA : MV CGA3 .even := MV.ofMultivector a.mv.evenPart .even
  let evenB : MV CGA3 .even := MV.ofMultivector b.mv.evenPart .even
  let oddA : MV CGA3 .odd := MV.ofMultivector a.mv.oddPart .odd
  let oddB : MV CGA3 .odd := MV.ofMultivector b.mv.oddPart .odd
  return packedApproxEq (MV.mulDirect fullA fullB) (MV.mulTC fullA fullB) (tol := 1e-6) &&
    packedApproxEq (MV.mulDirect evenA evenB) (MV.mulTC evenA evenB) (tol := 1e-6) &&
    packedApproxEq (MV.mulDirect evenA oddB) (MV.mulTC evenA oddB) (tol := 1e-6) &&
    packedApproxEq (MV.mulDirect oddA evenB) (MV.mulTC oddA evenB) (tol := 1e-6) &&
    packedApproxEq (MV.mulDirect oddA oddB) (MV.mulTC oddA oddB) (tol := 1e-6)

/-! ## PGA3 Packed MV Reference Tests -/

/-- PGA3 packed full `MV` round-trip preserves all dense coefficients. -/
def prop_mv_pga3_full_roundtrip : Gen Bool := do
  let a ← genPGA3DenseMv
  let packed : MV PGA3 .full := MV.ofMultivector a.mv .full
  return packedMatchesDense packed a.mv

/-- PGA3 even and odd packed projections match dense even/odd projection. -/
def prop_mv_pga3_parity_projection : Gen Bool := do
  let a ← genPGA3DenseMv
  let evenPacked : MV PGA3 .even := MV.ofMultivector a.mv .even
  let oddPacked : MV PGA3 .odd := MV.ofMultivector a.mv .odd
  return packedMatchesDense evenPacked a.mv.evenPart &&
    packedMatchesDense oddPacked a.mv.oddPart

/-- PGA3 packed `MV` grade projection agrees with dense grade projection. -/
def prop_mv_pga3_grade_projection_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let k ← Gen.choose Nat 0 4 (by omega)
  let denseEven := a.mv.evenPart
  let denseOdd := a.mv.oddPart
  let full : MV PGA3 .full := MV.ofMultivector a.mv .full
  let even : MV PGA3 .even := MV.ofMultivector denseEven .even
  let odd : MV PGA3 .odd := MV.ofMultivector denseOdd .odd
  return packedMatchesDense (MV.gradeProject full k.val) (a.mv.gradeProject k.val) &&
    packedMatchesDense (MV.gradeProject even k.val) (denseEven.gradeProject k.val) &&
    packedMatchesDense (MV.gradeProject odd k.val) (denseOdd.gradeProject k.val)

/-- PGA3 packed `MV.scalarPart` agrees with dense scalar extraction across storage tags. -/
def prop_mv_pga3_scalar_part_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let denseEven := a.mv.evenPart
  let denseOdd := a.mv.oddPart
  let full : MV PGA3 .full := MV.ofMultivector a.mv .full
  let even : MV PGA3 .even := MV.ofMultivector denseEven .even
  let odd : MV PGA3 .odd := MV.ofMultivector denseOdd .odd
  return approxEq full.scalarPart a.mv.scalarPart &&
    approxEq even.scalarPart denseEven.scalarPart &&
    approxEq odd.scalarPart denseOdd.scalarPart

/-- PGA3 packed norm-squared agrees with dense references across storage tags. -/
def prop_mv_pga3_normSq_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  return packedNormSqMatchesDense a.mv

/-- PGA3 packed reverse norm-squared agrees with dense references across storage tags. -/
def prop_mv_pga3_normSqRev_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  return packedNormSqRevMatchesDense a.mv

/-- PGA3 packed scalar product agrees with dense references across storage tags. -/
def prop_mv_pga3_scalar_product_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  return packedScalarProductMatchesDense a.mv b.mv

/-- PGA3 full packed `MV` linear operations agree with dense references. -/
def prop_mv_pga3_full_linear_ops_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  let packedA : MV PGA3 .full := MV.ofMultivector a.mv .full
  let packedB : MV PGA3 .full := MV.ofMultivector b.mv .full
  let scale : Float := 1.75
  return packedMatchesDense (packedA + packedB) (a.mv + b.mv) &&
    packedMatchesDense (-packedA) (-a.mv) &&
    packedMatchesDense (scale * packedA) (a.mv.smul scale)

/-- PGA3 even packed `MV` linear operations agree with dense references. -/
def prop_mv_pga3_even_linear_ops_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  let denseA := a.mv.evenPart
  let denseB := b.mv.evenPart
  let packedA : MV PGA3 .even := MV.ofMultivector denseA .even
  let packedB : MV PGA3 .even := MV.ofMultivector denseB .even
  let scale : Float := -2.25
  return packedMatchesDense (packedA + packedB) (denseA + denseB) &&
    packedMatchesDense (-packedA) (-denseA) &&
    packedMatchesDense (scale * packedA) (denseA.smul scale)

/-- PGA3 odd packed `MV` linear operations agree with dense references. -/
def prop_mv_pga3_odd_linear_ops_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  let denseA := a.mv.oddPart
  let denseB := b.mv.oddPart
  let packedA : MV PGA3 .odd := MV.ofMultivector denseA .odd
  let packedB : MV PGA3 .odd := MV.ofMultivector denseB .odd
  let scale : Float := 0.5
  return packedMatchesDense (packedA + packedB) (denseA + denseB) &&
    packedMatchesDense (-packedA) (-denseA) &&
    packedMatchesDense (scale * packedA) (denseA.smul scale)

/-- PGA3 full packed `MV` projectors agree with dense even/odd projection. -/
def prop_mv_pga3_full_projectors_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let packed : MV PGA3 .full := MV.ofMultivector a.mv .full
  return packedMatchesDense (MV.evenPart packed) a.mv.evenPart &&
    packedMatchesDense (MV.oddPart packed) a.mv.oddPart

/-- PGA3 packed even/odd widening into full storage agrees with dense references. -/
def prop_mv_pga3_widen_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let evenPacked : MV PGA3 .even := MV.ofMultivector a.mv.evenPart .even
  let oddPacked : MV PGA3 .odd := MV.ofMultivector a.mv.oddPart .odd
  let evenFull : MV PGA3 .full := evenPacked
  let oddFull : MV PGA3 .full := oddPacked
  return packedMatchesDense evenFull a.mv.evenPart &&
    packedMatchesDense oddFull a.mv.oddPart

/-- PGA3 packed `MV.setCoeff` agrees with dense reference across storage tags. -/
def prop_mv_pga3_setCoeff_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let maskSub ← Gen.choose Nat 0 16 (by omega)
  let value ← genSmallFloat
  let mask := maskSub.val
  let full : MV PGA3 .full := MV.ofMultivector a.mv .full
  let even : MV PGA3 .even := MV.ofMultivector a.mv.evenPart .even
  let odd : MV PGA3 .odd := MV.ofMultivector a.mv.oddPart .odd
  return packedMatchesDense (full.setCoeff mask value)
      (denseAfterPackedSetCoeff .full a.mv mask value) &&
    packedMatchesDense (even.setCoeff mask value)
      (denseAfterPackedSetCoeff .even a.mv mask value) &&
    packedMatchesDense (odd.setCoeff mask value)
      (denseAfterPackedSetCoeff .odd a.mv mask value)

/-- PGA3 packed `MV.ofPairs` matches dense public constructor behavior. -/
def prop_mv_pga3_ofPairs_dense : Bool :=
  let pairs : List (Nat × Float) :=
    [(0, 1.0), (1, 2.0), (3, 3.5), (5, -4.0), (8, 6.0), (16, 9.0),
      (3, -1.5)]
  packedOfPairsMatchesDense PGA3 .full pairs &&
    packedOfPairsMatchesDense PGA3 .even pairs &&
    packedOfPairsMatchesDense PGA3 .odd pairs

/-- PGA3 packed full multiplication agrees with dense multiplication. -/
def prop_mv_pga3_full_mul_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  let packedA : MV PGA3 .full := MV.ofMultivector a.mv .full
  let packedB : MV PGA3 .full := MV.ofMultivector b.mv .full
  return packedMatchesDense (packedA * packedB) (a.mv * b.mv) (tol := 1e-6)

/-- PGA3 packed even × even multiplication agrees with dense multiplication. -/
def prop_mv_pga3_even_mul_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  let denseA := a.mv.evenPart
  let denseB := b.mv.evenPart
  let packedA : MV PGA3 .even := MV.ofMultivector denseA .even
  let packedB : MV PGA3 .even := MV.ofMultivector denseB .even
  return packedMatchesDense (packedA * packedB) (denseA * denseB) (tol := 1e-6)

/-- PGA3 packed even × odd multiplication agrees with dense multiplication. -/
def prop_mv_pga3_even_odd_mul_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  let denseA := a.mv.evenPart
  let denseB := b.mv.oddPart
  let packedA : MV PGA3 .even := MV.ofMultivector denseA .even
  let packedB : MV PGA3 .odd := MV.ofMultivector denseB .odd
  return packedMatchesDense (packedA * packedB) (denseA * denseB) (tol := 1e-6)

/-- PGA3 packed odd × even multiplication agrees with dense multiplication. -/
def prop_mv_pga3_odd_even_mul_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  let denseA := a.mv.oddPart
  let denseB := b.mv.evenPart
  let packedA : MV PGA3 .odd := MV.ofMultivector denseA .odd
  let packedB : MV PGA3 .even := MV.ofMultivector denseB .even
  return packedMatchesDense (packedA * packedB) (denseA * denseB) (tol := 1e-6)

/-- PGA3 packed odd × odd multiplication agrees with dense multiplication. -/
def prop_mv_pga3_odd_mul_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  let denseA := a.mv.oddPart
  let denseB := b.mv.oddPart
  let packedA : MV PGA3 .odd := MV.ofMultivector denseA .odd
  let packedB : MV PGA3 .odd := MV.ofMultivector denseB .odd
  return packedMatchesDense (packedA * packedB) (denseA * denseB) (tol := 1e-6)

/-- PGA3 packed wedge agrees with dense wedge across full/even/odd storage. -/
def prop_mv_pga3_wedge_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  return packedWedgeMatchesDense a.mv b.mv

/-- PGA3 packed left contraction agrees with dense left contraction across storage tags. -/
def prop_mv_pga3_left_contract_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  return packedLeftContractMatchesDense a.mv b.mv

/-- PGA3 packed right contraction agrees with dense right contraction across storage tags. -/
def prop_mv_pga3_right_contract_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  return packedRightContractMatchesDense a.mv b.mv

/-- PGA3 full packed derived products agree with dense references. -/
def prop_mv_pga3_full_derived_products_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  return packedFullDerivedProductsMatchDense a.mv b.mv

/-- PGA3 packed reverse agrees with dense reverse. -/
def prop_mv_pga3_reverse_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let denseEven := a.mv.evenPart
  let denseOdd := a.mv.oddPart
  let full : MV PGA3 .full := MV.ofMultivector a.mv .full
  let even : MV PGA3 .even := MV.ofMultivector denseEven .even
  let odd : MV PGA3 .odd := MV.ofMultivector denseOdd .odd
  return packedMatchesDense (MV.rev full) a.mv.reverse &&
    packedMatchesDense (MV.rev even) denseEven.reverse &&
    packedMatchesDense (MV.rev odd) denseOdd.reverse

/-- PGA3 packed involute and Clifford conjugate agree with dense involutions. -/
def prop_mv_pga3_involutions_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let denseEven := a.mv.evenPart
  let denseOdd := a.mv.oddPart
  let full : MV PGA3 .full := MV.ofMultivector a.mv .full
  let even : MV PGA3 .even := MV.ofMultivector denseEven .even
  let odd : MV PGA3 .odd := MV.ofMultivector denseOdd .odd
  return packedMatchesDense (MV.involute full) a.mv.involute &&
    packedMatchesDense (MV.conjugate full) a.mv.conjugate &&
    packedMatchesDense (MV.involute even) denseEven.involute &&
    packedMatchesDense (MV.conjugate even) denseEven.conjugate &&
    packedMatchesDense (MV.involute odd) denseOdd.involute &&
    packedMatchesDense (MV.conjugate odd) denseOdd.conjugate

/-- PGA3 packed sandwich product agrees with dense sandwich product for even versors. -/
def prop_mv_pga3_sandwich_dense : Gen Bool := do
  let r ← genPGA3DenseMv
  let x ← genPGA3DenseMv
  let denseR := r.mv.evenPart
  let denseX := x.mv.oddPart
  let packedR : MV PGA3 .even := MV.ofMultivector denseR .even
  let packedX : MV PGA3 .odd := MV.ofMultivector denseX .odd
  return packedMatchesDense (mvSandwich packedR packedX) (denseR.sandwich denseX) (tol := 1e-6)

/-- PGA3 full packed `MV` `GAlgebra` operations agree with dense references. -/
def prop_mv_pga3_galgebra_ops_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  let k ← Gen.choose Nat 0 4 (by omega)
  let scale ← genSmallFloat
  return packedGAlgebraOpsMatchDense (sig := PGA3) a.mv b.mv k.val scale

/-- PGA3 packed full `MV` `GAlgebra` dispatch agrees with dense sandwiching. -/
def prop_mv_pga3_galgebra_sandwich_dense : Gen Bool := do
  let r ← genPGA3DenseMv
  let x ← genPGA3DenseMv
  let packedR : MV PGA3 .full := MV.ofMultivector r.mv .full
  let packedX : MV PGA3 .full := MV.ofMultivector x.mv .full
  let generic :=
    Grassmann.sandwich (sig := PGA3) (M := MV PGA3 .full) (F := Float) packedR packedX
  return packedMatchesDense generic (r.mv.sandwich x.mv) (tol := 1e-6)

/-- PGA3 packed full `MV` `GAlgebra` normSq agrees with dense normSq. -/
def prop_mv_pga3_galgebra_normSq_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let packed : MV PGA3 .full := MV.ofMultivector a.mv .full
  return approxEq
    (Grassmann.normSq (sig := PGA3) (M := MV PGA3 .full) (F := Float) packed)
    a.mv.normSq (tol := 1e-6)

/-- PGA3 packed full `MV` generic normalization/inverse helpers agree with dense references. -/
def prop_mv_pga3_galgebra_unit_helpers_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  return packedGAlgebraUnitHelpersMatchDense (sig := PGA3) a.mv

/-! ## PGA3 Point-Cloud Transform Tests -/

/-- A small deterministic point cloud with axis-aligned and mixed coordinates. -/
def pga3PointCloud : List (Float × Float × Float) :=
  [ (0.0, 0.0, 0.0),
    (1.0, 0.0, 0.0),
    (0.0, 1.0, 0.0),
    (0.0, 0.0, 1.0),
    (1.5, -2.0, 0.25),
    (-3.0, 0.5, 2.0) ]

/-- Local test constant for angle-based PGA3 motors. -/
def pga3TestPi : Float := 3.14159265358979323846

/-- Approximate equality for extracted 3D coordinates. -/
def coordsApproxEq (a b : Float × Float × Float) (tol : Float := 1e-6) : Bool :=
  approxEq a.1 b.1 tol &&
    approxEq a.2.1 b.2.1 tol &&
    approxEq a.2.2 b.2.2 tol

/-- Generate bounded 3D coordinates for user-facing transform checks. -/
def genCoord3 (scale : Float := 3.0) : Gen (Float × Float × Float) := do
  let x ← genFloat scale
  let y ← genFloat scale
  let z ← genFloat scale
  return (x, y, z)

/-- Packed PGA point constructors round-trip through coordinate extraction. -/
def prop_pga3_point3_extract_point_cloud : Bool :=
  pga3PointCloud.all fun c =>
    coordsApproxEq (PGA.extractPoint3 (PGA.point3 c.1 c.2.1 c.2.2)) c

/-- Generated packed PGA points match the dense proof-friendly constructor. -/
def prop_pga3_generated_point3_dense : Gen Bool := do
  let c ← genCoord3 4.0
  return packedMatchesDense
    (PGA.point3 c.1 c.2.1 c.2.2)
    (PGA.Proof.point c.1 c.2.1 c.2.2)

/-- Generated packed PGA planes match the dense proof-friendly constructor. -/
def prop_pga3_generated_plane3_dense : Gen Bool := do
  let normal ← genCoord3 2.0
  let d ← genFloat 2.0
  return packedMatchesDense
    (PGA.plane3 normal.1 normal.2.1 normal.2.2 d)
    (PGA.Proof.plane normal.1 normal.2.1 normal.2.2 d)

/-- Generated packed PGA lines match the dense proof-friendly constructor. -/
def prop_pga3_generated_line3_dense : Gen Bool := do
  let dir ← genCoord3 2.0
  let moment ← genCoord3 2.0
  return packedMatchesDense
    (PGA.line3 dir.1 dir.2.1 dir.2.2 moment.1 moment.2.1 moment.2.2)
    (PGA.Proof.lineFromDirMoment
      dir.1 dir.2.1 dir.2.2
      moment.1 moment.2.1 moment.2.2)

/-- Generated packed PGA rotation motors match the dense proof-friendly constructor. -/
def prop_pga3_generated_motor3_dense : Gen Bool := do
  let axis ← genCoord3 1.0
  let θ ← genFloat pga3TestPi
  return packedMatchesDense
    (PGA.motor3 axis.1 axis.2.1 axis.2.2 θ)
    (PGA.Proof.rotor axis.1 axis.2.1 axis.2.2 θ)

/-- The identity packed motor preserves every point in the deterministic cloud. -/
def prop_pga3_identity_motor_point_cloud : Bool :=
  let identity := PGA.Motor.identity PGA3
  pga3PointCloud.all fun c =>
    let p := PGA.point3 c.1 c.2.1 c.2.2
    coordsApproxEq (PGA.extractPoint3 (PGA.Motor.transformPoint identity p)) c

/-- Packed point transforms agree with the dense PGA reference on a fixed cloud. -/
def pga3PackedMotorMatchesDensePointCloud
    (packedMotor : PGA.Motor PGA3) (denseMotor : Multivector PGA3 Float) : Bool :=
  pga3PointCloud.all fun c =>
    let packedPoint := PGA.point3 c.1 c.2.1 c.2.2
    let densePoint := PGA.Proof.point c.1 c.2.1 c.2.2
    let packedCoords := PGA.extractPoint3 (PGA.Motor.transformPoint packedMotor packedPoint)
    let denseCoords := PGA.Proof.extractPoint (PGA.Proof.applyMotor denseMotor densePoint)
    coordsApproxEq packedCoords denseCoords

/-- Generated packed point transforms agree with the dense PGA reference. -/
def prop_pga3_generated_motor_point_dense : Gen Bool := do
  let c ← genCoord3 2.0
  let axis ← genCoord3 1.0
  let θ ← genFloat pga3TestPi
  let packedMotor := PGA.motor3 axis.1 axis.2.1 axis.2.2 θ
  let denseMotor := PGA.Proof.rotor axis.1 axis.2.1 axis.2.2 θ
  let packedPoint := PGA.point3 c.1 c.2.1 c.2.2
  let densePoint := PGA.Proof.point c.1 c.2.1 c.2.2
  let packedResult := PGA.Motor.transformPoint packedMotor packedPoint
  let denseResult := PGA.Proof.applyMotor denseMotor densePoint
  return packedMatchesDense packedResult denseResult (tol := 1e-6) &&
    coordsApproxEq (PGA.extractPoint3 packedResult) (PGA.Proof.extractPoint denseResult)
      (tol := 1e-5)

/-- Generated packed plane transforms agree with the dense PGA reference. -/
def prop_pga3_generated_motor_plane_dense : Gen Bool := do
  let normal ← genCoord3 2.0
  let d ← genFloat 2.0
  let axis ← genCoord3 1.0
  let θ ← genFloat pga3TestPi
  let packedMotor := PGA.motor3 axis.1 axis.2.1 axis.2.2 θ
  let denseMotor := PGA.Proof.rotor axis.1 axis.2.1 axis.2.2 θ
  let packedPlane := PGA.plane3 normal.1 normal.2.1 normal.2.2 d
  let densePlane := PGA.Proof.plane normal.1 normal.2.1 normal.2.2 d
  return packedMatchesDense
    (PGA.Motor.transformPlane packedMotor packedPlane)
    (PGA.Proof.applyMotor denseMotor densePlane)
    (tol := 1e-6)

/-- Generated packed line transforms agree with the dense PGA reference. -/
def prop_pga3_generated_motor_line_dense : Gen Bool := do
  let dir ← genCoord3 2.0
  let moment ← genCoord3 2.0
  let axis ← genCoord3 1.0
  let θ ← genFloat pga3TestPi
  let packedMotor := PGA.motor3 axis.1 axis.2.1 axis.2.2 θ
  let denseMotor := PGA.Proof.rotor axis.1 axis.2.1 axis.2.2 θ
  let packedLine :=
    PGA.line3 dir.1 dir.2.1 dir.2.2 moment.1 moment.2.1 moment.2.2
  let denseLine :=
    PGA.Proof.lineFromDirMoment
      dir.1 dir.2.1 dir.2.2
      moment.1 moment.2.1 moment.2.2
  return packedMatchesDense
    (PGA.Motor.transformLine packedMotor packedLine)
    (PGA.Proof.applyMotor denseMotor denseLine)
    (tol := 1e-6)

/-- Z-axis rotor point-cloud transforms use the same convention as the dense reference. -/
def prop_pga3_z_rotor_point_cloud_dense : Bool :=
  let θ := pga3TestPi / 2.0
  pga3PackedMotorMatchesDensePointCloud
    (PGA.motor3 0.0 0.0 1.0 θ)
    (PGA.Proof.rotor 0.0 0.0 1.0 θ)

/-- Composed packed motors transform point clouds like composed dense motors. -/
def prop_pga3_composed_motor_point_cloud_dense : Bool :=
  let θ₁ := pga3TestPi / 4.0
  let θ₂ := pga3TestPi / 3.0
  let packedA := PGA.motor3 0.0 0.0 1.0 θ₁
  let packedB := PGA.motor3 1.0 0.0 0.0 θ₂
  let denseA := PGA.Proof.rotor 0.0 0.0 1.0 θ₁
  let denseB := PGA.Proof.rotor 1.0 0.0 0.0 θ₂
  pga3PackedMotorMatchesDensePointCloud
    (PGA.Motor.compose packedB packedA)
    (denseB * denseA)

/-- Packed motor composition matches sequential point-cloud application. -/
def prop_pga3_composed_motor_point_cloud_sequential : Bool :=
  let θ₁ := pga3TestPi / 4.0
  let θ₂ := pga3TestPi / 3.0
  let packedA := PGA.motor3 0.0 0.0 1.0 θ₁
  let packedB := PGA.motor3 1.0 0.0 0.0 θ₂
  let composed := PGA.Motor.compose packedB packedA
  pga3PointCloud.all fun c =>
    let point := PGA.point3 c.1 c.2.1 c.2.2
    let sequential :=
      PGA.Motor.transformPoint packedB (PGA.Motor.transformPoint packedA point)
    let composedPoint := PGA.Motor.transformPoint composed point
    coordsApproxEq (PGA.extractPoint3 composedPoint) (PGA.extractPoint3 sequential)

/-- Generated composed packed motors transform generated points like dense motors,
and match sequential packed application. -/
def prop_pga3_generated_composed_motor_point_dense : Gen Bool := do
  let point ← genCoord3 2.0
  let axisA ← genCoord3 1.0
  let axisB ← genCoord3 1.0
  let thetaA ← genFloat pga3TestPi
  let thetaB ← genFloat pga3TestPi
  let packedA := PGA.motor3 axisA.1 axisA.2.1 axisA.2.2 thetaA
  let packedB := PGA.motor3 axisB.1 axisB.2.1 axisB.2.2 thetaB
  let denseA := PGA.Proof.rotor axisA.1 axisA.2.1 axisA.2.2 thetaA
  let denseB := PGA.Proof.rotor axisB.1 axisB.2.1 axisB.2.2 thetaB
  let packedComposed := PGA.Motor.compose packedB packedA
  let denseComposed := denseB * denseA
  let packedPoint := PGA.point3 point.1 point.2.1 point.2.2
  let densePoint := PGA.Proof.point point.1 point.2.1 point.2.2
  let composedResult := PGA.Motor.transformPoint packedComposed packedPoint
  let denseResult := PGA.Proof.applyMotor denseComposed densePoint
  let sequentialResult :=
    PGA.Motor.transformPoint packedB (PGA.Motor.transformPoint packedA packedPoint)
  return packedMatchesDense composedResult denseResult (tol := 1e-6) &&
    packedApproxEq composedResult sequentialResult (tol := 1e-6) &&
    coordsApproxEq (PGA.extractPoint3 composedResult) (PGA.Proof.extractPoint denseResult)
      (tol := 1e-5) &&
    coordsApproxEq (PGA.extractPoint3 composedResult) (PGA.extractPoint3 sequentialResult)
      (tol := 1e-5)

/-- Generated composed packed motors transform generated planes like dense motors. -/
def prop_pga3_generated_composed_motor_plane_dense : Gen Bool := do
  let normal ← genCoord3 2.0
  let d ← genFloat 2.0
  let axisA ← genCoord3 1.0
  let axisB ← genCoord3 1.0
  let thetaA ← genFloat pga3TestPi
  let thetaB ← genFloat pga3TestPi
  let packedA := PGA.motor3 axisA.1 axisA.2.1 axisA.2.2 thetaA
  let packedB := PGA.motor3 axisB.1 axisB.2.1 axisB.2.2 thetaB
  let denseA := PGA.Proof.rotor axisA.1 axisA.2.1 axisA.2.2 thetaA
  let denseB := PGA.Proof.rotor axisB.1 axisB.2.1 axisB.2.2 thetaB
  let packedPlane := PGA.plane3 normal.1 normal.2.1 normal.2.2 d
  let densePlane := PGA.Proof.plane normal.1 normal.2.1 normal.2.2 d
  return packedMatchesDense
    (PGA.Motor.transformPlane (PGA.Motor.compose packedB packedA) packedPlane)
    (PGA.Proof.applyMotor (denseB * denseA) densePlane)
    (tol := 1e-6)

/-- Generated composed packed motors transform generated lines like dense motors. -/
def prop_pga3_generated_composed_motor_line_dense : Gen Bool := do
  let dir ← genCoord3 2.0
  let moment ← genCoord3 2.0
  let axisA ← genCoord3 1.0
  let axisB ← genCoord3 1.0
  let thetaA ← genFloat pga3TestPi
  let thetaB ← genFloat pga3TestPi
  let packedA := PGA.motor3 axisA.1 axisA.2.1 axisA.2.2 thetaA
  let packedB := PGA.motor3 axisB.1 axisB.2.1 axisB.2.2 thetaB
  let denseA := PGA.Proof.rotor axisA.1 axisA.2.1 axisA.2.2 thetaA
  let denseB := PGA.Proof.rotor axisB.1 axisB.2.1 axisB.2.2 thetaB
  let packedLine :=
    PGA.line3 dir.1 dir.2.1 dir.2.2 moment.1 moment.2.1 moment.2.2
  let denseLine :=
    PGA.Proof.lineFromDirMoment
      dir.1 dir.2.1 dir.2.2
      moment.1 moment.2.1 moment.2.2
  return packedMatchesDense
    (PGA.Motor.transformLine (PGA.Motor.compose packedB packedA) packedLine)
    (PGA.Proof.applyMotor (denseB * denseA) denseLine)
    (tol := 1e-6)

/-! ## CGA3 Point-Cloud Transform Tests -/

/-- Deterministic translations used to check the CGA translator path. -/
def cga3TranslationCloud : List (Float × Float × Float) :=
  [ (0.5, 0.25, -0.75),
    (-1.0, 2.0, 0.5),
    (3.0, -1.5, 0.0) ]

/-- Apply a CGA translator and extract Euclidean coordinates. -/
def cga3TranslateCoords (point delta : Float × Float × Float) : Float × Float × Float :=
  let p := CGA.point point.1 point.2.1 point.2.2
  let translator := CGA.translator delta.1 delta.2.1 delta.2.2
  CGA.extractPoint (CGA.transform translator p)

/-- CGA translators shift embedded Euclidean points by their translation vector. -/
def prop_cga3_translator_point_cloud : Bool :=
  pga3PointCloud.all fun point =>
    cga3TranslationCloud.all fun delta =>
      let expected := (point.1 + delta.1, point.2.1 + delta.2.1, point.2.2 + delta.2.2)
      coordsApproxEq (cga3TranslateCoords point delta) expected

/-- CGA null basis vectors square to zero and have the expected dual pairing. -/
def prop_cga3_null_basis_vectors : Bool :=
  let einf : Multivector CGA3 Float := CGA.einf
  let eo : Multivector CGA3 Float := CGA.eo
  approxEq (einf * einf).scalarPart 0.0 (tol := 1e-8) &&
    approxEq (eo * eo).scalarPart 0.0 (tol := 1e-8) &&
    approxEq (einf * eo).scalarPart (-1.0) (tol := 1e-8) &&
    approxEq (eo * einf).scalarPart (-1.0) (tol := 1e-8)

/-- Deterministic CGA point embeddings are null vectors. -/
def prop_cga3_point_cloud_null_embeddings : Bool :=
  pga3PointCloud.all fun point =>
    let p := CGA.point point.1 point.2.1 point.2.2
    approxEq (p * p).scalarPart 0.0 (tol := 1e-6)

/-- Generated CGA point embeddings are null vectors. -/
def prop_cga3_generated_point_null_embeddings : Gen Bool := do
  let point ← genCoord3 4.0
  let p := CGA.point point.1 point.2.1 point.2.2
  return approxEq (p * p).scalarPart 0.0 (tol := 1e-6)

/-- Generated CGA translators shift generated Euclidean points by the same vector. -/
def prop_cga3_generated_translator_point : Gen Bool := do
  let point ← genCoord3 3.0
  let delta ← genCoord3 2.0
  let expected := (point.1 + delta.1, point.2.1 + delta.2.1, point.2.2 + delta.2.2)
  return coordsApproxEq (cga3TranslateCoords point delta) expected (tol := 1e-5)

/-- Composed CGA translators add their Euclidean translation vectors on points. -/
def prop_cga3_translator_composition_point : Gen Bool := do
  let point ← genCoord3 2.0
  let delta₁ ← genCoord3 1.5
  let delta₂ ← genCoord3 1.5
  let p := CGA.point point.1 point.2.1 point.2.2
  let t₁ := CGA.translator delta₁.1 delta₁.2.1 delta₁.2.2
  let t₂ := CGA.translator delta₂.1 delta₂.2.1 delta₂.2.2
  let expected :=
    ( point.1 + delta₁.1 + delta₂.1,
      point.2.1 + delta₁.2.1 + delta₂.2.1,
      point.2.2 + delta₁.2.2 + delta₂.2.2 )
  return coordsApproxEq (CGA.extractPoint (CGA.transform (t₂ * t₁) p)) expected (tol := 1e-5)

/-! ## CGA3 Packed MV Reference Tests -/

/-- CGA3 packed full `MV` round-trip preserves all dense coefficients. -/
def prop_mv_cga3_full_roundtrip : Gen Bool := do
  let a ← genCGA3DenseMv
  let packed : MV CGA3 .full := MV.ofMultivector a.mv .full
  return packedMatchesDense packed a.mv

/-- CGA3 even and odd packed projections match dense even/odd projection. -/
def prop_mv_cga3_parity_projection : Gen Bool := do
  let a ← genCGA3DenseMv
  let evenPacked : MV CGA3 .even := MV.ofMultivector a.mv .even
  let oddPacked : MV CGA3 .odd := MV.ofMultivector a.mv .odd
  return packedMatchesDense evenPacked a.mv.evenPart &&
    packedMatchesDense oddPacked a.mv.oddPart

/-- CGA3 packed `MV` grade projection agrees with dense grade projection. -/
def prop_mv_cga3_grade_projection_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let k ← Gen.choose Nat 0 5 (by omega)
  let denseEven := a.mv.evenPart
  let denseOdd := a.mv.oddPart
  let full : MV CGA3 .full := MV.ofMultivector a.mv .full
  let even : MV CGA3 .even := MV.ofMultivector denseEven .even
  let odd : MV CGA3 .odd := MV.ofMultivector denseOdd .odd
  return packedMatchesDense (MV.gradeProject full k.val) (a.mv.gradeProject k.val) &&
    packedMatchesDense (MV.gradeProject even k.val) (denseEven.gradeProject k.val) &&
    packedMatchesDense (MV.gradeProject odd k.val) (denseOdd.gradeProject k.val)

/-- CGA3 packed `MV.scalarPart` agrees with dense scalar extraction across storage tags. -/
def prop_mv_cga3_scalar_part_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let denseEven := a.mv.evenPart
  let denseOdd := a.mv.oddPart
  let full : MV CGA3 .full := MV.ofMultivector a.mv .full
  let even : MV CGA3 .even := MV.ofMultivector denseEven .even
  let odd : MV CGA3 .odd := MV.ofMultivector denseOdd .odd
  return approxEq full.scalarPart a.mv.scalarPart &&
    approxEq even.scalarPart denseEven.scalarPart &&
    approxEq odd.scalarPart denseOdd.scalarPart

/-- CGA3 packed norm-squared agrees with dense references across storage tags. -/
def prop_mv_cga3_normSq_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  return packedNormSqMatchesDense a.mv

/-- CGA3 packed reverse norm-squared agrees with dense references across storage tags. -/
def prop_mv_cga3_normSqRev_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  return packedNormSqRevMatchesDense a.mv

/-- CGA3 packed scalar product agrees with dense references across storage tags. -/
def prop_mv_cga3_scalar_product_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  return packedScalarProductMatchesDense a.mv b.mv

/-- CGA3 full packed `MV` linear operations agree with dense references. -/
def prop_mv_cga3_full_linear_ops_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  let packedA : MV CGA3 .full := MV.ofMultivector a.mv .full
  let packedB : MV CGA3 .full := MV.ofMultivector b.mv .full
  let scale : Float := 1.75
  return packedMatchesDense (packedA + packedB) (a.mv + b.mv) &&
    packedMatchesDense (-packedA) (-a.mv) &&
    packedMatchesDense (scale * packedA) (a.mv.smul scale)

/-- CGA3 even packed `MV` linear operations agree with dense references. -/
def prop_mv_cga3_even_linear_ops_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  let denseA := a.mv.evenPart
  let denseB := b.mv.evenPart
  let packedA : MV CGA3 .even := MV.ofMultivector denseA .even
  let packedB : MV CGA3 .even := MV.ofMultivector denseB .even
  let scale : Float := -2.25
  return packedMatchesDense (packedA + packedB) (denseA + denseB) &&
    packedMatchesDense (-packedA) (-denseA) &&
    packedMatchesDense (scale * packedA) (denseA.smul scale)

/-- CGA3 odd packed `MV` linear operations agree with dense references. -/
def prop_mv_cga3_odd_linear_ops_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  let denseA := a.mv.oddPart
  let denseB := b.mv.oddPart
  let packedA : MV CGA3 .odd := MV.ofMultivector denseA .odd
  let packedB : MV CGA3 .odd := MV.ofMultivector denseB .odd
  let scale : Float := 0.5
  return packedMatchesDense (packedA + packedB) (denseA + denseB) &&
    packedMatchesDense (-packedA) (-denseA) &&
    packedMatchesDense (scale * packedA) (denseA.smul scale)

/-- CGA3 full packed `MV` projectors agree with dense even/odd projection. -/
def prop_mv_cga3_full_projectors_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let packed : MV CGA3 .full := MV.ofMultivector a.mv .full
  return packedMatchesDense (MV.evenPart packed) a.mv.evenPart &&
    packedMatchesDense (MV.oddPart packed) a.mv.oddPart

/-- CGA3 packed even/odd widening into full storage agrees with dense references. -/
def prop_mv_cga3_widen_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let evenPacked : MV CGA3 .even := MV.ofMultivector a.mv.evenPart .even
  let oddPacked : MV CGA3 .odd := MV.ofMultivector a.mv.oddPart .odd
  let evenFull : MV CGA3 .full := evenPacked
  let oddFull : MV CGA3 .full := oddPacked
  return packedMatchesDense evenFull a.mv.evenPart &&
    packedMatchesDense oddFull a.mv.oddPart

/-- CGA3 packed `MV.setCoeff` agrees with dense reference across storage tags. -/
def prop_mv_cga3_setCoeff_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let maskSub ← Gen.choose Nat 0 32 (by omega)
  let value ← genSmallFloat
  let mask := maskSub.val
  let full : MV CGA3 .full := MV.ofMultivector a.mv .full
  let even : MV CGA3 .even := MV.ofMultivector a.mv.evenPart .even
  let odd : MV CGA3 .odd := MV.ofMultivector a.mv.oddPart .odd
  return packedMatchesDense (full.setCoeff mask value)
      (denseAfterPackedSetCoeff .full a.mv mask value) &&
    packedMatchesDense (even.setCoeff mask value)
      (denseAfterPackedSetCoeff .even a.mv mask value) &&
    packedMatchesDense (odd.setCoeff mask value)
      (denseAfterPackedSetCoeff .odd a.mv mask value)

/-- CGA3 packed `MV.ofPairs` matches dense public constructor behavior. -/
def prop_mv_cga3_ofPairs_dense : Bool :=
  let pairs : List (Nat × Float) :=
    [(0, -0.5), (1, 1.0), (3, -2.0), (7, 4.0), (18, 5.0), (31, -6.0),
      (32, 7.0), (18, -8.0)]
  packedOfPairsMatchesDense CGA3 .full pairs &&
    packedOfPairsMatchesDense CGA3 .even pairs &&
    packedOfPairsMatchesDense CGA3 .odd pairs

/-- CGA3 packed full multiplication agrees with dense multiplication. -/
def prop_mv_cga3_full_mul_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  let packedA : MV CGA3 .full := MV.ofMultivector a.mv .full
  let packedB : MV CGA3 .full := MV.ofMultivector b.mv .full
  return packedMatchesDense (packedA * packedB) (a.mv * b.mv) (tol := 1e-6)

/-- CGA3 packed even × even multiplication agrees with dense multiplication. -/
def prop_mv_cga3_even_mul_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  let denseA := a.mv.evenPart
  let denseB := b.mv.evenPart
  let packedA : MV CGA3 .even := MV.ofMultivector denseA .even
  let packedB : MV CGA3 .even := MV.ofMultivector denseB .even
  return packedMatchesDense (packedA * packedB) (denseA * denseB) (tol := 1e-6)

/-- CGA3 packed even × odd multiplication agrees with dense multiplication. -/
def prop_mv_cga3_even_odd_mul_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  let denseA := a.mv.evenPart
  let denseB := b.mv.oddPart
  let packedA : MV CGA3 .even := MV.ofMultivector denseA .even
  let packedB : MV CGA3 .odd := MV.ofMultivector denseB .odd
  return packedMatchesDense (packedA * packedB) (denseA * denseB) (tol := 1e-6)

/-- CGA3 packed odd × even multiplication agrees with dense multiplication. -/
def prop_mv_cga3_odd_even_mul_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  let denseA := a.mv.oddPart
  let denseB := b.mv.evenPart
  let packedA : MV CGA3 .odd := MV.ofMultivector denseA .odd
  let packedB : MV CGA3 .even := MV.ofMultivector denseB .even
  return packedMatchesDense (packedA * packedB) (denseA * denseB) (tol := 1e-6)

/-- CGA3 packed odd × odd multiplication agrees with dense multiplication. -/
def prop_mv_cga3_odd_mul_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  let denseA := a.mv.oddPart
  let denseB := b.mv.oddPart
  let packedA : MV CGA3 .odd := MV.ofMultivector denseA .odd
  let packedB : MV CGA3 .odd := MV.ofMultivector denseB .odd
  return packedMatchesDense (packedA * packedB) (denseA * denseB) (tol := 1e-6)

/-- CGA3 packed wedge agrees with dense wedge across full/even/odd storage. -/
def prop_mv_cga3_wedge_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  return packedWedgeMatchesDense a.mv b.mv

/-- CGA3 packed left contraction agrees with dense left contraction across storage tags. -/
def prop_mv_cga3_left_contract_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  return packedLeftContractMatchesDense a.mv b.mv

/-- CGA3 packed right contraction agrees with dense right contraction across storage tags. -/
def prop_mv_cga3_right_contract_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  return packedRightContractMatchesDense a.mv b.mv

/-- CGA3 full packed derived products agree with dense references. -/
def prop_mv_cga3_full_derived_products_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  return packedFullDerivedProductsMatchDense a.mv b.mv

/-- CGA3 packed reverse agrees with dense reverse. -/
def prop_mv_cga3_reverse_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let denseEven := a.mv.evenPart
  let denseOdd := a.mv.oddPart
  let full : MV CGA3 .full := MV.ofMultivector a.mv .full
  let even : MV CGA3 .even := MV.ofMultivector denseEven .even
  let odd : MV CGA3 .odd := MV.ofMultivector denseOdd .odd
  return packedMatchesDense (MV.rev full) a.mv.reverse &&
    packedMatchesDense (MV.rev even) denseEven.reverse &&
    packedMatchesDense (MV.rev odd) denseOdd.reverse

/-- CGA3 packed involute and Clifford conjugate agree with dense involutions. -/
def prop_mv_cga3_involutions_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let denseEven := a.mv.evenPart
  let denseOdd := a.mv.oddPart
  let full : MV CGA3 .full := MV.ofMultivector a.mv .full
  let even : MV CGA3 .even := MV.ofMultivector denseEven .even
  let odd : MV CGA3 .odd := MV.ofMultivector denseOdd .odd
  return packedMatchesDense (MV.involute full) a.mv.involute &&
    packedMatchesDense (MV.conjugate full) a.mv.conjugate &&
    packedMatchesDense (MV.involute even) denseEven.involute &&
    packedMatchesDense (MV.conjugate even) denseEven.conjugate &&
    packedMatchesDense (MV.involute odd) denseOdd.involute &&
    packedMatchesDense (MV.conjugate odd) denseOdd.conjugate

/-- CGA3 packed sandwich product agrees with dense sandwich product for even versors. -/
def prop_mv_cga3_sandwich_dense : Gen Bool := do
  let r ← genCGA3DenseMv
  let x ← genCGA3DenseMv
  let denseR := r.mv.evenPart
  let denseX := x.mv.oddPart
  let packedR : MV CGA3 .even := MV.ofMultivector denseR .even
  let packedX : MV CGA3 .odd := MV.ofMultivector denseX .odd
  return packedMatchesDense (mvSandwich packedR packedX) (denseR.sandwich denseX) (tol := 1e-6)

/-- CGA3 full packed `MV` `GAlgebra` operations agree with dense references. -/
def prop_mv_cga3_galgebra_ops_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  let k ← Gen.choose Nat 0 5 (by omega)
  let scale ← genSmallFloat
  return packedGAlgebraOpsMatchDense (sig := CGA3) a.mv b.mv k.val scale

/-- CGA3 packed full `MV` `GAlgebra` dispatch agrees with dense sandwiching. -/
def prop_mv_cga3_galgebra_sandwich_dense : Gen Bool := do
  let r ← genCGA3DenseMv
  let x ← genCGA3DenseMv
  let packedR : MV CGA3 .full := MV.ofMultivector r.mv .full
  let packedX : MV CGA3 .full := MV.ofMultivector x.mv .full
  let generic :=
    Grassmann.sandwich (sig := CGA3) (M := MV CGA3 .full) (F := Float) packedR packedX
  return packedMatchesDense generic (r.mv.sandwich x.mv) (tol := 1e-6)

/-- CGA3 packed full `MV` `GAlgebra` normSq agrees with dense normSq. -/
def prop_mv_cga3_galgebra_normSq_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let packed : MV CGA3 .full := MV.ofMultivector a.mv .full
  return approxEq
    (Grassmann.normSq (sig := CGA3) (M := MV CGA3 .full) (F := Float) packed)
    a.mv.normSq (tol := 1e-6)

/-- CGA3 packed full `MV` generic normalization/inverse helpers agree with dense references. -/
def prop_mv_cga3_galgebra_unit_helpers_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  return packedGAlgebraUnitHelpersMatchDense (sig := CGA3) a.mv

/-! ## Sparse Reference Tests -/

/-- Sparse addition agrees with dense addition. -/
def prop_sparse_add_dense (a b : R3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (a.mv + b.mv) (denseA + denseB)

/-- Sparse geometric multiplication agrees with dense multiplication. -/
def prop_sparse_mul_dense (a b : R3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (a.mv * b.mv) (denseA * denseB) (tol := 1e-6)

/-- Sparse wedge product agrees with dense wedge product. -/
def prop_sparse_wedge_dense (a b : R3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (a.mv ⋀ₛ b.mv) (denseA ⋀ᵐ denseB) (tol := 1e-6)

/-- Sparse left contraction agrees with dense left contraction. -/
def prop_sparse_leftContract_dense (a b : R3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (MultivectorS.leftContract a.mv b.mv) (denseA ⌋ᵐ denseB)
    (tol := 1e-6)

/-- Sparse right contraction agrees with dense right contraction. -/
def prop_sparse_rightContract_dense (a b : R3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (MultivectorS.rightContract a.mv b.mv) (denseA ⌊ᵐ denseB)
    (tol := 1e-6)

/-- Sparse scalar product agrees with dense scalar product. -/
def prop_sparse_scalarProduct_dense (a b : R3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  approxEq (MultivectorS.scalarProduct a.mv b.mv) (denseA.scalarProduct denseB)
    (tol := 1e-6)

/-- Sparse inner product agrees with dense grade-decomposition reference. -/
def prop_sparse_innerProduct_dense (a b : R3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (MultivectorS.innerProduct a.mv b.mv)
    (denseInnerProductRef denseA denseB) (tol := 1e-6)

/-- Sparse regressive product agrees with dense regressive product. -/
def prop_sparse_regressive_dense (a b : R3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (a.mv ∨ₛ b.mv) (denseA ⋁ᵐ denseB) (tol := 1e-6)

/-- Sparse commutator agrees with dense commutator. -/
def prop_sparse_commutator_dense (a b : R3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (MultivectorS.commutatorProduct a.mv b.mv)
    (Multivector.commutator denseA denseB) (tol := 1e-6)

/-- Sparse anticommutator agrees with dense anticommutator. -/
def prop_sparse_anticommutator_dense (a b : R3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (MultivectorS.anticommutatorProduct a.mv b.mv)
    (Multivector.antiCommutator denseA denseB) (tol := 1e-6)

/-- Sparse reverse agrees with dense reverse. -/
def prop_sparse_reverse_dense (a : R3Mv) : Bool :=
  sparseMatchesDense a.mv.reverse (sparseToDenseRef a.mv).reverse

/-- Sparse involute agrees with dense involute. -/
def prop_sparse_involute_dense (a : R3Mv) : Bool :=
  sparseMatchesDense a.mv.involute (sparseToDenseRef a.mv).involute

/-- Sparse conjugate agrees with dense conjugate. -/
def prop_sparse_conjugate_dense (a : R3Mv) : Bool :=
  sparseMatchesDense a.mv.conjugate (sparseToDenseRef a.mv).conjugate

/-- Sparse grade projection agrees with dense grade projection. -/
def prop_sparse_gradeProject_dense : Gen Bool := do
  let a : R3Mv ← Arbitrary.arbitrary
  let k ← Gen.choose Nat 0 3 (by omega)
  return sparseMatchesDense (a.mv.gradeProject k.val) ((sparseToDenseRef a.mv).gradeProject k.val)

/-- Sparse `GAlgebra` operations agree with dense references through the polymorphic API. -/
def sparseGAlgebraOpsMatchDense {n : Nat} {sig : Signature n}
    (a b : MultivectorS sig Float) (k : Nat) (scale : Float)
    (tol : Float := 1e-6) : Bool :=
  let inst := (inferInstance : GAlgebra sig (MultivectorS sig Float) Float)
  let denseA := sparseToDenseRef a
  let denseB := sparseToDenseRef b
  let basisOk :=
    (List.finRange n).all fun i =>
      sparseMatchesDense (inst.basisVector i) (Multivector.basis i) tol
  let bladeOk :=
    (List.range (2 ^ n)).all fun mask =>
      sparseMatchesDense
        (inst.blade (BitVec.ofNat n mask))
        (Multivector.ofBlade ⟨BitVec.ofNat n mask⟩ : Multivector sig Float)
        tol
  sparseMatchesDense inst.zero Multivector.zero tol &&
    sparseMatchesDense inst.one Multivector.one tol &&
    sparseMatchesDense (inst.scalar scale) (Multivector.scalar scale) tol &&
    basisOk &&
    bladeOk &&
    sparseMatchesDense (inst.add a b) (denseA + denseB) tol &&
    sparseMatchesDense (inst.neg a) (-denseA) tol &&
    sparseMatchesDense (inst.smul scale a) (denseA.smul scale) tol &&
    sparseMatchesDense (inst.mul a b) (denseA * denseB) tol &&
    sparseMatchesDense (inst.wedge a b) (denseA ⋀ᵐ denseB) tol &&
    sparseMatchesDense (inst.leftContract a b) (denseA ⌋ᵐ denseB) tol &&
    sparseMatchesDense (inst.rightContract a b) (denseA ⌊ᵐ denseB) tol &&
    sparseMatchesDense (inst.reverse a) denseA.reverse tol &&
    sparseMatchesDense (inst.involute a) denseA.involute tol &&
    sparseMatchesDense (inst.conjugate a) denseA.conjugate tol &&
    sparseMatchesDense (inst.gradeProject a k) (denseA.gradeProject k) tol &&
    approxEq (inst.scalarPart a) denseA.scalarPart tol

/-- R3 sparse `GAlgebra` operations agree with dense references. -/
def prop_sparse_galgebra_ops_dense : Gen Bool := do
  let a : R3Mv ← Arbitrary.arbitrary
  let b : R3Mv ← Arbitrary.arbitrary
  let k ← Gen.choose Nat 0 3 (by omega)
  let scale ← genSmallFloat
  return sparseGAlgebraOpsMatchDense (sig := R3) a.mv b.mv k.val scale

/-- Sparse grade projection is idempotent for all grades up to `maxGrade`. -/
def sparseGradeProjectIdempotent {n : Nat} {sig : Signature n} (maxGrade : Nat)
    (m : MultivectorS sig Float) : Bool :=
  (List.range (maxGrade + 1)).all fun k =>
    mvApproxEq ((m.gradeProject k).gradeProject k) (m.gradeProject k)

/-- Distinct sparse grade projections are orthogonal. -/
def sparseGradeProjectOrthogonal {n : Nat} {sig : Signature n} (maxGrade : Nat)
    (m : MultivectorS sig Float) : Bool :=
  (List.range (maxGrade + 1)).all fun j =>
    (List.range (maxGrade + 1)).all fun k =>
      j == k || mvApproxEq ((m.gradeProject j).gradeProject k) (0 : MultivectorS sig Float)

/-- Summing all sparse grade projections reconstructs the multivector. -/
def sparseGradeProjectDecomposition {n : Nat} {sig : Signature n} (maxGrade : Nat)
    (m : MultivectorS sig Float) : Bool :=
  let projected := (List.range (maxGrade + 1)).foldl
    (init := (0 : MultivectorS sig Float)) fun acc k => acc + m.gradeProject k
  mvApproxEq projected m

/-- R3 sparse grade projections are idempotent. -/
def prop_sparse_gradeProject_idempotent (a : R3Mv) : Bool :=
  sparseGradeProjectIdempotent 3 a.mv

/-- R3 distinct sparse grade projections are orthogonal. -/
def prop_sparse_gradeProject_orthogonal (a : R3Mv) : Bool :=
  sparseGradeProjectOrthogonal 3 a.mv

/-- R3 sparse grade projections decompose the multivector. -/
def prop_sparse_gradeProject_decomposition (a : R3Mv) : Bool :=
  sparseGradeProjectDecomposition 3 a.mv

/-! ## PGA3 Sparse Reference Tests -/

/-- PGA3 sparse addition agrees with dense addition. -/
def prop_sparse_pga3_add_dense (a b : PGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (a.mv + b.mv) (denseA + denseB)

/-- PGA3 sparse geometric multiplication agrees with dense multiplication. -/
def prop_sparse_pga3_mul_dense (a b : PGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (a.mv * b.mv) (denseA * denseB) (tol := 1e-6)

/-- PGA3 sparse wedge product agrees with dense wedge product. -/
def prop_sparse_pga3_wedge_dense (a b : PGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (a.mv ⋀ₛ b.mv) (denseA ⋀ᵐ denseB) (tol := 1e-6)

/-- PGA3 sparse left contraction agrees with dense left contraction. -/
def prop_sparse_pga3_leftContract_dense (a b : PGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (MultivectorS.leftContract a.mv b.mv) (denseA ⌋ᵐ denseB)
    (tol := 1e-6)

/-- PGA3 sparse right contraction agrees with dense right contraction. -/
def prop_sparse_pga3_rightContract_dense (a b : PGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (MultivectorS.rightContract a.mv b.mv) (denseA ⌊ᵐ denseB)
    (tol := 1e-6)

/-- PGA3 sparse scalar product agrees with dense scalar product. -/
def prop_sparse_pga3_scalarProduct_dense (a b : PGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  approxEq (MultivectorS.scalarProduct a.mv b.mv) (denseA.scalarProduct denseB)
    (tol := 1e-6)

/-- PGA3 sparse inner product agrees with dense grade-decomposition reference. -/
def prop_sparse_pga3_innerProduct_dense (a b : PGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (MultivectorS.innerProduct a.mv b.mv)
    (denseInnerProductRef denseA denseB) (tol := 1e-6)

/-- PGA3 sparse regressive product agrees with dense regressive product. -/
def prop_sparse_pga3_regressive_dense (a b : PGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (a.mv ∨ₛ b.mv) (denseA ⋁ᵐ denseB) (tol := 1e-6)

/-- PGA3 sparse commutator agrees with dense commutator. -/
def prop_sparse_pga3_commutator_dense (a b : PGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (MultivectorS.commutatorProduct a.mv b.mv)
    (Multivector.commutator denseA denseB) (tol := 1e-6)

/-- PGA3 sparse anticommutator agrees with dense anticommutator. -/
def prop_sparse_pga3_anticommutator_dense (a b : PGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (MultivectorS.anticommutatorProduct a.mv b.mv)
    (Multivector.antiCommutator denseA denseB) (tol := 1e-6)

/-- PGA3 sparse reverse agrees with dense reverse. -/
def prop_sparse_pga3_reverse_dense (a : PGA3Mv) : Bool :=
  sparseMatchesDense a.mv.reverse (sparseToDenseRef a.mv).reverse

/-- PGA3 sparse involute agrees with dense involute. -/
def prop_sparse_pga3_involute_dense (a : PGA3Mv) : Bool :=
  sparseMatchesDense a.mv.involute (sparseToDenseRef a.mv).involute

/-- PGA3 sparse conjugate agrees with dense conjugate. -/
def prop_sparse_pga3_conjugate_dense (a : PGA3Mv) : Bool :=
  sparseMatchesDense a.mv.conjugate (sparseToDenseRef a.mv).conjugate

/-- PGA3 sparse grade projection agrees with dense grade projection. -/
def prop_sparse_pga3_gradeProject_dense : Gen Bool := do
  let a : PGA3Mv ← Arbitrary.arbitrary
  let k ← Gen.choose Nat 0 4 (by omega)
  return sparseMatchesDense (a.mv.gradeProject k.val) ((sparseToDenseRef a.mv).gradeProject k.val)

/-- PGA3 sparse `GAlgebra` operations agree with dense references. -/
def prop_sparse_pga3_galgebra_ops_dense : Gen Bool := do
  let a : PGA3Mv ← Arbitrary.arbitrary
  let b : PGA3Mv ← Arbitrary.arbitrary
  let k ← Gen.choose Nat 0 4 (by omega)
  let scale ← genSmallFloat
  return sparseGAlgebraOpsMatchDense (sig := PGA3) a.mv b.mv k.val scale

/-- PGA3 sparse grade projections are idempotent. -/
def prop_sparse_pga3_gradeProject_idempotent (a : PGA3Mv) : Bool :=
  sparseGradeProjectIdempotent 4 a.mv

/-- PGA3 distinct sparse grade projections are orthogonal. -/
def prop_sparse_pga3_gradeProject_orthogonal (a : PGA3Mv) : Bool :=
  sparseGradeProjectOrthogonal 4 a.mv

/-- PGA3 sparse grade projections decompose the multivector. -/
def prop_sparse_pga3_gradeProject_decomposition (a : PGA3Mv) : Bool :=
  sparseGradeProjectDecomposition 4 a.mv

/-! ## CGA3 Sparse Reference Tests -/

/-- CGA3 sparse addition agrees with dense addition. -/
def prop_sparse_cga3_add_dense (a b : CGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (a.mv + b.mv) (denseA + denseB)

/-- CGA3 sparse geometric multiplication agrees with dense multiplication. -/
def prop_sparse_cga3_mul_dense (a b : CGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (a.mv * b.mv) (denseA * denseB) (tol := 1e-6)

/-- CGA3 sparse wedge product agrees with dense wedge product. -/
def prop_sparse_cga3_wedge_dense (a b : CGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (a.mv ⋀ₛ b.mv) (denseA ⋀ᵐ denseB) (tol := 1e-6)

/-- CGA3 sparse left contraction agrees with dense left contraction. -/
def prop_sparse_cga3_leftContract_dense (a b : CGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (MultivectorS.leftContract a.mv b.mv) (denseA ⌋ᵐ denseB)
    (tol := 1e-6)

/-- CGA3 sparse right contraction agrees with dense right contraction. -/
def prop_sparse_cga3_rightContract_dense (a b : CGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (MultivectorS.rightContract a.mv b.mv) (denseA ⌊ᵐ denseB)
    (tol := 1e-6)

/-- CGA3 sparse scalar product agrees with dense scalar product. -/
def prop_sparse_cga3_scalarProduct_dense (a b : CGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  approxEq (MultivectorS.scalarProduct a.mv b.mv) (denseA.scalarProduct denseB)
    (tol := 1e-6)

/-- CGA3 sparse inner product agrees with dense grade-decomposition reference. -/
def prop_sparse_cga3_innerProduct_dense (a b : CGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (MultivectorS.innerProduct a.mv b.mv)
    (denseInnerProductRef denseA denseB) (tol := 1e-6)

/-- CGA3 sparse regressive product agrees with dense regressive product. -/
def prop_sparse_cga3_regressive_dense (a b : CGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (a.mv ∨ₛ b.mv) (denseA ⋁ᵐ denseB) (tol := 1e-6)

/-- CGA3 sparse commutator agrees with dense commutator. -/
def prop_sparse_cga3_commutator_dense (a b : CGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (MultivectorS.commutatorProduct a.mv b.mv)
    (Multivector.commutator denseA denseB) (tol := 1e-6)

/-- CGA3 sparse anticommutator agrees with dense anticommutator. -/
def prop_sparse_cga3_anticommutator_dense (a b : CGA3Mv) : Bool :=
  let denseA := sparseToDenseRef a.mv
  let denseB := sparseToDenseRef b.mv
  sparseMatchesDense (MultivectorS.anticommutatorProduct a.mv b.mv)
    (Multivector.antiCommutator denseA denseB) (tol := 1e-6)

/-- CGA3 sparse reverse agrees with dense reverse. -/
def prop_sparse_cga3_reverse_dense (a : CGA3Mv) : Bool :=
  sparseMatchesDense a.mv.reverse (sparseToDenseRef a.mv).reverse

/-- CGA3 sparse involute agrees with dense involute. -/
def prop_sparse_cga3_involute_dense (a : CGA3Mv) : Bool :=
  sparseMatchesDense a.mv.involute (sparseToDenseRef a.mv).involute

/-- CGA3 sparse conjugate agrees with dense conjugate. -/
def prop_sparse_cga3_conjugate_dense (a : CGA3Mv) : Bool :=
  sparseMatchesDense a.mv.conjugate (sparseToDenseRef a.mv).conjugate

/-- CGA3 sparse grade projection agrees with dense grade projection. -/
def prop_sparse_cga3_gradeProject_dense : Gen Bool := do
  let a : CGA3Mv ← Arbitrary.arbitrary
  let k ← Gen.choose Nat 0 5 (by omega)
  return sparseMatchesDense (a.mv.gradeProject k.val) ((sparseToDenseRef a.mv).gradeProject k.val)

/-- CGA3 sparse `GAlgebra` operations agree with dense references. -/
def prop_sparse_cga3_galgebra_ops_dense : Gen Bool := do
  let a : CGA3Mv ← Arbitrary.arbitrary
  let b : CGA3Mv ← Arbitrary.arbitrary
  let k ← Gen.choose Nat 0 5 (by omega)
  let scale ← genSmallFloat
  return sparseGAlgebraOpsMatchDense (sig := CGA3) a.mv b.mv k.val scale

/-- CGA3 sparse grade projections are idempotent. -/
def prop_sparse_cga3_gradeProject_idempotent (a : CGA3Mv) : Bool :=
  sparseGradeProjectIdempotent 5 a.mv

/-- CGA3 distinct sparse grade projections are orthogonal. -/
def prop_sparse_cga3_gradeProject_orthogonal (a : CGA3Mv) : Bool :=
  sparseGradeProjectOrthogonal 5 a.mv

/-- CGA3 sparse grade projections decompose the multivector. -/
def prop_sparse_cga3_gradeProject_decomposition (a : CGA3Mv) : Bool :=
  sparseGradeProjectDecomposition 5 a.mv

/-! ## Truncated MV Reference Tests -/

/-- Truncated `GAlgebra` operations agree with dense references after truncation. -/
def truncatedGAlgebraOpsMatchDense {n : Nat} {sig : Signature n} {maxGrade : Nat}
    (a b : Multivector sig Float) (k : Nat) (scale : Float)
    (tol : Float := 1e-6) : Bool :=
  let inst := (inferInstance : GAlgebra sig (TruncatedMV sig maxGrade Float) Float)
  let truncA := truncatedOfDense (maxGrade := maxGrade) a
  let truncB := truncatedOfDense (maxGrade := maxGrade) b
  let denseA := truncateDenseToGrade maxGrade a
  let denseB := truncateDenseToGrade maxGrade b
  let basisOk :=
    (List.finRange n).all fun i =>
      truncatedMatchesDense (inst.basisVector i) (Multivector.basis i) tol
  let bladeOk :=
    (List.range (2 ^ n)).all fun mask =>
      truncatedMatchesDense
        (inst.blade (BitVec.ofNat n mask))
        (Multivector.ofBlade ⟨BitVec.ofNat n mask⟩ : Multivector sig Float)
        tol
  truncatedMatchesDense inst.zero Multivector.zero tol &&
    truncatedMatchesDense inst.one Multivector.one tol &&
    truncatedMatchesDense (inst.scalar scale) (Multivector.scalar scale) tol &&
    basisOk &&
    bladeOk &&
    truncatedMatchesDense (inst.add truncA truncB) (denseA + denseB) tol &&
    truncatedMatchesDense (inst.neg truncA) (-denseA) tol &&
    truncatedMatchesDense (inst.smul scale truncA) (denseA.smul scale) tol &&
    truncatedMatchesDense (inst.mul truncA truncB) (denseA * denseB) tol &&
    truncatedMatchesDense (inst.wedge truncA truncB) (denseA ⋀ᵐ denseB) tol &&
    truncatedMatchesDense (inst.leftContract truncA truncB) (denseA ⌋ᵐ denseB) tol &&
    truncatedMatchesDense (inst.rightContract truncA truncB) (denseA ⌊ᵐ denseB) tol &&
    truncatedMatchesDense (inst.reverse truncA) denseA.reverse tol &&
    truncatedMatchesDense (inst.involute truncA) denseA.involute tol &&
    truncatedMatchesDense (inst.conjugate truncA) denseA.conjugate tol &&
    truncatedMatchesDense (inst.gradeProject truncA k) (denseA.gradeProject k) tol &&
    approxEq (inst.scalarPart truncA) denseA.scalarPart tol

/-- PGA3 truncated multiplication preserves the null projective basis square. -/
def prop_truncated_pga3_null_basis_square : Bool :=
  let e0T : TruncatedMV PGA3 2 Float := TruncatedMV.basis ⟨3, by omega⟩
  let e0Dense : Multivector PGA3 Float := Multivector.basis ⟨3, by omega⟩
  truncatedMatchesDense (e0T * e0T) (e0Dense * e0Dense) (tol := 1e-9)

/-- R3 truncated `GAlgebra` operations agree with dense references up to grade 2. -/
def prop_truncated_r3_galgebra_ops_dense : Gen Bool := do
  let a ← genR3DenseMv
  let b ← genR3DenseMv
  let k ← Gen.choose Nat 0 3 (by omega)
  let scale ← genSmallFloat
  return truncatedGAlgebraOpsMatchDense (sig := R3) (maxGrade := 2)
    a.mv b.mv k.val scale

/-- PGA3 truncated `GAlgebra` operations agree with dense references up to grade 2. -/
def prop_truncated_pga3_galgebra_ops_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let b ← genPGA3DenseMv
  let k ← Gen.choose Nat 0 4 (by omega)
  let scale ← genSmallFloat
  return truncatedGAlgebraOpsMatchDense (sig := PGA3) (maxGrade := 2)
    a.mv b.mv k.val scale

/-- CGA3 truncated `GAlgebra` operations agree with dense references up to grade 2. -/
def prop_truncated_cga3_galgebra_ops_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let b ← genCGA3DenseMv
  let k ← Gen.choose Nat 0 5 (by omega)
  let scale ← genSmallFloat
  return truncatedGAlgebraOpsMatchDense (sig := CGA3) (maxGrade := 2)
    a.mv b.mv k.val scale

/-! ## Representation Conversion Tests -/

/-- R3 dense → sparse → dense round-trip preserves coefficients. -/
def prop_repr_r3_dense_sparse_roundtrip : Gen Bool := do
  let a ← genR3DenseMv
  return denseSparseRoundtripMatches a.mv

/-- R3 sparse → dense → sparse round-trip preserves coefficients. -/
def prop_repr_r3_sparse_dense_roundtrip (a : R3Mv) : Bool :=
  sparseDenseRoundtripMatches a.mv

/-- PGA3 dense → sparse → dense round-trip preserves coefficients. -/
def prop_repr_pga3_dense_sparse_roundtrip : Gen Bool := do
  let a ← genPGA3DenseMv
  return denseSparseRoundtripMatches a.mv

/-- PGA3 sparse → dense → sparse round-trip preserves coefficients. -/
def prop_repr_pga3_sparse_dense_roundtrip (a : PGA3Mv) : Bool :=
  sparseDenseRoundtripMatches a.mv

/-- CGA3 dense → sparse → dense round-trip preserves coefficients. -/
def prop_repr_cga3_dense_sparse_roundtrip : Gen Bool := do
  let a ← genCGA3DenseMv
  return denseSparseRoundtripMatches a.mv

/-- CGA3 sparse → dense → sparse round-trip preserves coefficients. -/
def prop_repr_cga3_sparse_dense_roundtrip (a : CGA3Mv) : Bool :=
  sparseDenseRoundtripMatches a.mv

/-! ## Algebraic Properties -/

/-- Commutativity of addition -/
def prop_add_comm (a b : R3Mv) : Bool :=
  mvApproxEq (a.mv + b.mv) (b.mv + a.mv)

/-- Associativity of addition -/
def prop_add_assoc (a b c : R3Mv) : Bool :=
  mvApproxEq ((a.mv + b.mv) + c.mv) (a.mv + (b.mv + c.mv))

/-- Zero is additive identity -/
def prop_add_zero (a : R3Mv) : Bool :=
  mvApproxEq (a.mv + 0) a.mv && mvApproxEq (0 + a.mv) a.mv

/-- Negation gives additive inverse -/
def prop_add_neg (a : R3Mv) : Bool :=
  mvApproxEq (a.mv + (-a.mv)) 0

/-- Associativity of geometric product -/
def prop_mul_assoc (a b c : R3Mv) : Bool :=
  -- Use looser tolerance for products due to floating point accumulation
  mvApproxEq ((a.mv * b.mv) * c.mv) (a.mv * (b.mv * c.mv)) (tol := 1e-6)

/-- One is multiplicative identity -/
def prop_mul_one (a : R3Mv) : Bool :=
  mvApproxEq (a.mv * 1) a.mv && mvApproxEq (1 * a.mv) a.mv

/-- Left contraction by scalar one keeps all grades, not only the scalar part. -/
def prop_scalar_left_contraction_keeps_all_grades : Bool :=
  let denseE1 : Multivector R3 Float := Multivector.basis ⟨0, by omega⟩
  let denseA : Multivector R3 Float := Multivector.scalar 2.0 + denseE1
  let denseLhs := (1 : Multivector R3 Float) ⌋ᵐ denseA
  let sparseE1 : MultivectorS R3 Float := MultivectorS.basis ⟨0, by omega⟩
  let sparseA : MultivectorS R3 Float := MultivectorS.scalar 2.0 + sparseE1
  let sparseLhs := MultivectorS.leftContract (1 : MultivectorS R3 Float) sparseA
  denseMvApproxEq denseLhs denseA (tol := 1e-12) &&
    !denseMvApproxEq denseLhs denseA.grade0 (tol := 1e-12) &&
    approxEq (denseLhs.coeffs ⟨1, by omega⟩) 1.0 (tol := 1e-12) &&
    mvApproxEq sparseLhs sparseA (tol := 1e-12) &&
    !mvApproxEq sparseLhs (sparseA.gradeProject 0) (tol := 1e-12) &&
    approxEq (sparseLhs.coeff 1) 1.0 (tol := 1e-12)

/-- Right contraction by scalar one keeps all grades, not only the scalar part. -/
def prop_scalar_right_contraction_keeps_all_grades : Bool :=
  let denseE1 : Multivector R3 Float := Multivector.basis ⟨0, by omega⟩
  let denseA : Multivector R3 Float := Multivector.scalar 2.0 + denseE1
  let denseLhs := denseA ⌊ᵐ (1 : Multivector R3 Float)
  let sparseE1 : MultivectorS R3 Float := MultivectorS.basis ⟨0, by omega⟩
  let sparseA : MultivectorS R3 Float := MultivectorS.scalar 2.0 + sparseE1
  let sparseLhs := MultivectorS.rightContract sparseA (1 : MultivectorS R3 Float)
  denseMvApproxEq denseLhs denseA (tol := 1e-12) &&
    !denseMvApproxEq denseLhs denseA.grade0 (tol := 1e-12) &&
    approxEq (denseLhs.coeffs ⟨1, by omega⟩) 1.0 (tol := 1e-12) &&
    mvApproxEq sparseLhs sparseA (tol := 1e-12) &&
    !mvApproxEq sparseLhs (sparseA.gradeProject 0) (tol := 1e-12) &&
    approxEq (sparseLhs.coeff 1) 1.0 (tol := 1e-12)

/-- Scalar part alone does not prove `R * R† = 1` as a full multivector. -/
def prop_unit_rotor_scalar_part_hypothesis_insufficient : Bool :=
  let c := 1.0 / Float.sqrt 2.0
  let e1 : MultivectorS R3 Float := MultivectorS.basis ⟨0, by omega⟩
  let R : MultivectorS R3 Float := MultivectorS.scalar c + e1.smul c
  let rr := R * R†ₛ
  let denseE1 : Multivector R3 Float := Multivector.basis ⟨0, by omega⟩
  let denseR : Multivector R3 Float := Multivector.scalar c + denseE1.smul c
  let denseRR := denseR * denseR†
  let sparseHasNonScalar :=
    approxEq rr.scalarPart 1.0 (tol := 1e-12) &&
    approxEq (rr.coeff 1) 1.0 (tol := 1e-12) &&
    !mvApproxEq rr (MultivectorS.scalar 1.0 : MultivectorS R3 Float) (tol := 1e-12)
  let denseHasNonScalar :=
    approxEq denseRR.scalarPart 1.0 (tol := 1e-12) &&
    approxEq (denseRR.coeffs ⟨1, by omega⟩) 1.0 (tol := 1e-12) &&
    !denseMvApproxEq denseRR (Multivector.scalar 1.0 : Multivector R3 Float) (tol := 1e-12)
  sparseHasNonScalar && denseHasNonScalar

/-- Scalar-part normalization alone does not make sandwiching norm-preserving. -/
def prop_scalar_part_rotor_hypothesis_does_not_preserve_norm : Bool :=
  let c := 1.0 / Float.sqrt 2.0
  let e1 : Multivector R3 Float := Multivector.basis ⟨0, by omega⟩
  let e2 : Multivector R3 Float := Multivector.basis ⟨1, by omega⟩
  let R : Multivector R3 Float := Multivector.scalar c + e1.smul c
  let rr := R * R†
  let sandwiched := R * e2 * R†
  approxEq rr.scalarPart 1.0 (tol := 1e-12) &&
    !denseMvApproxEq rr (Multivector.scalar 1.0 : Multivector R3 Float) (tol := 1e-12) &&
    approxEq e2.norm 1.0 (tol := 1e-12) &&
    approxEq sandwiched.norm 0.0 (tol := 1e-12)

/-- Nonzero reverse norm alone does not make `R† / normSq` a right inverse. -/
def prop_reverse_norm_formula_requires_scalar_reverse_product : Bool :=
  let e1 : Multivector R3 Float := Multivector.basis ⟨0, by omega⟩
  let R : Multivector R3 Float := Multivector.scalar 1.0 + e1
  let rr := R * R†
  let candidate := R * (R†.smul (1.0 / R.normSq))
  approxEq R.normSq 2.0 (tol := 1e-12) &&
    !denseMvApproxEq rr (Multivector.scalar R.normSq : Multivector R3 Float) (tol := 1e-12) &&
    approxEq candidate.scalarPart 1.0 (tol := 1e-12) &&
    approxEq (candidate.coeffs ⟨1, by omega⟩) 1.0 (tol := 1e-12) &&
    !denseMvApproxEq candidate (Multivector.one : Multivector R3 Float) (tol := 1e-12)

/-- The scalar unit is a two-sided identity for the sparse wedge product. -/
def sparseWedgeOneIdentity {n : Nat} {sig : Signature n}
    (m : MultivectorS sig Float) : Bool :=
  let one : MultivectorS sig Float := 1
  mvApproxEq (one ⋀ₛ m) m && mvApproxEq (m ⋀ₛ one) m

/-- R3 sparse wedge has scalar one as a two-sided identity. -/
def prop_wedge_one_identity (a : R3Mv) : Bool :=
  sparseWedgeOneIdentity a.mv

/-- PGA3 sparse wedge has scalar one as a two-sided identity. -/
def prop_pga3_wedge_one_identity (a : PGA3Mv) : Bool :=
  sparseWedgeOneIdentity a.mv

/-- CGA3 sparse wedge has scalar one as a two-sided identity. -/
def prop_cga3_wedge_one_identity (a : CGA3Mv) : Bool :=
  sparseWedgeOneIdentity a.mv

/-- Left distributivity -/
def prop_left_distrib (a b c : R3Mv) : Bool :=
  mvApproxEq (a.mv * (b.mv + c.mv)) (a.mv * b.mv + a.mv * c.mv) (tol := 1e-6)

/-- Right distributivity -/
def prop_right_distrib (a b c : R3Mv) : Bool :=
  mvApproxEq ((a.mv + b.mv) * c.mv) (a.mv * c.mv + b.mv * c.mv) (tol := 1e-6)

/-- Wedge product anticommutativity for grade-1 elements -/
def prop_wedge_anticomm_grade1 : Gen Bool := do
  -- Generate pure vectors (grade 1)
  let c1 ← genSmallFloat
  let c2 ← genSmallFloat
  let c3 ← genSmallFloat
  let d1 ← genSmallFloat
  let d2 ← genSmallFloat
  let d3 ← genSmallFloat
  let v : MultivectorS R3 Float := MultivectorS.ofList [(1, c1), (2, c2), (4, c3)]
  let w : MultivectorS R3 Float := MultivectorS.ofList [(1, d1), (2, d2), (4, d3)]
  let vw := v.wedgeProduct w
  let wv := w.wedgeProduct v
  return mvApproxEq vw (-wv) (tol := 1e-6)

/-- Reverse is an anti-automorphism: (ab)† = b†a† -/
def prop_reverse_antimorphism (a b : R3Mv) : Bool :=
  let ab := a.mv * b.mv
  let rev_ab := ab.reverse
  let rev_a_rev_b := b.mv.reverse * a.mv.reverse
  mvApproxEq rev_ab rev_a_rev_b (tol := 1e-6)

/-- Reverse is involutive: (a†)† = a -/
def prop_reverse_involutive (a : R3Mv) : Bool :=
  mvApproxEq a.mv.reverse.reverse a.mv

/-- Grade involution is involutive: (â)^ = a -/
def prop_involute_involutive (a : R3Mv) : Bool :=
  mvApproxEq a.mv.involute.involute a.mv

/-- Clifford conjugate is involutive -/
def prop_conjugate_involutive (a : R3Mv) : Bool :=
  mvApproxEq a.mv.conjugate.conjugate a.mv

/-! ## Basis Vector Properties -/

/-- R3 basis vectors square to 1 -/
def prop_R3_basis_squares : Bool :=
  let e1 : MultivectorS R3 Float := MultivectorS.basis ⟨0, by omega⟩
  let e2 : MultivectorS R3 Float := MultivectorS.basis ⟨1, by omega⟩
  let e3 : MultivectorS R3 Float := MultivectorS.basis ⟨2, by omega⟩
  approxEq (e1 * e1).scalarPart 1.0 &&
  approxEq (e2 * e2).scalarPart 1.0 &&
  approxEq (e3 * e3).scalarPart 1.0

/-- Distinct R3 basis vectors anticommute -/
def prop_R3_basis_anticommute : Bool :=
  let e1 : MultivectorS R3 Float := MultivectorS.basis ⟨0, by omega⟩
  let e2 : MultivectorS R3 Float := MultivectorS.basis ⟨1, by omega⟩
  let e3 : MultivectorS R3 Float := MultivectorS.basis ⟨2, by omega⟩
  mvApproxEq (e1 * e2) (-(e2 * e1)) &&
  mvApproxEq (e2 * e3) (-(e3 * e2)) &&
  mvApproxEq (e1 * e3) (-(e3 * e1))

/-- CGA3 signature verification -/
def prop_CGA3_signature : Bool :=
  let w1 : MultivectorS CGA3 Float := MultivectorS.basis ⟨0, by omega⟩
  let w2 : MultivectorS CGA3 Float := MultivectorS.basis ⟨1, by omega⟩
  let w3 : MultivectorS CGA3 Float := MultivectorS.basis ⟨2, by omega⟩
  let w4 : MultivectorS CGA3 Float := MultivectorS.basis ⟨3, by omega⟩
  let w5 : MultivectorS CGA3 Float := MultivectorS.basis ⟨4, by omega⟩
  approxEq (w1 * w1).scalarPart 1.0 &&
  approxEq (w2 * w2).scalarPart 1.0 &&
  approxEq (w3 * w3).scalarPart 1.0 &&
  approxEq (w4 * w4).scalarPart 1.0 &&
  approxEq (w5 * w5).scalarPart (-1.0)

/-- PGA3 signature verification, including the degenerate projective basis vector. -/
def prop_PGA3_signature : Bool :=
  let e1 : MultivectorS PGA3 Float := MultivectorS.basis ⟨0, by omega⟩
  let e2 : MultivectorS PGA3 Float := MultivectorS.basis ⟨1, by omega⟩
  let e3 : MultivectorS PGA3 Float := MultivectorS.basis ⟨2, by omega⟩
  let e0 : MultivectorS PGA3 Float := MultivectorS.basis ⟨3, by omega⟩
  approxEq (e1 * e1).scalarPart 1.0 &&
  approxEq (e2 * e2).scalarPart 1.0 &&
  approxEq (e3 * e3).scalarPart 1.0 &&
  approxEq (e0 * e0).scalarPart 0.0

/-- Float encoding of the diagonal signature value for a basis vector. -/
def basisSquareFloat {n : Nat} (sig : Signature n) (i : Fin n) : Float :=
  if sig.isDegenerate i then 0.0
  else if sig.isPositive i then 1.0
  else -1.0

/-- Sparse and dense basis-vector squares follow the signature exactly. -/
def basisSquaresMatchSignature {n : Nat} (sig : Signature n) : Bool :=
  (List.finRange n).all fun i =>
    let expected := basisSquareFloat sig i
    let sparseE : MultivectorS sig Float := MultivectorS.basis i
    let denseE : Multivector sig Float := Multivector.basis i
    mvApproxEq (sparseE * sparseE)
        (MultivectorS.scalar expected : MultivectorS sig Float) (tol := 1e-12) &&
      denseMvApproxEq (denseE * denseE)
        (Multivector.scalar expected : Multivector sig Float) (tol := 1e-12)

/-- Distinct sparse and dense basis vectors anticommute. -/
def basisPairsAnticommute {n : Nat} (sig : Signature n) : Bool :=
  (List.finRange n).all fun i =>
    (List.finRange n).all fun j =>
      if i == j then true
      else
        let sparseI : MultivectorS sig Float := MultivectorS.basis i
        let sparseJ : MultivectorS sig Float := MultivectorS.basis j
        let denseI : Multivector sig Float := Multivector.basis i
        let denseJ : Multivector sig Float := Multivector.basis j
        mvApproxEq (sparseI * sparseJ) (-(sparseJ * sparseI)) (tol := 1e-12) &&
          denseMvApproxEq (denseI * denseJ) (-(denseJ * denseI)) (tol := 1e-12)

/-- Basis-vector anchor identities for a whole signature. -/
def basisVectorAnchorIdentities {n : Nat} (sig : Signature n) : Bool :=
  basisSquaresMatchSignature sig && basisPairsAnticommute sig

/-- R3 basis-vector anchors hold in both sparse and dense representations. -/
def prop_R3_basis_anchor_identities : Bool :=
  basisVectorAnchorIdentities R3

/-- PGA3 basis-vector anchors include the degenerate projective basis square. -/
def prop_PGA3_basis_anchor_identities : Bool :=
  basisVectorAnchorIdentities PGA3

/-- CGA3 basis-vector anchors include the extra negative conformal basis vector. -/
def prop_CGA3_basis_anchor_identities : Bool :=
  basisVectorAnchorIdentities CGA3

/-- Specialized R3 cross product agrees with the generic Hodge-dual construction. -/
def prop_R3_crossProduct3D_matches_hodge_cross : Bool :=
  let e1v : Multivector R3 Float := vector3 1.0 0.0 0.0
  let e2v : Multivector R3 Float := vector3 0.0 1.0 0.0
  let e3v : Multivector R3 Float := vector3 0.0 0.0 1.0
  let samples : List (Multivector R3 Float × Multivector R3 Float) := [
    (e1v, e2v),
    (e2v, e3v),
    (e3v, e1v),
    (vector3 1.0 2.0 3.0, vector3 (-4.0) 0.5 2.0),
    (vector3 0.25 (-0.75) 1.5, vector3 2.0 3.0 (-1.0))
  ]
  denseMvApproxEq (e1v ×₃ e2v) e3v &&
    denseMvApproxEq (e2v ×₃ e3v) e1v &&
    denseMvApproxEq (e3v ×₃ e1v) e2v &&
    samples.all fun pair =>
      denseMvApproxEq (pair.1 ×₃ pair.2) (LinearAlgebra.cross pair.1 pair.2) (tol := 1e-9)

/-! ## Rotor Exponential Properties -/

/-- Unit R3 bivector used to cross-check the closed-form rotor exponential. -/
def r3E12Sparse : MultivectorS R3 Float :=
  let e1 : MultivectorS R3 Float := MultivectorS.basis ⟨0, by omega⟩
  let e2 : MultivectorS R3 Float := MultivectorS.basis ⟨1, by omega⟩
  e1 * e2

/-- Unit CGA3 bivector with positive square for hyperbolic exponential checks. -/
def cga3EPlusEMinusSparse : MultivectorS CGA3 Float :=
  let eplus : MultivectorS CGA3 Float := MultivectorS.basis ⟨3, by omega⟩
  let eminus : MultivectorS CGA3 Float := MultivectorS.basis ⟨4, by omega⟩
  eplus * eminus

/-- Representative half-angle samples for rotor exponential checks. -/
def rotorExpSampleAngles : List Float :=
  [(-1.2), (-0.75), 0.0, 0.375, 0.7853981633974483, 1.2]

/-- Scalar Taylor helpers agree with Lean's runtime Float transcendental functions. -/
def prop_scalar_taylor_functions_match_float : Bool :=
  rotorExpSampleAngles.all fun x =>
    approxEq (expTaylor x 24) (Float.exp x) (tol := 1e-9) &&
    approxEq (sinTaylor x 18) (Float.sin x) (tol := 1e-9) &&
    approxEq (cosTaylor x 18) (Float.cos x) (tol := 1e-9) &&
    approxEq (sinhTaylor x 18) (Float.sinh x) (tol := 1e-9) &&
    approxEq (coshTaylor x 18) (Float.cosh x) (tol := 1e-9)

/-- R3 `expBivector` agrees with the generic sparse Taylor series on a unit bivector. -/
def prop_expBivector_r3_e12_matches_series : Bool :=
  rotorExpSampleAngles.all fun θ =>
    let B := r3E12Sparse.smul θ
    mvApproxEq (expBivector B) (expTaylorMV B 24) (tol := 1e-5)

/-- Hyperbolic `expBivector` agrees with the generic sparse Taylor series. -/
def prop_expBivector_cga3_ePlusEMinus_matches_series : Bool :=
  rotorExpSampleAngles.all fun θ =>
    let B := cga3EPlusEMinusSparse.smul θ
    mvApproxEq (expBivector B) (expTaylorMV B 24) (tol := 1e-5)

/-- Scalar-square exponential uses the exact elliptic closed form for R3 rotors. -/
def prop_expScalarSquareBivector_r3_closed_form : Bool :=
  rotorExpSampleAngles.all fun θ =>
    let B := r3E12Sparse.smul θ
    let R := expScalarSquareBivector B
    !hasNonScalarPart (B * B) &&
      approxEq R.scalarPart (Float.cos θ) (tol := 1e-12) &&
      approxEq (R.coeff 3) (Float.sin θ) (tol := 1e-12)

/-- Scalar-square exponential uses the exact hyperbolic closed form in CGA. -/
def prop_expScalarSquareBivector_cga3_closed_form : Bool :=
  rotorExpSampleAngles.all fun θ =>
    let B := cga3EPlusEMinusSparse.smul θ
    let R := expScalarSquareBivector B
    !hasNonScalarPart (B * B) &&
      approxEq R.scalarPart (Float.cosh θ) (tol := 1e-12) &&
      approxEq (R.coeff 24) (Float.sinh θ) (tol := 1e-12)

/-- Return true when a sparse multivector has any non-scalar coefficient. -/
def sparseHasNonScalarPart {n : Nat} {sig : Signature n}
    (m : MultivectorS sig Float) : Bool :=
  !(mvApproxEq m (m.gradeProject 0) (tol := 1e-9))

/-- Mixed conformal generator from the documented torus example. -/
def cga3TorusGeneratorSparse : MultivectorS CGA3 Float :=
  let e1 : MultivectorS CGA3 Float := MultivectorS.basis ⟨0, by omega⟩
  let e2 : MultivectorS CGA3 Float := MultivectorS.basis ⟨1, by omega⟩
  let e3 : MultivectorS CGA3 Float := MultivectorS.basis ⟨2, by omega⟩
  let eplus : MultivectorS CGA3 Float := MultivectorS.basis ⟨3, by omega⟩
  let eminus : MultivectorS CGA3 Float := MultivectorS.basis ⟨4, by omega⟩
  let e12 := e1 * e2
  let einf3 := (eplus + eminus) ⋀ₛ e3
  e12.smul (3.0 / 7.0) + einf3

/--
The mixed conformal generator from the documented Grassmann.jl torus example does
not square to a scalar, so the scalar-square `expBivector` shortcut is not a
valid exact port path for that example.
-/
def prop_cga3_torus_generator_square_non_scalar : Bool :=
  let generator := cga3TorusGeneratorSparse
  let square := generator * generator
  sparseHasNonScalarPart square &&
    approxEq square.scalarPart (-((3.0 / 7.0) * (3.0 / 7.0))) (tol := 1e-9)

/-- Non-scalar-square conformal bivectors use the Taylor fallback, not the scalar shortcut. -/
def prop_expBivector_cga3_torus_generator_matches_series : Bool :=
  [(-0.5), (-0.25), 0.125, 0.375, 0.5].all fun θ =>
    let B := cga3TorusGeneratorSparse.smul θ
    sparseHasNonScalarPart (B * B) &&
      hasNonScalarPart (B * B) &&
      mvApproxEq (expBivector B) (expTaylorMV B 30) (tol := 1e-7)

/-- Non-scalar-square bivectors take the Taylor fallback in the reusable helper. -/
def prop_expScalarSquareBivector_fallback_matches_series : Bool :=
  [(-0.5), (-0.25), 0.125, 0.375, 0.5].all fun θ =>
    let B := cga3TorusGeneratorSparse.smul θ
    sparseHasNonScalarPart (B * B) &&
      hasNonScalarPart (B * B) &&
      mvApproxEq
        (expScalarSquareBivector B (fallbackTerms := 30))
        (expTaylorMV B 30)
        (tol := 1e-7)

/-! ### Documented Projective Julia Example Exponentials -/

namespace ProjectiveJulia

open Grassmann.JuliaExamples

/-- Parameter samples covering the exact projective Julia oracle range. -/
def plottedSamples : List Float :=
  let π := Grassmann.JuliaExamples.pi
  [(-2.0 * π), (-π), -1.0, -0.5, 0.0, 0.5, 1.0, π, (2.0 * π)]

/-- Smaller samples where the generic Taylor exponential is still a stable reference. -/
def localTaylorSamples : List Float :=
  [(-1.0), (-0.5), (-0.25), 0.0, 0.25, 0.5, 1.0]

def vec3ApproxEq (a b : Vec3) (tol : Float := 1e-6) : Bool :=
  approxEq a.x b.x tol && approxEq a.y b.y tol && approxEq a.z b.z tol

def torusPart12 (t : Float) : ProjectiveMV :=
  MultivectorS.smul (((3.0 / 7.0) * pi) * t) (projE1 * projE2)

def torusPartInf3 (t : Float) : ProjectiveMV :=
  MultivectorS.smul (pi * t) (projInf * projE3)

def torusPointTaylor (t : Float) : Vec3 :=
  let rotor := expTaylorMV (MultivectorS.smul (pi * t) projectiveTorusGenerator) 40
  projectiveDown (rotor * projectiveUp { x := 1.0, y := 1.0, z := 1.0 } * rotor†ₛ)

def orbit2PointTaylor (t : Float) : Vec3 :=
  let generator := MultivectorS.smul (t / 2.0) (projInf * projectiveOrbitVector t)
  let motor := expTaylorMV generator 40
  projectiveDown (motor * projectiveUp projectiveOrbitBasePoint * motor†ₛ)

def streamFieldMatchesTaylor (input : Vec3 -> ProjectiveMV) (p : Vec3) : Bool :=
  vec3ApproxEq
    (projectiveMotorOutputVector projectiveOrbWaveMotor (input p))
    (projectiveMotorOutputVector projectiveOrbWaveMotorTaylor (input p))
    (tol := 1e-6)

def scalarSquareBivectorSamples : List ProjectiveMV :=
  let θs := localTaylorSamples
  θs.flatMap fun θ =>
    [ torusPart12 θ,
      torusPartInf3 θ,
      MultivectorS.smul (θ / 2.0) (projInf * projectiveOrbitVector θ) ]

/-- The projective closed form agrees with Taylor series on stable local samples. -/
def prop_projective_scalar_square_exp_matches_series_locally : Bool :=
  scalarSquareBivectorSamples.all fun B =>
    !hasNonScalarPart (B * B) &&
      mvApproxEq
        (expProjectiveScalarSquareBivector B)
        (expTaylorMV B 40)
        (tol := 1e-6)

/-- Scalar-square projective exponentials have the expected inverse over the plotted range. -/
def prop_projective_scalar_square_exp_inverse : Bool :=
  plottedSamples.all fun t =>
    [torusPart12 t, torusPartInf3 t,
      MultivectorS.smul (t / 2.0) (projInf * projectiveOrbitVector t)].all fun B =>
      let motor := expProjectiveScalarSquareBivector B
      let inverse := expProjectiveScalarSquareBivector (B.smul (-1.0))
      mvApproxEq (motor * inverse) (MultivectorS.scalar 1.0 : ProjectiveMV) (tol := 1e-6)

/-- The two projective torus summands commute, justifying the factored exponential path. -/
def prop_projective_torus_parts_commute : Bool :=
  plottedSamples.all fun t =>
    let a := torusPart12 t
    let b := torusPartInf3 t
    let expA := expProjectiveScalarSquareBivector a
    let expB := expProjectiveScalarSquareBivector b
    mvApproxEq (a * b) (b * a) &&
      mvApproxEq (expA * expB) (expB * expA) (tol := 1e-6)

/-- The factored torus evaluator matches the previous Taylor path where Taylor is stable. -/
def prop_projective_torus_factored_matches_local_taylor : Bool :=
  localTaylorSamples.all fun t =>
    vec3ApproxEq (documentedProjectiveTorusPoint t) (torusPointTaylor t) (tol := 1e-5)

/-- The closed-form orbit-2 evaluator matches the previous Taylor path where Taylor is stable. -/
def prop_projective_orbit2_closed_form_matches_local_taylor : Bool :=
  localTaylorSamples.all fun t =>
    vec3ApproxEq (documentedProjectiveOrbit2Point t) (orbit2PointTaylor t) (tol := 1e-5)

/-- The documented projective stream-field summands commute, justifying the factored motor. -/
def prop_projective_stream_motor_parts_commute : Bool :=
  let a := MultivectorS.smul (pi / 4.0) (projE1 * projE2)
  let b := MultivectorS.smul (pi / 4.0) (projInf * projE3)
  let expA := expProjectiveScalarSquareBivector a
  let expB := expProjectiveScalarSquareBivector b
  mvApproxEq (a * b) (b * a) &&
    mvApproxEq (expA * expB) (expB * expA) (tol := 1e-6)

/-- The plotted `orb` and `wave` stream fields match the whole documented exponential locally. -/
def prop_projective_stream_fields_match_local_taylor : Bool :=
  streamWitnessSamples.all fun p =>
    streamFieldMatchesTaylor projectiveOrbInputPoint p &&
      streamFieldMatchesTaylor projectiveWaveInputVector p

end ProjectiveJulia

/-! ### Documented Conformal Julia Example Exponentials -/

namespace ConformalJulia

open Grassmann.JuliaExamples

def helixPointTaylor (t : Float) : Vec3 :=
  let generator := conformalHelixPart12 t + conformalHelixPartInf3 t
  let motor := expTaylorMV generator 40
  conformalDown (motor * conformalPoint conformalHelixBasePoint * motor†ₛ)

/-- The conformal helix summands commute, justifying the factored motor path. -/
def prop_conformal_helix_parts_commute : Bool :=
  ProjectiveJulia.plottedSamples.all fun t =>
    let a := conformalHelixPart12 t
    let b := conformalHelixPartInf3 t
    let expA := expScalarSquareBivector a
    let expB := expScalarSquareBivector b
    mvApproxEq (a * b) (b * a) &&
      mvApproxEq (expA * expB) (expB * expA) (tol := 1e-6)

/-- The plotted closed form matches the sparse CGA motor over the rendered range. -/
def prop_conformal_helix_closed_form_matches_motor : Bool :=
  ProjectiveJulia.plottedSamples.all fun t =>
    ProjectiveJulia.vec3ApproxEq
      (documentedConformalHelixPoint t)
      (documentedConformalHelixMotorPoint t)
      (tol := 1e-6)

/-- The factored conformal helix motor matches the generic Taylor path locally. -/
def prop_conformal_helix_motor_matches_local_taylor : Bool :=
  ProjectiveJulia.localTaylorSamples.all fun t =>
    ProjectiveJulia.vec3ApproxEq
      (documentedConformalHelixMotorPoint t)
      (helixPointTaylor t)
      (tol := 1e-5)

end ConformalJulia

/-! ### Julia Visual Example Coverage -/

namespace JuliaExampleCoverage

open Grassmann.JuliaExamples

/-- The plot-producing examples documented by Grassmann.jl's algebra page. -/
def expectedFilenames : List String :=
  [ "plane-1.svg", "plane-2.svg", "plane-3.svg", "plane-4.svg", "plane-5.svg", "plane-6.svg",
    "torus.svg", "helix.svg", "orbit-2.svg", "orbit-4.svg", "orb.svg", "wave.svg" ]

def noDuplicateStrings : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && noDuplicateStrings xs

def generatedFilenames : List String :=
  allExamples.map Prod.fst

def generatedReferenceNames : List String :=
  allExamples.map fun ex => referenceName ex.1

def expectedReferenceNames : List String :=
  expectedFilenames.map referenceName

/-- The Lean generator still covers exactly the documented Julia plot examples. -/
def prop_julia_example_names_complete : Bool :=
  generatedFilenames == expectedFilenames &&
    generatedReferenceNames == expectedReferenceNames &&
    allExamples.length == expectedFilenames.length &&
    noDuplicateStrings generatedFilenames &&
    noDuplicateStrings generatedReferenceNames

def svgContainsVisibleGeometry (body : String) : Bool :=
  body.contains "<svg" &&
    body.contains "</svg>" &&
    body.contains "fill=\"#ffffff\"" &&
    (body.contains "<path" || body.contains "<line") &&
    body.length > 1000

/-- Every Lean visual example has a plausible non-empty SVG payload. -/
def prop_julia_example_svgs_nonempty : Bool :=
  allExamples.all fun ex => svgContainsVisibleGeometry ex.2

def manifestContainsExample (filename : String) : Bool :=
  let name := referenceName filename
  manifestJson.contains ("\"name\":\"" ++ name ++ "\"") &&
    manifestJson.contains ("\"lean\":\"lean/" ++ filename ++ "\"") &&
    manifestJson.contains ("\"julia\":\"" ++ juliaReferenceUrl filename ++ "\"")

/-- The machine-readable manifest lists every generated Lean/Julia comparison pair. -/
def prop_julia_example_manifest_covers_examples : Bool :=
  manifestJson.contains s!"\"example_count\":{expectedFilenames.length}" &&
    expectedFilenames.all manifestContainsExample

def manifestContainsWitnessGroup (key : String) (entries : List String) : Bool :=
  manifestJson.contains ("\"" ++ key ++ "\":[") &&
    entries.all fun entry => manifestJson.contains entry

/-- The machine-readable manifest keeps every exact formula witness group wired in. -/
def prop_julia_example_manifest_covers_witnesses : Bool :=
  orbitWitnessEntries.length == 10 &&
    projectivePlotWitnessEntries.length == 15 &&
    conformalPlotWitnessEntries.length == 5 &&
    projectiveStreamFieldWitnessEntries.length == 10 &&
    manifestContainsWitnessGroup "cga_orbit_translation_witnesses" orbitWitnessEntries &&
    manifestContainsWitnessGroup "projective_plot_formula_witnesses"
      projectivePlotWitnessEntries &&
    manifestContainsWitnessGroup "conformal_plot_formula_witnesses" conformalPlotWitnessEntries &&
    manifestContainsWitnessGroup "projective_stream_field_witnesses"
      projectiveStreamFieldWitnessEntries

def comparisonHtmlContainsExample (filename : String) : Bool :=
  let label := referenceName filename
  comparisonHtml.contains s!"<h2>{label}</h2>" &&
    comparisonHtml.contains ("lean/" ++ filename) &&
    comparisonHtml.contains (juliaReferenceUrl filename)

/-- The side-by-side comparison page references every generated Lean and Julia artifact. -/
def prop_julia_example_comparison_html_covers_examples : Bool :=
  comparisonHtml.contains "<!doctype html>" &&
    expectedFilenames.all comparisonHtmlContainsExample

end JuliaExampleCoverage

/-! ## High-Dimensional Exact Stress Tests -/

/-- Five-dimensional Euclidean signature used by exact stress checks. -/
abbrev R5Stress : Signature 5 := Signature.euclidean 5

/-- R4 blade from a bit mask for exact stress checks. -/
def stressBlade4 (mask : Nat) : Blade R4 :=
  ⟨BitVec.ofNat 4 mask⟩

/-- R5 blade from a bit mask for exact stress checks. -/
def stressBlade5 (mask : Nat) : Blade R5Stress :=
  ⟨BitVec.ofNat 5 mask⟩

/-- R4 basis blade as an exact dense integer multivector. -/
def stressMv4 (mask : Nat) : Multivector R4 Int :=
  Multivector.ofBlade (stressBlade4 mask)

/-- R5 basis blade as an exact dense integer multivector. -/
def stressMv5 (mask : Nat) : Multivector R5Stress Int :=
  Multivector.ofBlade (stressBlade5 mask)

/-- Exact coefficient-wise equality for dense integer multivectors. -/
def denseIntEq {n : Nat} {sig : Signature n} (a b : Multivector sig Int) : Bool :=
  (List.finRange (2 ^ n)).all fun i => a.coeffs i == b.coeffs i

/-- Euclidean `⋆⋆` sign on a grade-`k` basis blade in dimension `n`. -/
def euclideanHodgeSquareSign (n k : Nat) : Int :=
  if (k * (n - k)) % 2 == 0 then 1 else -1

/-- Every basis blade satisfies the Euclidean `⋆⋆` sign convention. -/
def hodgeSquareMatchesEuclideanBasis {n : Nat} (sig : Signature n) : Bool :=
  (List.range (2 ^ n)).all fun mask =>
    let blade : Blade sig := ⟨BitVec.ofNat n mask⟩
    let mv : Multivector sig Int := Multivector.ofBlade blade
    let k := grade (BitVec.ofNat n mask)
    denseIntEq (⋆ᵐ(⋆ᵐmv)) (mv.smul (euclideanHodgeSquareSign n k))

/-! ## Exact Blade Reference Tests -/

/-- Basis blade from a bit mask for exact blade-product checks. -/
def bladeFromMask {n : Nat} (sig : Signature n) (mask : Nat) : Blade sig :=
  ⟨BitVec.ofNat n mask⟩

/-- Interpret a signed blade product as an exact dense integer multivector. -/
def bladeProductToDenseInt {n : Nat} {sig : Signature n} (bp : BladeProduct sig) :
    Multivector sig Int :=
  match bp with
  | .zero => 0
  | .nonzero sign blade => (Multivector.ofBlade blade).smul sign

/-- Blade regressive product agrees with dense regressive product on every basis pair. -/
def bladeRegressiveMatchesDense {n : Nat} (sig : Signature n) : Bool :=
  (List.range (2 ^ n)).all fun i =>
    (List.range (2 ^ n)).all fun j =>
      let a := bladeFromMask sig i
      let b := bladeFromMask sig j
      let denseA : Multivector sig Int := Multivector.ofBlade a
      let denseB : Multivector sig Int := Multivector.ofBlade b
      denseIntEq (bladeProductToDenseInt (regressiveProductBlades a b))
        (denseA ⋁ᵐ denseB)

/-- R3 blade regressive products match the dense oracle exactly. -/
def prop_blade_regressive_r3_dense : Bool :=
  bladeRegressiveMatchesDense R3

/-- PGA3 blade regressive products match the dense oracle exactly. -/
def prop_blade_regressive_pga3_dense : Bool :=
  bladeRegressiveMatchesDense PGA3

/-- CGA3 blade regressive products match the dense oracle exactly. -/
def prop_blade_regressive_cga3_dense : Bool :=
  bladeRegressiveMatchesDense CGA3

/-- R5 exact basis, anticommutation, and wedge checks. -/
def prop_R5_exact_basis_wedge : Bool :=
  let e1 := stressMv5 0b00001
  let e2 := stressMv5 0b00010
  let e3 := stressMv5 0b00100
  let e4 := stressMv5 0b01000
  let e5 := stressMv5 0b10000
  let e14 := stressBlade5 0b01001
  let ps := stressBlade5 0b11111
  let wedgeAll := ((((e1 ⋀ᵐ e2) ⋀ᵐ e3) ⋀ᵐ e4) ⋀ᵐ e5)
  (e1 * e1).scalarPart == 1 &&
  (e5 * e5).scalarPart == 1 &&
  denseIntEq (e1 * e2 + e2 * e1) (0 : Multivector R5Stress Int) &&
  wedgeAll.coeff ps == 1 &&
  denseIntEq (e3 ⋀ᵐ e3) (0 : Multivector R5Stress Int) &&
  (e1 ⋀ᵐ e4).coeff e14 == 1 &&
  (e4 ⋀ᵐ e1).coeff e14 == -1

/-- R5 exact unnormalized rotor and contraction checks. -/
def prop_R5_exact_rotor_contraction : Bool :=
  let e1 := stressMv5 0b00001
  let e2 := stressMv5 0b00010
  let e3 := stressMv5 0b00100
  let b12 := e1 * e2
  let one : Multivector R5Stress Int := Multivector.one
  let r := one + b12
  let rinv := one - b12
  let rotE1 := r * e1 * r†
  let rotE3 := r * e3 * r†
  let e12 := e1 ⋀ᵐ e2
  let e123 := e12 ⋀ᵐ e3
  (b12 * b12).scalarPart == -1 &&
  denseIntEq (r * rinv) (Multivector.scalar 2 : Multivector R5Stress Int) &&
  rotE1.coeff (stressBlade5 0b00001) == 0 &&
  rotE1.coeff (stressBlade5 0b00010) == -2 &&
  rotE3.coeff (stressBlade5 0b00001) == 0 &&
  rotE3.coeff (stressBlade5 0b00010) == 0 &&
  rotE3.coeff (stressBlade5 0b00100) == 2 &&
  denseIntEq (e1 ⌋ᵐ e12) e2 &&
  denseIntEq (e3 ⌋ᵐ e12) (0 : Multivector R5Stress Int) &&
  denseIntEq (e12 ⌋ᵐ e123) e3

/-- R4 exact Hodge dual and determinant checks. -/
def prop_R4_exact_hodge_det : Bool :=
  let e1 := stressMv4 0b0001
  let e2 := stressMv4 0b0010
  let e3 := stressMv4 0b0100
  let e4 := stressMv4 0b1000
  let ps := stressBlade4 0b1111
  let e234 := stressBlade4 0b1110
  let scaled1 := e1.smul 2
  let scaled2 := e2.smul 3
  let scaled3 := e3.smul 5
  let scaled4 := e4.smul 7
  (⋆ᵐ(Multivector.one : Multivector R4 Int)).coeff ps == 1 &&
  (⋆ᵐe1).coeff e234 == 1 &&
  LinearAlgebra.det [e1, e2, e3, e4] == 1 &&
  LinearAlgebra.det [e2, e1, e3, e4] == -1 &&
  LinearAlgebra.det [scaled1, scaled2, scaled3, scaled4] == 210

/-- R4 exact Hodge dual squares with the expected Euclidean signs on all basis blades. -/
def prop_R4_exact_hodge_square_basis : Bool :=
  hodgeSquareMatchesEuclideanBasis R4

/-- R5 exact Hodge dual squares with the expected Euclidean signs on all basis blades. -/
def prop_R5_exact_hodge_square_basis : Bool :=
  hodgeSquareMatchesEuclideanBasis R5Stress

/-- R4 exact rotor composition and identity checks. -/
def prop_R4_exact_composition_identity : Bool :=
  let e1 := stressMv4 0b0001
  let e2 := stressMv4 0b0010
  let e3 := stressMv4 0b0100
  let e4 := stressMv4 0b1000
  let r12 := (Multivector.one : Multivector R4 Int) + e1 * e2
  let r34 := (Multivector.one : Multivector R4 Int) + e3 * e4
  let r := r12 * r34
  let rotE1 := r * e1 * r†
  let a := e1 + e2
  let b := e2 + e3
  let reverseDiff := (a * b)† - b† * a†
  let mv := (Multivector.one : Multivector R4 Int) + e1 + e1 * e2
  let involuteDiff := (mvˆ)ˆ - mv
  let v := e1.smul 3 + e4.smul 4
  let vSq := v * v
  rotE1.coeff (stressBlade4 0b0001) == 0 &&
  rotE1.coeff (stressBlade4 0b0010) == -4 &&
  denseIntEq reverseDiff (0 : Multivector R4 Int) &&
  denseIntEq involuteDiff (0 : Multivector R4 Int) &&
  vSq.scalarPart == 25 &&
  vSq.coeff (stressBlade4 0b0001) == 0 &&
  vSq.coeff (stressBlade4 0b1000) == 0

/-! ## Test Runner -/

/-- Result of a property test -/
structure PropTestResult where
  name : String
  passed : Bool
  numTests : Nat
  message : String := ""
  deriving Repr

instance : ToString PropTestResult where
  toString r :=
    let status := if r.passed then "PASS" else "FAIL"
    let msg := if r.message.isEmpty then "" else s!" ({r.message})"
    s!"[{status}] {r.name} ({Nat.repr r.numTests} tests){msg}"

/-- Run a Bool property multiple times -/
def runBoolProp (name : String) (prop : Bool) : PropTestResult :=
  { name := name, passed := prop, numTests := 1 }

/-- Run a randomized property test -/
def runRandomProp (name : String) (prop : R3Mv → Bool)
    (numTests : Nat := 100) : IO PropTestResult := do
  let mut passed := true
  let mut failMsg := ""
  for i in [0:numTests] do
    let mv ← Gen.run Arbitrary.arbitrary (i * 2)
    if !prop mv then
      passed := false
      failMsg := s!"Failed on test {Nat.repr i}"
      break
  return { name := name, passed := passed, numTests := numTests, message := failMsg }

/-- Run a randomized property test with two arguments -/
def runRandomProp2 (name : String) (prop : R3Mv → R3Mv → Bool)
    (numTests : Nat := 100) : IO PropTestResult := do
  let mut passed := true
  let mut failMsg := ""
  for i in [0:numTests] do
    let a ← Gen.run Arbitrary.arbitrary (i * 2)
    let b ← Gen.run Arbitrary.arbitrary (i * 2 + 1)
    if !prop a b then
      passed := false
      failMsg := s!"Failed on test {Nat.repr i}"
      break
  return { name := name, passed := passed, numTests := numTests, message := failMsg }

/-- Run a randomized property test with three arguments -/
def runRandomProp3 (name : String) (prop : R3Mv → R3Mv → R3Mv → Bool)
    (numTests : Nat := 50) : IO PropTestResult := do
  let mut passed := true
  let mut failMsg := ""
  for i in [0:numTests] do
    let a ← Gen.run Arbitrary.arbitrary (i * 3)
    let b ← Gen.run Arbitrary.arbitrary (i * 3 + 1)
    let c ← Gen.run Arbitrary.arbitrary (i * 3 + 2)
    if !prop a b c then
      passed := false
      failMsg := s!"Failed on test {Nat.repr i}"
      break
  return { name, passed, numTests, message := failMsg }

/-- Run a randomized PGA3 property test. -/
def runRandomPGA3Prop (name : String) (prop : PGA3Mv → Bool)
    (numTests : Nat := 100) : IO PropTestResult := do
  let mut passed := true
  let mut failMsg := ""
  for i in [0:numTests] do
    let mv : PGA3Mv ← Gen.run Arbitrary.arbitrary (i * 2)
    if !prop mv then
      passed := false
      failMsg := s!"Failed on test {Nat.repr i}"
      break
  return { name := name, passed := passed, numTests := numTests, message := failMsg }

/-- Run a randomized PGA3 property test with two arguments. -/
def runRandomPGA3Prop2 (name : String) (prop : PGA3Mv → PGA3Mv → Bool)
    (numTests : Nat := 100) : IO PropTestResult := do
  let mut passed := true
  let mut failMsg := ""
  for i in [0:numTests] do
    let a : PGA3Mv ← Gen.run Arbitrary.arbitrary (i * 2)
    let b : PGA3Mv ← Gen.run Arbitrary.arbitrary (i * 2 + 1)
    if !prop a b then
      passed := false
      failMsg := s!"Failed on test {Nat.repr i}"
      break
  return { name := name, passed := passed, numTests := numTests, message := failMsg }

/-- Run a randomized CGA3 property test. -/
def runRandomCGA3Prop (name : String) (prop : CGA3Mv → Bool)
    (numTests : Nat := 100) : IO PropTestResult := do
  let mut passed := true
  let mut failMsg := ""
  for i in [0:numTests] do
    let mv : CGA3Mv ← Gen.run Arbitrary.arbitrary (i * 2)
    if !prop mv then
      passed := false
      failMsg := s!"Failed on test {Nat.repr i}"
      break
  return { name := name, passed := passed, numTests := numTests, message := failMsg }

/-- Run a randomized CGA3 property test with two arguments. -/
def runRandomCGA3Prop2 (name : String) (prop : CGA3Mv → CGA3Mv → Bool)
    (numTests : Nat := 100) : IO PropTestResult := do
  let mut passed := true
  let mut failMsg := ""
  for i in [0:numTests] do
    let a : CGA3Mv ← Gen.run Arbitrary.arbitrary (i * 2)
    let b : CGA3Mv ← Gen.run Arbitrary.arbitrary (i * 2 + 1)
    if !prop a b then
      passed := false
      failMsg := s!"Failed on test {Nat.repr i}"
      break
  return { name := name, passed := passed, numTests := numTests, message := failMsg }

/-- Run a Gen Bool property -/
def runGenProp (name : String) (prop : Gen Bool) (numTests : Nat := 100) : IO PropTestResult := do
  let mut passed := true
  let mut failMsg := ""
  for i in [0:numTests] do
    let result ← Gen.run prop (i * 2)
    if !result then
      passed := false
      failMsg := s!"Failed on test {Nat.repr i}"
      break
  return { name := name, passed := passed, numTests := numTests, message := failMsg }

/-- Run exact blade-product checks against dense reference results. -/
def runBladeReferenceTests : IO (List PropTestResult) := do
  IO.println "\n┌─ Blade vs Dense Reference ────────────────────┐"
  let bladeR3 := runBoolProp "R3 blade regressive product" prop_blade_regressive_r3_dense
  IO.println s!"│ {bladeR3}"
  let bladePGA3 := runBoolProp "PGA3 blade regressive product" prop_blade_regressive_pga3_dense
  IO.println s!"│ {bladePGA3}"
  let bladeCGA3 := runBoolProp "CGA3 blade regressive product" prop_blade_regressive_cga3_dense
  IO.println s!"│ {bladeCGA3}"
  IO.println "└────────────────────────────────────────────────┘"
  return [bladeR3, bladePGA3, bladeCGA3]

/-- Run native-vector baseline checks against dense reference results. -/
def runNativeReferenceTests : IO (List PropTestResult) := do
  IO.println "\n┌─ Native Vector vs Dense Reference ───────────┐"
  let native1 ← runGenProp "Native full round-trip" prop_native_full_roundtrip
  IO.println s!"│ {native1}"
  let native1a := runBoolProp "Native ofPairs dense reference" prop_native_ofPairs_dense
  IO.println s!"│ {native1a}"
  let native2 ← runGenProp "Native grade projection" prop_native_grade_projection_dense
  IO.println s!"│ {native2}"
  let native3 ← runGenProp "Native parity projection" prop_native_parity_projection_dense
  IO.println s!"│ {native3}"
  let native4 ← runGenProp "Native multiplication" prop_native_mul_dense
  IO.println s!"│ {native4}"
  let native5 ← runGenProp "Native wedge" prop_native_wedge_dense
  IO.println s!"│ {native5}"
  let native6 ← runGenProp "Native reverse" prop_native_reverse_dense
  IO.println s!"│ {native6}"
  let native6s ← runGenProp "Native scalar part" prop_native_scalar_part_dense
  IO.println s!"│ {native6s}"
  let native6i ← runGenProp "Native involutions" prop_native_involutions_dense
  IO.println s!"│ {native6i}"
  let native6a ← runGenProp "Native left contraction" prop_native_left_contract_dense
  IO.println s!"│ {native6a}"
  let native6b ← runGenProp "Native right contraction" prop_native_right_contract_dense
  IO.println s!"│ {native6b}"
  let native6c ← runGenProp "Native Hodge dual" prop_native_hodge_dual_dense
  IO.println s!"│ {native6c}"
  let native6d ← runGenProp "Native regressive product" prop_native_regressive_dense
  IO.println s!"│ {native6d}"
  let native6ops ← runGenProp "Native GAlgebra operations" prop_native_galgebra_ops_dense 50
  IO.println s!"│ {native6ops}"
  let native6g ← runGenProp "Native GAlgebra sandwich" prop_native_galgebra_sandwich_dense
  IO.println s!"│ {native6g}"
  let native6n ← runGenProp "Native GAlgebra normSq" prop_native_galgebra_normSq_dense
  IO.println s!"│ {native6n}"
  let native7 ← runGenProp "PGA3 native full round-trip" prop_native_pga3_full_roundtrip
  IO.println s!"│ {native7}"
  let native7a := runBoolProp "PGA3 native ofPairs dense reference"
    prop_native_pga3_ofPairs_dense
  IO.println s!"│ {native7a}"
  let native8 ← runGenProp "PGA3 native grade projection" prop_native_pga3_grade_projection_dense
  IO.println s!"│ {native8}"
  let native9 ← runGenProp "PGA3 native parity projection" prop_native_pga3_parity_projection_dense
  IO.println s!"│ {native9}"
  let native10 ← runGenProp "PGA3 native multiplication" prop_native_pga3_mul_dense
  IO.println s!"│ {native10}"
  let native11 ← runGenProp "PGA3 native wedge" prop_native_pga3_wedge_dense
  IO.println s!"│ {native11}"
  let native12 ← runGenProp "PGA3 native reverse" prop_native_pga3_reverse_dense
  IO.println s!"│ {native12}"
  let native12s ← runGenProp "PGA3 native scalar part" prop_native_pga3_scalar_part_dense
  IO.println s!"│ {native12s}"
  let native12i ← runGenProp "PGA3 native involutions" prop_native_pga3_involutions_dense
  IO.println s!"│ {native12i}"
  let native12a ← runGenProp "PGA3 native left contraction" prop_native_pga3_left_contract_dense
  IO.println s!"│ {native12a}"
  let native12b ← runGenProp "PGA3 native right contraction" prop_native_pga3_right_contract_dense
  IO.println s!"│ {native12b}"
  let native12c ← runGenProp "PGA3 native Hodge dual" prop_native_pga3_hodge_dual_dense
  IO.println s!"│ {native12c}"
  let native12d ← runGenProp "PGA3 native regressive product" prop_native_pga3_regressive_dense
  IO.println s!"│ {native12d}"
  let native12ops ← runGenProp "PGA3 native GAlgebra operations"
    prop_native_pga3_galgebra_ops_dense 40
  IO.println s!"│ {native12ops}"
  let native12g ← runGenProp "PGA3 native GAlgebra sandwich"
    prop_native_pga3_galgebra_sandwich_dense
  IO.println s!"│ {native12g}"
  let native12n ← runGenProp "PGA3 native GAlgebra normSq"
    prop_native_pga3_galgebra_normSq_dense
  IO.println s!"│ {native12n}"
  let native13 ← runGenProp "CGA3 native full round-trip" prop_native_cga3_full_roundtrip
  IO.println s!"│ {native13}"
  let native13a := runBoolProp "CGA3 native ofPairs dense reference"
    prop_native_cga3_ofPairs_dense
  IO.println s!"│ {native13a}"
  let native14 ← runGenProp "CGA3 native grade projection" prop_native_cga3_grade_projection_dense
  IO.println s!"│ {native14}"
  let native15 ← runGenProp "CGA3 native parity projection" prop_native_cga3_parity_projection_dense
  IO.println s!"│ {native15}"
  let native16 ← runGenProp "CGA3 native multiplication" prop_native_cga3_mul_dense
  IO.println s!"│ {native16}"
  let native17 ← runGenProp "CGA3 native wedge" prop_native_cga3_wedge_dense
  IO.println s!"│ {native17}"
  let native18 ← runGenProp "CGA3 native reverse" prop_native_cga3_reverse_dense
  IO.println s!"│ {native18}"
  let native18s ← runGenProp "CGA3 native scalar part" prop_native_cga3_scalar_part_dense
  IO.println s!"│ {native18s}"
  let native18i ← runGenProp "CGA3 native involutions" prop_native_cga3_involutions_dense
  IO.println s!"│ {native18i}"
  let native18a ← runGenProp "CGA3 native left contraction" prop_native_cga3_left_contract_dense
  IO.println s!"│ {native18a}"
  let native18b ← runGenProp "CGA3 native right contraction" prop_native_cga3_right_contract_dense
  IO.println s!"│ {native18b}"
  let native18c ← runGenProp "CGA3 native Hodge dual" prop_native_cga3_hodge_dual_dense
  IO.println s!"│ {native18c}"
  let native18d ← runGenProp "CGA3 native regressive product" prop_native_cga3_regressive_dense
  IO.println s!"│ {native18d}"
  let native18ops ← runGenProp "CGA3 native GAlgebra operations"
    prop_native_cga3_galgebra_ops_dense 20
  IO.println s!"│ {native18ops}"
  let native18g ← runGenProp "CGA3 native GAlgebra sandwich"
    prop_native_cga3_galgebra_sandwich_dense
  IO.println s!"│ {native18g}"
  let native18n ← runGenProp "CGA3 native GAlgebra normSq"
    prop_native_cga3_galgebra_normSq_dense
  IO.println s!"│ {native18n}"
  IO.println "└────────────────────────────────────────────────┘"
  return [
    native1, native1a, native2, native3, native4, native5, native6, native6s,
    native6i, native6a, native6b, native6c, native6d, native6ops, native6g,
    native6n, native7, native7a, native8, native9, native10, native11, native12,
    native12s, native12i, native12a, native12b, native12c, native12d, native12ops,
    native12g, native12n, native13, native13a, native14, native15, native16,
    native17, native18, native18s, native18i, native18a, native18b, native18c,
    native18d, native18ops, native18g, native18n]

/-- Run sign-table fast-path checks against generic dense multiplication. -/
def runSignTableReferenceTests : IO (List PropTestResult) := do
  IO.println "\n┌─ SignTable vs Generic Multiplication ─────────┐"
  let table1 ← runGenProp "R3 table multiplication" prop_sign_table_r3_mul_generic
  IO.println s!"│ {table1}"
  let table2 ← runGenProp "PGA3 table multiplication" prop_sign_table_pga3_mul_generic
  IO.println s!"│ {table2}"
  let table3 ← runGenProp "CGA3 table multiplication" prop_sign_table_cga3_mul_generic
  IO.println s!"│ {table3}"
  IO.println "└────────────────────────────────────────────────┘"
  return [table1, table2, table3]

/-- Run R3 packed-MV baseline checks against dense reference results. -/
def runPackedReferenceTests : IO (List PropTestResult) := do
  IO.println "\n┌─ Packed MV vs Dense Reference ────────────────┐"
  let r13 := runBoolProp "MV layout invariants" prop_mv_layout_invariants
  IO.println s!"│ {r13}"
  let r14 ← runGenProp "MV full round-trip" prop_mv_full_roundtrip
  IO.println s!"│ {r14}"
  let r15 ← runGenProp "MV parity projection" prop_mv_parity_projection
  IO.println s!"│ {r15}"
  let r15p ← runGenProp "MV grade projection" prop_mv_grade_projection_dense
  IO.println s!"│ {r15p}"
  let r15s ← runGenProp "MV scalar part" prop_mv_scalar_part_dense
  IO.println s!"│ {r15s}"
  let r15n ← runGenProp "MV parity normSq" prop_mv_normSq_dense
  IO.println s!"│ {r15n}"
  let r15nr ← runGenProp "MV parity normSqRev" prop_mv_normSqRev_dense
  IO.println s!"│ {r15nr}"
  let r15sp ← runGenProp "MV scalar product" prop_mv_scalar_product_dense
  IO.println s!"│ {r15sp}"
  let r15a ← runGenProp "MV full linear ops" prop_mv_full_linear_ops_dense
  IO.println s!"│ {r15a}"
  let r15b ← runGenProp "MV even linear ops" prop_mv_even_linear_ops_dense
  IO.println s!"│ {r15b}"
  let r15c ← runGenProp "MV odd linear ops" prop_mv_odd_linear_ops_dense
  IO.println s!"│ {r15c}"
  let r15d ← runGenProp "MV full projectors" prop_mv_full_projectors_dense
  IO.println s!"│ {r15d}"
  let r15e ← runGenProp "MV parity widening" prop_mv_widen_dense
  IO.println s!"│ {r15e}"
  let r15f := runBoolProp "MV parity guarded coeff" prop_mv_parity_guard_coeff
  IO.println s!"│ {r15f}"
  let r15g := runBoolProp "MV parity guarded setCoeff" prop_mv_parity_guard_setCoeff
  IO.println s!"│ {r15g}"
  let r15h ← runGenProp "MV setCoeff dense reference" prop_mv_setCoeff_dense
  IO.println s!"│ {r15h}"
  let r15i := runBoolProp "MV ofPairs dense reference" prop_mv_ofPairs_dense
  IO.println s!"│ {r15i}"
  let r16 ← runGenProp "MV full multiplication" prop_mv_full_mul_dense
  IO.println s!"│ {r16}"
  let r17 ← runGenProp "MV even*even multiplication" prop_mv_even_mul_dense
  IO.println s!"│ {r17}"
  let r18 ← runGenProp "MV even*odd multiplication" prop_mv_even_odd_mul_dense
  IO.println s!"│ {r18}"
  let r19 ← runGenProp "MV odd*even multiplication" prop_mv_odd_even_mul_dense
  IO.println s!"│ {r19}"
  let r20 ← runGenProp "MV odd*odd multiplication" prop_mv_odd_mul_dense
  IO.println s!"│ {r20}"
  let r20a ← runGenProp "MV wedge" prop_mv_wedge_dense
  IO.println s!"│ {r20a}"
  let r20b ← runGenProp "MV left contraction" prop_mv_left_contract_dense
  IO.println s!"│ {r20b}"
  let r20c ← runGenProp "MV right contraction" prop_mv_right_contract_dense
  IO.println s!"│ {r20c}"
  let r20d ← runGenProp "MV full derived products" prop_mv_full_derived_products_dense
  IO.println s!"│ {r20d}"
  let r21 ← runGenProp "MV reverse" prop_mv_reverse_dense
  IO.println s!"│ {r21}"
  let r21a ← runGenProp "MV involutions" prop_mv_involutions_dense
  IO.println s!"│ {r21a}"
  let r22 ← runGenProp "MV sandwich" prop_mv_sandwich_dense 50
  IO.println s!"│ {r22}"
  let r22ops ← runGenProp "MV GAlgebra operations" prop_mv_galgebra_ops_dense 50
  IO.println s!"│ {r22ops}"
  let r22a ← runGenProp "MV GAlgebra sandwich" prop_mv_galgebra_sandwich_dense 50
  IO.println s!"│ {r22a}"
  let r22b ← runGenProp "MV GAlgebra normSq" prop_mv_galgebra_normSq_dense 50
  IO.println s!"│ {r22b}"
  let r22c ← runGenProp "MV GAlgebra unit helpers" prop_mv_galgebra_unit_helpers_dense 50
  IO.println s!"│ {r22c}"
  IO.println "└────────────────────────────────────────────────┘"
  return [r13, r14, r15, r15p, r15s, r15n, r15nr, r15sp, r15a, r15b, r15c, r15d,
    r15e, r15f, r15g, r15h, r15i, r16, r17, r18, r19, r20, r20a, r20b, r20c,
    r20d, r21, r21a, r22, r22ops, r22a, r22b, r22c]

/-- Run direct-dispatch vs typeclass-dispatch multiplication checks. -/
def runMVDispatchReferenceTests : IO (List PropTestResult) := do
  IO.println "\n┌─ Packed MV Dispatch Equivalence ──────────────┐"
  let dispatch1 ← runGenProp "R3 MV direct/typeclass multiplication"
    prop_mv_r3_dispatch_mul_equivalence 40
  IO.println s!"│ {dispatch1}"
  let dispatch2 ← runGenProp "PGA3 MV direct/typeclass multiplication"
    prop_mv_pga3_dispatch_mul_equivalence 30
  IO.println s!"│ {dispatch2}"
  let dispatch3 ← runGenProp "CGA3 MV direct/typeclass multiplication"
    prop_mv_cga3_dispatch_mul_equivalence 20
  IO.println s!"│ {dispatch3}"
  IO.println "└────────────────────────────────────────────────┘"
  return [dispatch1, dispatch2, dispatch3]

/-- Run PGA3 packed-MV baseline checks against dense reference results. -/
def runPGA3PackedReferenceTests : IO (List PropTestResult) := do
  IO.println "\n┌─ PGA3 Packed MV vs Dense Reference ───────────┐"
  let pgaMv1 ← runGenProp "PGA3 MV full round-trip" prop_mv_pga3_full_roundtrip
  IO.println s!"│ {pgaMv1}"
  let pgaMv2 ← runGenProp "PGA3 MV parity projection" prop_mv_pga3_parity_projection
  IO.println s!"│ {pgaMv2}"
  let pgaMv2p ← runGenProp "PGA3 MV grade projection" prop_mv_pga3_grade_projection_dense
  IO.println s!"│ {pgaMv2p}"
  let pgaMv2s ← runGenProp "PGA3 MV scalar part" prop_mv_pga3_scalar_part_dense
  IO.println s!"│ {pgaMv2s}"
  let pgaMv2n ← runGenProp "PGA3 MV parity normSq" prop_mv_pga3_normSq_dense
  IO.println s!"│ {pgaMv2n}"
  let pgaMv2nr ← runGenProp "PGA3 MV parity normSqRev" prop_mv_pga3_normSqRev_dense
  IO.println s!"│ {pgaMv2nr}"
  let pgaMv2sp ← runGenProp "PGA3 MV scalar product" prop_mv_pga3_scalar_product_dense
  IO.println s!"│ {pgaMv2sp}"
  let pgaMv2a ← runGenProp "PGA3 MV full linear ops" prop_mv_pga3_full_linear_ops_dense
  IO.println s!"│ {pgaMv2a}"
  let pgaMv2b ← runGenProp "PGA3 MV even linear ops" prop_mv_pga3_even_linear_ops_dense
  IO.println s!"│ {pgaMv2b}"
  let pgaMv2c ← runGenProp "PGA3 MV odd linear ops" prop_mv_pga3_odd_linear_ops_dense
  IO.println s!"│ {pgaMv2c}"
  let pgaMv2d ← runGenProp "PGA3 MV full projectors" prop_mv_pga3_full_projectors_dense
  IO.println s!"│ {pgaMv2d}"
  let pgaMv2e ← runGenProp "PGA3 MV parity widening" prop_mv_pga3_widen_dense
  IO.println s!"│ {pgaMv2e}"
  let pgaMv2f ← runGenProp "PGA3 MV setCoeff dense reference" prop_mv_pga3_setCoeff_dense
  IO.println s!"│ {pgaMv2f}"
  let pgaMv2g := runBoolProp "PGA3 MV ofPairs dense reference" prop_mv_pga3_ofPairs_dense
  IO.println s!"│ {pgaMv2g}"
  let pgaMv3 ← runGenProp "PGA3 MV full multiplication" prop_mv_pga3_full_mul_dense
  IO.println s!"│ {pgaMv3}"
  let pgaMv4 ← runGenProp "PGA3 MV even*even multiplication" prop_mv_pga3_even_mul_dense
  IO.println s!"│ {pgaMv4}"
  let pgaMv5 ← runGenProp "PGA3 MV even*odd multiplication" prop_mv_pga3_even_odd_mul_dense
  IO.println s!"│ {pgaMv5}"
  let pgaMv6 ← runGenProp "PGA3 MV odd*even multiplication" prop_mv_pga3_odd_even_mul_dense
  IO.println s!"│ {pgaMv6}"
  let pgaMv7 ← runGenProp "PGA3 MV odd*odd multiplication" prop_mv_pga3_odd_mul_dense
  IO.println s!"│ {pgaMv7}"
  let pgaMv7a ← runGenProp "PGA3 MV wedge" prop_mv_pga3_wedge_dense
  IO.println s!"│ {pgaMv7a}"
  let pgaMv7b ← runGenProp "PGA3 MV left contraction" prop_mv_pga3_left_contract_dense
  IO.println s!"│ {pgaMv7b}"
  let pgaMv7c ← runGenProp "PGA3 MV right contraction" prop_mv_pga3_right_contract_dense
  IO.println s!"│ {pgaMv7c}"
  let pgaMv7d ← runGenProp "PGA3 MV full derived products"
    prop_mv_pga3_full_derived_products_dense
  IO.println s!"│ {pgaMv7d}"
  let pgaMv8 ← runGenProp "PGA3 MV reverse" prop_mv_pga3_reverse_dense
  IO.println s!"│ {pgaMv8}"
  let pgaMv8a ← runGenProp "PGA3 MV involutions" prop_mv_pga3_involutions_dense
  IO.println s!"│ {pgaMv8a}"
  let pgaMv9 ← runGenProp "PGA3 MV sandwich" prop_mv_pga3_sandwich_dense 50
  IO.println s!"│ {pgaMv9}"
  let pgaMv9ops ← runGenProp "PGA3 MV GAlgebra operations"
    prop_mv_pga3_galgebra_ops_dense 40
  IO.println s!"│ {pgaMv9ops}"
  let pgaMv9a ← runGenProp "PGA3 MV GAlgebra sandwich"
    prop_mv_pga3_galgebra_sandwich_dense 40
  IO.println s!"│ {pgaMv9a}"
  let pgaMv9b ← runGenProp "PGA3 MV GAlgebra normSq"
    prop_mv_pga3_galgebra_normSq_dense 40
  IO.println s!"│ {pgaMv9b}"
  let pgaMv9c ← runGenProp "PGA3 MV GAlgebra unit helpers"
    prop_mv_pga3_galgebra_unit_helpers_dense 40
  IO.println s!"│ {pgaMv9c}"
  IO.println "└────────────────────────────────────────────────┘"
  return [pgaMv1, pgaMv2, pgaMv2p, pgaMv2s, pgaMv2n, pgaMv2nr, pgaMv2sp,
    pgaMv2a, pgaMv2b, pgaMv2c, pgaMv2d, pgaMv2e, pgaMv2f, pgaMv2g, pgaMv3,
    pgaMv4, pgaMv5, pgaMv6, pgaMv7, pgaMv7a, pgaMv7b, pgaMv7c, pgaMv7d, pgaMv8,
    pgaMv8a, pgaMv9, pgaMv9ops, pgaMv9a, pgaMv9b, pgaMv9c]

/-- Run user-facing PGA3 point-cloud transform checks. -/
def runPGA3PointCloudTransformTests : IO (List PropTestResult) := do
  IO.println "\n┌─ PGA3 Point-Cloud Motor Transforms ───────────┐"
  let pointCloud1 := runBoolProp "PGA3 point constructor/extractor"
    prop_pga3_point3_extract_point_cloud
  IO.println s!"│ {pointCloud1}"
  let pointCloud1a ← runGenProp "PGA3 generated point constructor vs dense"
    prop_pga3_generated_point3_dense
  IO.println s!"│ {pointCloud1a}"
  let pointCloud1b ← runGenProp "PGA3 generated motor constructor vs dense"
    prop_pga3_generated_motor3_dense
  IO.println s!"│ {pointCloud1b}"
  let pointCloud1c ← runGenProp "PGA3 generated plane constructor vs dense"
    prop_pga3_generated_plane3_dense
  IO.println s!"│ {pointCloud1c}"
  let pointCloud1d ← runGenProp "PGA3 generated line constructor vs dense"
    prop_pga3_generated_line3_dense
  IO.println s!"│ {pointCloud1d}"
  let pointCloud2 := runBoolProp "PGA3 identity motor point cloud"
    prop_pga3_identity_motor_point_cloud
  IO.println s!"│ {pointCloud2}"
  let pointCloud3 := runBoolProp "PGA3 z-rotor point cloud vs dense"
    prop_pga3_z_rotor_point_cloud_dense
  IO.println s!"│ {pointCloud3}"
  let pointCloud4 := runBoolProp "PGA3 composed motor point cloud vs dense"
    prop_pga3_composed_motor_point_cloud_dense
  IO.println s!"│ {pointCloud4}"
  let pointCloud5 := runBoolProp "PGA3 composed motor point cloud sequential"
    prop_pga3_composed_motor_point_cloud_sequential
  IO.println s!"│ {pointCloud5}"
  let pointCloud6 ← runGenProp "PGA3 generated motor point transform vs dense"
    prop_pga3_generated_motor_point_dense 50
  IO.println s!"│ {pointCloud6}"
  let pointCloud7 ← runGenProp "PGA3 generated motor plane transform vs dense"
    prop_pga3_generated_motor_plane_dense 50
  IO.println s!"│ {pointCloud7}"
  let pointCloud8 ← runGenProp "PGA3 generated motor line transform vs dense"
    prop_pga3_generated_motor_line_dense 50
  IO.println s!"│ {pointCloud8}"
  let pointCloud9 ← runGenProp "PGA3 generated composed motor point vs dense"
    prop_pga3_generated_composed_motor_point_dense 50
  IO.println s!"│ {pointCloud9}"
  let pointCloud10 ← runGenProp "PGA3 generated composed motor plane vs dense"
    prop_pga3_generated_composed_motor_plane_dense 50
  IO.println s!"│ {pointCloud10}"
  let pointCloud11 ← runGenProp "PGA3 generated composed motor line vs dense"
    prop_pga3_generated_composed_motor_line_dense 50
  IO.println s!"│ {pointCloud11}"
  IO.println "└────────────────────────────────────────────────┘"
  return [pointCloud1, pointCloud1a, pointCloud1b, pointCloud1c, pointCloud1d,
    pointCloud2, pointCloud3, pointCloud4, pointCloud5, pointCloud6, pointCloud7,
    pointCloud8, pointCloud9, pointCloud10, pointCloud11]

/-- Run user-facing CGA3 point-cloud transform checks. -/
def runCGA3PointCloudTransformTests : IO (List PropTestResult) := do
  IO.println "\n┌─ CGA3 Point Geometry and Translations ────────┐"
  let pointCloud0 := runBoolProp "CGA3 null basis vectors"
    prop_cga3_null_basis_vectors
  IO.println s!"│ {pointCloud0}"
  let pointCloud0a := runBoolProp "CGA3 point cloud null embeddings"
    prop_cga3_point_cloud_null_embeddings
  IO.println s!"│ {pointCloud0a}"
  let pointCloud0b ← runGenProp "CGA3 generated point null embeddings"
    prop_cga3_generated_point_null_embeddings 25
  IO.println s!"│ {pointCloud0b}"
  let pointCloud1 := runBoolProp "CGA3 translator point cloud"
    prop_cga3_translator_point_cloud
  IO.println s!"│ {pointCloud1}"
  let pointCloud2 ← runGenProp "CGA3 generated translator point"
    prop_cga3_generated_translator_point 5
  IO.println s!"│ {pointCloud2}"
  let pointCloud3 ← runGenProp "CGA3 translator composition point"
    prop_cga3_translator_composition_point 5
  IO.println s!"│ {pointCloud3}"
  IO.println "└────────────────────────────────────────────────┘"
  return [pointCloud0, pointCloud0a, pointCloud0b, pointCloud1, pointCloud2, pointCloud3]

/-- Run CGA3 packed-MV baseline checks against dense reference results. -/
def runCGA3PackedReferenceTests : IO (List PropTestResult) := do
  IO.println "\n┌─ CGA3 Packed MV vs Dense Reference ───────────┐"
  let cgaMv1 ← runGenProp "CGA3 MV full round-trip" prop_mv_cga3_full_roundtrip
  IO.println s!"│ {cgaMv1}"
  let cgaMv2 ← runGenProp "CGA3 MV parity projection" prop_mv_cga3_parity_projection
  IO.println s!"│ {cgaMv2}"
  let cgaMv2p ← runGenProp "CGA3 MV grade projection" prop_mv_cga3_grade_projection_dense
  IO.println s!"│ {cgaMv2p}"
  let cgaMv2s ← runGenProp "CGA3 MV scalar part" prop_mv_cga3_scalar_part_dense
  IO.println s!"│ {cgaMv2s}"
  let cgaMv2n ← runGenProp "CGA3 MV parity normSq" prop_mv_cga3_normSq_dense
  IO.println s!"│ {cgaMv2n}"
  let cgaMv2nr ← runGenProp "CGA3 MV parity normSqRev" prop_mv_cga3_normSqRev_dense
  IO.println s!"│ {cgaMv2nr}"
  let cgaMv2sp ← runGenProp "CGA3 MV scalar product" prop_mv_cga3_scalar_product_dense
  IO.println s!"│ {cgaMv2sp}"
  let cgaMv2a ← runGenProp "CGA3 MV full linear ops" prop_mv_cga3_full_linear_ops_dense
  IO.println s!"│ {cgaMv2a}"
  let cgaMv2b ← runGenProp "CGA3 MV even linear ops" prop_mv_cga3_even_linear_ops_dense
  IO.println s!"│ {cgaMv2b}"
  let cgaMv2c ← runGenProp "CGA3 MV odd linear ops" prop_mv_cga3_odd_linear_ops_dense
  IO.println s!"│ {cgaMv2c}"
  let cgaMv2d ← runGenProp "CGA3 MV full projectors" prop_mv_cga3_full_projectors_dense
  IO.println s!"│ {cgaMv2d}"
  let cgaMv2e ← runGenProp "CGA3 MV parity widening" prop_mv_cga3_widen_dense
  IO.println s!"│ {cgaMv2e}"
  let cgaMv2f ← runGenProp "CGA3 MV setCoeff dense reference" prop_mv_cga3_setCoeff_dense
  IO.println s!"│ {cgaMv2f}"
  let cgaMv2g := runBoolProp "CGA3 MV ofPairs dense reference" prop_mv_cga3_ofPairs_dense
  IO.println s!"│ {cgaMv2g}"
  let cgaMv3 ← runGenProp "CGA3 MV full multiplication" prop_mv_cga3_full_mul_dense
  IO.println s!"│ {cgaMv3}"
  let cgaMv4 ← runGenProp "CGA3 MV even*even multiplication" prop_mv_cga3_even_mul_dense
  IO.println s!"│ {cgaMv4}"
  let cgaMv5 ← runGenProp "CGA3 MV even*odd multiplication" prop_mv_cga3_even_odd_mul_dense
  IO.println s!"│ {cgaMv5}"
  let cgaMv6 ← runGenProp "CGA3 MV odd*even multiplication" prop_mv_cga3_odd_even_mul_dense
  IO.println s!"│ {cgaMv6}"
  let cgaMv7 ← runGenProp "CGA3 MV odd*odd multiplication" prop_mv_cga3_odd_mul_dense
  IO.println s!"│ {cgaMv7}"
  let cgaMv7a ← runGenProp "CGA3 MV wedge" prop_mv_cga3_wedge_dense
  IO.println s!"│ {cgaMv7a}"
  let cgaMv7b ← runGenProp "CGA3 MV left contraction" prop_mv_cga3_left_contract_dense
  IO.println s!"│ {cgaMv7b}"
  let cgaMv7c ← runGenProp "CGA3 MV right contraction" prop_mv_cga3_right_contract_dense
  IO.println s!"│ {cgaMv7c}"
  let cgaMv7d ← runGenProp "CGA3 MV full derived products"
    prop_mv_cga3_full_derived_products_dense
  IO.println s!"│ {cgaMv7d}"
  let cgaMv8 ← runGenProp "CGA3 MV reverse" prop_mv_cga3_reverse_dense
  IO.println s!"│ {cgaMv8}"
  let cgaMv8a ← runGenProp "CGA3 MV involutions" prop_mv_cga3_involutions_dense
  IO.println s!"│ {cgaMv8a}"
  let cgaMv9 ← runGenProp "CGA3 MV sandwich" prop_mv_cga3_sandwich_dense 50
  IO.println s!"│ {cgaMv9}"
  let cgaMv9ops ← runGenProp "CGA3 MV GAlgebra operations"
    prop_mv_cga3_galgebra_ops_dense 20
  IO.println s!"│ {cgaMv9ops}"
  let cgaMv9a ← runGenProp "CGA3 MV GAlgebra sandwich"
    prop_mv_cga3_galgebra_sandwich_dense 20
  IO.println s!"│ {cgaMv9a}"
  let cgaMv9b ← runGenProp "CGA3 MV GAlgebra normSq"
    prop_mv_cga3_galgebra_normSq_dense 20
  IO.println s!"│ {cgaMv9b}"
  let cgaMv9c ← runGenProp "CGA3 MV GAlgebra unit helpers"
    prop_mv_cga3_galgebra_unit_helpers_dense 20
  IO.println s!"│ {cgaMv9c}"
  IO.println "└────────────────────────────────────────────────┘"
  return [cgaMv1, cgaMv2, cgaMv2p, cgaMv2s, cgaMv2n, cgaMv2nr, cgaMv2sp,
    cgaMv2a, cgaMv2b, cgaMv2c, cgaMv2d, cgaMv2e, cgaMv2f, cgaMv2g, cgaMv3,
    cgaMv4, cgaMv5, cgaMv6, cgaMv7, cgaMv7a, cgaMv7b, cgaMv7c, cgaMv7d, cgaMv8,
    cgaMv8a, cgaMv9, cgaMv9ops, cgaMv9a, cgaMv9b, cgaMv9c]

/-- Run sparse-MV baseline checks against dense reference results. -/
def runSparseReferenceTests : IO (List PropTestResult) := do
  IO.println "\n┌─ Sparse vs Dense Reference ───────────────────┐"
  let r23 ← runRandomProp2 "Sparse addition" prop_sparse_add_dense
  IO.println s!"│ {r23}"
  let r24 ← runRandomProp2 "Sparse multiplication" prop_sparse_mul_dense
  IO.println s!"│ {r24}"
  let r25 ← runRandomProp2 "Sparse wedge" prop_sparse_wedge_dense
  IO.println s!"│ {r25}"
  let r25a ← runRandomProp2 "Sparse left contraction" prop_sparse_leftContract_dense
  IO.println s!"│ {r25a}"
  let r25b ← runRandomProp2 "Sparse right contraction" prop_sparse_rightContract_dense
  IO.println s!"│ {r25b}"
  let r25c ← runRandomProp2 "Sparse scalar product" prop_sparse_scalarProduct_dense
  IO.println s!"│ {r25c}"
  let r25g ← runRandomProp2 "Sparse inner product" prop_sparse_innerProduct_dense
  IO.println s!"│ {r25g}"
  let r25d ← runRandomProp2 "Sparse regressive product" prop_sparse_regressive_dense
  IO.println s!"│ {r25d}"
  let r25e ← runRandomProp2 "Sparse commutator" prop_sparse_commutator_dense
  IO.println s!"│ {r25e}"
  let r25f ← runRandomProp2 "Sparse anticommutator" prop_sparse_anticommutator_dense
  IO.println s!"│ {r25f}"
  let r26 ← runRandomProp "Sparse reverse" prop_sparse_reverse_dense
  IO.println s!"│ {r26}"
  let r27 ← runRandomProp "Sparse involute" prop_sparse_involute_dense
  IO.println s!"│ {r27}"
  let r28 ← runRandomProp "Sparse conjugate" prop_sparse_conjugate_dense
  IO.println s!"│ {r28}"
  let r29 ← runGenProp "Sparse grade projection" prop_sparse_gradeProject_dense
  IO.println s!"│ {r29}"
  let r29ops ← runGenProp "Sparse GAlgebra operations" prop_sparse_galgebra_ops_dense 50
  IO.println s!"│ {r29ops}"
  let r29a ← runRandomProp "Sparse grade idempotence" prop_sparse_gradeProject_idempotent
  IO.println s!"│ {r29a}"
  let r29b ← runRandomProp "Sparse grade orthogonality" prop_sparse_gradeProject_orthogonal
  IO.println s!"│ {r29b}"
  let r29c ← runRandomProp "Sparse grade decomposition" prop_sparse_gradeProject_decomposition
  IO.println s!"│ {r29c}"
  IO.println "└────────────────────────────────────────────────┘"
  return [r23, r24, r25, r25a, r25b, r25c, r25g, r25d, r25e, r25f, r26,
    r27, r28, r29, r29ops, r29a, r29b, r29c]

/-- Run PGA3 sparse-MV baseline checks against dense reference results. -/
def runPGA3SparseReferenceTests : IO (List PropTestResult) := do
  IO.println "\n┌─ PGA3 Sparse vs Dense Reference ──────────────┐"
  let pgaSparse1 ← runRandomPGA3Prop2 "PGA3 sparse addition" prop_sparse_pga3_add_dense
  IO.println s!"│ {pgaSparse1}"
  let pgaSparse2 ← runRandomPGA3Prop2 "PGA3 sparse multiplication" prop_sparse_pga3_mul_dense
  IO.println s!"│ {pgaSparse2}"
  let pgaSparse3 ← runRandomPGA3Prop2 "PGA3 sparse wedge" prop_sparse_pga3_wedge_dense
  IO.println s!"│ {pgaSparse3}"
  let pgaSparse3a ← runRandomPGA3Prop2 "PGA3 sparse left contraction"
    prop_sparse_pga3_leftContract_dense
  IO.println s!"│ {pgaSparse3a}"
  let pgaSparse3b ← runRandomPGA3Prop2 "PGA3 sparse right contraction"
    prop_sparse_pga3_rightContract_dense
  IO.println s!"│ {pgaSparse3b}"
  let pgaSparse3c ← runRandomPGA3Prop2 "PGA3 sparse scalar product"
    prop_sparse_pga3_scalarProduct_dense
  IO.println s!"│ {pgaSparse3c}"
  let pgaSparse3g ← runRandomPGA3Prop2 "PGA3 sparse inner product"
    prop_sparse_pga3_innerProduct_dense
  IO.println s!"│ {pgaSparse3g}"
  let pgaSparse3d ← runRandomPGA3Prop2 "PGA3 sparse regressive product"
    prop_sparse_pga3_regressive_dense
  IO.println s!"│ {pgaSparse3d}"
  let pgaSparse3e ← runRandomPGA3Prop2 "PGA3 sparse commutator"
    prop_sparse_pga3_commutator_dense
  IO.println s!"│ {pgaSparse3e}"
  let pgaSparse3f ← runRandomPGA3Prop2 "PGA3 sparse anticommutator"
    prop_sparse_pga3_anticommutator_dense
  IO.println s!"│ {pgaSparse3f}"
  let pgaSparse4 ← runRandomPGA3Prop "PGA3 sparse reverse" prop_sparse_pga3_reverse_dense
  IO.println s!"│ {pgaSparse4}"
  let pgaSparse5 ← runRandomPGA3Prop "PGA3 sparse involute" prop_sparse_pga3_involute_dense
  IO.println s!"│ {pgaSparse5}"
  let pgaSparse6 ← runRandomPGA3Prop "PGA3 sparse conjugate" prop_sparse_pga3_conjugate_dense
  IO.println s!"│ {pgaSparse6}"
  let pgaSparse7 ← runGenProp "PGA3 sparse grade projection" prop_sparse_pga3_gradeProject_dense
  IO.println s!"│ {pgaSparse7}"
  let pgaSparse7ops ← runGenProp "PGA3 sparse GAlgebra operations"
    prop_sparse_pga3_galgebra_ops_dense 40
  IO.println s!"│ {pgaSparse7ops}"
  let pgaSparse8 ← runRandomPGA3Prop "PGA3 sparse grade idempotence"
    prop_sparse_pga3_gradeProject_idempotent
  IO.println s!"│ {pgaSparse8}"
  let pgaSparse9 ← runRandomPGA3Prop "PGA3 sparse grade orthogonality"
    prop_sparse_pga3_gradeProject_orthogonal
  IO.println s!"│ {pgaSparse9}"
  let pgaSparse10 ← runRandomPGA3Prop "PGA3 sparse grade decomposition"
    prop_sparse_pga3_gradeProject_decomposition
  IO.println s!"│ {pgaSparse10}"
  IO.println "└────────────────────────────────────────────────┘"
  return [pgaSparse1, pgaSparse2, pgaSparse3, pgaSparse3a, pgaSparse3b,
    pgaSparse3c, pgaSparse3g, pgaSparse3d, pgaSparse3e, pgaSparse3f,
    pgaSparse4, pgaSparse5, pgaSparse6, pgaSparse7, pgaSparse7ops,
    pgaSparse8, pgaSparse9, pgaSparse10]

/-- Run CGA3 sparse-MV baseline checks against dense reference results. -/
def runCGA3SparseReferenceTests : IO (List PropTestResult) := do
  IO.println "\n┌─ CGA3 Sparse vs Dense Reference ──────────────┐"
  let r30 ← runRandomCGA3Prop2 "CGA3 sparse addition" prop_sparse_cga3_add_dense
  IO.println s!"│ {r30}"
  let r31 ← runRandomCGA3Prop2 "CGA3 sparse multiplication" prop_sparse_cga3_mul_dense
  IO.println s!"│ {r31}"
  let r32 ← runRandomCGA3Prop2 "CGA3 sparse wedge" prop_sparse_cga3_wedge_dense
  IO.println s!"│ {r32}"
  let r32a ← runRandomCGA3Prop2 "CGA3 sparse left contraction"
    prop_sparse_cga3_leftContract_dense
  IO.println s!"│ {r32a}"
  let r32b ← runRandomCGA3Prop2 "CGA3 sparse right contraction"
    prop_sparse_cga3_rightContract_dense
  IO.println s!"│ {r32b}"
  let r32c ← runRandomCGA3Prop2 "CGA3 sparse scalar product"
    prop_sparse_cga3_scalarProduct_dense
  IO.println s!"│ {r32c}"
  let r32g ← runRandomCGA3Prop2 "CGA3 sparse inner product"
    prop_sparse_cga3_innerProduct_dense
  IO.println s!"│ {r32g}"
  let r32d ← runRandomCGA3Prop2 "CGA3 sparse regressive product"
    prop_sparse_cga3_regressive_dense
  IO.println s!"│ {r32d}"
  let r32e ← runRandomCGA3Prop2 "CGA3 sparse commutator"
    prop_sparse_cga3_commutator_dense
  IO.println s!"│ {r32e}"
  let r32f ← runRandomCGA3Prop2 "CGA3 sparse anticommutator"
    prop_sparse_cga3_anticommutator_dense
  IO.println s!"│ {r32f}"
  let r33 ← runRandomCGA3Prop "CGA3 sparse reverse" prop_sparse_cga3_reverse_dense
  IO.println s!"│ {r33}"
  let r34 ← runRandomCGA3Prop "CGA3 sparse involute" prop_sparse_cga3_involute_dense
  IO.println s!"│ {r34}"
  let r35 ← runRandomCGA3Prop "CGA3 sparse conjugate" prop_sparse_cga3_conjugate_dense
  IO.println s!"│ {r35}"
  let r36 ← runGenProp "CGA3 sparse grade projection" prop_sparse_cga3_gradeProject_dense
  IO.println s!"│ {r36}"
  let r36ops ← runGenProp "CGA3 sparse GAlgebra operations"
    prop_sparse_cga3_galgebra_ops_dense 20
  IO.println s!"│ {r36ops}"
  let r37 ← runRandomCGA3Prop "CGA3 sparse grade idempotence"
    prop_sparse_cga3_gradeProject_idempotent
  IO.println s!"│ {r37}"
  let r38 ← runRandomCGA3Prop "CGA3 sparse grade orthogonality"
    prop_sparse_cga3_gradeProject_orthogonal
  IO.println s!"│ {r38}"
  let r39 ← runRandomCGA3Prop "CGA3 sparse grade decomposition"
    prop_sparse_cga3_gradeProject_decomposition
  IO.println s!"│ {r39}"
  IO.println "└────────────────────────────────────────────────┘"
  return [r30, r31, r32, r32a, r32b, r32c, r32g, r32d, r32e, r32f, r33,
    r34, r35, r36, r36ops, r37, r38, r39]

/-- Run truncated-MV checks against dense references after dropping high grades. -/
def runTruncatedReferenceTests : IO (List PropTestResult) := do
  IO.println "\n┌─ Truncated MV vs Dense Reference ─────────────┐"
  let t1 := runBoolProp "PGA3 truncated null basis square"
    prop_truncated_pga3_null_basis_square
  IO.println s!"│ {t1}"
  let t2 ← runGenProp "R3 truncated GAlgebra operations"
    prop_truncated_r3_galgebra_ops_dense 50
  IO.println s!"│ {t2}"
  let t3 ← runGenProp "PGA3 truncated GAlgebra operations"
    prop_truncated_pga3_galgebra_ops_dense 40
  IO.println s!"│ {t3}"
  let t4 ← runGenProp "CGA3 truncated GAlgebra operations"
    prop_truncated_cga3_galgebra_ops_dense 20
  IO.println s!"│ {t4}"
  IO.println "└────────────────────────────────────────────────┘"
  return [t1, t2, t3, t4]

/-- Run public dense/sparse representation conversion checks. -/
def runReprConversionTests : IO (List PropTestResult) := do
  IO.println "\n┌─ Representation Conversion ───────────────────┐"
  let repr1 ← runGenProp "R3 dense-sparse round-trip" prop_repr_r3_dense_sparse_roundtrip
  IO.println s!"│ {repr1}"
  let repr2 ← runRandomProp "R3 sparse-dense round-trip" prop_repr_r3_sparse_dense_roundtrip
  IO.println s!"│ {repr2}"
  let repr3 ← runGenProp "PGA3 dense-sparse round-trip" prop_repr_pga3_dense_sparse_roundtrip
  IO.println s!"│ {repr3}"
  let repr4 ← runRandomPGA3Prop "PGA3 sparse-dense round-trip"
    prop_repr_pga3_sparse_dense_roundtrip
  IO.println s!"│ {repr4}"
  let repr5 ← runGenProp "CGA3 dense-sparse round-trip" prop_repr_cga3_dense_sparse_roundtrip
  IO.println s!"│ {repr5}"
  let repr6 ← runRandomCGA3Prop "CGA3 sparse-dense round-trip"
    prop_repr_cga3_sparse_dense_roundtrip
  IO.println s!"│ {repr6}"
  IO.println "└────────────────────────────────────────────────┘"
  return [repr1, repr2, repr3, repr4, repr5, repr6]

/-- Run high-dimensional exact dense stress checks. -/
def runHighDimStressTests : IO (List PropTestResult) := do
  IO.println "\n┌─ High-D Exact Stress Checks ──────────────────┐"
  let s1 := runBoolProp "R5 basis and wedge" prop_R5_exact_basis_wedge
  IO.println s!"│ {s1}"
  let s2 := runBoolProp "R5 rotor and contraction" prop_R5_exact_rotor_contraction
  IO.println s!"│ {s2}"
  let s3 := runBoolProp "R4 Hodge and determinant" prop_R4_exact_hodge_det
  IO.println s!"│ {s3}"
  let s4 := runBoolProp "R4 Hodge square basis signs" prop_R4_exact_hodge_square_basis
  IO.println s!"│ {s4}"
  let s5 := runBoolProp "R5 Hodge square basis signs" prop_R5_exact_hodge_square_basis
  IO.println s!"│ {s5}"
  let s6 := runBoolProp "R4 composition and identities" prop_R4_exact_composition_identity
  IO.println s!"│ {s6}"
  let s7 := runBoolProp "R3 cross product matches Hodge cross"
    prop_R3_crossProduct3D_matches_hodge_cross
  IO.println s!"│ {s7}"
  IO.println "└────────────────────────────────────────────────┘"
  return [s1, s2, s3, s4, s5, s6, s7]

/-- Run rotor exponential checks against generic series and known CGA preconditions. -/
def runRotorExpReferenceTests : IO (List PropTestResult) := do
  IO.println "\n┌─ Rotor Exponential Reference Checks ──────────┐"
  let r1 := runBoolProp "scalar Taylor helpers match Float"
    prop_scalar_taylor_functions_match_float
  IO.println s!"│ {r1}"
  let r2 := runBoolProp "R3 expBivector matches sparse series"
    prop_expBivector_r3_e12_matches_series
  IO.println s!"│ {r2}"
  let r3 := runBoolProp "CGA3 hyperbolic expBivector matches series"
    prop_expBivector_cga3_ePlusEMinus_matches_series
  IO.println s!"│ {r3}"
  let r3a := runBoolProp "R3 scalar-square exp closed form"
    prop_expScalarSquareBivector_r3_closed_form
  IO.println s!"│ {r3a}"
  let r3b := runBoolProp "CGA3 scalar-square exp closed form"
    prop_expScalarSquareBivector_cga3_closed_form
  IO.println s!"│ {r3b}"
  let r4 := runBoolProp "CGA3 torus generator square non-scalar"
    prop_cga3_torus_generator_square_non_scalar
  IO.println s!"│ {r4}"
  let r5 := runBoolProp "CGA3 torus expBivector falls back to series"
    prop_expBivector_cga3_torus_generator_matches_series
  IO.println s!"│ {r5}"
  let r5a := runBoolProp "Scalar-square exp fallback matches series"
    prop_expScalarSquareBivector_fallback_matches_series
  IO.println s!"│ {r5a}"
  let r6 := runBoolProp "Projective scalar-square exp matches local series"
    ProjectiveJulia.prop_projective_scalar_square_exp_matches_series_locally
  IO.println s!"│ {r6}"
  let r7 := runBoolProp "Projective scalar-square exp inverse"
    ProjectiveJulia.prop_projective_scalar_square_exp_inverse
  IO.println s!"│ {r7}"
  let r8 := runBoolProp "Projective torus factored parts commute"
    ProjectiveJulia.prop_projective_torus_parts_commute
  IO.println s!"│ {r8}"
  let r9 := runBoolProp "Projective torus factored evaluator matches local Taylor"
    ProjectiveJulia.prop_projective_torus_factored_matches_local_taylor
  IO.println s!"│ {r9}"
  let r10 := runBoolProp "Projective orbit-2 closed form matches local Taylor"
    ProjectiveJulia.prop_projective_orbit2_closed_form_matches_local_taylor
  IO.println s!"│ {r10}"
  let r11 := runBoolProp "Projective stream motor parts commute"
    ProjectiveJulia.prop_projective_stream_motor_parts_commute
  IO.println s!"│ {r11}"
  let r12 := runBoolProp "Projective stream fields match local Taylor"
    ProjectiveJulia.prop_projective_stream_fields_match_local_taylor
  IO.println s!"│ {r12}"
  let r13 := runBoolProp "Conformal helix factored parts commute"
    ConformalJulia.prop_conformal_helix_parts_commute
  IO.println s!"│ {r13}"
  let r14 := runBoolProp "Conformal helix closed form matches motor"
    ConformalJulia.prop_conformal_helix_closed_form_matches_motor
  IO.println s!"│ {r14}"
  let r15 := runBoolProp "Conformal helix motor matches local Taylor"
    ConformalJulia.prop_conformal_helix_motor_matches_local_taylor
  IO.println s!"│ {r15}"
  IO.println "└────────────────────────────────────────────────┘"
  return [r1, r2, r3, r3a, r3b, r4, r5, r5a, r6, r7, r8, r9, r10, r11, r12,
    r13, r14, r15]

/-- Run pure coverage checks for the Lean Julia-example visual generator. -/
def runJuliaExampleCoverageTests : IO (List PropTestResult) := do
  IO.println "\n┌─ Julia Example Visual Coverage ───────────────┐"
  let j1 := runBoolProp "Julia example names complete"
    JuliaExampleCoverage.prop_julia_example_names_complete
  IO.println s!"│ {j1}"
  let j2 := runBoolProp "Julia example SVG payloads non-empty"
    JuliaExampleCoverage.prop_julia_example_svgs_nonempty
  IO.println s!"│ {j2}"
  let j3 := runBoolProp "Julia example manifest covers pairs"
    JuliaExampleCoverage.prop_julia_example_manifest_covers_examples
  IO.println s!"│ {j3}"
  let j4 := runBoolProp "Julia example manifest covers witnesses"
    JuliaExampleCoverage.prop_julia_example_manifest_covers_witnesses
  IO.println s!"│ {j4}"
  let j5 := runBoolProp "Julia comparison HTML covers pairs"
    JuliaExampleCoverage.prop_julia_example_comparison_html_covers_examples
  IO.println s!"│ {j5}"
  IO.println "└────────────────────────────────────────────────┘"
  return [j1, j2, j3, j4, j5]

/-- Run all property tests -/
def runPropertyTests : IO Unit := do
  IO.println "╔══════════════════════════════════════════════╗"
  IO.println "║  Grassmann Algebra Property Tests (Plausible) ║"
  IO.println "╚══════════════════════════════════════════════╝"
  IO.println ""
  -- Basis properties (deterministic)
  IO.println "┌─ Basis Properties ────────────────────────────┐"
  IO.println s!"│ {runBoolProp "R3 basis vectors square to 1" prop_R3_basis_squares}"
  IO.println s!"│ {runBoolProp "R3 basis anticommute" prop_R3_basis_anticommute}"
  IO.println s!"│ {runBoolProp "CGA3 signature correct" prop_CGA3_signature}"
  IO.println s!"│ {runBoolProp "PGA3 signature correct" prop_PGA3_signature}"
  IO.println s!"│ {runBoolProp "R3 basis anchors" prop_R3_basis_anchor_identities}"
  IO.println s!"│ {runBoolProp "PGA3 basis anchors" prop_PGA3_basis_anchor_identities}"
  IO.println s!"│ {runBoolProp "CGA3 basis anchors" prop_CGA3_basis_anchor_identities}"
  IO.println "└────────────────────────────────────────────────┘"
  -- Additive properties
  IO.println "\n┌─ Addition Properties ─────────────────────────┐"
  let r1 ← runRandomProp2 "Addition commutes" prop_add_comm
  IO.println s!"│ {r1}"
  let r2 ← runRandomProp3 "Addition associates" prop_add_assoc
  IO.println s!"│ {r2}"
  let r3 ← runRandomProp "Zero is identity" prop_add_zero
  IO.println s!"│ {r3}"
  let r4 ← runRandomProp "Negation inverts" prop_add_neg
  IO.println s!"│ {r4}"
  IO.println "└────────────────────────────────────────────────┘"
  -- Multiplicative properties
  IO.println "\n┌─ Multiplication Properties ───────────────────┐"
  let r5 ← runRandomProp3 "Multiplication associates" prop_mul_assoc 30
  IO.println s!"│ {r5}"
  let r6 ← runRandomProp "One is identity" prop_mul_one
  IO.println s!"│ {r6}"
  let r6scalarContract := runBoolProp "Scalar left contraction keeps all grades"
    prop_scalar_left_contraction_keeps_all_grades
  IO.println s!"│ {r6scalarContract}"
  let r6rightContract := runBoolProp "Scalar right contraction keeps all grades"
    prop_scalar_right_contraction_keeps_all_grades
  IO.println s!"│ {r6rightContract}"
  let r6a := runBoolProp "Scalar-part unit rotor hypothesis is insufficient"
    prop_unit_rotor_scalar_part_hypothesis_insufficient
  IO.println s!"│ {r6a}"
  let r6b := runBoolProp "Scalar-part rotor hypothesis does not preserve norm"
    prop_scalar_part_rotor_hypothesis_does_not_preserve_norm
  IO.println s!"│ {r6b}"
  let r6c := runBoolProp "Reverse-norm inverse formula needs scalar product"
    prop_reverse_norm_formula_requires_scalar_reverse_product
  IO.println s!"│ {r6c}"
  let r7 ← runRandomProp3 "Left distributivity" prop_left_distrib 30
  IO.println s!"│ {r7}"
  let r8 ← runRandomProp3 "Right distributivity" prop_right_distrib 30
  IO.println s!"│ {r8}"
  IO.println "└────────────────────────────────────────────────┘"
  -- Wedge and involutions
  IO.println "\n┌─ Wedge & Involution Properties ───────────────┐"
  let r9 ← runGenProp "Wedge anticommutes (vectors)" prop_wedge_anticomm_grade1
  IO.println s!"│ {r9}"
  let r9a ← runRandomProp "Wedge one identity" prop_wedge_one_identity
  IO.println s!"│ {r9a}"
  let r9b ← runRandomPGA3Prop "PGA3 wedge one identity" prop_pga3_wedge_one_identity
  IO.println s!"│ {r9b}"
  let r9c ← runRandomCGA3Prop "CGA3 wedge one identity" prop_cga3_wedge_one_identity
  IO.println s!"│ {r9c}"
  let r10 ← runRandomProp2 "Reverse anti-morphism" prop_reverse_antimorphism
  IO.println s!"│ {r10}"
  let r11 ← runRandomProp "Reverse involutive" prop_reverse_involutive
  IO.println s!"│ {r11}"
  let r12 ← runRandomProp "Involute involutive" prop_involute_involutive
  IO.println s!"│ {r12}"
  let r13 ← runRandomProp "Conjugate involutive" prop_conjugate_involutive
  IO.println s!"│ {r13}"
  IO.println "└────────────────────────────────────────────────┘"
  let bladeResults ← runBladeReferenceTests
  let nativeResults ← runNativeReferenceTests
  let signTableResults ← runSignTableReferenceTests
  let packedResults ← runPackedReferenceTests
  let dispatchResults ← runMVDispatchReferenceTests
  let pgaPackedResults ← runPGA3PackedReferenceTests
  let pgaPointCloudResults ← runPGA3PointCloudTransformTests
  let cgaPointCloudResults ← runCGA3PointCloudTransformTests
  let cgaPackedResults ← runCGA3PackedReferenceTests
  let sparseResults ← runSparseReferenceTests
  let pgaSparseResults ← runPGA3SparseReferenceTests
  let cgaSparseResults ← runCGA3SparseReferenceTests
  let truncatedResults ← runTruncatedReferenceTests
  let reprResults ← runReprConversionTests
  let stressResults ← runHighDimStressTests
  let rotorExpResults ← runRotorExpReferenceTests
  let juliaExampleResults ← runJuliaExampleCoverageTests
  -- Summary
  let coreResults := [r1, r2, r3, r4, r5, r6, r6scalarContract, r6rightContract,
    r6a, r6b, r6c, r7, r8, r9, r9a, r9b, r9c, r10, r11, r12, r13]
  let countPassed (results : List PropTestResult) := results.filter (·.passed) |>.length
  let passCount :=
    countPassed coreResults +
    countPassed bladeResults +
    countPassed nativeResults +
    countPassed signTableResults +
    countPassed packedResults +
    countPassed dispatchResults +
    countPassed pgaPackedResults +
    countPassed pgaPointCloudResults +
    countPassed cgaPointCloudResults +
    countPassed cgaPackedResults +
    countPassed sparseResults +
    countPassed pgaSparseResults +
    countPassed cgaSparseResults +
    countPassed truncatedResults +
    countPassed reprResults +
    countPassed stressResults +
    countPassed rotorExpResults +
    countPassed juliaExampleResults
  let basisProps := [prop_R3_basis_squares, prop_R3_basis_anticommute, prop_CGA3_signature,
    prop_PGA3_signature, prop_R3_basis_anchor_identities, prop_PGA3_basis_anchor_identities,
    prop_CGA3_basis_anchor_identities]
  let basisPass := basisProps.filter id |>.length
  let total :=
    coreResults.length +
    bladeResults.length +
    nativeResults.length +
    signTableResults.length +
    packedResults.length +
    dispatchResults.length +
    pgaPackedResults.length +
    pgaPointCloudResults.length +
    cgaPointCloudResults.length +
    cgaPackedResults.length +
    sparseResults.length +
    pgaSparseResults.length +
    cgaSparseResults.length +
    truncatedResults.length +
    reprResults.length +
    stressResults.length +
    rotorExpResults.length +
    juliaExampleResults.length +
    basisProps.length
  let totalPass := passCount + basisPass
  IO.println ""
  IO.println "╔══════════════════════════════════════════════╗"
  IO.println s!"║  Summary: {Nat.repr totalPass}/{Nat.repr total} property tests passed          ║"
  IO.println "╚══════════════════════════════════════════════╝"

-- Quick check using Plausible's built-in #test
-- #test ∀ (a b : R3Mv), a.mv + b.mv = b.mv + a.mv

/-! ## Optimization Consistency Tests

These tests verify that optimized implementations (sparse, table-based)
produce identical results to naive implementations.
-/

namespace OptimizationTests

open Grassmann

/-- Generate a pseudo-random R3 dense vector from seed -/
def randVector (seed : Nat) : Multivector R3 Float :=
  let s := seed.toFloat
  vector3 (Float.sin (s * 1.1)) (Float.cos (s * 2.3)) (Float.sin (s * 3.7))

/-- Generate a pseudo-random R3 dense bivector from seed -/
def randBivector (seed : Nat) : Multivector R3 Float :=
  let s := seed.toFloat
  bivector3 (Float.sin (s * 1.2)) (Float.cos (s * 2.5)) (Float.sin (s * 3.8))

/-- Generate a pseudo-random normalized R3 rotor from seed -/
def randRotor (seed : Nat) : Multivector R3 Float :=
  let B := randBivector seed
  let angle := Float.sin (seed.toFloat * 0.7) * 3.14159
  buildRotorFromHalfAngle B (Float.cos (angle/2)) (Float.sin (angle/2))
  |>.normalize

/-- Max absolute difference between dense multivectors -/
def maxDiff (a b : Multivector R3 Float) : Float :=
  (List.finRange 8).foldl (init := 0.0) fun acc i =>
    let diff := Float.abs (a.coeffs i - b.coeffs i)
    if diff > acc then diff else acc

/-- Test sparse sandwich vs naive sandwich -/
def testSparseSandwich (seed1 seed2 : Nat) : Bool :=
  let rotor := randRotor seed1
  let v := randVector seed2
  let naive := rotor.sandwich v
  let sparse := R3Fast.sandwichFast rotor v
  maxDiff naive sparse < 1e-10

/-- Test sparse rotor multiplication vs naive -/
def testSparseRotorMul (seed1 seed2 : Nat) : Bool :=
  let r1 := randRotor seed1
  let r2 := randRotor seed2
  let naive := r1 * r2
  let sparse := R3Fast.rotorMul r1 r2
  maxDiff naive sparse < 1e-10

/-- Test optimized vector squared vs naive -/
def testOptVectorSquared (seed : Nat) : Bool :=
  let v := randVector seed
  let naive := (v * v).scalarPart
  let opt := vectorSquaredScalar v
  Float.abs (naive - opt) < 1e-10

/-- Test sparse vector wedge vs naive -/
def testSparseVectorWedge (seed1 seed2 : Nat) : Bool :=
  let v1 := randVector seed1
  let v2 := randVector seed2
  let naive := v1 ⋀ᵐ v2
  let sparse := R3Fast.vectorWedge v1 v2
  maxDiff naive sparse < 1e-10

/-- Test table-based geometric product vs naive -/
def testTableGeoProduct (seed1 seed2 : Nat) : Bool :=
  let v1 := randVector seed1
  let v2 := randVector seed2
  let naive := v1 * v2
  let table := Multivector.geometricProductWithTable R3SignTable v1 v2
  maxDiff naive table < 1e-10

/-- Test table-based sandwich vs naive -/
def testTableSandwich (seed1 seed2 : Nat) : Bool :=
  let rotor := randRotor seed1
  let v := randVector seed2
  let naive := rotor.sandwich v
  let table := sandwichWithTable R3SignTable rotor v
  maxDiff naive table < 1e-10

/-- Run optimization consistency tests -/
def runOptimizationTests (numTests : Nat := 100) : IO Unit := do
  IO.println "\n┌─ Optimization Consistency Tests ──────────────┐"
  let seeds := List.range numTests
  let sparseSandwich := seeds.all fun s => testSparseSandwich s (s + 1)
  IO.println s!"│ Sparse sandwich: {if sparseSandwich then "PASS" else "FAIL"}"
  let sparseRotor := seeds.all fun s => testSparseRotorMul s (s + 3)
  IO.println s!"│ Sparse rotor mul: {if sparseRotor then "PASS" else "FAIL"}"
  let optVSq := seeds.all fun s => testOptVectorSquared s
  IO.println s!"│ Optimized v²: {if optVSq then "PASS" else "FAIL"}"
  let sparseWedge := seeds.all fun s => testSparseVectorWedge s (s + 5)
  IO.println s!"│ Sparse wedge: {if sparseWedge then "PASS" else "FAIL"}"
  let tableGeo := seeds.all fun s => testTableGeoProduct s (s + 7)
  IO.println s!"│ Table geometric: {if tableGeo then "PASS" else "FAIL"}"
  let tableSandwich := seeds.all fun s => testTableSandwich s (s + 11)
  IO.println s!"│ Table sandwich: {if tableSandwich then "PASS" else "FAIL"}"
  IO.println "└────────────────────────────────────────────────┘"
  let allPass := sparseSandwich && sparseRotor && optVSq && sparseWedge &&
                 tableGeo && tableSandwich
  if allPass then
    IO.println s!"  All 6 test categories PASSED ({Nat.repr (6 * numTests)} total test cases) ✓"
  else
    IO.println "  Some optimization tests FAILED ✗"

end OptimizationTests

/-! ## Grassmann.jl Oracle Reference

These are the Julia commands to verify our results match Grassmann.jl:

```julia
using Grassmann
@basis V"+++"

# Test associativity with random multivectors
a = rand()*v1 + rand()*v2 + rand()*v3 + rand()*v12 + rand()*v23 + rand()*v13 + rand()*v123
b = rand()*v1 + rand()*v2 + rand()*v3 + rand()*v12 + rand()*v23 + rand()*v13 + rand()*v123
c = rand()*v1 + rand()*v2 + rand()*v3 + rand()*v12 + rand()*v23 + rand()*v13 + rand()*v123
@assert isapprox((a*b)*c, a*(b*c); atol=1e-10)

# Test reverse anti-morphism
@assert isapprox(~(a*b), ~b * ~a; atol=1e-10)

# Test rotor normalization
θ = rand() * π
B = v12  # Unit bivector
R = exp(θ/2 * B)
@assert isapprox(R * ~R, 1; atol=1e-10)

# Test sandwich preserves vector grade
w = rand()*v1 + rand()*v2 + rand()*v3
rotated = R * w * ~R
@assert grade(rotated) == 1  # Still a vector

# Test sandwich preserves norm
@assert isapprox(abs(w), abs(rotated); atol=1e-10)

# Test rotor composition
R1 = exp(rand()*v12/2)
R2 = exp(rand()*v23/2)
w = rand()*v1 + rand()*v2 + rand()*v3
lhs = R2 * (R1 * w * ~R1) * ~R2
rhs = (R2*R1) * w * ~(R2*R1)
@assert isapprox(lhs, rhs; atol=1e-8)

# Test vector squared is scalar
w = rand()*v1 + rand()*v2 + rand()*v3
sq = w * w
@assert typeof(sq) <: Real  # Scalar only

# Test bivector squared is scalar (in R3)
B = rand()*v12 + rand()*v23 + rand()*v13
Bsq = B * B
@assert typeof(Bsq) <: Real  # Scalar only in 3D
```
-/

/-- Run full property test suite including optimization tests -/
def runFullPropertyTests : IO Unit := do
  runPropertyTests
  OptimizationTests.runOptimizationTests 100

-- Run a small optimization test suite during build
#eval OptimizationTests.runOptimizationTests 20

end Grassmann.PropertyTests

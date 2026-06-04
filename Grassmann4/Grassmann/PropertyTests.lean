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
import Grassmann.StaticOpt
import Grassmann.MV
import Grassmann.BladeIndex
import Grassmann.SignTables

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

/-- Create CGA3Mv from coefficient list -/
def CGA3Mv.ofList (coeffs : List (Nat × Float)) : CGA3Mv :=
  ⟨MultivectorS.ofList coeffs⟩

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

/-- Compare a packed `MV` result against its dense reference. -/
def packedMatchesDense {n : Nat} {sig : Signature n} {p : Parity}
    (packed : MV sig p) (dense : Multivector sig Float) (tol : Float := 1e-9) : Bool :=
  denseMvApproxEq (MV.toMultivector packed) dense tol

/-! ## Native Vector Reference Tests -/

/-- Convert a dense reference multivector to the native-vector baseline. -/
def nativeOfDense {n : Nat} {sig : Signature n} (m : Multivector sig Float) : NativeMV sig :=
  ⟨Vector.ofFn fun i => m.coeffs i⟩

/-- Compare a native-vector result against its dense reference coefficient-wise. -/
def nativeMatchesDense {n : Nat} {sig : Signature n} (native : NativeMV sig)
    (dense : Multivector sig Float) (tol : Float := 1e-9) : Bool :=
  (List.finRange (2 ^ n)).all fun i =>
    approxEq (native.coeff i.val) (dense.coeffs i) tol

/-- Native-vector round-trip preserves all dense coefficients. -/
def prop_native_full_roundtrip : Gen Bool := do
  let a ← genR3DenseMv
  return nativeMatchesDense (nativeOfDense a.mv) a.mv

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

/-- Packed reverse agrees with dense reverse. -/
def prop_mv_reverse_dense : Gen Bool := do
  let a ← genR3DenseMv
  let packed : MV R3 .full := MV.ofMultivector a.mv .full
  return packedMatchesDense (MV.rev packed) a.mv.reverse

/-- Packed sandwich product agrees with dense sandwich product for even versors. -/
def prop_mv_sandwich_dense : Gen Bool := do
  let r ← genR3DenseMv
  let x ← genR3DenseMv
  let denseR := r.mv.evenPart
  let denseX := x.mv.oddPart
  let packedR : MV R3 .even := MV.ofMultivector denseR .even
  let packedX : MV R3 .odd := MV.ofMultivector denseX .odd
  return packedMatchesDense (mvSandwich packedR packedX) (denseR.sandwich denseX) (tol := 1e-6)

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

/-- PGA3 packed reverse agrees with dense reverse. -/
def prop_mv_pga3_reverse_dense : Gen Bool := do
  let a ← genPGA3DenseMv
  let packed : MV PGA3 .full := MV.ofMultivector a.mv .full
  return packedMatchesDense (MV.rev packed) a.mv.reverse

/-- PGA3 packed sandwich product agrees with dense sandwich product for even versors. -/
def prop_mv_pga3_sandwich_dense : Gen Bool := do
  let r ← genPGA3DenseMv
  let x ← genPGA3DenseMv
  let denseR := r.mv.evenPart
  let denseX := x.mv.oddPart
  let packedR : MV PGA3 .even := MV.ofMultivector denseR .even
  let packedX : MV PGA3 .odd := MV.ofMultivector denseX .odd
  return packedMatchesDense (mvSandwich packedR packedX) (denseR.sandwich denseX) (tol := 1e-6)

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

/-- CGA3 packed reverse agrees with dense reverse. -/
def prop_mv_cga3_reverse_dense : Gen Bool := do
  let a ← genCGA3DenseMv
  let packed : MV CGA3 .full := MV.ofMultivector a.mv .full
  return packedMatchesDense (MV.rev packed) a.mv.reverse

/-- CGA3 packed sandwich product agrees with dense sandwich product for even versors. -/
def prop_mv_cga3_sandwich_dense : Gen Bool := do
  let r ← genCGA3DenseMv
  let x ← genCGA3DenseMv
  let denseR := r.mv.evenPart
  let denseX := x.mv.oddPart
  let packedR : MV CGA3 .even := MV.ofMultivector denseR .even
  let packedX : MV CGA3 .odd := MV.ofMultivector denseX .odd
  return packedMatchesDense (mvSandwich packedR packedX) (denseR.sandwich denseX) (tol := 1e-6)

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

/-- Run native-vector baseline checks against dense reference results. -/
def runNativeReferenceTests : IO (List PropTestResult) := do
  IO.println "\n┌─ Native Vector vs Dense Reference ───────────┐"
  let native1 ← runGenProp "Native full round-trip" prop_native_full_roundtrip
  IO.println s!"│ {native1}"
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
  IO.println "└────────────────────────────────────────────────┘"
  return [native1, native2, native3, native4, native5, native6]

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
  let r14 ← runGenProp "MV full round-trip" prop_mv_full_roundtrip
  IO.println s!"│ {r14}"
  let r15 ← runGenProp "MV parity projection" prop_mv_parity_projection
  IO.println s!"│ {r15}"
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
  let r21 ← runGenProp "MV reverse" prop_mv_reverse_dense
  IO.println s!"│ {r21}"
  let r22 ← runGenProp "MV sandwich" prop_mv_sandwich_dense 50
  IO.println s!"│ {r22}"
  IO.println "└────────────────────────────────────────────────┘"
  return [r14, r15, r16, r17, r18, r19, r20, r21, r22]

/-- Run PGA3 packed-MV baseline checks against dense reference results. -/
def runPGA3PackedReferenceTests : IO (List PropTestResult) := do
  IO.println "\n┌─ PGA3 Packed MV vs Dense Reference ───────────┐"
  let pgaMv1 ← runGenProp "PGA3 MV full round-trip" prop_mv_pga3_full_roundtrip
  IO.println s!"│ {pgaMv1}"
  let pgaMv2 ← runGenProp "PGA3 MV parity projection" prop_mv_pga3_parity_projection
  IO.println s!"│ {pgaMv2}"
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
  let pgaMv8 ← runGenProp "PGA3 MV reverse" prop_mv_pga3_reverse_dense
  IO.println s!"│ {pgaMv8}"
  let pgaMv9 ← runGenProp "PGA3 MV sandwich" prop_mv_pga3_sandwich_dense 50
  IO.println s!"│ {pgaMv9}"
  IO.println "└────────────────────────────────────────────────┘"
  return [pgaMv1, pgaMv2, pgaMv3, pgaMv4, pgaMv5, pgaMv6, pgaMv7, pgaMv8, pgaMv9]

/-- Run CGA3 packed-MV baseline checks against dense reference results. -/
def runCGA3PackedReferenceTests : IO (List PropTestResult) := do
  IO.println "\n┌─ CGA3 Packed MV vs Dense Reference ───────────┐"
  let cgaMv1 ← runGenProp "CGA3 MV full round-trip" prop_mv_cga3_full_roundtrip
  IO.println s!"│ {cgaMv1}"
  let cgaMv2 ← runGenProp "CGA3 MV parity projection" prop_mv_cga3_parity_projection
  IO.println s!"│ {cgaMv2}"
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
  let cgaMv8 ← runGenProp "CGA3 MV reverse" prop_mv_cga3_reverse_dense
  IO.println s!"│ {cgaMv8}"
  let cgaMv9 ← runGenProp "CGA3 MV sandwich" prop_mv_cga3_sandwich_dense 50
  IO.println s!"│ {cgaMv9}"
  IO.println "└────────────────────────────────────────────────┘"
  return [cgaMv1, cgaMv2, cgaMv3, cgaMv4, cgaMv5, cgaMv6, cgaMv7, cgaMv8, cgaMv9]

/-- Run sparse-MV baseline checks against dense reference results. -/
def runSparseReferenceTests : IO (List PropTestResult) := do
  IO.println "\n┌─ Sparse vs Dense Reference ───────────────────┐"
  let r23 ← runRandomProp2 "Sparse addition" prop_sparse_add_dense
  IO.println s!"│ {r23}"
  let r24 ← runRandomProp2 "Sparse multiplication" prop_sparse_mul_dense
  IO.println s!"│ {r24}"
  let r25 ← runRandomProp2 "Sparse wedge" prop_sparse_wedge_dense
  IO.println s!"│ {r25}"
  let r26 ← runRandomProp "Sparse reverse" prop_sparse_reverse_dense
  IO.println s!"│ {r26}"
  let r27 ← runRandomProp "Sparse involute" prop_sparse_involute_dense
  IO.println s!"│ {r27}"
  let r28 ← runRandomProp "Sparse conjugate" prop_sparse_conjugate_dense
  IO.println s!"│ {r28}"
  let r29 ← runGenProp "Sparse grade projection" prop_sparse_gradeProject_dense
  IO.println s!"│ {r29}"
  IO.println "└────────────────────────────────────────────────┘"
  return [r23, r24, r25, r26, r27, r28, r29]

/-- Run CGA3 sparse-MV baseline checks against dense reference results. -/
def runCGA3SparseReferenceTests : IO (List PropTestResult) := do
  IO.println "\n┌─ CGA3 Sparse vs Dense Reference ──────────────┐"
  let r30 ← runRandomCGA3Prop2 "CGA3 sparse addition" prop_sparse_cga3_add_dense
  IO.println s!"│ {r30}"
  let r31 ← runRandomCGA3Prop2 "CGA3 sparse multiplication" prop_sparse_cga3_mul_dense
  IO.println s!"│ {r31}"
  let r32 ← runRandomCGA3Prop2 "CGA3 sparse wedge" prop_sparse_cga3_wedge_dense
  IO.println s!"│ {r32}"
  let r33 ← runRandomCGA3Prop "CGA3 sparse reverse" prop_sparse_cga3_reverse_dense
  IO.println s!"│ {r33}"
  let r34 ← runRandomCGA3Prop "CGA3 sparse involute" prop_sparse_cga3_involute_dense
  IO.println s!"│ {r34}"
  let r35 ← runRandomCGA3Prop "CGA3 sparse conjugate" prop_sparse_cga3_conjugate_dense
  IO.println s!"│ {r35}"
  let r36 ← runGenProp "CGA3 sparse grade projection" prop_sparse_cga3_gradeProject_dense
  IO.println s!"│ {r36}"
  IO.println "└────────────────────────────────────────────────┘"
  return [r30, r31, r32, r33, r34, r35, r36]

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
  let r7 ← runRandomProp3 "Left distributivity" prop_left_distrib 30
  IO.println s!"│ {r7}"
  let r8 ← runRandomProp3 "Right distributivity" prop_right_distrib 30
  IO.println s!"│ {r8}"
  IO.println "└────────────────────────────────────────────────┘"
  -- Wedge and involutions
  IO.println "\n┌─ Wedge & Involution Properties ───────────────┐"
  let r9 ← runGenProp "Wedge anticommutes (vectors)" prop_wedge_anticomm_grade1
  IO.println s!"│ {r9}"
  let r10 ← runRandomProp2 "Reverse anti-morphism" prop_reverse_antimorphism
  IO.println s!"│ {r10}"
  let r11 ← runRandomProp "Reverse involutive" prop_reverse_involutive
  IO.println s!"│ {r11}"
  let r12 ← runRandomProp "Involute involutive" prop_involute_involutive
  IO.println s!"│ {r12}"
  let r13 ← runRandomProp "Conjugate involutive" prop_conjugate_involutive
  IO.println s!"│ {r13}"
  IO.println "└────────────────────────────────────────────────┘"
  let nativeResults ← runNativeReferenceTests
  let signTableResults ← runSignTableReferenceTests
  let packedResults ← runPackedReferenceTests
  let pgaPackedResults ← runPGA3PackedReferenceTests
  let cgaPackedResults ← runCGA3PackedReferenceTests
  let sparseResults ← runSparseReferenceTests
  let cgaSparseResults ← runCGA3SparseReferenceTests
  -- Summary
  let coreResults := [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13]
  let countPassed (results : List PropTestResult) := results.filter (·.passed) |>.length
  let passCount :=
    countPassed coreResults +
    countPassed nativeResults +
    countPassed signTableResults +
    countPassed packedResults +
    countPassed pgaPackedResults +
    countPassed cgaPackedResults +
    countPassed sparseResults +
    countPassed cgaSparseResults
  let basisPass := if prop_R3_basis_squares && prop_R3_basis_anticommute && prop_CGA3_signature
                   then 3 else 0
  let total :=
    coreResults.length + nativeResults.length + signTableResults.length + packedResults.length +
    pgaPackedResults.length + cgaPackedResults.length + sparseResults.length +
    cgaSparseResults.length + 3
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

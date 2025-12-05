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
import Grassmann.Products
import Grassmann.Manifold

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
    s!"[{status}] {r.name} ({r.numTests} tests){msg}"

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
      failMsg := s!"Failed on test {i}"
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
      failMsg := s!"Failed on test {i}"
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
      failMsg := s!"Failed on test {i}"
      break
  return { name, passed, numTests, message := failMsg }

/-- Run a Gen Bool property -/
def runGenProp (name : String) (prop : Gen Bool) (numTests : Nat := 100) : IO PropTestResult := do
  let mut passed := true
  let mut failMsg := ""
  for i in [0:numTests] do
    let result ← Gen.run prop (i * 2)
    if !result then
      passed := false
      failMsg := s!"Failed on test {i}"
      break
  return { name := name, passed := passed, numTests := numTests, message := failMsg }

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

  -- Summary
  let allResults := [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13]
  let passCount := allResults.filter (·.passed) |>.length
  let basisPass := if prop_R3_basis_squares && prop_R3_basis_anticommute && prop_CGA3_signature
                   then 3 else 0
  let total := allResults.length + 3
  let totalPass := passCount + basisPass

  IO.println ""
  IO.println "╔══════════════════════════════════════════════╗"
  IO.println s!"║  Summary: {totalPass}/{total} property tests passed          ║"
  IO.println "╚══════════════════════════════════════════════╝"

-- Quick check using Plausible's built-in #test
-- #test ∀ (a b : R3Mv), a.mv + b.mv = b.mv + a.mv

end Grassmann.PropertyTests

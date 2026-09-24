/-
  Grassmann/LCBridge.lean - Bridge between Levi-Civita and Grassmann types

  This module provides conversions between:
  - LeviCivita.Fast.FastLC.LC - General purpose LC numbers
  - LeviCivita.Compact.LC - Ultra-fast fixed-slot LC for AD
  - LeviCivita.Hyper.Vector3/Bivector3/Rotor3 - GA primitives with LC coefficients
  - Grassmann.Multivector - Our general multivector type

  The key insight: LC numbers give us automatic differentiation "for free"
  by computing f(x + ε) and extracting the ε coefficient as the derivative.
-/
import Grassmann.Multivector
import Grassmann.PGA
import LeviCivita.Fast
import LeviCivita.CompactLC
import LeviCivita.HyperBivector

namespace Grassmann.LCBridge

open LeviCivita.Fast.FastLC
-- Note: Don't open LeviCivita.Compact.LC to avoid ambiguity with FastLC
open LeviCivita.Hyper

/-! ## Type Aliases for Clarity -/

/-- LC number for general computation -/
abbrev LCNum := LeviCivita.Fast.FastLC.LC

/-- Compact LC for ultra-fast AD (fixed 7 slots) -/
abbrev CompactNum := LeviCivita.Compact.LC

/-! ## Multivector with LC Coefficients

A multivector whose coefficients are LC numbers, enabling automatic
differentiation of geometric algebra operations.
-/

/-- Multivector with FastLC coefficients -/
abbrev MultivectorLC (sig : Signature n) := Multivector sig LCNum

/-- Multivector with Compact LC coefficients (faster but limited range) -/
abbrev MultivectorCompact (sig : Signature n) := Multivector sig CompactNum

/-! ## Conversion Functions -/

/-- Lift a Float multivector to LC multivector (constant, no infinitesimal part) -/
def liftToLC {sig : Signature n} (m : Multivector sig Float) : MultivectorLC sig :=
  ⟨fun i => ofFloat (m.coeffs i)⟩

/-- Extract standard (real) part from LC multivector -/
def stdPart {sig : Signature n} (m : MultivectorLC sig) : Multivector sig Float :=
  ⟨fun i => std (m.coeffs i)⟩

/-- Extract derivative part (coefficient of ε) from LC multivector -/
def derivPart {sig : Signature n} (m : MultivectorLC sig) : Multivector sig Float :=
  ⟨fun i =>
    let lc := m.coeffs i
    -- Multiply by H = 1/ε to extract ε coefficient
    std (lc * H)⟩

/-- Lift Float multivector to Compact LC (ultra-fast) -/
def liftToCompact {sig : Signature n} (m : Multivector sig Float) : MultivectorCompact sig :=
  ⟨fun i => LeviCivita.Compact.LC.ofFloat (m.coeffs i)⟩

/-- Extract standard part from Compact LC multivector -/
def stdPartCompact {sig : Signature n} (m : MultivectorCompact sig) : Multivector sig Float :=
  ⟨fun i => LeviCivita.Compact.LC.std (m.coeffs i)⟩

/-! ## PGA3 with LC Coefficients -/

/-- PGA3 motor with LC coefficients -/
abbrev MotorLC := MultivectorLC PGA3

/-- PGA3 point with LC coefficients -/
abbrev PointLC := MultivectorLC PGA3

/-! ## Hyper Types ↔ Multivector Conversions -/

/-- Convert Hyper.Vector3 to PGA3 vector (grade-1 multivector) -/
def hyperVectorToPGA (v : Vector3) : MultivectorLC PGA3 :=
  -- PGA3 vector: x*e1 + y*e2 + z*e3
  -- Indices: e1=2, e2=4, e3=8
  ⟨fun i =>
    if i.val = 2 then v.x
    else if i.val = 4 then v.y
    else if i.val = 8 then v.z
    else 0⟩

/-- Extract PGA3 vector to Hyper.Vector3 -/
def pgaToHyperVector (m : MultivectorLC PGA3) : Vector3 :=
  ⟨m.coeffs ⟨2, by decide⟩,   -- e1
   m.coeffs ⟨4, by decide⟩,   -- e2
   m.coeffs ⟨8, by decide⟩⟩   -- e3

/-- Convert Hyper.Bivector3 to PGA3 bivector -/
def hyperBivectorToPGA (b : Bivector3) : MultivectorLC PGA3 :=
  -- PGA3 bivectors: e12=6, e13=10, e23=12
  ⟨fun i =>
    if i.val = 6 then b.xy
    else if i.val = 10 then b.xz
    else if i.val = 12 then b.yz
    else 0⟩

/-- Extract PGA3 bivector to Hyper.Bivector3 -/
def pgaToHyperBivector (m : MultivectorLC PGA3) : Bivector3 :=
  ⟨m.coeffs ⟨6, by decide⟩,   -- e12
   m.coeffs ⟨10, by decide⟩,  -- e13
   m.coeffs ⟨12, by decide⟩⟩  -- e23

/-! ## Automatic Differentiation via LC

The key pattern: to differentiate f at point x,
compute f(x + ε) and extract the ε coefficient.
-/

/-- Differentiate a scalar-valued function on multivectors.
    Returns (f(x), ∇f(x)) -/
def diffScalar {sig : Signature n}
    (f : MultivectorLC sig → LCNum)
    (x : Multivector sig Float)
    (direction : Multivector sig Float)
    : Float × Float :=
  -- Create x + ε·direction
  let xLC := liftToLC x
  let dirLC := liftToLC direction
  let xPerturbedCoeffs : Fin (2^n) → LCNum := fun i =>
    xLC.coeffs i + epsilon * dirLC.coeffs i
  let xPerturbed : MultivectorLC sig := ⟨xPerturbedCoeffs⟩
  -- Evaluate f(x + ε·direction)
  let result := f xPerturbed
  -- Extract value and directional derivative
  (std result, std (result * H))

/-- Differentiate a multivector-valued function.
    Returns (f(x), Df(x)[direction]) -/
def diffMultivector {sig : Signature n}
    (f : MultivectorLC sig → MultivectorLC sig)
    (x : Multivector sig Float)
    (direction : Multivector sig Float)
    : Multivector sig Float × Multivector sig Float :=
  let xLC := liftToLC x
  let dirLC := liftToLC direction
  let xPerturbedCoeffs : Fin (2^n) → LCNum := fun i =>
    xLC.coeffs i + epsilon * dirLC.coeffs i
  let xPerturbed : MultivectorLC sig := ⟨xPerturbedCoeffs⟩
  let result := f xPerturbed
  (stdPart result, derivPart result)

/-! ## Smooth Step Functions

For collision detection, we need smooth approximations to step functions.
LC numbers handle this naturally via ε-thick boundaries.
-/

/-- Smooth Heaviside step: H(x) ≈ 1 if x > 0, 0 if x < 0
    With LC, the transition happens over an ε-thick region. -/
def smoothHeaviside (x : LCNum) : LCNum :=
  -- Use sigmoid approximation: 1 / (1 + exp(-k*x))
  -- For LC, we can use a simpler polynomial approximation
  let stdX := std x
  if stdX > 1.0 then ofFloat 1.0
  else if stdX < -1.0 then ofFloat 0.0
  else
    -- In transition region: 0.5 + 0.5*x - 0.125*x³ (cubic smoothstep)
    let half := ofFloat 0.5
    let eighth := ofFloat 0.125
    half + half * x - eighth * x * x * x

/-- Smooth ramp: max(0, x) with ε-smooth corner -/
def smoothRamp (x : LCNum) : LCNum :=
  x * smoothHeaviside x

/-- Smooth absolute value with ε-smooth corner at origin -/
def smoothAbs (x : LCNum) : LCNum :=
  -- |x| ≈ x * sign(x) with smooth sign
  let sign := ofFloat 2.0 * smoothHeaviside x - ofFloat 1.0
  x * sign

/-! ## Tests -/

-- Test LC lift and extraction
#eval!
  let m : Multivector R3 Float := Multivector.scalar 3.14
  let mLC := liftToLC m
  let mBack := stdPart mLC
  mBack.scalarPart
-- Expected: 3.14

-- Test differentiation: d/dx (x²) at x=3 should be 6
#eval!
  let f : LCNum → LCNum := fun x => x * x
  let x := LeviCivita.Fast.FastLC.ofFloat 3.0
  let result := f (x + LeviCivita.Fast.FastLC.epsilon)
  LeviCivita.Fast.FastLC.std (result * LeviCivita.Fast.FastLC.H)
-- Expected: 6.0

-- Test Hyper.Vector3 conversion roundtrip
#eval!
  let v : Vector3 := Vector3.ofFloats 1.0 2.0 3.0
  let pga := hyperVectorToPGA v
  let v' := pgaToHyperVector pga
  Vector3.std v'
-- Expected: (1.0, 2.0, 3.0)

end Grassmann.LCBridge

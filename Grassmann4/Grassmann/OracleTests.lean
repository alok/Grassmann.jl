/-
  Grassmann/OracleTests.lean - Tests comparing against Grassmann.jl

  Each test includes the corresponding Julia code to verify results.
  Run the Julia code and compare against the Lean results.

  Julia setup:
  ```julia
  using Grassmann
  @basis V"+++"  # R3 Euclidean
  ```
-/
import Grassmann.Multivector
import Grassmann.LinearAlgebra
import Grassmann.SparseMultivector
import Grassmann.RotorExp
import Grassmann.GANotation

namespace Grassmann.OracleTests

open Grassmann
open Grassmann.LinearAlgebra

/-! ## Basic Blade Products

Julia:
```julia
v1 * v1  # 1 (vector squared = norm²)
v1 * v2  # v12 (geometric product)
v2 * v1  # -v12 (anticommutative)
v12 * v12  # -1 (bivector squared)
v123 * v123  # -1 (pseudoscalar squared)
```
-/

section BladeProductOracle

-- e1 * e1 = 1
#eval (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int) *
      (Multivector.ofBlade (e1 : Blade R3)) |>.scalarPart
-- Expected: 1 | Julia: scalar(v1 * v1) = 1

-- e1 * e2 = e12
#eval let e1v := (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)
      let e2v := (Multivector.ofBlade (e2 : Blade R3))
      (e1v * e2v).coeff e12
-- Expected: 1 | Julia: (v1 * v2)[2] coefficient

-- e2 * e1 = -e12
#eval let e1v := (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)
      let e2v := (Multivector.ofBlade (e2 : Blade R3))
      (e2v * e1v).coeff e12
-- Expected: -1 | Julia: (v2 * v1)[2] coefficient

-- e12 * e12 = -1
#eval (Multivector.ofBlade (e12 : Blade R3) : Multivector R3 Int) *
      (Multivector.ofBlade (e12 : Blade R3)) |>.scalarPart
-- Expected: -1 | Julia: scalar(v12 * v12) = -1

-- e123 * e123 = -1 (in odd dimensions)
#eval (Multivector.ofBlade (e123 : Blade R3) : Multivector R3 Int) *
      (Multivector.ofBlade (e123 : Blade R3)) |>.scalarPart
-- Expected: -1 | Julia: scalar(v123 * v123) = -1

end BladeProductOracle

/-! ## Wedge Products

Julia:
```julia
v1 ∧ v2  # v12
v1 ∧ v1  # 0
v1 ∧ v12  # 0 (shared index)
v3 ∧ v12  # v123
```
-/

section WedgeProductOracle

-- e1 ∧ e2 = e12
#eval let e1v := (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)
      let e2v := (Multivector.ofBlade (e2 : Blade R3))
      (e1v ⋀ᵐ e2v).coeff e12
-- Expected: 1 | Julia: (v1 ∧ v2) = v12

-- e2 ∧ e1 = -e12
#eval let e1v := (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)
      let e2v := (Multivector.ofBlade (e2 : Blade R3))
      (e2v ⋀ᵐ e1v).coeff e12
-- Expected: -1 | Julia: (v2 ∧ v1) = -v12

-- e1 ∧ e1 = 0
#eval let e1v := (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)
      (e1v ⋀ᵐ e1v).scalarPart
-- Expected: 0 | Julia: v1 ∧ v1 = 0

-- e3 ∧ e12 = e123 (or -e123 depending on ordering)
#eval let e3v := (Multivector.ofBlade (e3 : Blade R3) : Multivector R3 Int)
      let e12v := (Multivector.ofBlade (e12 : Blade R3))
      (e3v ⋀ᵐ e12v).coeff e123
-- Expected: 1 or -1 | Julia: v3 ∧ v12

end WedgeProductOracle

/-! ## Contractions

Julia:
```julia
v1 ⌋ v12  # v2 (left contraction)
v2 ⌋ v12  # -v1
v1 ⌋ v123  # v23
```
-/

section ContractionOracle

-- e1 ⌋ e12 = e2
#eval let e1v := (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)
      let e12v := (Multivector.ofBlade (e12 : Blade R3))
      (e1v ⌋ᵐ e12v).coeff e2
-- Expected: 1 | Julia: (v1 ⌋ v12) should give v2

-- e2 ⌋ e12 = -e1
#eval let e2v := (Multivector.ofBlade (e2 : Blade R3) : Multivector R3 Int)
      let e12v := (Multivector.ofBlade (e12 : Blade R3))
      (e2v ⌋ᵐ e12v).coeff e1
-- Expected: -1 | Julia: (v2 ⌋ v12) should give -v1

-- e1 ⌋ e123 = e23
#eval let e1v := (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)
      let e123v := (Multivector.ofBlade (e123 : Blade R3))
      (e1v ⌋ᵐ e123v).coeff e23
-- Expected: 1 | Julia: (v1 ⌋ v123) should give e23

end ContractionOracle

/-! ## Involutions

Julia:
```julia
~v1  # v1 (reverse of grade 1)
~v12  # -v12 (reverse of grade 2)
~v123  # -v123 (reverse of grade 3)
v1'  # -v1 (involute)
v12'  # v12 (involute)
```
-/

section InvolutionOracle

-- Reverse of e1 = e1
#eval (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)†.coeff e1
-- Expected: 1 | Julia: ~v1 = v1

-- Reverse of e12 = -e12
#eval (Multivector.ofBlade (e12 : Blade R3) : Multivector R3 Int)†.coeff e12
-- Expected: -1 | Julia: ~v12 = -v12

-- Reverse of e123 = -e123
#eval (Multivector.ofBlade (e123 : Blade R3) : Multivector R3 Int)†.coeff e123
-- Expected: -1 | Julia: ~v123 = -v123

-- Involute of e1 = -e1
#eval (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)ˆ.coeff e1
-- Expected: -1 | Julia: v1' = -v1

-- Involute of e12 = e12
#eval (Multivector.ofBlade (e12 : Blade R3) : Multivector R3 Int)ˆ.coeff e12
-- Expected: 1 | Julia: v12' = v12

end InvolutionOracle

/-! ## Rotation Tests

Julia:
```julia
R = 1 + v12  # Unnormalized 45° rotor
x = v1
R * x * ~R  # Should give -2*v2
```
-/

section RotationOracle

-- (1 + e12) * e1 * (1 + e12)† = -2*e2
#eval let R : Multivector R3 Int := Multivector.scalar 1 + Multivector.ofBlade e12
      let x : Multivector R3 Int := Multivector.ofBlade e1
      let result := R * x * R†
      (result.coeff e1, result.coeff e2)
-- Expected: (0, -2) | Julia: (R * v1 * ~R) coefficients

-- (1 + e12) * e2 * (1 + e12)† = 2*e1
#eval let R : Multivector R3 Int := Multivector.scalar 1 + Multivector.ofBlade e12
      let x : Multivector R3 Int := Multivector.ofBlade e2
      let result := R * x * R†
      (result.coeff e1, result.coeff e2)
-- Expected: (2, 0) | Julia: (R * v2 * ~R) coefficients

end RotationOracle

/-! ## Spacetime Algebra Tests

Julia:
```julia
@basis V"+---"  # Cl(1,3) Minkowski
# e1² = 1 (timelike), e2² = e3² = e4² = -1 (spacelike)
```
-/

section STAOracle

-- In Cl(1,3): e1² = +1 (timelike)
#eval let e1sta := (Multivector.ofBlade (e1 : Blade STA) : Multivector STA Int)
      (e1sta * e1sta).scalarPart
-- Expected: 1 | Julia with V"+---": v1 * v1 = 1

-- In Cl(1,3): e2² = -1 (spacelike)
#eval let e2sta := (Multivector.ofBlade (e2 : Blade STA) : Multivector STA Int)
      (e2sta * e2sta).scalarPart
-- Expected: -1 | Julia with V"+---": v2 * v2 = -1

-- In Cl(1,3): e3² = -1 (spacelike)
#eval let e3sta := (Multivector.ofBlade (e3 : Blade STA) : Multivector STA Int)
      (e3sta * e3sta).scalarPart
-- Expected: -1 | Julia with V"+---": v3 * v3 = -1

-- In Cl(1,3): e4² = -1 (spacelike)
#eval let e4sta := (Multivector.ofBlade (e4 : Blade STA) : Multivector STA Int)
      (e4sta * e4sta).scalarPart
-- Expected: -1 | Julia with V"+---": v4 * v4 = -1

end STAOracle

/-! ## Complex Number Tests (Cl(0,1))

Julia:
```julia
@basis V"-"  # Cl(0,1) = Complex numbers
# e1² = -1 (like i²)
(1 + v1) * (1 + v1)  # 2*v1 (since (1+i)² = 2i)
```
-/

section ComplexOracle

-- In Cl(0,1): e1² = -1
#eval let e1c := (Multivector.ofBlade (e1 : Blade ℂ_sig) : Multivector ℂ_sig Int)
      (e1c * e1c).scalarPart
-- Expected: -1 | Julia with V"-": v1 * v1 = -1

-- (1 + e1)² = 1 + 2e1 + e1² = 1 + 2e1 - 1 = 2e1
#eval let one_plus_i : Multivector ℂ_sig Int :=
        Multivector.scalar 1 + Multivector.ofBlade (e1 : Blade ℂ_sig)
      let sq := one_plus_i * one_plus_i
      (sq.scalarPart, sq.coeff (e1 : Blade ℂ_sig))
-- Expected: (0, 2) | Julia: (1 + v1)² = 2*v1

end ComplexOracle

/-! ## Quaternion Tests (Cl(0,2))

Julia:
```julia
@basis V"--"  # Cl(0,2) = Quaternions
# e1² = e2² = -1, e12² = -1
# i = e1, j = e2, k = e12
# i*j = k, j*k = i, k*i = j
```
-/

section QuaternionOracle

-- In Cl(0,2): e1² = -1
#eval let e1q := (Multivector.ofBlade (e1 : Blade ℍ_sig) : Multivector ℍ_sig Int)
      (e1q * e1q).scalarPart
-- Expected: -1 | Julia: i² = -1

-- In Cl(0,2): e2² = -1
#eval let e2q := (Multivector.ofBlade (e2 : Blade ℍ_sig) : Multivector ℍ_sig Int)
      (e2q * e2q).scalarPart
-- Expected: -1 | Julia: j² = -1

-- In Cl(0,2): e12² = -1
#eval let e12q := (Multivector.ofBlade (e12 : Blade ℍ_sig) : Multivector ℍ_sig Int)
      (e12q * e12q).scalarPart
-- Expected: -1 | Julia: k² = -1

-- i * j = k: e1 * e2 = e12
#eval let e1q := (Multivector.ofBlade (e1 : Blade ℍ_sig) : Multivector ℍ_sig Int)
      let e2q := (Multivector.ofBlade (e2 : Blade ℍ_sig))
      (e1q * e2q).coeff (e12 : Blade ℍ_sig)
-- Expected: 1 | Julia: i * j = k

-- j * i = -k: e2 * e1 = -e12
#eval let e1q := (Multivector.ofBlade (e1 : Blade ℍ_sig) : Multivector ℍ_sig Int)
      let e2q := (Multivector.ofBlade (e2 : Blade ℍ_sig))
      (e2q * e1q).coeff (e12 : Blade ℍ_sig)
-- Expected: -1 | Julia: j * i = -k

end QuaternionOracle

/-! ## Cross Product Oracle

Julia:
```julia
@basis V"+++"
# Cross product via Hodge dual of wedge
a × b = ⋆(a ∧ b)
v1 × v2 = v3
v2 × v3 = v1
v3 × v1 = v2
```
-/

section CrossProductOracle

-- e1 × e2 = e3 (disabled: depends on Float Ring sorry)
-- #eval let c := cross
--         (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Float)
--         (Multivector.ofBlade (e2 : Blade R3))
--       (c.coeff (e1 : Blade R3), c.coeff (e2 : Blade R3), c.coeff (e3 : Blade R3))
-- Expected: (0, 0, 1) | Julia: v1 × v2 = v3

-- e2 × e3 = e1
-- #eval let c := cross
--         (Multivector.ofBlade (e2 : Blade R3) : Multivector R3 Float)
--         (Multivector.ofBlade (e3 : Blade R3))
--       (c.coeff (e1 : Blade R3), c.coeff (e2 : Blade R3), c.coeff (e3 : Blade R3))
-- Expected: (1, 0, 0) | Julia: v2 × v3 = v1

-- e3 × e1 = e2
-- #eval let c := cross
--         (Multivector.ofBlade (e3 : Blade R3) : Multivector R3 Float)
--         (Multivector.ofBlade (e1 : Blade R3))
--       (c.coeff (e1 : Blade R3), c.coeff (e2 : Blade R3), c.coeff (e3 : Blade R3))
-- Expected: (0, 1, 0) | Julia: v3 × v1 = v2

end CrossProductOracle

/-! ## Determinant Oracle

Julia:
```julia
# 3x3 determinant via exterior algebra
det([a b c]) = (a ∧ b ∧ c) / (v1 ∧ v2 ∧ v3)
```
-/

section DeterminantOracle

-- Identity matrix det = 1 (disabled: depends on Float Ring sorry)
-- #eval let v1 : Multivector R3 Float := Multivector.ofBlade (e1 : Blade R3)
--       let v2 : Multivector R3 Float := Multivector.ofBlade (e2 : Blade R3)
--       let v3 : Multivector R3 Float := Multivector.ofBlade (e3 : Blade R3)
--       det [v1, v2, v3]
-- Expected: 1 | Julia: standard identity

-- Scaled diagonal det = product of diagonal
-- #eval let v1 : Multivector R3 Float := (Multivector.ofBlade (e1 : Blade R3)).smul 2
--       let v2 : Multivector R3 Float := (Multivector.ofBlade (e2 : Blade R3)).smul 3
--       let v3 : Multivector R3 Float := (Multivector.ofBlade (e3 : Blade R3)).smul 4
--       det [v1, v2, v3]
-- Expected: 24 | Julia: 2 * 3 * 4 = 24

-- Swapping columns negates determinant
-- #eval let v1 : Multivector R3 Float := Multivector.ofBlade (e1 : Blade R3)
--       let v2 : Multivector R3 Float := Multivector.ofBlade (e2 : Blade R3)
--       let v3 : Multivector R3 Float := Multivector.ofBlade (e3 : Blade R3)
--       det [v2, v1, v3]  -- swapped v1 and v2
-- Expected: -1 | Julia: one swap = -1

end DeterminantOracle

/-! ## Sparse Multivector Oracle Tests

These use the sparse representation from SparseMultivector.lean.

Julia:
```julia
using Grassmann
@basis V"+++"
# All operations should match the sparse implementation
```
-/

section SparseOracle
open Grassmann

-- Sparse geometric product: e1 * e2 = e12
#eval! let sig : Signature 3 := Signature.euclidean 3  -- Euclidean
       let e1s : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       let e2s : MultivectorS sig Float := MultivectorS.basis ⟨1, by omega⟩
       let result := e1s * e2s
       result.coeffBlade ⟨3⟩  -- e12 = bit pattern 011
-- Expected: 1.0 | Julia: (v1 * v2)[v12] = 1

-- Sparse: e2 * e1 = -e12
#eval! let sig : Signature 3 := Signature.euclidean 3
       let e1s : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       let e2s : MultivectorS sig Float := MultivectorS.basis ⟨1, by omega⟩
       let result := e2s * e1s
       result.coeffBlade ⟨3⟩
-- Expected: -1.0 | Julia: (v2 * v1)[v12] = -1

-- Sparse: e1² = 1 in Euclidean
#eval! let sig : Signature 3 := Signature.euclidean 3
       let e1s : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       (e1s * e1s).scalarPart
-- Expected: 1.0 | Julia: scalar(v1 * v1) = 1

-- Sparse: e12² = -1
#eval! let sig : Signature 3 := Signature.euclidean 3
       let e1s : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       let e2s : MultivectorS sig Float := MultivectorS.basis ⟨1, by omega⟩
       let e12s := e1s * e2s
       (e12s * e12s).scalarPart
-- Expected: -1.0 | Julia: scalar(v12 * v12) = -1

-- Sparse wedge: e1 ∧ e2 = e12
#eval! let sig : Signature 3 := Signature.euclidean 3
       let e1s : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       let e2s : MultivectorS sig Float := MultivectorS.basis ⟨1, by omega⟩
       (e1s ⋀ₛ e2s).coeffBlade ⟨3⟩
-- Expected: 1.0 | Julia: (v1 ∧ v2)[v12] = 1

-- Sparse wedge: e1 ∧ e1 = 0
#eval! let sig : Signature 3 := Signature.euclidean 3
       let e1s : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       (e1s ⋀ₛ e1s).nnz
-- Expected: 0 | Julia: v1 ∧ v1 = 0

end SparseOracle

/-! ## Rotor Exponential Oracle Tests

Julia:
```julia
using Grassmann
@basis V"+++"
B = π/4 * v12  # Bivector for 90° rotation
R = exp(B)     # cos(π/4) + sin(π/4)*v12 ≈ (0.707, 0.707*v12)
```
-/

section RotorExpOracle
open Grassmann

-- π/4 for 90° rotation (half-angle representation)
def piOver4 : Float := 0.7853981633974483

-- exp(0) = 1
#eval! let sig : Signature 3 := Signature.euclidean 3
       let zero : MultivectorS sig Float := MultivectorS.zero
       let result := expBivector zero
       result.scalarPart
-- Expected: 1.0 | Julia: exp(0) = 1

-- exp(π/4 * e12): scalar part should be cos(π/4) ≈ 0.707
#eval! let sig : Signature 3 := Signature.euclidean 3
       let e1s : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       let e2s : MultivectorS sig Float := MultivectorS.basis ⟨1, by omega⟩
       let B := (e1s * e2s).smul piOver4
       let R := expBivector B
       R.scalarPart
-- Expected: ~0.707107 | Julia: scalar(exp(π/4 * v12)) ≈ cos(π/4)

-- exp(π/4 * e12): bivector part should be sin(π/4) ≈ 0.707
#eval! let sig : Signature 3 := Signature.euclidean 3
       let e1s : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       let e2s : MultivectorS sig Float := MultivectorS.basis ⟨1, by omega⟩
       let B := (e1s * e2s).smul piOver4
       let R := expBivector B
       R.coeffBlade ⟨3⟩  -- e12 coefficient
-- Expected: ~0.707107 | Julia: exp(π/4 * v12)[v12] ≈ sin(π/4)

-- Rotor sandwich: rotate e1 by 90° around e12 gives -e2 (clockwise in e1-e2 plane)
#eval! let sig : Signature 3 := Signature.euclidean 3
       let e1s : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       let e2s : MultivectorS sig Float := MultivectorS.basis ⟨1, by omega⟩
       let B := (e1s * e2s).smul piOver4  -- 90° = π/2, half-angle = π/4
       let R := expBivector B
       let rotated := R * e1s * R†ₛ
       (rotated.coeffBlade ⟨1⟩, rotated.coeffBlade ⟨2⟩)  -- (e1 coeff, e2 coeff)
-- Expected: (~0, ~-1) | Julia: R * v1 * ~R gives -v2 (clockwise)

-- Rotor sandwich: rotate e2 by 90° around e12 gives e1 (clockwise in e1-e2 plane)
#eval! let sig : Signature 3 := Signature.euclidean 3
       let e1s : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       let e2s : MultivectorS sig Float := MultivectorS.basis ⟨1, by omega⟩
       let B := (e1s * e2s).smul piOver4
       let R := expBivector B
       let rotated := R * e2s * R†ₛ
       (rotated.coeffBlade ⟨1⟩, rotated.coeffBlade ⟨2⟩)
-- Expected: (~1, ~0) | Julia: R * v2 * ~R gives v1 (clockwise)

end RotorExpOracle

/-! ## Grade Projection Oracle Tests

Julia:
```julia
M = 1 + v1 + v12 + v123  # Mixed-grade multivector
grade(M, 0)  # 1 (scalar)
grade(M, 1)  # v1 (vector)
grade(M, 2)  # v12 (bivector)
grade(M, 3)  # v123 (trivector)
```
-/

section GradeProjectOracle
open Grassmann

-- Grade 0 projection
#eval! let sig : Signature 3 := Signature.euclidean 3
       let s : MultivectorS sig Float := MultivectorS.scalar 5.0
       let e1s : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       let M := s + e1s
       (gradeProject M 0).scalarPart
-- Expected: 5.0 | Julia: grade(5 + v1, 0) = 5

-- Grade 1 projection
#eval! let sig : Signature 3 := Signature.euclidean 3
       let s : MultivectorS sig Float := MultivectorS.scalar 5.0
       let e1s : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       let M := s + e1s.smul 3.0
       (gradeProject M 1).coeffBlade ⟨1⟩
-- Expected: 3.0 | Julia: grade(5 + 3*v1, 1) = 3*v1

-- Grade 2 projection of pure vector is 0
#eval! let sig : Signature 3 := Signature.euclidean 3
       let e1s : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       (gradeProject e1s 2).nnz
-- Expected: 0 | Julia: grade(v1, 2) = 0

end GradeProjectOracle

/-! ## Minkowski/STA Oracle Tests

Julia:
```julia
@basis V"+---"  # Cl(1,3) spacetime
v1 * v1  # +1 (timelike)
v2 * v2  # -1 (spacelike)
```
-/

section MinkowskiSparseOracle
open Grassmann

-- Timelike squared (e0² = +1) in signature +---
#eval! let sig : Signature 4 := ⟨BitVec.ofNat 4 0b1110, 0⟩  -- e1,e2,e3 negative
       let e0 : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       (e0 * e0).scalarPart
-- Expected: 1.0 | Julia: v1² = 1 in V"+---"

-- Spacelike squared (e1² = -1) in signature +---
#eval! let sig : Signature 4 := ⟨BitVec.ofNat 4 0b1110, 0⟩
       let e1 : MultivectorS sig Float := MultivectorS.basis ⟨1, by omega⟩
       (e1 * e1).scalarPart
-- Expected: -1.0 | Julia: v2² = -1 in V"+---"

-- Minkowski inner product of null vector (light-like)
-- In +---, a null vector satisfies v·v = 0
#eval! let sig : Signature 4 := ⟨BitVec.ofNat 4 0b1110, 0⟩
       let e0 : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       let e1 : MultivectorS sig Float := MultivectorS.basis ⟨1, by omega⟩
       let null := e0 + e1  -- Light-like: (1,1,0,0), should have norm² = 1 - 1 = 0
       (null * null).scalarPart
-- Expected: 0.0 | Julia: (v1 + v2)² = 0 for light-like

end MinkowskiSparseOracle

/-! ## 11D Rotation Oracle Tests (High-Dimensional Stress Test)

Julia:
```julia
@basis V"++++++++++++"  # 11D Euclidean
# Rotation in e1-e2 plane
```
-/

section HighDimOracle
open Grassmann

-- 11D: e1² = 1
#eval! let sig : Signature 11 := Signature.euclidean 11
       let e1 : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       (e1 * e1).scalarPart
-- Expected: 1.0 | Julia: v1² = 1 in 11D Euclidean

-- 11D: e1 * e2 = e12
#eval! let sig : Signature 11 := Signature.euclidean 11
       let e1 : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       let e2 : MultivectorS sig Float := MultivectorS.basis ⟨1, by omega⟩
       (e1 * e2).coeffBlade ⟨3⟩
-- Expected: 1.0 | Julia: (v1 * v2)[v12] = 1

-- 11D rotation: rotate e1 by 90° around e12 (gives -e2 due to clockwise convention)
#eval! let sig : Signature 11 := Signature.euclidean 11
       let e1 : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
       let e2 : MultivectorS sig Float := MultivectorS.basis ⟨1, by omega⟩
       let B := (e1 * e2).smul piOver4
       let R := expBivector B
       let rotated := R * e1 * R†ₛ
       -- Check it's approximately -e2 (clockwise rotation)
       let err := (rotated.coeffBlade ⟨2⟩ + 1.0).abs  -- +1 because we expect -1
       err < 0.001
-- Expected: true | Julia: rotation gives -v2 (clockwise)

end HighDimOracle

end Grassmann.OracleTests

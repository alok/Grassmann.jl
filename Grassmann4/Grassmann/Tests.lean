/-
  Grassmann/Tests.lean - Comprehensive test suite

  Tests that can be verified against Grassmann.jl as an oracle.
  Run corresponding Julia code to verify results.

  Julia verification code:
  ```julia
  using Grassmann
  @basis V"+++"  # R3 Euclidean

  # Then test each operation
  ```
-/
import Grassmann.Multivector

namespace Grassmann.Tests

open Grassmann

/-! ## Blade Product Tests

These test the basic blade products that form the foundation.
-/

section BladeProducts

-- Geometric product of basis vectors
#eval geometricProductBlades (e1 : Blade R3) (e1 : Blade R3)  -- e1*e1 = 1
#eval geometricProductBlades (e1 : Blade R3) (e2 : Blade R3)  -- e1*e2 = e12
#eval geometricProductBlades (e2 : Blade R3) (e1 : Blade R3)  -- e2*e1 = -e12
#eval geometricProductBlades (e1 : Blade R3) (e3 : Blade R3)  -- e1*e3 = e13
#eval geometricProductBlades (e2 : Blade R3) (e3 : Blade R3)  -- e2*e3 = e23

-- Geometric product of bivectors
#eval geometricProductBlades (e12 : Blade R3) (e12 : Blade R3)  -- e12*e12 = -1
#eval geometricProductBlades (e12 : Blade R3) (e23 : Blade R3)  -- e12*e23 = e13 or -e13?
#eval geometricProductBlades (e23 : Blade R3) (e12 : Blade R3)  -- e23*e12 = ?

-- Mixed grades
#eval geometricProductBlades (e1 : Blade R3) (e12 : Blade R3)  -- e1*e12 = e2
#eval geometricProductBlades (e12 : Blade R3) (e1 : Blade R3)  -- e12*e1 = -e2
#eval geometricProductBlades (e1 : Blade R3) (e23 : Blade R3)  -- e1*e23 = e123

-- Wedge products
#eval wedgeProductBlades (e1 : Blade R3) (e2 : Blade R3)  -- e1∧e2 = e12
#eval wedgeProductBlades (e1 : Blade R3) (e1 : Blade R3)  -- e1∧e1 = 0
#eval wedgeProductBlades (e1 : Blade R3) (e12 : Blade R3) -- e1∧e12 = 0 (share e1)
#eval wedgeProductBlades (e3 : Blade R3) (e12 : Blade R3) -- e3∧e12 = e123

-- Left contractions
#eval leftContractionBlades (e1 : Blade R3) (e12 : Blade R3)  -- e1⌋e12 = e2
#eval leftContractionBlades (e2 : Blade R3) (e12 : Blade R3)  -- e2⌋e12 = -e1
#eval leftContractionBlades (e1 : Blade R3) (e123 : Blade R3) -- e1⌋e123 = e23
#eval leftContractionBlades (e12 : Blade R3) (e123 : Blade R3) -- e12⌋e123 = e3 or -e3?

-- Scalar products
#eval scalarProductBlades (e1 : Blade R3) (e1 : Blade R3)  -- 1
#eval scalarProductBlades (e1 : Blade R3) (e2 : Blade R3)  -- 0
#eval scalarProductBlades (e12 : Blade R3) (e12 : Blade R3) -- -1
#eval scalarProductBlades (e123 : Blade R3) (e123 : Blade R3) -- -1

end BladeProducts

/-! ## Multivector Algebra Tests -/

section MultivectorAlgebra

-- Create basis multivectors
def mv_e1 : Multivector R3 Int := Multivector.ofBlade e1
def mv_e2 : Multivector R3 Int := Multivector.ofBlade e2
def mv_e3 : Multivector R3 Int := Multivector.ofBlade e3
def mv_e12 : Multivector R3 Int := Multivector.ofBlade e12
def mv_e23 : Multivector R3 Int := Multivector.ofBlade e23
def mv_e13 : Multivector R3 Int := Multivector.ofBlade e13
def mv_e123 : Multivector R3 Int := Multivector.ofBlade e123

-- Anticommutativity: e1*e2 + e2*e1 = 0
#eval (mv_e1 * mv_e2 + mv_e2 * mv_e1).scalarPart  -- 0
#eval (mv_e1 * mv_e2 + mv_e2 * mv_e1).coeff e12   -- 0

-- Vector squares
#eval (mv_e1 * mv_e1).scalarPart  -- 1
#eval (mv_e2 * mv_e2).scalarPart  -- 1
#eval (mv_e3 * mv_e3).scalarPart  -- 1

-- Sum of vectors squared
-- (e1 + e2)² = e1² + e1e2 + e2e1 + e2² = 1 + 0 + 1 = 2
#eval let v := mv_e1 + mv_e2
      (v * v).scalarPart  -- 2

-- (e1 + e2 + e3)² = 3
#eval let v := mv_e1 + mv_e2 + mv_e3
      (v * v).scalarPart  -- 3

-- Bivector squares
#eval (mv_e12 * mv_e12).scalarPart  -- -1
#eval (mv_e23 * mv_e23).scalarPart  -- -1
#eval (mv_e13 * mv_e13).scalarPart  -- -1

-- Pseudoscalar square
-- e123² = e1e2e3e1e2e3 = -e1e2e1e2e3e3 = -e1e2e1e2 = e1e1e2e2 = 1... wait
-- Actually in 3D: e123² = e1e2e3·e1e2e3 = (-1)^(3·2/2) * (signature contributions)
-- = (-1)^3 * 1 = -1
#eval (mv_e123 * mv_e123).scalarPart  -- -1

-- Duality: e1 * e23 = e123
#eval (mv_e1 * mv_e23).coeff e123  -- 1

-- Reverse tests
#eval mv_e1†.coeff e1   -- 1 (vectors unchanged)
#eval mv_e12†.coeff e12 -- -1 (bivectors flip)
#eval mv_e123†.coeff e123 -- -1 (grade 3 flips)

-- Grade involution
#eval mv_e1ˆ.coeff e1   -- -1 (odd grade)
#eval mv_e12ˆ.coeff e12 -- 1 (even grade)
#eval mv_e123ˆ.coeff e123 -- -1 (odd grade)

-- Conjugate = reverse ∘ involute
#eval mv_e1‡.coeff e1    -- -1
#eval mv_e12‡.coeff e12  -- -1
#eval mv_e123‡.coeff e123 -- 1

end MultivectorAlgebra

/-! ## Spacetime Algebra Tests (Minkowski) -/

section SpacetimeAlgebra

-- STA has signature (+,-,-,-)
-- First basis vector squares to +1 (timelike)
-- Others square to -1 (spacelike)

def sta_e1 : Multivector STA Int := Multivector.ofBlade (e1 : Blade STA)
def sta_e2 : Multivector STA Int := Multivector.ofBlade (e2 : Blade STA)
def sta_e3 : Multivector STA Int := Multivector.ofBlade (e3 : Blade STA)
def sta_e4 : Multivector STA Int := Multivector.ofBlade (e4 : Blade STA)

-- Check metric: e1² = -1 (first is timelike in Cl(1,3))
-- Actually wait - Cl(1,3) has 1 positive, 3 negative
-- So e1² = +1 (the positive one), e2² = e3² = e4² = -1
#eval (sta_e1 * sta_e1).scalarPart  -- depends on Cl(1,3) convention
#eval (sta_e2 * sta_e2).scalarPart
#eval (sta_e3 * sta_e3).scalarPart
#eval (sta_e4 * sta_e4).scalarPart

end SpacetimeAlgebra

/-! ## Algebraic Identity Tests -/

section AlgebraicIdentities

-- Test: a * b = a ∧ b + a ⌋ b (for vector a and blade b)
-- For orthogonal vectors: a * b = a ∧ b
#eval let a := mv_e1
      let b := mv_e2
      let prod := a * b
      let wedge := a ⋀ᵐ b
      (prod.coeff e12, wedge.coeff e12)  -- should be equal

-- For same vector: a * a = a ⌋ a = a² (scalar)
#eval let a := mv_e1
      let prod := a * a
      let contract := a ⌋ᵐ a
      (prod.scalarPart, contract.scalarPart)  -- both 1

-- Distributivity: a * (b + c) = a * b + a * c
#eval let a := mv_e1
      let b := mv_e2
      let c := mv_e3
      let lhs := a * (b + c)
      let rhs := a * b + a * c
      (lhs.coeff e12, rhs.coeff e12, lhs.coeff e13, rhs.coeff e13)

-- Associativity: (a * b) * c = a * (b * c)
#eval let a := mv_e1
      let b := mv_e2
      let c := mv_e3
      let lhs := (a * b) * c
      let rhs := a * (b * c)
      (lhs.coeff e123, rhs.coeff e123)  -- both should be 1

end AlgebraicIdentities

/-! ## Rotation Tests

In GA, rotations are done via sandwich product: R * v * R†
where R is a rotor (unit even multivector).

For a rotation by angle θ in the e12 plane:
R = cos(θ/2) + sin(θ/2) * e12
-/

section RotationTests

-- 90° rotation in e12 plane: R = (1 + e12) / √2
-- For integers, we can't normalize, but we can check the structure

-- R * e1 * R† should give e2 (for 90° rotation)
-- Let's verify the sandwich product structure

def rotor90 : Multivector R3 Int :=
  Multivector.scalar 1 + mv_e12  -- Unnormalized (1 + e12)

-- The sandwich product: check coefficients of R*e1*R†
#eval let x := mv_e1
      let R := rotor90
      let result := Multivector.sandwich R x
      (result.coeff e1, result.coeff e2, result.coeff e3)  -- Should transform e1

-- More detailed: compute R * e1
#eval (rotor90 * mv_e1).coeff e1
#eval (rotor90 * mv_e1).coeff e2
#eval (rotor90 * mv_e1).coeff e12

-- And R * e1 * R†
#eval let Rx := rotor90 * mv_e1
      let RxRt := Rx * rotor90†
      (RxRt.coeff e1, RxRt.coeff e2)

end RotationTests

/-! ## Reflection Tests

Reflection of vector v through hyperplane with normal n:
v' = -n * v * n⁻¹ = -n * v * n (when n² = 1)
-/

section ReflectionTests

-- Reflect e1 through e2 (plane perpendicular to e2)
-- -e2 * e1 * e2 = -e2 * e1 * e2 = -(-e1 * e2) * e2 = e1 * e2 * e2 = e1
-- Wait, that's wrong for reflection. Let me recalculate.

-- Reflection formula: v' = n * v * n (for unit n)
-- Reflect e1 through e2-axis (normal n = e2):
-- e2 * e1 * e2 = -e1 * e2 * e2 = -e1 * 1 = -e1 (wrong)
-- Actually: e2 * e1 = -e1 * e2 = -e12
-- Then: -e12 * e2 = -e12 * e2 = -(-e1) = e1
-- Hmm, still e1. Let me think...

-- Actually reflection through hyperplane with normal n:
-- v → -n v n⁻¹ for v perpendicular to n
-- v → v for v parallel to n

-- For e2 * e1 * e2:
-- e2 * e1 = -e12 (anticommute)
-- -e12 * e2 = -(e1 * e2) * e2 = -e1 * (e2 * e2) = -e1 * 1 = -e1
#eval let n := mv_e2
      let v := mv_e1
      let reflected := n * v * n
      (reflected.coeff e1, reflected.coeff e2)  -- (-1, 0) - reflects e1 to -e1

-- e2 is perpendicular to e1, so reflection through e2-hyperplane flips e1
-- This is correct!

end ReflectionTests

/-! ## Grade Projection Tests -/

section GradeProjection

-- Mixed multivector: 2 + 3*e1 + 4*e12 + 5*e123
def mixed : Multivector R3 Int :=
  Multivector.scalar 2 + mv_e1.smul 3 + mv_e12.smul 4 + mv_e123.smul 5

#eval mixed.scalarPart  -- 2
#eval mixed.grade0.scalarPart  -- 2
#eval mixed.grade1.coeff e1  -- 3
#eval mixed.grade2.coeff e12  -- 4
#eval (mixed.gradeProject 3).coeff e123  -- 5

-- Even part: 2 + 4*e12
#eval mixed.evenPart.scalarPart  -- 2
#eval mixed.evenPart.coeff e12  -- 4
#eval mixed.evenPart.coeff e1  -- 0

-- Odd part: 3*e1 + 5*e123
#eval mixed.oddPart.coeff e1  -- 3
#eval mixed.oddPart.coeff e123  -- 5
#eval mixed.oddPart.scalarPart  -- 0

end GradeProjection

/-! ## Sign Computation Tests

Verify the parityjoin algorithm against known results.
-/

section SignTests

-- Transposition counts
#eval countTranspositions 0b001 0b010 3  -- e1 past e2: need to count
#eval countTranspositions 0b010 0b001 3  -- e2 past e1
#eval countTranspositions 0b001 0b100 3  -- e1 past e3

-- Geometric signs
#eval geometricSign R3 (e1 : Blade R3) (e2 : Blade R3)  -- 1
#eval geometricSign R3 (e2 : Blade R3) (e1 : Blade R3)  -- -1
#eval geometricSign R3 (e12 : Blade R3) (e12 : Blade R3) -- -1

-- Wedge signs
#eval wedgeSign R3 (e1 : Blade R3) (e2 : Blade R3)  -- 1
#eval wedgeSign R3 (e2 : Blade R3) (e1 : Blade R3)  -- -1
#eval wedgeSign R3 (e1 : Blade R3) (e1 : Blade R3)  -- 0

end SignTests

end Grassmann.Tests

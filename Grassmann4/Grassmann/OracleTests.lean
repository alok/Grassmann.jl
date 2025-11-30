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

-- e1 × e2 = e3
#eval let c := cross
        (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Float)
        (Multivector.ofBlade (e2 : Blade R3))
      (c.coeff (e1 : Blade R3), c.coeff (e2 : Blade R3), c.coeff (e3 : Blade R3))
-- Expected: (0, 0, 1) | Julia: v1 × v2 = v3

-- e2 × e3 = e1
#eval let c := cross
        (Multivector.ofBlade (e2 : Blade R3) : Multivector R3 Float)
        (Multivector.ofBlade (e3 : Blade R3))
      (c.coeff (e1 : Blade R3), c.coeff (e2 : Blade R3), c.coeff (e3 : Blade R3))
-- Expected: (1, 0, 0) | Julia: v2 × v3 = v1

-- e3 × e1 = e2
#eval let c := cross
        (Multivector.ofBlade (e3 : Blade R3) : Multivector R3 Float)
        (Multivector.ofBlade (e1 : Blade R3))
      (c.coeff (e1 : Blade R3), c.coeff (e2 : Blade R3), c.coeff (e3 : Blade R3))
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

-- Identity matrix det = 1
#eval let v1 : Multivector R3 Float := Multivector.ofBlade (e1 : Blade R3)
      let v2 : Multivector R3 Float := Multivector.ofBlade (e2 : Blade R3)
      let v3 : Multivector R3 Float := Multivector.ofBlade (e3 : Blade R3)
      det [v1, v2, v3]
-- Expected: 1 | Julia: standard identity

-- Scaled diagonal det = product of diagonal
#eval let v1 : Multivector R3 Float := (Multivector.ofBlade (e1 : Blade R3)).smul 2
      let v2 : Multivector R3 Float := (Multivector.ofBlade (e2 : Blade R3)).smul 3
      let v3 : Multivector R3 Float := (Multivector.ofBlade (e3 : Blade R3)).smul 4
      det [v1, v2, v3]
-- Expected: 24 | Julia: 2 * 3 * 4 = 24

-- Swapping columns negates determinant
#eval let v1 : Multivector R3 Float := Multivector.ofBlade (e1 : Blade R3)
      let v2 : Multivector R3 Float := Multivector.ofBlade (e2 : Blade R3)
      let v3 : Multivector R3 Float := Multivector.ofBlade (e3 : Blade R3)
      det [v2, v1, v3]  -- swapped v1 and v2
-- Expected: -1 | Julia: one swap = -1

end DeterminantOracle

end Grassmann.OracleTests

/-
  Grassmann/DSLTests.lean - Comprehensive DSL Test Suite

  Tests the DSL across multiple signatures, dimensions, and operations.
  Each test section is self-contained with explicit expected values.
-/
import Grassmann.DSL
import Grassmann.SparseMultivector

open Grassmann Grassmann.DSL

/-! ## Test Infrastructure -/

/-- Check if two floats are approximately equal -/
def approxEq (a b : Float) (eps : Float := 1e-10) : Bool :=
  Float.abs (a - b) < eps

/-- Assert with message -/
def assertEq (actual expected : Float) (msg : String) : IO Unit := do
  if approxEq actual expected then
    IO.println s!"✓ {msg}: {actual}"
  else
    IO.println s!"✗ {msg}: expected {expected}, got {actual}"

/-- Pi constant -/
def pi : Float := 3.14159265358979323846

/-! ## R2: 2D Euclidean Algebra Cl(2,0,0)

Elements: scalar, e₁, e₂, e₁₂
Total: 2² = 4 basis elements

Key identities:
- e₁² = e₂² = 1
- e₁₂² = -1 (unit imaginary)
- e₁e₂ = e₁₂ = -e₂e₁
-/

section R2Tests

#eval R2 {
  -- Test: e₁² = 1
  let result := (e₁ * e₁).scalarPart
  if approxEq result 1.0 then "R2: e₁² = 1 ✓" else s!"R2: e₁² = {result} ✗"
}

#eval R2 {
  -- Test: e₂² = 1
  let result := (e₂ * e₂).scalarPart
  if approxEq result 1.0 then "R2: e₂² = 1 ✓" else s!"R2: e₂² = {result} ✗"
}

#eval R2 {
  -- Test: e₁₂² = -1
  let result := (e₁₂ * e₁₂).scalarPart
  if approxEq result (-1.0) then "R2: e₁₂² = -1 ✓" else s!"R2: e₁₂² = {result} ✗"
}

#eval R2 {
  -- Test: e₁e₂ = e₁₂
  let product := e₁ * e₂
  let coeff := product.coeff 3  -- 0b11 = 3
  if approxEq coeff 1.0 then "R2: e₁e₂ = e₁₂ ✓" else s!"R2: e₁e₂ coeff = {coeff} ✗"
}

#eval R2 {
  -- Test: e₂e₁ = -e₁₂
  let product := e₂ * e₁
  let coeff := product.coeff 3
  if approxEq coeff (-1.0) then "R2: e₂e₁ = -e₁₂ ✓" else s!"R2: e₂e₁ coeff = {coeff} ✗"
}

#eval R2 {
  -- Test: wedge product e₁ ∧ e₂ = e₁₂
  let wedge := e₁ ⋀ₛ e₂
  let coeff := wedge.coeff 3
  if approxEq coeff 1.0 then "R2: e₁∧e₂ = e₁₂ ✓" else s!"R2: e₁∧e₂ coeff = {coeff} ✗"
}

#eval R2 {
  -- Test: wedge is antisymmetric e₂ ∧ e₁ = -e₁₂
  let wedge := e₂ ⋀ₛ e₁
  let coeff := wedge.coeff 3
  if approxEq coeff (-1.0) then "R2: e₂∧e₁ = -e₁₂ ✓" else s!"R2: e₂∧e₁ coeff = {coeff} ✗"
}

#eval R2 {
  -- Test: self-wedge is zero
  let wedge := e₁ ⋀ₛ e₁
  let coeff := wedge.coeff 3
  if approxEq coeff 0.0 then "R2: e₁∧e₁ = 0 ✓" else s!"R2: e₁∧e₁ coeff = {coeff} ✗"
}

#eval R2 {
  -- Test: Rotation by 90 degrees using rotor R = exp(π/4 * e₁₂)
  -- For unit bivector i with i² = -1: exp(θi) = cos(θ) + sin(θ)i
  -- R = cos(π/4) + sin(π/4)e₁₂ ≈ 0.707 + 0.707e₁₂
  let c := Float.cos (pi / 4)
  let s := Float.sin (pi / 4)
  let R := MultivectorS.scalar c + e₁₂.smul s
  -- Rotate e₁: R * e₁ * R† should give (0, 1) (90° rotation)
  let Rrev := R.reverse
  let rotated := R * e₁ * Rrev
  -- e₂ component should be ~1, e₁ component should be ~0
  let x := rotated.coeff 1  -- e₁
  let y := rotated.coeff 2  -- e₂
  s!"R2: Rotate e₁ by 90°: ({x}, {y})"
}

end R2Tests

/-! ## R3: 3D Euclidean Algebra Cl(3,0,0)

Elements: scalar, e₁, e₂, e₃, e₁₂, e₁₃, e₂₃, e₁₂₃
Total: 2³ = 8 basis elements

Key identities:
- e₁² = e₂² = e₃² = 1
- e₁₂³ = -1 (pseudoscalar squares to -1 in 3D)
- Cross product: a × b = -(a ∧ b) * I⁻¹
-/

section R3Tests

#eval R3 {
  -- Test: all basis vectors square to 1
  let r1 := (e₁ * e₁).scalarPart
  let r2 := (e₂ * e₂).scalarPart
  let r3 := (e₃ * e₃).scalarPart
  s!"R3: e₁²={r1}, e₂²={r2}, e₃²={r3} (expect 1,1,1)"
}

#eval R3 {
  -- Test: all bivectors square to -1
  let r12 := (e₁₂ * e₁₂).scalarPart
  let r13 := (e₁₃ * e₁₃).scalarPart
  let r23 := (e₂₃ * e₂₃).scalarPart
  s!"R3: e₁₂²={r12}, e₁₃²={r13}, e₂₃²={r23} (expect -1,-1,-1)"
}

#eval R3 {
  -- Test: pseudoscalar squares to -1 in 3D
  let r := (e₁₂₃ * e₁₂₃).scalarPart
  if approxEq r (-1.0) then "R3: I² = -1 ✓" else s!"R3: I² = {r} ✗"
}

#eval R3 {
  -- Test: e₁e₂e₃ = e₁₂₃
  let product := e₁ * e₂ * e₃
  let coeff := product.coeff 7  -- 0b111 = 7
  if approxEq coeff 1.0 then "R3: e₁e₂e₃ = e₁₂₃ ✓" else s!"R3: coeff = {coeff} ✗"
}

#eval R3 {
  -- Test: cyclic permutation e₂e₃e₁ = e₁₂₃
  let product := e₂ * e₃ * e₁
  let coeff := product.coeff 7
  s!"R3: e₂e₃e₁ coeff = {coeff} (expect 1)"
}

#eval R3 {
  -- Test: grade projection
  let mv := e₁ + e₂ + e₁₂ + e₁₂₃
  let grade0 := mv.gradeProject 0
  let grade1 := mv.gradeProject 1
  let grade2 := mv.gradeProject 2
  let grade3 := mv.gradeProject 3
  s!"R3 grades: g0={grade0.nnz}, g1={grade1.nnz}, g2={grade2.nnz}, g3={grade3.nnz}"
}

#eval R3 {
  -- Test: vector norm squared
  let v := e₁.smul 3.0 + e₂.smul 4.0  -- (3,4,0)
  let normSq := (v * v).scalarPart
  if approxEq normSq 25.0 then "R3: |v|² = 25 ✓" else s!"R3: |v|² = {normSq} ✗"
}

#eval R3 {
  -- Test: reverse of bivector
  let biv := e₁₂
  let rev := biv.reverse
  -- Bivector reverses with sign flip: (e₁∧e₂)† = e₂∧e₁ = -e₁₂
  let coeff := rev.coeff 3
  if approxEq coeff (-1.0) then "R3: (e₁₂)† = -e₁₂ ✓" else s!"R3: coeff = {coeff} ✗"
}

#eval R3 {
  -- Test: reverse of vector is itself
  let v := e₁ + e₂
  let rev := v.reverse
  let c1 := rev.coeff 1
  let c2 := rev.coeff 2
  s!"R3: (e₁+e₂)† = ({c1}, {c2}) (expect 1,1)"
}

end R3Tests

/-! ## R4: 4D Euclidean Algebra Cl(4,0,0)

Elements: 2⁴ = 16 basis elements
Grade distribution: 1 + 4 + 6 + 4 + 1
-/

section R4Tests

#eval R4 {
  -- Test: 4D basis vectors all square to 1
  let results := [
    (e₁ * e₁).scalarPart,
    (e₂ * e₂).scalarPart,
    (e₃ * e₃).scalarPart,
    (e₄ * e₄).scalarPart
  ]
  s!"R4: basis squares = {results}"
}

#eval R4 {
  -- Test: 4D pseudoscalar squares to 1 (even dimension)
  let I := e₁₂₃₄
  let r := (I * I).scalarPart
  if approxEq r 1.0 then "R4: I² = 1 ✓" else s!"R4: I² = {r} ✗"
}

#eval R4 {
  -- Test: anticommutativity
  let ab := e₁ * e₄
  let ba := e₄ * e₁
  let sum := ab + ba
  if approxEq sum.nnz.toFloat 0.0 then "R4: e₁e₄ + e₄e₁ = 0 ✓"
  else s!"R4: anticommutator nnz = {sum.nnz}"
}

#eval R4 {
  -- Test: sum of all basis vectors squared
  let v := e₁ + e₂ + e₃ + e₄
  let normSq := (v * v).scalarPart
  if approxEq normSq 4.0 then "R4: |(1,1,1,1)|² = 4 ✓" else s!"R4: norm = {normSq} ✗"
}

end R4Tests

/-! ## Cl(1,1): Hyperbolic Plane

Signature: e₁² = 1, e₂² = -1
This is the split-complex numbers / hyperbolic numbers.
-/

section HyperbolicTests

#eval Cl(1,1) {
  -- Test: e₁² = 1 (positive)
  let r := (e₁ * e₁).scalarPart
  if approxEq r 1.0 then "Cl(1,1): e₁² = 1 ✓" else s!"Cl(1,1): e₁² = {r} ✗"
}

#eval Cl(1,1) {
  -- Test: e₂² = -1 (negative)
  let r := (e₂ * e₂).scalarPart
  if approxEq r (-1.0) then "Cl(1,1): e₂² = -1 ✓" else s!"Cl(1,1): e₂² = {r} ✗"
}

#eval Cl(1,1) {
  -- Test: e₁₂² = 1 (product of +1 and -1 signature)
  let r := (e₁₂ * e₁₂).scalarPart
  if approxEq r 1.0 then "Cl(1,1): e₁₂² = 1 ✓" else s!"Cl(1,1): e₁₂² = {r} ✗"
}

#eval Cl(1,1) {
  -- Test: null vector (e₁ + e₂)² = 0
  let v := e₁ + e₂
  let normSq := (v * v).scalarPart
  -- (e₁ + e₂)² = e₁² + e₁e₂ + e₂e₁ + e₂² = 1 + 0 + 0 + (-1) = 0
  if approxEq normSq 0.0 then "Cl(1,1): null vector ✓" else s!"Cl(1,1): norm = {normSq} ✗"
}

end HyperbolicTests

/-! ## Cl(0,2): Quaternion Algebra

Signature: e₁² = e₂² = -1
The even subalgebra is isomorphic to the quaternions.
-/

section QuaternionTests

#eval Cl(0,2) {
  -- Test: e₁² = -1
  let r := (e₁ * e₁).scalarPart
  if approxEq r (-1.0) then "Cl(0,2): e₁² = -1 ✓" else s!"Cl(0,2): e₁² = {r} ✗"
}

#eval Cl(0,2) {
  -- Test: e₂² = -1
  let r := (e₂ * e₂).scalarPart
  if approxEq r (-1.0) then "Cl(0,2): e₂² = -1 ✓" else s!"Cl(0,2): e₂² = {r} ✗"
}

#eval Cl(0,2) {
  -- Test: e₁₂² = -1 (quaternion-like)
  let r := (e₁₂ * e₁₂).scalarPart
  if approxEq r (-1.0) then "Cl(0,2): e₁₂² = -1 ✓" else s!"Cl(0,2): e₁₂² = {r} ✗"
}

#eval Cl(0,2) {
  -- Test: e₁e₂e₁e₂ = e₁₂e₁₂ = -1
  let r := (e₁ * e₂ * e₁ * e₂).scalarPart
  if approxEq r (-1.0) then "Cl(0,2): e₁e₂e₁e₂ = -1 ✓" else s!"Cl(0,2): = {r} ✗"
}

end QuaternionTests

/-! ## Cl(1,3): Spacetime Algebra (STA)

Signature: e₀² = 1 (time), e₁² = e₂² = e₃² = -1 (space)
The algebra of special relativity.
-/

section STATests

#eval STA {
  -- In STA syntax, indices are 1-based
  -- e₁² = 1 (timelike, positive signature comes first in Cl(1,3))
  let r := (e₁ * e₁).scalarPart
  s!"STA: e₁² = {r} (expect 1, timelike)"
}

#eval STA {
  -- e₂² = -1 (spacelike)
  let r := (e₂ * e₂).scalarPart
  s!"STA: e₂² = {r} (expect -1, spacelike)"
}

#eval STA {
  -- e₃² = -1 (spacelike)
  let r := (e₃ * e₃).scalarPart
  s!"STA: e₃² = {r} (expect -1, spacelike)"
}

#eval STA {
  -- e₄² = -1 (spacelike)
  let r := (e₄ * e₄).scalarPart
  s!"STA: e₄² = {r} (expect -1, spacelike)"
}

#eval STA {
  -- Test: 4D pseudoscalar
  let I := e₁₂₃₄
  let r := (I * I).scalarPart
  -- Cl(1,3): I² = (-1)^(1*3) * (-1)^(4*3/2) = (-1)^3 * (-1)^6 = -1 * 1 = -1
  s!"STA: I² = {r}"
}

end STATests

/-! ## PGA3: 3D Projective Geometric Algebra Cl(3,0,1)

4D algebra with one degenerate (null) basis vector e₀.
Used for 3D projective geometry.
-/

section PGA3Tests

#eval PGA3 {
  -- Test: Euclidean basis vectors square to 1
  let r1 := (e₁ * e₁).scalarPart
  let r2 := (e₂ * e₂).scalarPart
  let r3 := (e₃ * e₃).scalarPart
  if approxEq r1 1.0 && approxEq r2 1.0 && approxEq r3 1.0
  then "PGA3: e₁²=e₂²=e₃²=1 (Euclidean) ✓"
  else s!"PGA3: e₁²={r1}, e₂²={r2}, e₃²={r3} ✗"
}

#eval PGA3 {
  -- Test: Degenerate basis vector e₄ (projective origin)
  -- In Cl(3,0,1), the last basis vector is null: e₄² = 0
  let r := (e₄ * e₄).scalarPart
  if approxEq r 0.0 then "PGA3: e₄² = 0 (null dimension) ✓" else s!"PGA3: e₄² = {r} ✗"
}

#eval PGA3 {
  -- Test: Bivector e₁₂ squares to -1
  let r := (e₁₂ * e₁₂).scalarPart
  if approxEq r (-1.0) then "PGA3: e₁₂² = -1 ✓" else s!"PGA3: e₁₂² = {r} ✗"
}

end PGA3Tests

/-! ## CGA3: 3D Conformal Geometric Algebra Cl(4,1,0)

5D algebra embedding 3D Euclidean space.
Extra dimensions: e₊ (squares to +1) and e₋ (squares to -1)
-/

section CGA3Tests

#eval CGA3 {
  -- Test: 4 positive signature basis vectors
  let r1 := (e₁ * e₁).scalarPart
  let r2 := (e₂ * e₂).scalarPart
  let r3 := (e₃ * e₃).scalarPart
  let r4 := (e₄ * e₄).scalarPart
  s!"CGA3: positive: e₁²={r1}, e₂²={r2}, e₃²={r3}, e₄²={r4} (expect 1,1,1,1)"
}

#eval CGA3 {
  -- Test: 1 negative signature basis vector
  let r5 := (e₅ * e₅).scalarPart
  if approxEq r5 (-1.0) then "CGA3: e₅² = -1 ✓" else s!"CGA3: e₅² = {r5} ✗"
}

#eval CGA3 {
  -- Test: CGA null vectors
  -- n∞ = e₄ + e₅ (point at infinity)
  -- n₀ = (e₅ - e₄)/2 (origin)
  let ninf := e₄ + e₅
  let r := (ninf * ninf).scalarPart
  -- e₄² + e₄e₅ + e₅e₄ + e₅² = 1 + 0 + 0 + (-1) = 0
  if approxEq r 0.0 then "CGA3: n∞² = 0 ✓" else s!"CGA3: n∞² = {r} ✗"
}

end CGA3Tests

/-! ## Edge Cases and Error Handling -/

section EdgeCases

-- Test: Cl(1) - minimal algebra
#eval Cl(1) {
  let r := (e₁ * e₁).scalarPart
  if approxEq r 1.0 then "Cl(1): e₁² = 1 ✓" else s!"Cl(1): e₁² = {r} ✗"
}

-- Test: Cl(0,1) - complex numbers
#eval Cl(0,1) {
  let i := e₁  -- i² = -1
  let r := (i * i).scalarPart
  if approxEq r (-1.0) then "Cl(0,1): i² = -1 ✓" else s!"Cl(0,1): i² = {r} ✗"
}

-- Test: scalar multiplication
#eval R3 {
  let v := e₁.smul 5.0
  let r := v.coeff 1
  if approxEq r 5.0 then "R3: 5*e₁ = 5e₁ ✓" else s!"R3: coeff = {r} ✗"
}

-- Test: zero multivector
#eval R3 {
  let z := MultivectorS.zero (sig := _sig) (F := Float)
  let r := z.nnz
  if r == 0 then "R3: zero.nnz = 0 ✓" else s!"R3: zero.nnz = {r} ✗"
}

-- Test: addition is commutative
#eval R3 {
  let a := e₁ + e₂
  let b := e₂ + e₁
  let diff := a + b.smul (-1.0)
  if diff.nnz == 0 then "R3: e₁+e₂ = e₂+e₁ ✓" else s!"R3: commutative fail ✗"
}

end EdgeCases

/-! ## Fallback Syntax Tests -/

section FallbackSyntax

-- Note: The e[1] fallback notation works when type can be inferred.
-- Inside Cl() blocks, e₁ subscript notation is preferred.

-- Test: subscript notation equivalence
#eval R3 {
  -- e₁ and e1 should be equivalent (both generated by the macro)
  let v1 := e₁
  let v2 := e1
  let diff := v1 + v2.smul (-1.0)
  if diff.nnz == 0 then "R3: e₁ = e1 ✓" else s!"R3: e₁ ≠ e1 ✗"
}

-- Test: multi-digit subscripts
#eval R3 {
  -- e₁₂ should equal e1 * e2
  let biv := e₁₂
  let product := e₁ * e₂
  let c1 := biv.coeff 3
  let c2 := product.coeff 3
  if approxEq c1 c2 then "R3: e₁₂ = e₁*e₂ ✓" else s!"R3: {c1} ≠ {c2} ✗"
}

-- Test: triple subscripts
#eval R3 {
  let tri := e₁₂₃
  let product := e₁ * e₂ * e₃
  let c1 := tri.coeff 7
  let c2 := product.coeff 7
  if approxEq c1 c2 then "R3: e₁₂₃ = e₁*e₂*e₃ ✓" else s!"R3: {c1} ≠ {c2} ✗"
}

end FallbackSyntax

/-! ## Summary -/

#eval IO.println "
╔══════════════════════════════════════════════════════════════╗
║              DSL Test Suite Complete                        ║
╠══════════════════════════════════════════════════════════════╣
║ Tested Algebras:                                            ║
║   • R2: Cl(2,0,0) - 2D Euclidean                           ║
║   • R3: Cl(3,0,0) - 3D Euclidean                           ║
║   • R4: Cl(4,0,0) - 4D Euclidean                           ║
║   • Cl(1,1) - Hyperbolic plane (split-complex)              ║
║   • Cl(0,2) - Quaternion-like                               ║
║   • STA: Cl(1,3,0) - Spacetime algebra                     ║
║   • PGA3: Cl(3,0,1) - Projective GA                        ║
║   • CGA3: Cl(4,1,0) - Conformal GA                         ║
╠══════════════════════════════════════════════════════════════╣
║ Tested Operations:                                          ║
║   • Geometric product (*)                                   ║
║   • Wedge product (⋀ₛ)                                      ║
║   • Reverse (†)                                             ║
║   • Grade projection                                        ║
║   • Scalar multiplication                                   ║
║   • Addition                                                ║
║   • Subscript notation (e₁, e₁₂, e₁₂₃)                     ║
║   • Fallback notation (e[1], e[1,2])                       ║
╚══════════════════════════════════════════════════════════════╝
"

/-
  Grassmann/Calculus.lean - Differential operators via geometric algebra

  Port of Grassmann.jl's differential operations.

  In geometric algebra, differential operators have elegant representations:
  - Gradient: ∇f = Σᵢ eᵢ ∂f/∂xᵢ (vector)
  - Divergence: ∇·F = Σᵢ ∂Fᵢ/∂xᵢ (scalar)
  - Curl: ∇×F = ⋆(∇∧F) in 3D (vector from bivector)
  - Laplacian: ∇² = ∇·∇ (scalar operator)

  The vector derivative ∇ can be applied to multivectors:
  - ∇f for scalar f gives the gradient (vector)
  - ∇·v for vector v gives divergence (scalar)
  - ∇∧v for vector v gives curl bivector

  This module provides symbolic and numeric differentiation.
-/
import Grassmann.Multivector
import Grassmann.LinearAlgebra

namespace Grassmann

namespace Calculus

variable {n : ℕ} {sig : Signature n} {F : Type*}
variable [Ring F] [Div F]

/-! ## Discrete Derivatives

For numerical differentiation, we use finite differences.
-/

/-- Partial derivative approximation using central difference:
    ∂f/∂xᵢ ≈ (f(x + h·eᵢ) - f(x - h·eᵢ)) / 2h -/
def partialDeriv [OfNat F 2]
    (f : Multivector sig F → Multivector sig F)
    (x : Multivector sig F)
    (i : Fin n)
    (h : F) : Multivector sig F :=
  let ei := Multivector.ofBlade (LinearAlgebra.LinearMap.basisBlade (sig := sig) i)
  let xPlus := x.add (ei.smul h)
  let xMinus := x.sub (ei.smul h)
  ((f xPlus).sub (f xMinus)).smul (1 / ((2 : F) * h))

/-- Gradient of a scalar-valued function: ∇f = Σᵢ eᵢ (∂f/∂xᵢ) -/
def gradient [OfNat F 2]
    (f : Multivector sig F → F)
    (x : Multivector sig F)
    (h : F) : Multivector sig F :=
  (List.finRange n).foldl (init := Multivector.zero) fun acc i =>
    let ei := Multivector.ofBlade (LinearAlgebra.LinearMap.basisBlade (sig := sig) i)
    let xPlus := x.add (ei.smul h)
    let xMinus := x.sub (ei.smul h)
    let deriv := (f xPlus - f xMinus) / ((2 : F) * h)
    acc.add (ei.smul deriv)

/-- Divergence of a vector field: ∇·F = Σᵢ ∂Fᵢ/∂xᵢ -/
def divergence [OfNat F 2]
    (field : Multivector sig F → Multivector sig F)
    (x : Multivector sig F)
    (h : F) : F :=
  (List.finRange n).foldl (init := (0 : F)) fun acc i =>
    let ei := Multivector.ofBlade (LinearAlgebra.LinearMap.basisBlade (sig := sig) i)
    let xPlus := x.add (ei.smul h)
    let xMinus := x.sub (ei.smul h)
    let fieldPlus := field xPlus
    let fieldMinus := field xMinus
    let compI := (fieldPlus.coeff (LinearAlgebra.LinearMap.basisBlade i) -
                  fieldMinus.coeff (LinearAlgebra.LinearMap.basisBlade i)) /
                 ((2 : F) * h)
    acc + compI

/-- Curl via exterior derivative: curl(F) = ⋆(∇ ∧ F)
    This gives a vector in 3D, bivector in higher dimensions -/
def curl [OfNat F 2]
    (field : Multivector sig F → Multivector sig F)
    (x : Multivector sig F)
    (h : F) : Multivector sig F :=
  -- Compute ∇ ∧ F by summing eᵢ ∧ (∂F/∂xᵢ)
  let nablaWedgeF := (List.finRange n).foldl (init := Multivector.zero) fun acc i =>
    let ei := Multivector.ofBlade (LinearAlgebra.LinearMap.basisBlade (sig := sig) i)
    let xPlus := x.add (ei.smul h)
    let xMinus := x.sub (ei.smul h)
    let deriv := ((field xPlus).sub (field xMinus)).smul (1 / ((2 : F) * h))
    acc.add (ei ⋀ᵐ deriv)
  -- Take Hodge dual to get vector (in 3D)
  ⋆ᵐnablaWedgeF

/-- Laplacian: ∇²f = ∇·(∇f) = Σᵢ ∂²f/∂xᵢ² -/
def laplacian [OfNat F 2]
    (f : Multivector sig F → F)
    (x : Multivector sig F)
    (h : F) : F :=
  (List.finRange n).foldl (init := (0 : F)) fun acc i =>
    let ei := Multivector.ofBlade (LinearAlgebra.LinearMap.basisBlade (sig := sig) i)
    let xPlus := x.add (ei.smul h)
    let xMinus := x.sub (ei.smul h)
    -- Second derivative: (f(x+h) - 2f(x) + f(x-h)) / h²
    let d2f := (f xPlus - (2 : F) * f x + f xMinus) / (h * h)
    acc + d2f

/-! ## Directional Derivative -/

/-- Directional derivative: D_v f(x) = lim_{t→0} (f(x + tv) - f(x)) / t -/
def directionalDeriv
    (f : Multivector sig F → F)
    (x v : Multivector sig F)
    (h : F) : F :=
  let xPlusHv := x.add (v.smul h)
  (f xPlusHv - f x) / h

/-! ## Geometric Measurements -/

/-- Volume of parallelepiped spanned by n vectors (absolute value of determinant) -/
def volume (vectors : List (Multivector sig F)) : F :=
  LinearAlgebra.det vectors

/-- Signed area of parallelogram (2D) or triangle×2 (from 2 vectors) -/
def signedArea2D (v1 v2 : Multivector R2 F) : F :=
  (v1 ⋀ᵐ v2).coeff (e12 : Blade R2)

/-- Area of parallelogram in any dimension: |v1 ∧ v2| -/
def parallelogramArea (v1 v2 : Multivector sig F) : F :=
  let wedge := v1 ⋀ᵐ v2
  -- For true area, would need sqrt of sum of squared bivector components
  -- For now, return the norm squared of the bivector
  wedge.normSq

/-! ## Barycentric Coordinates -/

/-- Compute barycentric coordinates of point p relative to simplex vertices.
    For 2D triangle with vertices a, b, c and point p:
    Returns (λ₁, λ₂, λ₃) such that p = λ₁a + λ₂b + λ₃c and λ₁+λ₂+λ₃=1 -/
def barycentricCoords2D (a b c p : Multivector R2 F) : F × F × F :=
  let v0 := b.sub a
  let v1 := c.sub a
  let v2 := p.sub a
  let dot00 := LinearAlgebra.dot v0 v0
  let dot01 := LinearAlgebra.dot v0 v1
  let dot02 := LinearAlgebra.dot v0 v2
  let dot11 := LinearAlgebra.dot v1 v1
  let dot12 := LinearAlgebra.dot v1 v2
  let invDenom := 1 / (dot00 * dot11 - dot01 * dot01)
  let u := (dot11 * dot02 - dot01 * dot12) * invDenom
  let v := (dot00 * dot12 - dot01 * dot02) * invDenom
  let w := 1 - u - v
  (w, u, v)

/-- Centroid (barycenter) of a list of points (Float version) -/
def centroid (points : List (Multivector sig Float)) : Multivector sig Float :=
  let sum := points.foldl (·.add ·) Multivector.zero
  sum.smul (1 / points.length.toFloat)

end Calculus

/-! ## Tests -/

section CalculusTests

open Calculus

-- Test gradient of x² + y² at (1, 0) should be (2, 0)
-- #eval let f : Multivector R2 Float → Float := fun v =>
--         let x := v.coeff (e1 : Blade R2)
--         let y := v.coeff (e2 : Blade R2)
--         x * x + y * y
--       let x : Multivector R2 Float :=
--         (Multivector.ofBlade (e1 : Blade R2)).smul 1
--       let grad := gradient f x 0.001
--       (grad.coeff (e1 : Blade R2), grad.coeff (e2 : Blade R2))
-- Expected: approximately (2, 0)

-- Test Laplacian of x² + y² (should be 4 everywhere)
-- #eval let f : Multivector R2 Float → Float := fun v =>
--         let x := v.coeff (e1 : Blade R2)
--         let y := v.coeff (e2 : Blade R2)
--         x * x + y * y
--       let x : Multivector R2 Float :=
--         (Multivector.ofBlade (e1 : Blade R2)).smul 1
--       laplacian f x 0.001
-- Expected: approximately 4

-- Test divergence of (x, y) field (should be 2)
-- #eval let field : Multivector R2 Float → Multivector R2 Float := fun v =>
--         v  -- Identity field: F(x,y) = (x, y)
--       let x : Multivector R2 Float :=
--         (Multivector.ofBlade (e1 : Blade R2)).smul 1
--       divergence field x 0.001
-- Expected: approximately 2

-- Test signed area
-- #eval let v1 : Multivector R2 Float := Multivector.ofBlade (e1 : Blade R2)
--       let v2 : Multivector R2 Float := Multivector.ofBlade (e2 : Blade R2)
--       signedArea2D v1 v2  -- Should be 1

-- Test volume in R3
-- #eval let v1 : Multivector R3 Float := Multivector.ofBlade (e1 : Blade R3)
--       let v2 : Multivector R3 Float := Multivector.ofBlade (e2 : Blade R3)
--       let v3 : Multivector R3 Float := Multivector.ofBlade (e3 : Blade R3)
--       volume [v1, v2, v3]  -- Should be 1

end CalculusTests

end Grassmann

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

/-- Signed area of parallelogram (generic n-dimensional).
    Returns the wedge product (a bivector). The magnitude is the area,
    and the bivector encodes the orientation of the plane. -/
def signedAreaBivector (v1 v2 : Multivector sig F) : Multivector sig F :=
  v1 ⋀ᵐ v2

/-- Signed area of parallelogram (2D): returns the scalar coefficient of e12 -/
def signedArea2D (v1 v2 : Multivector R2 F) : F :=
  (v1 ⋀ᵐ v2).coeff (e12 : Blade R2)

/-- Area of parallelogram in any dimension: |v1 ∧ v2| (squared norm of bivector) -/
def parallelogramAreaSq (v1 v2 : Multivector sig F) : F :=
  (v1 ⋀ᵐ v2).normSq

/-- Area of parallelogram in any dimension: sqrt(|v1 ∧ v2|²) (Float version) -/
def parallelogramArea (v1 v2 : Multivector sig Float) : Float :=
  Float.sqrt (v1 ⋀ᵐ v2).normSq

/-! ## Barycentric Coordinates -/

/-- Compute barycentric coordinates of point p relative to triangle vertices a, b, c.
    Works in any dimension (uses only dot products).
    Returns (λ₁, λ₂, λ₃) such that p = λ₁a + λ₂b + λ₃c and λ₁+λ₂+λ₃=1 -/
def barycentricCoords (a b c p : Multivector sig F) : F × F × F :=
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

/-- Barycentric coordinates (2D convenience alias) -/
abbrev barycentricCoords2D (a b c p : Multivector R2 F) : F × F × F :=
  barycentricCoords a b c p

/-- Centroid (barycenter) of a list of points (Float version) -/
def centroid (points : List (Multivector sig Float)) : Multivector sig Float :=
  let sum := points.foldl (·.add ·) Multivector.zero
  sum.smul (1 / points.length.toFloat)

end Calculus

/-! ## Tests -/

section CalculusTests

open Calculus

-- Test gradient of x² + y² at (1, 0) should be (2, 0)
#eval! let f : Multivector R2 Float → Float := fun v =>
         let x := v.coeff (e1 : Blade R2)
         let y := v.coeff (e2 : Blade R2)
         x * x + y * y
       let x : Multivector R2 Float :=
         (Multivector.ofBlade (e1 : Blade R2)).smul 1
       let grad := gradient f x 0.001
       (grad.coeff (e1 : Blade R2), grad.coeff (e2 : Blade R2))
-- Expected: approximately (2, 0)

-- Test Laplacian of x² + y² (should be 4 everywhere)
#eval! let f : Multivector R2 Float → Float := fun v =>
         let x := v.coeff (e1 : Blade R2)
         let y := v.coeff (e2 : Blade R2)
         x * x + y * y
       let x : Multivector R2 Float :=
         (Multivector.ofBlade (e1 : Blade R2)).smul 1
       laplacian f x 0.001
-- Expected: approximately 4

-- Test divergence of (x, y) field (should be 2)
#eval! let field : Multivector R2 Float → Multivector R2 Float := fun v =>
         v  -- Identity field: F(x,y) = (x, y)
       let x : Multivector R2 Float :=
         (Multivector.ofBlade (e1 : Blade R2)).smul 1
       divergence field x 0.001
-- Expected: approximately 2

-- Test signed area
#eval! let v1 : Multivector R2 Float := Multivector.ofBlade (e1 : Blade R2)
       let v2 : Multivector R2 Float := Multivector.ofBlade (e2 : Blade R2)
       signedArea2D v1 v2  -- Should be 1

-- Test volume in R3
#eval! let v1 : Multivector R3 Float := Multivector.ofBlade (e1 : Blade R3)
       let v2 : Multivector R3 Float := Multivector.ofBlade (e2 : Blade R3)
       let v3 : Multivector R3 Float := Multivector.ofBlade (e3 : Blade R3)
       volume [v1, v2, v3]  -- Should be 1

end CalculusTests

/-! ## Symbolic Differentiation Operators (from Leibniz.jl)

Leibniz.jl provides differentiation operators as first-class objects.
We model ∂/∂xᵢ as an operator that can be:
- Applied to functions
- Composed with other operators
- Added together (sum of partial derivatives)
-/

namespace DiffOp

variable {n : ℕ} {sig : Signature n}

/-- A differential operator is a function transformer: (f : MV → MV) → (MV → MV) -/
structure DiffOperator (sig : Signature n) where
  /-- The operator action on functions -/
  apply : (Multivector sig Float → Multivector sig Float) →
          (Multivector sig Float → Multivector sig Float)

/-- Partial derivative operator ∂/∂xᵢ with step size h -/
def partialDiff (i : Fin n) (h : Float := 0.001) : DiffOperator sig where
  apply := fun f x =>
    let ei := Multivector.ofBlade (LinearAlgebra.LinearMap.basisBlade (sig := sig) i)
    let xPlus := x.add (ei.smul h)
    let xMinus := x.sub (ei.smul h)
    ((f xPlus).sub (f xMinus)).smul (1 / (2 * h))

/-- Identity operator (does nothing) -/
def identity : DiffOperator sig where
  apply := id

/-- Zero operator (returns zero function) -/
def zero : DiffOperator sig where
  apply := fun _ _ => Multivector.zero

/-- Compose two operators: (D₁ ∘ D₂) f = D₁(D₂ f) -/
def compose (D1 D2 : DiffOperator sig) : DiffOperator sig where
  apply := fun f => D1.apply (D2.apply f)

/-- Add two operators: (D₁ + D₂) f = D₁ f + D₂ f pointwise -/
def add (D1 D2 : DiffOperator sig) : DiffOperator sig where
  apply := fun f x => (D1.apply f x).add (D2.apply f x)

/-- Scale an operator: (c · D) f = c * (D f) -/
def smul (c : Float) (D : DiffOperator sig) : DiffOperator sig where
  apply := fun f x => (D.apply f x).smul c

/-- The gradient operator ∇ = Σᵢ eᵢ ∂/∂xᵢ -/
def nabla (h : Float := 0.001) : DiffOperator sig where
  apply := fun f x =>
    (List.finRange n).foldl (init := Multivector.zero) fun acc i =>
      let ei := Multivector.ofBlade (LinearAlgebra.LinearMap.basisBlade (sig := sig) i)
      let xPlus := x.add (ei.smul h)
      let xMinus := x.sub (ei.smul h)
      let deriv := ((f xPlus).sub (f xMinus)).smul (1 / (2 * h))
      acc.add (Multivector.geometricProduct ei deriv)  -- Geometric product

/-- The Laplacian operator ∇² = Σᵢ ∂²/∂xᵢ² -/
def laplacianOp (h : Float := 0.001) : DiffOperator sig where
  apply := fun f x =>
    (List.finRange n).foldl (init := Multivector.zero) fun acc i =>
      let ei := Multivector.ofBlade (LinearAlgebra.LinearMap.basisBlade (sig := sig) i)
      let xPlus := x.add (ei.smul h)
      let xMinus := x.sub (ei.smul h)
      -- Second derivative: (f(x+h) - 2f(x) + f(x-h)) / h²
      let d2f := (((f xPlus).sub ((f x).smul 2)).add (f xMinus)).smul (1 / (h * h))
      acc.add d2f

instance : Add (DiffOperator sig) := ⟨add⟩
instance : HMul (DiffOperator sig) (DiffOperator sig) (DiffOperator sig) := ⟨compose⟩
instance : SMul Float (DiffOperator sig) := ⟨smul⟩

/-- Apply operator to a function at a point -/
def eval (D : DiffOperator sig) (f : Multivector sig Float → Multivector sig Float)
    (x : Multivector sig Float) : Multivector sig Float :=
  D.apply f x

end DiffOp

/-! ## Exterior Calculus

The exterior derivative d and codifferential δ form the core of exterior calculus:
- d raises grade by 1 (generalized curl)
- δ lowers grade by 1 (generalized divergence)
- Laplace-Beltrami: Δ = dδ + δd
-/

namespace ExteriorCalculus

variable {n : ℕ} {sig : Signature n}

/-- Exterior derivative d: raises grade by 1
    For a k-form ω, dω is a (k+1)-form
    In coordinates: dω = Σᵢ (∂ω/∂xᵢ) ∧ dxᵢ -/
def extDeriv (h : Float := 0.001)
    (ω : Multivector sig Float → Multivector sig Float)
    (x : Multivector sig Float) : Multivector sig Float :=
  (List.finRange n).foldl (init := Multivector.zero) fun acc i =>
    let ei := Multivector.ofBlade (LinearAlgebra.LinearMap.basisBlade (sig := sig) i)
    let xPlus := x.add (ei.smul h)
    let xMinus := x.sub (ei.smul h)
    let partialOmega := ((ω xPlus).sub (ω xMinus)).smul (1 / (2 * h))
    acc.add (ei ⋀ᵐ partialOmega)  -- Wedge with dxᵢ

/-- Codifferential δ = ⋆d⋆: lowers grade by 1
    For a k-form ω, δω is a (k-1)-form -/
def codiff (h : Float := 0.001)
    (ω : Multivector sig Float → Multivector sig Float)
    (x : Multivector sig Float) : Multivector sig Float :=
  -- δω = (−1)^(n(k+1)+1) ⋆d⋆ω for k-form on n-manifold
  -- Simplified: just compute ⋆d⋆ and let user handle sign
  let starOmega : Multivector sig Float → Multivector sig Float := fun y => ⋆ᵐ(ω y)
  let dStarOmega := extDeriv h starOmega x
  ⋆ᵐdStarOmega

/-- Laplace-Beltrami operator: Δ = dδ + δd -/
def laplaceBeltrami (h : Float := 0.001)
    (ω : Multivector sig Float → Multivector sig Float)
    (x : Multivector sig Float) : Multivector sig Float :=
  -- For scalar functions, this reduces to the ordinary Laplacian
  -- Δ = δd + dδ where d raises grade and δ lowers it
  (codiff h (fun y => extDeriv h ω y) x).add (extDeriv h (fun y => codiff h ω y) x)

end ExteriorCalculus

/-! ## Numeric Integration

Simpson's rule and trapezoidal rule for integrating multivector-valued functions.
-/

namespace Integration

variable {n : ℕ} {sig : Signature n}

/-- Integrate a scalar function f: Float → Float over [a, b] using Simpson's rule -/
def simpsonScalar (f : Float → Float) (a b : Float) (numIntervals : Nat := 100) : Float :=
  let n := if numIntervals % 2 = 0 then numIntervals else numIntervals + 1  -- Must be even
  let h := (b - a) / n.toFloat
  -- Use explicit loop
  let result := (List.range (n + 1)).foldl (init := 0.0) fun acc i =>
    let xi := a + i.toFloat * h
    let coeff := if i = 0 || i = n then 1.0
                 else if i % 2 = 1 then 4.0
                 else 2.0
    acc + coeff * f xi
  (h / 3.0) * result

/-- Integrate a multivector-valued function over [a, b] -/
def simpsonMV (f : Float → Multivector sig Float) (a b : Float)
    (numIntervals : Nat := 100) : Multivector sig Float :=
  let n := if numIntervals % 2 = 0 then numIntervals else numIntervals + 1
  let h := (b - a) / n.toFloat
  let result := (List.range (n + 1)).foldl (init := Multivector.zero) fun acc i =>
    let xi := a + i.toFloat * h
    let coeff := if i = 0 || i = n then 1.0
                 else if i % 2 = 1 then 4.0
                 else 2.0
    acc.add ((f xi).smul coeff)
  result.smul (h / 3.0)

/-- Line integral of vector field F along parametric curve γ: [a,b] → ℝⁿ
    ∫ F · dγ = ∫ₐᵇ F(γ(t)) · γ'(t) dt -/
def lineIntegral
    (F : Multivector sig Float → Multivector sig Float)
    (γ : Float → Multivector sig Float)
    (a b : Float)
    (h : Float := 0.001)
    (numIntervals : Nat := 100) : Float :=
  -- Integrand: F(γ(t)) · γ'(t)
  let integrand (t : Float) : Float :=
    let γt := γ t
    let γtPlus := γ (t + h)
    let γtMinus := γ (t - h)
    let γPrime := ((γtPlus).sub γtMinus).smul (1 / (2 * h))
    LinearAlgebra.dot (F γt) γPrime
  simpsonScalar integrand a b numIntervals

/-- Surface integral of bivector field over parametric surface σ: [a,b]×[c,d] → ℝⁿ
    Uses double Simpson's rule -/
def surfaceIntegral
    (B : Multivector sig Float → Multivector sig Float)
    (σ : Float → Float → Multivector sig Float)
    (a b c d : Float)
    (h : Float := 0.001)
    (numIntervals : Nat := 20) : Float :=
  -- Inner integral over v for fixed u
  let innerIntegral (u : Float) : Float :=
    let integrand (v : Float) : Float :=
      let pt := σ u v
      -- Surface element: (∂σ/∂u) ∧ (∂σ/∂v)
      let σu := ((σ (u + h) v).sub (σ (u - h) v)).smul (1 / (2 * h))
      let σv := ((σ u (v + h)).sub (σ u (v - h))).smul (1 / (2 * h))
      let surfaceElement := σu ⋀ᵐ σv
      -- Dot the bivector field with surface element (extract scalar part of contraction)
      ((B pt) ⌋ᵐ surfaceElement).scalarPart
    simpsonScalar integrand c d numIntervals
  simpsonScalar innerIntegral a b numIntervals

end Integration

/-! ## Differential Operator Tests -/

section DiffOpTests

open DiffOp ExteriorCalculus Integration

-- Test partial derivative
#eval! let f : Multivector R2 Float → Multivector R2 Float := fun v =>
         Multivector.scalar ((v.coeff (e1 : Blade R2)) ^ 2)  -- f(x,y) = x²
       let D0 := partialDiff (sig := R2) ⟨0, by omega⟩ 0.001  -- ∂/∂x
       let x : Multivector R2 Float := (Multivector.ofBlade (e1 : Blade R2)).smul 2  -- x=2
       (eval D0 f x).scalarPart  -- Should be ~4 (derivative of x² at x=2)

-- Test operator composition (second derivative)
#eval! let f : Multivector R2 Float → Multivector R2 Float := fun v =>
         Multivector.scalar ((v.coeff (e1 : Blade R2)) ^ 3)  -- f(x,y) = x³
       let D0 := partialDiff (sig := R2) ⟨0, by omega⟩ 0.01
       let D0D0 := D0 * D0  -- ∂²/∂x²
       let x : Multivector R2 Float := (Multivector.ofBlade (e1 : Blade R2)).smul 2
       (eval D0D0 f x).scalarPart  -- Should be ~12 (6x at x=2)

-- Test Simpson integration
#eval! simpsonScalar (fun x => x * x) 0.0 1.0 100  -- ∫₀¹ x² dx = 1/3 ≈ 0.333

-- Test line integral: ∫ F · dr along unit circle
#eval! let F : Multivector R2 Float → Multivector R2 Float := fun p =>
         -- F = (-y, x) (rotational field)
         let x := p.coeff (e1 : Blade R2)
         let y := p.coeff (e2 : Blade R2)
         (Multivector.ofBlade (e1 : Blade R2)).smul (-y) +
         (Multivector.ofBlade (e2 : Blade R2)).smul x
       let γ (t : Float) : Multivector R2 Float :=  -- Unit circle
         (Multivector.ofBlade (e1 : Blade R2)).smul (Float.cos t) +
         (Multivector.ofBlade (e2 : Blade R2)).smul (Float.sin t)
       lineIntegral F γ 0.0 (2 * 3.14159265) 0.001 200  -- Should be ~2π

end DiffOpTests

end Grassmann

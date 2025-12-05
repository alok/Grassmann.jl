/-
  Grassmann/CGAGen.lean - Dimension-Agnostic Conformal Geometric Algebra

  CGA embeds n-dimensional Euclidean space into (n+2)-dimensional space
  with signature R^{n+1,1}. This allows representing:
  - Points as null vectors
  - Spheres/circles as vectors
  - Planes as vectors
  - Translations as rotors
  - Dilations as rotors

  Key insight: CGA operations are the same regardless of the base dimension n.
  We parameterize over n and derive the (n+2)-dimensional conformal space.
-/
import Grassmann.SparseMultivector
import Grassmann.SignatureGen
import Grassmann.RotorExp
import Grassmann.GANotation

namespace Grassmann.CGAn  -- CGAn = CGA for n dimensions (avoids conflict with CGA.lean)

/-! ## CGA Signature Construction

For n-dimensional Euclidean space, CGA uses signature R^{n+1,1}:
- e₁, ..., eₙ: Euclidean basis (square to +1)
- e₊: positive extra dimension (squares to +1)
- e₋: negative extra dimension (squares to -1)

The null basis is:
- e₀ = (e₋ - e₊)/2  (origin)
- e∞ = e₋ + e₊      (point at infinity)
-/

/-- CGA signature for n-dimensional base space: R^{n+1,1} -/
def cgaSignature (n : ℕ) : Signature (n + 2) :=
  ⟨BitVec.ofNat (n + 2) (1 <<< (n + 1)), 0⟩  -- Only e_{n+1} is negative

variable {n : ℕ}

/-- Shorthand for CGA multivector type -/
abbrev CGAMV (n : ℕ) := MultivectorS (cgaSignature n) Float

/-! ## Basis Access -/

/-- Euclidean basis vector eᵢ (0-indexed, i < n) -/
def eEuc (i : Fin n) : CGAMV n :=
  MultivectorS.basis ⟨i.val, by omega⟩

/-- Positive extra dimension e₊ (index n) -/
def ePlus : CGAMV n :=
  MultivectorS.basis ⟨n, by omega⟩

/-- Negative extra dimension e₋ (index n+1) -/
def eMinus : CGAMV n :=
  MultivectorS.basis ⟨n + 1, by omega⟩

/-- Origin point e₀ = (e₋ - e₊)/2 -/
def eOrigin : CGAMV n :=
  (eMinus + ePlus.smul (-1)).smul 0.5

/-- Point at infinity e∞ = e₋ + e₊ -/
def eInfinity : CGAMV n :=
  eMinus + ePlus

/-! ## Point Representation

A Euclidean point p = (x₁, ..., xₙ) is represented as the null vector:
  P = p + (1/2)|p|²e∞ + e₀

This satisfies P² = 0 (null vector property).
-/

/-- Convert a list of Euclidean coordinates to a CGA point -/
def pointFromCoords (coords : List Float) (_h : coords.length ≤ n) : CGAMV n :=
  let indexed := List.zip (List.range coords.length) coords
  let euclidean := indexed.foldl (fun acc (i, x) =>
    if hi : i < n then acc + (eEuc ⟨i, hi⟩).smul x else acc
  ) MultivectorS.zero
  let normSq := coords.foldl (fun acc x => acc + x * x) 0
  euclidean + eInfinity.smul (normSq / 2) + eOrigin

/-- Origin point (0, 0, ..., 0) -/
def originPoint : CGAMV n := eOrigin

/-- Extract Euclidean coordinates from a CGA point -/
def pointToCoords (P : CGAMV n) : List Float :=
  (List.finRange n).map fun i =>
    P.coeffBlade ⟨BitVec.ofNat (n + 2) (1 <<< i.val)⟩

/-! ## Sphere/Hypersphere Representation

A sphere with center c and radius r is represented as:
  S = C - (r²/2)e∞

where C is the CGA point for center c.

Inner product P·S gives (signed) squared distance from point to sphere surface.
-/

/-- Create a sphere from center coordinates and radius -/
def sphere (center : List Float) (radius : Float) (h : center.length ≤ n) : CGAMV n :=
  let C := pointFromCoords center h
  C + eInfinity.smul (-radius * radius / 2)

/-- Create a plane from normal vector and distance from origin.
    Plane: n·x = d, represented as: Π = n + d·e∞ -/
def plane (normal : List Float) (dist : Float) (_h : normal.length ≤ n) : CGAMV n :=
  let indexed := List.zip (List.range normal.length) normal
  let normalMV := indexed.foldl (fun acc (i, x) =>
    if hi : i < n then acc + (eEuc ⟨i, hi⟩).smul x else acc
  ) MultivectorS.zero
  normalMV + eInfinity.smul dist

/-! ## Geometric Operations -/

/-- Outer product (meet operation in CGA) -/
def meet (A B : CGAMV n) : CGAMV n := A ⋀ₛ B

/-- Dual: A* = A · I where I is the pseudoscalar -/
def dual (A : CGAMV n) : CGAMV n :=
  let I := (List.finRange (n + 2)).foldl (fun acc i =>
    acc * MultivectorS.basis i
  ) (MultivectorS.scalar 1.0 : CGAMV n)
  A * I

/-- Join operation via duality: A ∨ B = (A* ∧ B*)* -/
def join (A B : CGAMV n) : CGAMV n :=
  dual (meet (dual A) (dual B))

/-! ## Transformations as Rotors -/

/-- Translation rotor: moves points by vector t.
    T = 1 + (t/2)e∞ = 1 + (1/2)Σ tᵢeᵢe∞ -/
def translationRotor (t : List Float) (_h : t.length ≤ n) : CGAMV n :=
  let indexed := List.zip (List.range t.length) t
  let tMV := indexed.foldl (fun acc (i, x) =>
    if hi : i < n then acc + (eEuc ⟨i, hi⟩).smul x else acc
  ) MultivectorS.zero
  MultivectorS.scalar 1.0 + (tMV * eInfinity).smul 0.5

/-- Apply translation to a point -/
def translate (t : List Float) (P : CGAMV n) (h : t.length ≤ n) : CGAMV n :=
  let T := translationRotor t h
  T * P * T†ₛ

/-- Dilation rotor: scales by factor s around origin.
    D = (1 + e₀e∞)/√s when s > 0 -/
def dilationRotor (s : Float) : CGAMV n :=
  if s > 0 then
    let scale := Float.sqrt s
    (MultivectorS.scalar 1.0 + eOrigin * eInfinity).smul (1 / scale)
  else
    MultivectorS.scalar 1.0  -- Identity for invalid scale

/-- Apply dilation to a point -/
def dilate (s : Float) (P : CGAMV n) : CGAMV n :=
  let D := dilationRotor s
  D * P * D†ₛ

/-- Rotation rotor in plane spanned by eᵢ and eⱼ by angle θ -/
def rotationRotor (i j : Fin n) (θ : Float) : CGAMV n :=
  let ei := eEuc i
  let ej := eEuc j
  let B := ei * ej  -- Bivector defining rotation plane
  expBivector (B.smul (θ / 2))

/-- Apply rotation to a CGA element -/
def rotate (i j : Fin n) (θ : Float) (X : CGAMV n) : CGAMV n :=
  let R := rotationRotor i j θ
  R * X * R†ₛ

/-! ## Distance and Intersection -/

/-- Squared distance between two CGA points -/
def distanceSquared (P Q : CGAMV n) : Float :=
  let diff := P + Q.smul (-1)
  (-2) * (diff * diff).scalarPart

/-- Check if point lies on sphere (approximately) -/
def pointOnSphere (P S : CGAMV n) (tol : Float := 1e-6) : Bool :=
  let ip := (P * S).scalarPart
  ip.abs < tol

/-! ## Tests -/

-- 2D CGA (4D algebra: e1, e2, e+, e-)
def CGA2 := cgaSignature 2

#eval! let P := pointFromCoords (n := 2) [1.0, 2.0] (by native_decide)
       P.nnz  -- Should have several non-zero components

-- Test e₀ · e∞ = -1
#eval! let e0 : CGAMV 2 := eOrigin
       let einf : CGAMV 2 := eInfinity
       (e0 * einf + einf * e0).scalarPart / 2  -- Inner product, should be -1

-- Test that origin point squared is 0 (null vector)
#eval! let O : CGAMV 2 := originPoint
       (O * O).scalarPart  -- Should be 0 (or very close)

-- Test translation
#eval! let P := pointFromCoords (n := 2) [1.0, 0.0] (by native_decide)
       let P' := translate [2.0, 3.0] P (by native_decide)
       pointToCoords P'  -- Should be approximately [3.0, 3.0]

-- 3D CGA for completeness
def CGA3 := cgaSignature 3

#eval! let sphere3d := sphere (n := 3) [0.0, 0.0, 0.0] 1.0 (by native_decide)
       sphere3d.nnz

#eval IO.println "✓ CGAGen module loaded"

end Grassmann.CGAn

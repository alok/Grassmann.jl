/-
  Grassmann/VectorUtils.lean - Dimension-generic vector/geometric algebra utilities

  This module provides operations that work for any signature and dimension.
  For 3D-specific conveniences, see R3Utils.lean which builds on this.
-/
import Grassmann.Multivector
import Grassmann.LinearAlgebra
import Grassmann.Spinor

namespace Grassmann.VectorUtils

open Multivector LinearAlgebra

variable {n : ℕ} {sig : Signature n}

/-! ## Constants -/

/-- Pi constant -/
def pi : Float := 3.14159265358979323846

/-- Convert degrees to radians -/
def toRadians (d : Float) : Float := d * pi / 180

/-- Convert radians to degrees -/
def toDegrees (r : Float) : Float := r * 180 / pi

/-! ## Basic Vector Operations (generic) -/

/-- Magnitude (length) of a vector -/
def magnitude (v : Multivector sig Float) : Float := v.norm

/-- Squared magnitude of a vector -/
def magnitudeSq (v : Multivector sig Float) : Float := v.normSq

/-- Normalize a vector to unit length -/
def normalizeVec (v : Multivector sig Float) : Multivector sig Float := v.normalize

/-- Distance between two points -/
def distance (a b : Multivector sig Float) : Float := (a.sub b).norm

/-- Dot product of two vectors -/
def dotProduct (a b : Multivector sig Float) : Float := dot a b

/-! ## Projection Operations (generic) -/

/-- Project vector a onto vector b -/
def projectOnto (a b : Multivector sig Float) : Multivector sig Float :=
  let bb := dot b b
  if bb == 0 then Multivector.zero
  else b.smul (dot a b / bb)

/-- Reject vector a from vector b (perpendicular component) -/
def rejectFrom (a b : Multivector sig Float) : Multivector sig Float :=
  a.sub (projectOnto a b)

/-- Project vector onto a hyperplane defined by its normal -/
def projectOntoHyperplane (v normal : Multivector sig Float) : Multivector sig Float :=
  v.sub (projectOnto v normal)

/-! ## Angle Operations (generic) -/

/-- Angle between two vectors (radians) -/
def angleBetween (a b : Multivector sig Float) : Float :=
  LinearAlgebra.angle a b

/-! ## Geometric Constructions (generic) -/

/-- Midpoint of two vectors -/
def midpoint (a b : Multivector sig Float) : Multivector sig Float :=
  (a.add b).smul 0.5

/-- Linear interpolation between two vectors -/
def lerp (a b : Multivector sig Float) (t : Float) : Multivector sig Float :=
  (a.smul (1 - t)).add (b.smul t)

/-! ## Reflection Operations (generic) -/

/-- Reflect a vector through a hyperplane with given normal -/
def reflectThroughHyperplane (v normal : Multivector sig Float) : Multivector sig Float :=
  v.sub ((projectOnto v normal).smul 2)

/-- Reflect a vector through the origin -/
def reflectThroughOrigin (v : Multivector sig Float) : Multivector sig Float :=
  v.neg

/-! ## Spherical Linear Interpolation (generic) -/

/-- Spherical linear interpolation (for directions/rotations) -/
def slerp (a b : Multivector sig Float) (t : Float) : Multivector sig Float :=
  let aN := a.normalize
  let bN := b.normalize
  let d := dot aN bN
  if d > 0.9999 then
    (lerp aN bN t).normalize
  else
    let theta := Float.acos (if d < -1 then -1 else if d > 1 then 1 else d)
    let sinTheta := Float.sin theta
    let wa := Float.sin ((1 - t) * theta) / sinTheta
    let wb := Float.sin (t * theta) / sinTheta
    (aN.smul wa).add (bN.smul wb)

/-! ## Geometric Queries (generic) -/

/-- Check if two vectors are perpendicular -/
def isPerpendicular (a b : Multivector sig Float) (eps : Float := 1e-10) : Bool :=
  Float.abs (dot a b) < eps * a.norm * b.norm

/-- Check if three points are collinear (via linear dependence) -/
def areCollinear (a b c : Multivector sig Float) (eps : Float := 1e-10) : Bool :=
  -- Points are collinear if (b-a) ∧ (c-a) = 0
  let v1 := b.sub a
  let v2 := c.sub a
  (v1 ⋀ᵐ v2).normSq < eps * eps

/-! ## Rotor Operations (generic) -/

/-- Create a rotor for rotation in a bivector plane by an angle (radians).
    The bivector should be normalized (B² = -1 for Euclidean signature). -/
def rotorInPlane (bivector : Multivector sig Float) (angle : Float) : Spinor sig Float :=
  Spinor.fromAxisAngle bivector angle

/-- Rotate a vector using a rotor -/
def rotateWithRotor (R : Spinor sig Float) (v : Multivector sig Float) : Multivector sig Float :=
  R.rotate v

/-- Compose two rotations -/
def composeRotations (R1 R2 : Spinor sig Float) : Spinor sig Float :=
  R1.mul R2

/-! ## Basis Vector Utilities -/

/-- Get the i-th basis vector as a multivector -/
def basisVector (i : Fin n) : Multivector sig Float :=
  Multivector.ofBlade (Blade.basis i : Blade sig)

/-- Create a bivector from two basis indices (e_i ∧ e_j).
    Returns zero if i = j. -/
def basisBivector (i j : Fin n) : Multivector sig Float :=
  let ei := basisVector (sig := sig) i
  let ej := basisVector (sig := sig) j
  ei ⋀ᵐ ej

/-- Create a rotor for rotation in the plane spanned by basis vectors i and j.
    Assumes i ≠ j (otherwise the bivector is zero and this gives identity). -/
def rotorInBasisPlane (i j : Fin n) (angle : Float) : Spinor sig Float :=
  let B := basisBivector (sig := sig) i j
  -- Normalize the bivector (it should have norm 1 for orthonormal bases)
  let Bnorm := B.normalize
  Spinor.fromAxisAngle Bnorm angle

/-! ## Vector Construction from Components -/

/-- Create a vector from an array of components.
    Components correspond to basis vectors e_0, e_1, ..., e_{n-1} -/
def vectorFromArray (components : Array Float) : Multivector sig Float :=
  (List.finRange n).foldl (init := Multivector.zero) fun acc i =>
    let c := components.getD i.val 0.0
    acc.add ((basisVector i).smul c)

/-- Create a vector from a function giving each component -/
def vectorFromFn (f : Fin n → Float) : Multivector sig Float :=
  (List.finRange n).foldl (init := Multivector.zero) fun acc i =>
    acc.add ((basisVector i).smul (f i))

/-- Extract components of a vector as an array -/
def vectorComponents (v : Multivector sig Float) : Array Float :=
  Array.ofFn fun i => v.coeff (Blade.basis i : Blade sig)

/-! ## Cross Product Generalization (n-dimensions)

In n dimensions, the "cross product" generalizes to the Hodge dual of the wedge product.
For two vectors a, b in n dimensions: a × b = ⋆(a ∧ b)
This gives an (n-2)-vector in general, which is a vector only in 3D.
-/

/-- Generalized cross product: Hodge dual of wedge product.
    In 3D, this gives the usual cross product.
    In other dimensions, this gives an (n-2)-blade. -/
def generalizedCross (a b : Multivector sig Float) : Multivector sig Float :=
  (a ⋀ᵐ b).hodgeDual

/-! ## Volume Operations -/

/-- Volume of the parallelepiped spanned by n vectors (determinant via wedge product).
    For k < n vectors, gives the k-dimensional volume of the parallelotope. -/
def parallelotopeVolume (vectors : List (Multivector sig Float)) : Float :=
  let wedged := vectors.foldl (init := Multivector.one) fun acc v => acc ⋀ᵐ v
  Float.abs wedged.normSq.sqrt

/-- Area of parallelogram spanned by two vectors (in any dimension) -/
def parallelogramArea (a b : Multivector sig Float) : Float :=
  (a ⋀ᵐ b).norm

/-! ## Tests -/

section Tests

-- Test in R4 (4D Euclidean)
def R4 : Signature 4 := Signature.euclidean 4

#eval! let e0 : Multivector R4 Float := basisVector ⟨0, by omega⟩
      let e1 : Multivector R4 Float := basisVector ⟨1, by omega⟩
      dotProduct e0 e1  -- Should be 0

#eval! let e0 : Multivector R4 Float := basisVector ⟨0, by omega⟩
      magnitude e0  -- Should be 1

-- Test rotor in 4D
#eval! let B : Multivector R4 Float := basisBivector ⟨0, by omega⟩ ⟨1, by omega⟩
      B.normSq  -- Should be -1 for unit bivector in Euclidean space

-- Test vectorFromFn
#eval! let v : Multivector R4 Float := vectorFromFn (fun i => i.val.toFloat + 1)
      vectorComponents v  -- Should be #[1, 2, 3, 4]

end Tests

end Grassmann.VectorUtils

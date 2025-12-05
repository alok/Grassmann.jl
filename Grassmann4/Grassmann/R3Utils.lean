/-
  Grassmann/R3Utils.lean - Convenient 3D vector/geometric algebra utilities

  This module provides easy-to-use functions for common 3D geometry operations.
  All operations use the R3 (Euclidean 3D) signature.

  For dimension-generic operations, see VectorUtils.lean.
-/
import Grassmann.Multivector
import Grassmann.LinearAlgebra
import Grassmann.Spinor
import Grassmann.VectorUtils

namespace Grassmann.R3Utils

open Multivector LinearAlgebra VectorUtils

/-! ## Vector Construction (3D-specific) -/

/-- Create a 3D vector from components -/
def vec (x y z : Float) : Multivector R3 Float :=
  vector3 x y z

/-- Create a 3D vector from a list [x, y, z] -/
def vecFromList (components : List Float) : Multivector R3 Float :=
  match components with
  | [x, y, z] => vector3 x y z
  | _ => Multivector.zero

/-- Extract x, y, z components from a vector -/
def components (v : Multivector R3 Float) : Float × Float × Float :=
  (v.coeff (e1 : Blade R3), v.coeff (e2 : Blade R3), v.coeff (e3 : Blade R3))

/-- Unit vectors -/
def i : Multivector R3 Float := basisVector ⟨0, by omega⟩
def j : Multivector R3 Float := basisVector ⟨1, by omega⟩
def k : Multivector R3 Float := basisVector ⟨2, by omega⟩

/-! ## Basic Operations (wrappers for generic versions) -/

/-- Dot product of two 3D vectors -/
def dot3 (a b : Multivector R3 Float) : Float := VectorUtils.dotProduct a b

/-- Cross product of two 3D vectors (returns a vector) -/
def cross3 (a b : Multivector R3 Float) : Multivector R3 Float := cross a b

/-- Magnitude (length) of a 3D vector -/
def magnitude (v : Multivector R3 Float) : Float := VectorUtils.magnitude v

/-- Squared magnitude of a 3D vector -/
def magnitudeSq (v : Multivector R3 Float) : Float := VectorUtils.magnitudeSq v

/-- Normalize a 3D vector to unit length -/
def normalize (v : Multivector R3 Float) : Multivector R3 Float := normalizeVec v

/-- Distance between two points -/
def distance (a b : Multivector R3 Float) : Float := VectorUtils.distance a b

/-! ## Rotation Operations -/

/-- Create a rotor for rotation around an axis by an angle (radians) -/
def rotorFromAxisAngle (axis : Multivector R3 Float) (angle : Float) : Spinor R3 Float :=
  -- Normalize axis and create bivector plane
  let n := axis.normalize
  let halfAngle := angle / 2
  -- For axis along (nx, ny, nz), the bivector plane is:
  -- B = nx*e23 + ny*e13 + nz*e12 (note: e31 = -e13)
  let (nx, ny, nz) := components n
  let B := (Multivector.ofBlade (e23 : Blade R3)).smul nx +
           (Multivector.ofBlade (e13 : Blade R3)).smul (-ny) +
           (Multivector.ofBlade (e12 : Blade R3)).smul nz
  Spinor.fromAxisAngle B angle

/-- Rotate a vector around an axis by an angle -/
def rotateAroundAxis (v : Multivector R3 Float) (axis : Multivector R3 Float)
    (angle : Float) : Multivector R3 Float :=
  let R := rotorFromAxisAngle axis angle
  R.rotate v

/-- Rotate a vector around the X-axis -/
def rotateX (v : Multivector R3 Float) (angle : Float) : Multivector R3 Float :=
  (rotorX angle).rotate v

/-- Rotate a vector around the Y-axis -/
def rotateY (v : Multivector R3 Float) (angle : Float) : Multivector R3 Float :=
  (rotorY angle).rotate v

/-- Rotate a vector around the Z-axis -/
def rotateZ (v : Multivector R3 Float) (angle : Float) : Multivector R3 Float :=
  (rotorZ angle).rotate v

/-! ## Projection Operations (using generic versions) -/

/-- Project vector a onto vector b -/
def projectOnto3 (a b : Multivector R3 Float) : Multivector R3 Float :=
  VectorUtils.projectOnto a b

/-- Reject vector a from vector b (perpendicular component) -/
def rejectFrom3 (a b : Multivector R3 Float) : Multivector R3 Float :=
  VectorUtils.rejectFrom a b

/-- Project vector onto a plane defined by its normal -/
def projectOntoPlane (v normal : Multivector R3 Float) : Multivector R3 Float :=
  VectorUtils.projectOntoHyperplane v normal

/-! ## Angle Operations -/

/-- Angle between two vectors (radians) -/
def angleBetween (a b : Multivector R3 Float) : Float :=
  VectorUtils.angleBetween a b

/-- Signed angle between two vectors around an axis (radians) -/
def signedAngle (v1 v2 axis : Multivector R3 Float) : Float :=
  let angle := angleBetween v1 v2
  let c := cross3 v1 v2
  if dot3 c axis < 0 then -angle else angle

/-! ## Geometric Constructions -/

/-- Midpoint of two vectors -/
def midpoint (a b : Multivector R3 Float) : Multivector R3 Float :=
  VectorUtils.midpoint a b

/-- Linear interpolation between two vectors -/
def lerp (a b : Multivector R3 Float) (t : Float) : Multivector R3 Float :=
  VectorUtils.lerp a b t

/-- Compute the normal of a triangle given three vertices -/
def triangleNormal (p1 p2 p3 : Multivector R3 Float) : Multivector R3 Float :=
  let edge1 := p2.sub p1
  let edge2 := p3.sub p1
  (cross3 edge1 edge2).normalize

/-- Area of a triangle given three vertices -/
def triangleArea (p1 p2 p3 : Multivector R3 Float) : Float :=
  let edge1 := p2.sub p1
  let edge2 := p3.sub p1
  (cross3 edge1 edge2).norm / 2

/-! ## Reflection Operations -/

/-- Reflect a vector through a plane with given normal -/
def reflectThroughPlane (v normal : Multivector R3 Float) : Multivector R3 Float :=
  VectorUtils.reflectThroughHyperplane v normal

/-- Reflect a vector through the origin -/
def reflectThroughOrigin (v : Multivector R3 Float) : Multivector R3 Float :=
  VectorUtils.reflectThroughOrigin v

/-! ## Angle/Degree Conversion (re-export from VectorUtils) -/

/-- Pi constant -/
def pi : Float := VectorUtils.pi

/-- Convert degrees to radians -/
def degrees (d : Float) : Float := VectorUtils.toRadians d

/-- Convert radians to degrees -/
def toDegrees (r : Float) : Float := VectorUtils.toDegrees r

/-! ## Plane-Based Rotations -/

/-- Named rotation planes -/
inductive Plane where
  | xy  -- Rotation around Z axis
  | yz  -- Rotation around X axis
  | xz  -- Rotation around Y axis
  deriving Repr, DecidableEq

/-- Rotate a vector by an angle in a named plane -/
def rotate (v : Multivector R3 Float) (angle : Float) (plane : Plane) : Multivector R3 Float :=
  match plane with
  | .xy => rotateZ v angle
  | .yz => rotateX v angle
  | .xz => rotateY v (-angle)  -- Note: xz rotation is opposite convention

/-! ## Spherical Linear Interpolation -/

/-- Spherical linear interpolation (for directions/rotations) -/
def slerp (a b : Multivector R3 Float) (t : Float) : Multivector R3 Float :=
  VectorUtils.slerp a b t

/-! ## Geometric Queries -/

/-- Check if two vectors are parallel (3D-specific via cross product) -/
def isParallel (a b : Multivector R3 Float) (eps : Float := 1e-10) : Bool :=
  let crossMag := (cross3 a b).norm
  crossMag < eps * a.norm * b.norm

/-- Check if two vectors are perpendicular -/
def isPerpendicular (a b : Multivector R3 Float) (eps : Float := 1e-10) : Bool :=
  VectorUtils.isPerpendicular a b eps

/-- Check if three points are collinear -/
def areCollinear (a b c : Multivector R3 Float) (eps : Float := 1e-10) : Bool :=
  VectorUtils.areCollinear a b c eps

/-- Check if four points are coplanar (3D-specific) -/
def areCoplanar (a b c d : Multivector R3 Float) (eps : Float := 1e-10) : Bool :=
  let v1 := b.sub a
  let v2 := c.sub a
  let v3 := d.sub a
  Float.abs (dot3 v3 (cross3 v1 v2)) < eps

/-! ## Coordinate Conversions -/

/-- Create vector from spherical coordinates (r, theta, phi)
    theta = angle from +z axis (0 to π)
    phi = angle from +x axis in xy plane (0 to 2π) -/
def fromSpherical (r theta phi : Float) : Multivector R3 Float :=
  let sinTheta := Float.sin theta
  vec (r * sinTheta * Float.cos phi)
      (r * sinTheta * Float.sin phi)
      (r * Float.cos theta)

/-- Create vector from cylindrical coordinates (r, phi, z) -/
def fromCylindrical (r phi z : Float) : Multivector R3 Float :=
  vec (r * Float.cos phi) (r * Float.sin phi) z

/-! ## Triple Products -/

/-- Scalar triple product: a · (b × c) = det([a b c]) -/
def scalarTriple (a b c : Multivector R3 Float) : Float :=
  dot3 a (cross3 b c)

/-- Vector triple product: a × (b × c) = b(a·c) - c(a·b) -/
def vectorTriple (a b c : Multivector R3 Float) : Multivector R3 Float :=
  (b.smul (dot3 a c)).sub (c.smul (dot3 a b))

/-- Volume of parallelepiped spanned by three vectors -/
def volume (a b c : Multivector R3 Float) : Float :=
  Float.abs (scalarTriple a b c)

/-- Area of parallelogram spanned by two vectors -/
def parallelogramArea (a b : Multivector R3 Float) : Float :=
  VectorUtils.parallelogramArea a b

/-! ## Tests with Integers -/

section IntTests

-- Cross product test: i × j = k (using Int for exact computation)
#eval let iv : Multivector R3 Int := Multivector.ofBlade (e1 : Blade R3)
      let jv : Multivector R3 Int := Multivector.ofBlade (e2 : Blade R3)
      let c := cross iv jv
      (c.coeff (e1 : Blade R3), c.coeff (e2 : Blade R3), c.coeff (e3 : Blade R3))
-- Expected: (0, 0, 1)

-- Cross product: j × k = i
#eval let jv : Multivector R3 Int := Multivector.ofBlade (e2 : Blade R3)
      let kv : Multivector R3 Int := Multivector.ofBlade (e3 : Blade R3)
      let c := cross jv kv
      (c.coeff (e1 : Blade R3), c.coeff (e2 : Blade R3), c.coeff (e3 : Blade R3))
-- Expected: (1, 0, 0)

-- Cross product: k × i = j
#eval let kv : Multivector R3 Int := Multivector.ofBlade (e3 : Blade R3)
      let iv : Multivector R3 Int := Multivector.ofBlade (e1 : Blade R3)
      let c := cross kv iv
      (c.coeff (e1 : Blade R3), c.coeff (e2 : Blade R3), c.coeff (e3 : Blade R3))
-- Expected: (0, 1, 0)

-- Dot product test: i · i = 1
#eval let iv : Multivector R3 Int := Multivector.ofBlade (e1 : Blade R3)
      dot iv iv
-- Expected: 1

-- Dot product: i · j = 0
#eval let iv : Multivector R3 Int := Multivector.ofBlade (e1 : Blade R3)
      let jv : Multivector R3 Int := Multivector.ofBlade (e2 : Blade R3)
      dot iv jv
-- Expected: 0

end IntTests

end Grassmann.R3Utils

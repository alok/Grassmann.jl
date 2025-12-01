/-
  Grassmann/R3Utils.lean - Convenient 3D vector/geometric algebra utilities

  This module provides easy-to-use functions for common 3D geometry operations.
  All operations use the R3 (Euclidean 3D) signature.
-/
import Grassmann.Multivector
import Grassmann.LinearAlgebra
import Grassmann.Spinor

namespace Grassmann.R3Utils

open Multivector LinearAlgebra

/-! ## Vector Construction -/

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
def i : Multivector R3 Float := Multivector.ofBlade (e1 : Blade R3)
def j : Multivector R3 Float := Multivector.ofBlade (e2 : Blade R3)
def k : Multivector R3 Float := Multivector.ofBlade (e3 : Blade R3)

/-! ## Basic Operations -/

/-- Dot product of two 3D vectors -/
def dot3 (a b : Multivector R3 Float) : Float := dot a b

/-- Cross product of two 3D vectors (returns a vector) -/
def cross3 (a b : Multivector R3 Float) : Multivector R3 Float := cross a b

/-- Magnitude (length) of a 3D vector -/
def magnitude (v : Multivector R3 Float) : Float := v.norm

/-- Squared magnitude of a 3D vector -/
def magnitudeSq (v : Multivector R3 Float) : Float := v.normSq

/-- Normalize a 3D vector to unit length -/
def normalize (v : Multivector R3 Float) : Multivector R3 Float := v.normalize

/-- Distance between two points -/
def distance (a b : Multivector R3 Float) : Float := (a.sub b).norm

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

/-! ## Projection Operations -/

/-- Project vector a onto vector b -/
def projectOnto3 (a b : Multivector R3 Float) : Multivector R3 Float :=
  b.smul (dot3 a b / dot3 b b)

/-- Reject vector a from vector b (perpendicular component) -/
def rejectFrom3 (a b : Multivector R3 Float) : Multivector R3 Float :=
  a.sub (projectOnto3 a b)

/-- Project vector onto a plane defined by its normal -/
def projectOntoPlane (v normal : Multivector R3 Float) : Multivector R3 Float :=
  v.sub (projectOnto3 v normal)

/-! ## Angle Operations -/

/-- Angle between two vectors (radians) -/
def angleBetween (a b : Multivector R3 Float) : Float :=
  LinearAlgebra.angle a b

/-- Signed angle between two vectors around an axis (radians) -/
def signedAngle (v1 v2 axis : Multivector R3 Float) : Float :=
  let angle := angleBetween v1 v2
  let c := cross3 v1 v2
  if dot3 c axis < 0 then -angle else angle

/-! ## Geometric Constructions -/

/-- Midpoint of two vectors -/
def midpoint (a b : Multivector R3 Float) : Multivector R3 Float :=
  (a.add b).smul 0.5

/-- Linear interpolation between two vectors -/
def lerp (a b : Multivector R3 Float) (t : Float) : Multivector R3 Float :=
  (a.smul (1 - t)).add (b.smul t)

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
  v.sub ((projectOnto3 v normal).smul 2)

/-- Reflect a vector through the origin -/
def reflectThroughOrigin (v : Multivector R3 Float) : Multivector R3 Float :=
  v.neg

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

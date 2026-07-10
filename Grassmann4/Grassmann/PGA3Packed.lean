/-
  Grassmann/PGA3Packed.lean - Proof-free packed PGA3 API

  This is the supported high-performance Projective Geometric Algebra surface.
  It depends only on the packed `MV` runtime and keeps dense/reference proofs in
  `Grassmann.PGA` opt-in.

  PGA3 uses Cl(3,0,1), with canonical bit order e1, e2, e3, e0.
-/
import Grassmann.Blade
import Grassmann.MV

namespace Grassmann.PGA

/-! ## Basis masks

`Blade` stores an unoriented bit mask.  In particular mask `0b0101` is the
canonical blade `e13`; the historical `e31` name below is retained because the
semantic line/motor channel convention compensates for that orientation.
-/

def e1 : Blade PGA3 := ⟨0b0001⟩
def e2 : Blade PGA3 := ⟨0b0010⟩
def e3 : Blade PGA3 := ⟨0b0100⟩
def e0 : Blade PGA3 := ⟨0b1000⟩

def e01 : Blade PGA3 := ⟨0b1001⟩
def e02 : Blade PGA3 := ⟨0b1010⟩
def e03 : Blade PGA3 := ⟨0b1100⟩
def e12 : Blade PGA3 := ⟨0b0011⟩
def e13 : Blade PGA3 := ⟨0b0101⟩
/-- Historical semantic channel name for raw mask 5 (`e13 = -e31`). -/
def e31 : Blade PGA3 := e13
def e23 : Blade PGA3 := ⟨0b0110⟩

def e123 : Blade PGA3 := ⟨0b0111⟩
def e023 : Blade PGA3 := ⟨0b1110⟩
/-- Historical semantic channel name for raw mask 13 (`e013 = -e031`). -/
def e031 : Blade PGA3 := ⟨0b1101⟩
def e012 : Blade PGA3 := ⟨0b1011⟩
def e0123 : Blade PGA3 := ⟨0b1111⟩

/-! ## Packed Euclidean constructors -/

/-- Create a packed PGA3 point at Euclidean coordinates `(x, y, z)`. -/
@[inline, always_inline]
def point3 (x y z : Float) : Point PGA3 :=
  MV.pga3Point x y z

/-- Create a packed PGA3 plane with normal `(nx, ny, nz)` and offset `d`. -/
@[inline, always_inline]
def plane3 (nx ny nz d : Float) : Plane PGA3 :=
  MV.pga3Plane nx ny nz d

/-- Create a packed PGA3 line from direction and moment channels. -/
@[inline, always_inline]
def line3 (dx dy dz mx my mz : Float) : Line PGA3 :=
  MV.pga3Line dx dy dz mx my mz

/-- Create a packed PGA3 rotor.  The axis is expected to be normalized. -/
@[inline, always_inline]
def motor3 (axisX axisY axisZ angle : Float) : Motor PGA3 :=
  MV.pga3Rotor axisX axisY axisZ angle

/-- Create a packed PGA3 translator for displacement `(tx, ty, tz)`. -/
@[inline, always_inline]
def translator3 (tx ty tz : Float) : Motor PGA3 :=
  MV.pga3Translator tx ty tz

/-- Create a rigid motor that rotates first and then translates. -/
@[inline, always_inline]
def rigidMotor3 (axisX axisY axisZ angle tx ty tz : Float) : Motor PGA3 :=
  Motor.compose (translator3 tx ty tz) (motor3 axisX axisY axisZ angle)

/-- Extract Euclidean coordinates from a packed PGA3 point.

The zero triple represents a point at infinity (`weight = 0`). -/
@[inline, always_inline]
def extractPoint3 (p : Point PGA3) : Float × Float × Float :=
  PGA3Kernel.pointCoordinates p.toMV.coeffs

/-! ## Checked motor operations -/

namespace Motor

/-- Check that a packed PGA3 motor is finite, invertible, and satisfies the Study condition. -/
@[inline, always_inline]
def isValid3 (motor : @& Motor PGA3) (tolerance : Float := 1.0e-12) : Bool :=
  PGA3Kernel.motorIsValid motor.toMV.coeffs tolerance

/-- Check that a packed PGA3 motor is unit length and satisfies the Study condition. -/
@[inline, always_inline]
def isUnit3 (motor : @& Motor PGA3) (tolerance : Float := 1.0e-12) : Bool :=
  PGA3Kernel.motorIsUnit motor.toMV.coeffs tolerance

/-- Normalize a valid packed PGA3 motor. -/
@[inline]
def normalize3? (motor : @& Motor PGA3) (tolerance : Float := 1.0e-12) : Option (Motor PGA3) :=
  match PGA3Kernel.motorNormalize? motor.toMV.coeffs tolerance with
  | some coeffs => MV.ofDataArray? PGA3 .even coeffs
  | none => none

/-- Invert a valid packed PGA3 motor. -/
@[inline]
def inverse3? (motor : @& Motor PGA3) (tolerance : Float := 1.0e-12) : Option (Motor PGA3) :=
  match PGA3Kernel.motorInverse? motor.toMV.coeffs tolerance with
  | some coeffs => MV.ofDataArray? PGA3 .even coeffs
  | none => none

/--
Transform a flat array of `(x, y, z)` triples after validating both its length
and the motor. The returned array has the same length as the input.
-/
@[inline]
def transformXYZBatch3? (motor : @& Motor PGA3) (xyz : @& FloatArray)
    (tolerance : Float := 1.0e-12) : Option FloatArray :=
  if xyz.size % 3 == 0 && isValid3 motor tolerance then
    some (PGA3Kernel.motorApplyXYZBatch motor.toMV.coeffs xyz)
  else
    none

end Motor

end Grassmann.PGA

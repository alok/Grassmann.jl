/-
  Grassmann/CABI.lean - Internal Lean exports for the versioned C ABI

  This module is the only exported Lean-facing part of the foreign-function
  boundary. The public C header deliberately exposes no `lean_object` values:
  the C shim converts fixed-size arrays of doubles to Lean's native, unboxed
  `FloatArray`, invokes the shared Init-only PGA3 kernel, and copies the result
  into caller-owned output buffers.

  PGA3 packed coefficient layouts:
  - even/motor masks: [0, 3, 5, 6, 9, 10, 12, 15]
  - odd/point masks:  [1, 2, 4, 7, 8, 11, 13, 14]
-/
import Grassmann.PGA3Kernel

namespace Grassmann.CABI

/-- Construct a native packed PGA3 point. -/
@[export grassmann_lean_pga3_make_point_v1]
def makePoint (x y z : Float) : FloatArray :=
  PGA3Kernel.point x y z

/-- Construct a native packed PGA3 rotation motor. -/
@[export grassmann_lean_pga3_make_rotor_v1]
def makeRotor (axisX axisY axisZ angle : Float) : FloatArray :=
  PGA3Kernel.rotor axisX axisY axisZ angle

/-- Construct a native packed PGA3 translator. -/
@[export grassmann_lean_pga3_make_translator_v1]
def makeTranslator (x y z : Float) : FloatArray :=
  PGA3Kernel.translator x y z

/-- Compose packed motors as `after * before`. -/
@[export grassmann_lean_pga3_motor_compose_v1]
def motorCompose (after before : FloatArray) : FloatArray :=
  PGA3Kernel.motorMul after before

/-- Reverse a packed PGA3 motor. For a normalized motor, this is its inverse. -/
@[export grassmann_lean_pga3_motor_reverse_v1]
def motorReverse (motor : FloatArray) : FloatArray :=
  PGA3Kernel.motorReverse motor

/-- Transform a packed PGA3 point with the fixed motor sandwich product. -/
@[export grassmann_lean_pga3_motor_apply_point_v1]
def motorApplyPoint (motor point : FloatArray) : FloatArray :=
  PGA3Kernel.motorApplyPoint motor point

/-- Extract Euclidean `(x, y, z)` coordinates from a packed PGA3 point. -/
@[export grassmann_lean_pga3_extract_point_v1]
def extractPoint (point : FloatArray) : FloatArray :=
  PGA3Kernel.extractPoint point

/-!
ABI v1.1 implementation symbols. The public C shim validates pointers, packed
sizes, finite coefficients, the Study condition, and batch length before these
owned arrays cross into Lean.
-/

/-- Check the unit and Study conditions for a packed motor. -/
@[export grassmann_pga3_motor_is_unit_impl_v1]
def motorIsUnit (motor : FloatArray) (tolerance : Float) : Bool :=
  PGA3Kernel.motorIsUnit motor tolerance

/-- Normalize a packed motor already validated by the public C shim. -/
@[export grassmann_pga3_motor_normalize_impl_v1]
def motorNormalize (motor : FloatArray) : FloatArray :=
  PGA3Kernel.motorNormalizeUnchecked motor

/-- Invert a packed motor already validated by the public C shim. -/
@[export grassmann_pga3_motor_inverse_impl_v1]
def motorInverse (motor : FloatArray) : FloatArray :=
  PGA3Kernel.motorInverseUnchecked motor

/-- Transform validated flat XYZ triples with a packed motor. -/
@[export grassmann_pga3_motor_apply_xyz_batch_impl_v1]
def motorApplyXYZBatch (motor xyz : FloatArray) : FloatArray :=
  PGA3Kernel.motorApplyXYZBatch motor xyz

end Grassmann.CABI

/-
  Grassmann/UnrealFFI.lean - FFI exports for Unreal Engine integration

  Simple FFI layer that works with raw Float arrays.
  Uses pure computational functions, avoiding SciLean DataArray complexity.
-/
import Grassmann.Parity
import Grassmann.SignTables

namespace Grassmann.UnrealFFI

/-! ## Core PGA3 operations (pure Float computation) -/

/-- PGA3 dimension: 4D (3 Euclidean + 1 projective) → 2^4 = 16 coefficients -/
def pga3Dim : Nat := 16

/-- Create zero array of size n -/
@[inline] def zeros (n : Nat) : FloatArray :=
  ⟨(List.replicate n 0.0).toArray⟩

/-! ## PGA Point operations -/

/-- Create a PGA3 point from x,y,z coordinates.
    Point = e123 + x·e023 + y·e031 + z·e012
    Returns 16 floats. -/
@[export grassmann_pga_point]
def pgaPoint (x y z : Float) : FloatArray :=
  let arr := zeros 16
  -- e123 at index 7 (binary 0111)
  -- e023 at index 14 (binary 1110)
  -- e031 at index 13 (binary 1101)
  -- e012 at index 11 (binary 1011)
  let arr := arr.set! 7 1.0   -- w = 1 (homogeneous coord)
  let arr := arr.set! 14 x
  let arr := arr.set! 13 y
  let arr := arr.set! 11 z
  arr

/-- Extract x,y,z from a PGA point. Returns 3 floats. -/
@[export grassmann_pga_extract_point]
def pgaExtractPoint (coeffs : @& FloatArray) : FloatArray :=
  let w := coeffs.get! 7
  if w == 0.0 then
    ⟨#[0.0, 0.0, 0.0]⟩
  else
    ⟨#[coeffs.get! 14 / w, coeffs.get! 13 / w, coeffs.get! 11 / w]⟩

/-! ## PGA Motor operations -/

/-- Create a rotation motor from axis (dx,dy,dz) and angle theta.
    Rotor = cos(θ/2) + sin(θ/2)(dx·e23 + dy·e31 + dz·e12)
    Returns 16 floats. -/
@[export grassmann_pga_rotor]
def pgaRotor (dx dy dz theta : Float) : FloatArray :=
  let halfAngle := theta / 2.0
  let c := Float.cos halfAngle
  let s := Float.sin halfAngle
  let arr := zeros 16
  -- scalar at index 0
  -- e23 at index 6 (binary 0110)
  -- e31 at index 5 (binary 0101)
  -- e12 at index 3 (binary 0011)
  let arr := arr.set! 0 c
  let arr := arr.set! 6 (s * dx)
  let arr := arr.set! 5 (s * dy)
  let arr := arr.set! 3 (s * dz)
  arr

/-- Create a translation motor.
    Translator = 1 + (tx/2)e01 + (ty/2)e02 + (tz/2)e03
    Returns 16 floats. -/
@[export grassmann_pga_translator]
def pgaTranslator (tx ty tz : Float) : FloatArray :=
  let arr := zeros 16
  -- scalar at 0, e01 at 9, e02 at 10, e03 at 12
  let arr := arr.set! 0 1.0
  let arr := arr.set! 9 (tx * 0.5)
  let arr := arr.set! 10 (ty * 0.5)
  let arr := arr.set! 12 (tz * 0.5)
  arr

/-! ## Geometric product for PGA3 (even × even → even) -/

/-- Sign table for geometric product in Cl(3,0,1).
    Generated from signature (+,+,+,0) -/
private def geoSign (i j : Nat) : Float :=
  -- Simplified: for now just return the basic sign pattern
  -- Full implementation would use precomputed tables
  if i == j then 1.0 else
  if i < j then 1.0 else -1.0

/-- Geometric product of two motors (even-grade MVs).
    M1 * M2 using explicit coefficient computation. -/
@[export grassmann_pga_motor_compose]
def pgaMotorCompose (m1 m2 : @& FloatArray) : FloatArray :=
  -- For motors (even grade), we have: scalar, e12, e31, e23, e01, e02, e03, e0123
  -- Indices: 0 (scalar), 3 (e12), 5 (e31), 6 (e23), 9 (e01), 10 (e02), 12 (e03), 15 (e0123)
  let s1 := m1.get! 0
  let b12_1 := m1.get! 3
  let b31_1 := m1.get! 5
  let b23_1 := m1.get! 6
  let s2 := m2.get! 0
  let b12_2 := m2.get! 3
  let b31_2 := m2.get! 5
  let b23_2 := m2.get! 6
  -- Rotor part: R1 * R2 = (c1 + s1·B1)(c2 + s2·B2)
  -- scalar = c1·c2 - B1·B2 (for normalized bivectors)
  let newScalar := s1*s2 - (b12_1*b12_2 + b31_1*b31_2 + b23_1*b23_2)
  -- bivector = c1·B2 + c2·B1 + B1×B2 (cross product part)
  let newB12 := s1*b12_2 + s2*b12_1 + (b31_1*b23_2 - b23_1*b31_2)
  let newB31 := s1*b31_2 + s2*b31_1 + (b23_1*b12_2 - b12_1*b23_2)
  let newB23 := s1*b23_2 + s2*b23_1 + (b12_1*b31_2 - b31_1*b12_2)
  let arr := zeros 16
  let arr := arr.set! 0 newScalar
  let arr := arr.set! 3 newB12
  let arr := arr.set! 5 newB31
  let arr := arr.set! 6 newB23
  -- Translation part (simplified - full version needs more terms)
  let arr := arr.set! 9 (m1.get! 9 + m2.get! 9)
  let arr := arr.set! 10 (m1.get! 10 + m2.get! 10)
  let arr := arr.set! 12 (m1.get! 12 + m2.get! 12)
  arr

/-- Reverse of a motor (conjugate for rotors). -/
@[export grassmann_pga_motor_reverse]
def pgaMotorReverse (m : @& FloatArray) : FloatArray :=
  let arr := zeros 16
  -- Scalar unchanged
  let arr := arr.set! 0 (m.get! 0)
  -- Bivectors flip sign
  let arr := arr.set! 3 (-(m.get! 3))
  let arr := arr.set! 5 (-(m.get! 5))
  let arr := arr.set! 6 (-(m.get! 6))
  let arr := arr.set! 9 (-(m.get! 9))
  let arr := arr.set! 10 (-(m.get! 10))
  let arr := arr.set! 12 (-(m.get! 12))
  -- Pseudoscalar unchanged
  let arr := arr.set! 15 (m.get! 15)
  arr

/-! ## Motor application to points -/

/-- Apply motor to point: M * P * M†.
    Simplified version using explicit formulas. -/
@[export grassmann_pga_motor_apply_point]
def pgaMotorApplyPoint (motor point : @& FloatArray) : FloatArray :=
  -- Extract point coordinates
  let w := point.get! 7
  let x := if w == 0.0 then 0.0 else point.get! 14 / w
  let y := if w == 0.0 then 0.0 else point.get! 13 / w
  let z := if w == 0.0 then 0.0 else point.get! 11 / w
  -- Extract rotor components
  let s := motor.get! 0
  let b23 := motor.get! 6
  let b31 := motor.get! 5
  let b12 := motor.get! 3
  -- Convert to quaternion: q = (b23, b31, b12, s) = (qx, qy, qz, qw)
  let qx := b23
  let qy := b31
  let qz := b12
  let qw := s
  -- Rodrigues rotation formula: v' = v + 2w(q × v) + 2(q × (q × v))
  -- where q = (qx,qy,qz), w = qw, v = (x,y,z)
  -- Cross product q × v
  let cx := qy*z - qz*y
  let cy := qz*x - qx*z
  let cz := qx*y - qy*x
  -- Cross product q × (q × v)
  let ccx := qy*cz - qz*cy
  let ccy := qz*cx - qx*cz
  let ccz := qx*cy - qy*cx
  -- Final rotated position
  let rx := x + 2.0*qw*cx + 2.0*ccx
  let ry := y + 2.0*qw*cy + 2.0*ccy
  let rz := z + 2.0*qw*cz + 2.0*ccz
  -- Add translation
  let tx := motor.get! 9 * 2.0
  let ty := motor.get! 10 * 2.0
  let tz := motor.get! 12 * 2.0
  pgaPoint (rx + tx) (ry + ty) (rz + tz)

/-! ## Motor ↔ UE Transform conversions -/

/-- Convert PGA motor to quaternion (x,y,z,w) for FQuat. -/
@[export grassmann_pga_motor_to_quat]
def pgaMotorToQuat (motor : @& FloatArray) : FloatArray :=
  let w := motor.get! 0
  let xy := motor.get! 3
  let xz := motor.get! 5
  let yz := motor.get! 6
  let norm := Float.sqrt (w*w + xy*xy + xz*xz + yz*yz)
  if norm == 0.0 then
    ⟨#[0.0, 0.0, 0.0, 1.0]⟩
  else
    ⟨#[yz/norm, xz/norm, xy/norm, w/norm]⟩

/-- Convert PGA motor to translation (x,y,z) for FVector. -/
@[export grassmann_pga_motor_to_translation]
def pgaMotorToTranslation (motor : @& FloatArray) : FloatArray :=
  ⟨#[motor.get! 9 * 2.0, motor.get! 10 * 2.0, motor.get! 12 * 2.0]⟩

/-- Create motor from UE FQuat (x,y,z,w) and FVector (tx,ty,tz). -/
@[export grassmann_pga_motor_from_ue]
def pgaMotorFromUE (qx qy qz qw tx ty tz : Float) : FloatArray :=
  let arr := zeros 16
  let arr := arr.set! 0 qw        -- scalar
  let arr := arr.set! 3 qz        -- e12
  let arr := arr.set! 5 qy        -- e31
  let arr := arr.set! 6 qx        -- e23
  let arr := arr.set! 9 (tx * 0.5)   -- e01
  let arr := arr.set! 10 (ty * 0.5)  -- e02
  let arr := arr.set! 12 (tz * 0.5)  -- e03
  arr

/-! ## Distance and utility operations -/

/-- Euclidean distance squared between two points. -/
@[export grassmann_pga_distance_sq]
def pgaDistanceSq (x1 y1 z1 x2 y2 z2 : Float) : Float :=
  let dx := x2 - x1
  let dy := y2 - y1
  let dz := z2 - z1
  dx*dx + dy*dy + dz*dz

/-- Quaternion SLERP. -/
@[export grassmann_quat_slerp]
def quatSlerp (q1x q1y q1z q1w q2x q2y q2z q2w t : Float) : FloatArray :=
  let dot := q1x*q2x + q1y*q2y + q1z*q2z + q1w*q2w
  let (q2x, q2y, q2z, q2w, dot) :=
    if dot < 0.0 then (-q2x, -q2y, -q2z, -q2w, -dot) else (q2x, q2y, q2z, q2w, dot)
  let dot := min 1.0 (max (-1.0) dot)
  let theta := Float.acos dot
  let sinTheta := Float.sin theta
  if sinTheta.abs < 0.001 then
    ⟨#[(1.0 - t) * q1x + t * q2x,
       (1.0 - t) * q1y + t * q2y,
       (1.0 - t) * q1z + t * q2z,
       (1.0 - t) * q1w + t * q2w]⟩
  else
    let s1 := Float.sin ((1.0 - t) * theta) / sinTheta
    let s2 := Float.sin (t * theta) / sinTheta
    ⟨#[s1 * q1x + s2 * q2x,
       s1 * q1y + s2 * q2y,
       s1 * q1z + s2 * q2z,
       s1 * q1w + s2 * q2w]⟩

end Grassmann.UnrealFFI

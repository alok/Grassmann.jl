/-
  Grassmann/PGA3Kernel.lean - Init-only fixed-layout PGA3 runtime kernels

  This module is deliberately independent of Mathlib and the generic Grassmann
  type hierarchy. It is the shared computational source for the packed PGA3
  hot path and native bindings.

  Packed masks:
  - motor/even: [0, 3, 5, 6, 9, 10, 12, 15]
  - point/odd:  [1, 2, 4, 7, 8, 11, 13, 14]
-/
import Init.Data.FloatArray

namespace Grassmann.PGA3Kernel

/-- Eight zero coefficients in a fresh native `FloatArray`. -/
@[inline, always_inline]
def zero : FloatArray :=
  FloatArray.emptyWithCapacity 8
    |>.push 0.0
    |>.push 0.0
    |>.push 0.0
    |>.push 0.0
    |>.push 0.0
    |>.push 0.0
    |>.push 0.0
    |>.push 0.0

/-- Construct the native packed point for Euclidean coordinates `(x, y, z)`. -/
@[inline, always_inline]
def point (x y z : Float) : FloatArray :=
  FloatArray.emptyWithCapacity 8
    |>.push 0.0
    |>.push 0.0
    |>.push 0.0
    |>.push 1.0
    |>.push 0.0
    |>.push z
    |>.push y
    |>.push x

/-- Construct the native packed plane with normal `(nx, ny, nz)` and offset `d`. -/
@[inline, always_inline]
def plane (nx ny nz d : Float) : FloatArray :=
  FloatArray.emptyWithCapacity 8
    |>.push nx
    |>.push ny
    |>.push nz
    |>.push 0.0
    |>.push d
    |>.push 0.0
    |>.push 0.0
    |>.push 0.0

/-- Construct the native packed line from direction and moment channels. -/
@[inline, always_inline]
def line (dx dy dz mx my mz : Float) : FloatArray :=
  FloatArray.emptyWithCapacity 8
    |>.push 0.0
    |>.push dz
    |>.push dy
    |>.push dx
    |>.push mx
    |>.push my
    |>.push mz
    |>.push 0.0

/-- Construct a native packed rotor. The axis is expected to be normalized. -/
@[inline, always_inline]
def rotor (axisX axisY axisZ angle : Float) : FloatArray :=
  let halfAngle := angle / 2.0
  let c := Float.cos halfAngle
  let s := Float.sin halfAngle
  FloatArray.emptyWithCapacity 8
    |>.push c
    |>.push (s * axisZ)
    |>.push (s * axisY)
    |>.push (s * axisX)
    |>.push 0.0
    |>.push 0.0
    |>.push 0.0
    |>.push 0.0

/-- Construct the native packed translator for displacement `(x, y, z)`. -/
@[inline, always_inline]
def translator (x y z : Float) : FloatArray :=
  FloatArray.emptyWithCapacity 8
    |>.push 1.0
    |>.push 0.0
    |>.push 0.0
    |>.push 0.0
    |>.push (-(x / 2.0))
    |>.push (y / 2.0)
    |>.push (-(z / 2.0))
    |>.push 0.0

/--
Straight-line dual-quaternion product for native packed PGA3 motors.

Inputs are assumed to have exactly eight coefficients. This is the unchecked
hot path used by `MV`; the C shim enforces the same fixed-size invariant.
-/
@[inline, always_inline]
def motorMul (a : @& FloatArray) (b : @& FloatArray) : FloatArray :=
  let a0 := a.get! 0
  let a1 := a.get! 1
  let a2 := a.get! 2
  let a3 := a.get! 3
  let a4 := a.get! 4
  let a5 := a.get! 5
  let a6 := a.get! 6
  let a7 := a.get! 7
  let b0 := b.get! 0
  let b1 := b.get! 1
  let b2 := b.get! 2
  let b3 := b.get! 3
  let b4 := b.get! 4
  let b5 := b.get! 5
  let b6 := b.get! 6
  let b7 := b.get! 7
  let c0 := a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3
  let c1 := a0 * b1 + a1 * b0 - a2 * b3 + a3 * b2
  let c2 := a0 * b2 + a1 * b3 + a2 * b0 - a3 * b1
  let c3 := a0 * b3 - a1 * b2 + a2 * b1 + a3 * b0
  let c4 := a0 * b4 + a1 * b5 + a2 * b6 - a3 * b7
    + a4 * b0 - a5 * b1 - a6 * b2 - a7 * b3
  let c5 := a0 * b5 - a1 * b4 + a2 * b7 + a3 * b6
    + a4 * b1 + a5 * b0 - a6 * b3 + a7 * b2
  let c6 := a0 * b6 - a1 * b7 - a2 * b4 - a3 * b5
    + a4 * b2 + a5 * b3 + a6 * b0 - a7 * b1
  let c7 := a0 * b7 + a1 * b6 - a2 * b5 + a3 * b4
    + a4 * b3 - a5 * b2 + a6 * b1 + a7 * b0
  FloatArray.emptyWithCapacity 8
    |>.push c0
    |>.push c1
    |>.push c2
    |>.push c3
    |>.push c4
    |>.push c5
    |>.push c6
    |>.push c7

/-- Reverse a native packed PGA3 motor. -/
@[inline, always_inline]
def motorReverse (motor : @& FloatArray) : FloatArray :=
  FloatArray.emptyWithCapacity 8
    |>.push (motor.get! 0)
    |>.push (-(motor.get! 1))
    |>.push (-(motor.get! 2))
    |>.push (-(motor.get! 3))
    |>.push (-(motor.get! 4))
    |>.push (-(motor.get! 5))
    |>.push (-(motor.get! 6))
    |>.push (motor.get! 7)

/-- Squared norm of the real quaternion part of a packed PGA3 motor. -/
@[inline, always_inline]
def motorNormSq (motor : @& FloatArray) : Float :=
  let a0 := motor.get! 0
  let a1 := motor.get! 1
  let a2 := motor.get! 2
  let a3 := motor.get! 3
  a0 * a0 + a1 * a1 + a2 * a2 + a3 * a3

/--
Study scalar of a packed PGA3 motor.

For packed coefficients `[a0, ..., a7]`, the reverse product is
`motor * reverse motor = q + 2 * motorStudy motor * e0123`.
-/
@[inline, always_inline]
def motorStudy (motor : @& FloatArray) : Float :=
  let a0 := motor.get! 0
  let a1 := motor.get! 1
  let a2 := motor.get! 2
  let a3 := motor.get! 3
  let a4 := motor.get! 4
  let a5 := motor.get! 5
  let a6 := motor.get! 6
  let a7 := motor.get! 7
  a0 * a7 - a1 * a6 + a2 * a5 - a3 * a4

/-- Check that a packed motor represents a finite, invertible rigid motion. -/
@[inline, always_inline]
def motorIsValid (motor : @& FloatArray) (tolerance : Float) : Bool :=
  if motor.size != 8 || !tolerance.isFinite || tolerance < 0.0 then
    false
  else
    let q := motorNormSq motor
    let residual := 2.0 * motorStudy motor
    let invQ := 1.0 / q
    let bound := tolerance * q
    q.isFinite && invQ.isFinite && residual.isFinite && bound.isFinite &&
      q > tolerance && Float.abs residual ≤ bound

/-- Check the unit-motor and Study conditions at the requested tolerance. -/
@[inline, always_inline]
def motorIsUnit (motor : @& FloatArray) (tolerance : Float) : Bool :=
  let q := motorNormSq motor
  motorIsValid motor tolerance && Float.abs (q - 1.0) ≤ tolerance

/-- Normalize a motor already known to satisfy `motorIsValid`. -/
@[inline, always_inline]
def motorNormalizeUnchecked (motor : @& FloatArray) : FloatArray :=
  let scale := 1.0 / Float.sqrt (motorNormSq motor)
  FloatArray.emptyWithCapacity 8
    |>.push (motor.get! 0 * scale)
    |>.push (motor.get! 1 * scale)
    |>.push (motor.get! 2 * scale)
    |>.push (motor.get! 3 * scale)
    |>.push (motor.get! 4 * scale)
    |>.push (motor.get! 5 * scale)
    |>.push (motor.get! 6 * scale)
    |>.push (motor.get! 7 * scale)

/-- Normalize a finite rigid motor, rejecting ideal or Study-invalid inputs. -/
@[inline, always_inline]
def motorNormalize? (motor : @& FloatArray) (tolerance : Float) : Option FloatArray :=
  if motorIsValid motor tolerance then
    some (motorNormalizeUnchecked motor)
  else
    none

/-- Invert a motor already known to satisfy `motorIsValid`. -/
@[inline, always_inline]
def motorInverseUnchecked (motor : @& FloatArray) : FloatArray :=
  let scale := 1.0 / motorNormSq motor
  FloatArray.emptyWithCapacity 8
    |>.push (motor.get! 0 * scale)
    |>.push (-(motor.get! 1) * scale)
    |>.push (-(motor.get! 2) * scale)
    |>.push (-(motor.get! 3) * scale)
    |>.push (-(motor.get! 4) * scale)
    |>.push (-(motor.get! 5) * scale)
    |>.push (-(motor.get! 6) * scale)
    |>.push (motor.get! 7 * scale)

/-- Invert a finite rigid motor, rejecting ideal or Study-invalid inputs. -/
@[inline, always_inline]
def motorInverse? (motor : @& FloatArray) (tolerance : Float) : Option FloatArray :=
  if motorIsValid motor tolerance then
    some (motorInverseUnchecked motor)
  else
    none

/--
Fixed native packed even-by-odd geometric product.

Inputs use the even masks `[0,3,5,6,9,10,12,15]` and odd masks
`[1,2,4,7,8,11,13,14]`, and are assumed to have exactly eight coefficients.
-/
@[inline, always_inline]
def evenOddMul (a : @& FloatArray) (b : @& FloatArray) : FloatArray :=
  let a0 := a.get! 0
  let a1 := a.get! 1
  let a2 := a.get! 2
  let a3 := a.get! 3
  let a4 := a.get! 4
  let a5 := a.get! 5
  let a6 := a.get! 6
  let a7 := a.get! 7
  let b0 := b.get! 0
  let b1 := b.get! 1
  let b2 := b.get! 2
  let b3 := b.get! 3
  let b4 := b.get! 4
  let b5 := b.get! 5
  let b6 := b.get! 6
  let b7 := b.get! 7
  let c0 := a0 * b0 + a1 * b1 + a2 * b2 - a3 * b3
  let c1 := a0 * b1 - a1 * b0 + a2 * b3 + a3 * b2
  let c2 := a0 * b2 - a1 * b3 - a2 * b0 - a3 * b1
  let c3 := a0 * b3 + a1 * b2 - a2 * b1 + a3 * b0
  let c4 := a0 * b4 - a1 * b5 - a2 * b6 - a3 * b7
    - a4 * b0 - a5 * b1 - a6 * b2 + a7 * b3
  let c5 := a0 * b5 + a1 * b4 - a2 * b7 + a3 * b6
    - a4 * b1 + a5 * b0 - a6 * b3 - a7 * b2
  let c6 := a0 * b6 + a1 * b7 + a2 * b4 - a3 * b5
    - a4 * b2 + a5 * b3 + a6 * b0 + a7 * b1
  let c7 := a0 * b7 - a1 * b6 + a2 * b5 + a3 * b4
    - a4 * b3 - a5 * b2 + a6 * b1 - a7 * b0
  FloatArray.emptyWithCapacity 8
    |>.push c0
    |>.push c1
    |>.push c2
    |>.push c3
    |>.push c4
    |>.push c5
    |>.push c6
    |>.push c7

/--
Fixed native packed odd-by-even geometric product.

Inputs use the odd masks `[1,2,4,7,8,11,13,14]` and even masks
`[0,3,5,6,9,10,12,15]`, and are assumed to have exactly eight coefficients.
-/
@[inline, always_inline]
def oddEvenMul (a : @& FloatArray) (b : @& FloatArray) : FloatArray :=
  let a0 := a.get! 0
  let a1 := a.get! 1
  let a2 := a.get! 2
  let a3 := a.get! 3
  let a4 := a.get! 4
  let a5 := a.get! 5
  let a6 := a.get! 6
  let a7 := a.get! 7
  let b0 := b.get! 0
  let b1 := b.get! 1
  let b2 := b.get! 2
  let b3 := b.get! 3
  let b4 := b.get! 4
  let b5 := b.get! 5
  let b6 := b.get! 6
  let b7 := b.get! 7
  let c0 := a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3
  let c1 := a0 * b1 + a1 * b0 - a2 * b3 + a3 * b2
  let c2 := a0 * b2 + a1 * b3 + a2 * b0 - a3 * b1
  let c3 := a0 * b3 - a1 * b2 + a2 * b1 + a3 * b0
  let c4 := a0 * b4 + a1 * b5 + a2 * b6 - a3 * b7
    + a4 * b0 - a5 * b1 - a6 * b2 - a7 * b3
  let c5 := a0 * b5 - a1 * b4 + a2 * b7 + a3 * b6
    + a4 * b1 + a5 * b0 - a6 * b3 + a7 * b2
  let c6 := a0 * b6 - a1 * b7 - a2 * b4 - a3 * b5
    + a4 * b2 + a5 * b3 + a6 * b0 - a7 * b1
  let c7 := a0 * b7 + a1 * b6 - a2 * b5 + a3 * b4
    + a4 * b3 - a5 * b2 + a6 * b1 + a7 * b0
  FloatArray.emptyWithCapacity 8
    |>.push c0
    |>.push c1
    |>.push c2
    |>.push c3
    |>.push c4
    |>.push c5
    |>.push c6
    |>.push c7

/--
Apply a native packed motor to any packed odd PGA3 multivector.

This is the scalarized form of `motor * odd * reverse motor`. It preserves the
operation order of `evenOddMul` followed by `oddEvenMul`, but keeps the
intermediate coefficients in locals and allocates only the final array.
-/
@[inline, always_inline]
def motorSandwichOdd (motor : @& FloatArray) (odd : @& FloatArray) : FloatArray :=
  let m0 := motor.get! 0
  let m1 := motor.get! 1
  let m2 := motor.get! 2
  let m3 := motor.get! 3
  let m4 := motor.get! 4
  let m5 := motor.get! 5
  let m6 := motor.get! 6
  let m7 := motor.get! 7
  let p0 := odd.get! 0
  let p1 := odd.get! 1
  let p2 := odd.get! 2
  let p3 := odd.get! 3
  let p4 := odd.get! 4
  let p5 := odd.get! 5
  let p6 := odd.get! 6
  let p7 := odd.get! 7
  let t0 := m0 * p0 + m1 * p1 + m2 * p2 - m3 * p3
  let t1 := m0 * p1 - m1 * p0 + m2 * p3 + m3 * p2
  let t2 := m0 * p2 - m1 * p3 - m2 * p0 - m3 * p1
  let t3 := m0 * p3 + m1 * p2 - m2 * p1 + m3 * p0
  let t4 := m0 * p4 - m1 * p5 - m2 * p6 - m3 * p7
    - m4 * p0 - m5 * p1 - m6 * p2 + m7 * p3
  let t5 := m0 * p5 + m1 * p4 - m2 * p7 + m3 * p6
    - m4 * p1 + m5 * p0 - m6 * p3 - m7 * p2
  let t6 := m0 * p6 + m1 * p7 + m2 * p4 - m3 * p5
    - m4 * p2 + m5 * p3 + m6 * p0 + m7 * p1
  let t7 := m0 * p7 - m1 * p6 + m2 * p5 + m3 * p4
    - m4 * p3 - m5 * p2 + m6 * p1 - m7 * p0
  let r0 := m0
  let r1 := -m1
  let r2 := -m2
  let r3 := -m3
  let r4 := -m4
  let r5 := -m5
  let r6 := -m6
  let r7 := m7
  let c0 := t0 * r0 - t1 * r1 - t2 * r2 - t3 * r3
  let c1 := t0 * r1 + t1 * r0 - t2 * r3 + t3 * r2
  let c2 := t0 * r2 + t1 * r3 + t2 * r0 - t3 * r1
  let c3 := t0 * r3 - t1 * r2 + t2 * r1 + t3 * r0
  let c4 := t0 * r4 + t1 * r5 + t2 * r6 - t3 * r7
    + t4 * r0 - t5 * r1 - t6 * r2 - t7 * r3
  let c5 := t0 * r5 - t1 * r4 + t2 * r7 + t3 * r6
    + t4 * r1 + t5 * r0 - t6 * r3 + t7 * r2
  let c6 := t0 * r6 - t1 * r7 - t2 * r4 - t3 * r5
    + t4 * r2 + t5 * r3 + t6 * r0 - t7 * r1
  let c7 := t0 * r7 + t1 * r6 - t2 * r5 + t3 * r4
    + t4 * r3 - t5 * r2 + t6 * r1 + t7 * r0
  FloatArray.emptyWithCapacity 8
    |>.push c0
    |>.push c1
    |>.push c2
    |>.push c3
    |>.push c4
    |>.push c5
    |>.push c6
    |>.push c7

/-- Apply a native packed motor to a packed PGA3 point. -/
@[inline, always_inline]
def motorApplyPoint (motor : @& FloatArray) (p : @& FloatArray) : FloatArray :=
  motorSandwichOdd motor p

/-- Extract Euclidean coordinates from a native packed point. -/
@[inline, always_inline]
def pointCoordinates (p : @& FloatArray) : Float × Float × Float :=
  let w := p.get! 3
  if w == 0.0 then
    (0.0, 0.0, 0.0)
  else
    (p.get! 7 / w, p.get! 6 / w, p.get! 5 / w)

/-- Extract Euclidean coordinates into a native three-element `FloatArray`. -/
@[inline, always_inline]
def extractPoint (p : @& FloatArray) : FloatArray :=
  let (x, y, z) := pointCoordinates p
  FloatArray.emptyWithCapacity 3
    |>.push x
    |>.push y
    |>.push z

/--
Transform a flat array of Euclidean `(x, y, z)` triples with one packed motor.

The input length is assumed to be divisible by three. The motor's homogeneous
3x4 transform is computed once, then applied without allocating a packed point
or sandwich intermediate for each triple. A zero-norm motor maps every input
to the zero triple; checked callers should reject it with `motorIsValid`.
-/
@[inline]
def motorApplyXYZBatch (motor : @& FloatArray) (xyz : @& FloatArray) : FloatArray := Id.run do
  let m0 := motor.get! 0
  let m1 := motor.get! 1
  let m2 := motor.get! 2
  let m3 := motor.get! 3
  let m4 := motor.get! 4
  let m5 := motor.get! 5
  let m6 := motor.get! 6
  let m7 := motor.get! 7
  let q := m0 * m0 + m1 * m1 + m2 * m2 + m3 * m3
  let pointCount := xyz.size / 3
  let mut out := FloatArray.emptyWithCapacity (pointCount * 3)
  if q == 0.0 then
    for _ in [0:pointCount] do
      out := out.push 0.0 |>.push 0.0 |>.push 0.0
  else
    let invQ := 1.0 / q
    let xx := (m0 * m0 - m1 * m1 - m2 * m2 + m3 * m3) * invQ
    let xy := (-2.0 * (m0 * m1 - m2 * m3)) * invQ
    let xz := (2.0 * (m0 * m2 + m1 * m3)) * invQ
    let xt := (-2.0 * (m0 * m4 + m1 * m5 + m2 * m6 + m3 * m7)) * invQ
    let yx := (2.0 * (m0 * m1 + m2 * m3)) * invQ
    let yy := (m0 * m0 - m1 * m1 + m2 * m2 - m3 * m3) * invQ
    let yz := (-2.0 * (m0 * m3 - m1 * m2)) * invQ
    let yt := (2.0 * (m0 * m5 - m1 * m4 - m2 * m7 + m3 * m6)) * invQ
    let zx := (-2.0 * (m0 * m2 - m1 * m3)) * invQ
    let zy := (2.0 * (m0 * m3 + m1 * m2)) * invQ
    let zz := (m0 * m0 + m1 * m1 - m2 * m2 - m3 * m3) * invQ
    let zt := (-2.0 * (m0 * m6 + m1 * m7 - m2 * m4 - m3 * m5)) * invQ
    for i in [0:pointCount] do
      let base := i * 3
      let x := xyz.get! base
      let y := xyz.get! (base + 1)
      let z := xyz.get! (base + 2)
      out := out
        |>.push (xx * x + xy * y + xz * z + xt)
        |>.push (yx * x + yy * y + yz * z + yt)
        |>.push (zx * x + zy * y + zz * z + zt)
  return out

end Grassmann.PGA3Kernel

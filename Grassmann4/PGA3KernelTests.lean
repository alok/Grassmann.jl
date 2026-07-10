import Grassmann.PGA3Kernel
import Grassmann.PGATransforms

namespace Grassmann.PGA3KernelTests

private abbrev Coord3 := Float × Float × Float

private def pi : Float := 3.141592653589793
private def tolerance : Float := 1.0e-6

private def maxAbsDiff (a b : FloatArray) : Float :=
  (Array.range (min a.size b.size)).foldl
    (fun acc i =>
      let d := Float.abs (a.get! i - b.get! i)
      if d > acc then d else acc)
    0.0

private def basisPacked (index : Nat) : FloatArray :=
  PGA3Kernel.zero.set! index 1.0

private def composedMotorSandwichOdd
    (motor : FloatArray) (odd : FloatArray) : FloatArray :=
  PGA3Kernel.oddEvenMul
    (PGA3Kernel.evenOddMul motor odd)
    (PGA3Kernel.motorReverse motor)

private def coordsApproxEq (a b : Coord3) (tol : Float := tolerance) : Bool :=
  Float.abs (a.1 - b.1) ≤ tol &&
    Float.abs (a.2.1 - b.2.1) ≤ tol &&
    Float.abs (a.2.2 - b.2.2) ≤ tol

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw <| IO.userError s!"PGA3 kernel regression: {label}"

private def requireCoords (label : String) (actual expected : Coord3) : IO Unit :=
  require
    (s!"{label}: got ({actual.1}, {actual.2.1}, {actual.2.2}), " ++
      s!"expected ({expected.1}, {expected.2.1}, {expected.2.2})")
    (coordsApproxEq actual expected)

private def requireArrays
    (label : String) (actual expected : FloatArray) (tol : Float := tolerance) : IO Unit := do
  require s!"{label}: output sizes differ ({actual.size} versus {expected.size})"
    (actual.size == expected.size)
  let difference := maxAbsDiff actual expected
  require s!"{label}: maximum coefficient difference was {difference}"
    (difference ≤ tol)

/-
  Check every pair of packed even basis elements. This covers all 64 entries
  in the bilinear multiplication table, including the degenerate PGA terms.
-/
private def checkMotorMulBasis : IO Unit := do
  for i in Array.range 8 do
    for j in Array.range 8 do
      let a := basisPacked i
      let b := basisPacked j
      let kernelResult := PGA3Kernel.motorMul a b
      requireArrays s!"motorMul/MV basis pair ({i}, {j})"
        kernelResult (MV.mulKernelPGA3EvenEven a b)
        0.0
      requireArrays s!"motorMul/table basis pair ({i}, {j})"
        kernelResult
        (MV.mulKernelEvenEven 4 EvenMV.Kernel.evenMulSignPGA3 a b)
        0.0
      let evenOddResult := PGA3Kernel.evenOddMul a b
      requireArrays s!"evenOddMul/direct basis pair ({i}, {j})"
        evenOddResult (MV.mulKernelDirect PGA3 .even .odd a b)
        0.0
      requireArrays s!"evenOddMul/generic basis pair ({i}, {j})"
        evenOddResult (MV.mulKernelGeneric PGA3 .even .odd a b)
        0.0
      let oddEvenResult := PGA3Kernel.oddEvenMul a b
      requireArrays s!"oddEvenMul/direct basis pair ({i}, {j})"
        oddEvenResult (MV.mulKernelDirect PGA3 .odd .even a b)
        0.0
      requireArrays s!"oddEvenMul/generic basis pair ({i}, {j})"
        oddEvenResult (MV.mulKernelGeneric PGA3 .odd .even a b)
        0.0
      requireArrays s!"motorSandwichOdd/composed basis pair ({i}, {j})"
        (PGA3Kernel.motorSandwichOdd a b)
        (composedMotorSandwichOdd a b)
        0.0
      let packedMotor :=
        (MV.ofDataArray? PGA3 .even a).getD (MV.zero PGA3 .even)
      let packedOdd :=
        (MV.ofDataArray? PGA3 .odd b).getD (MV.zero PGA3 .odd)
      requireArrays s!"mvSandwich/composed basis pair ({i}, {j})"
        (mvSandwich packedMotor packedOdd).coeffs
        (composedMotorSandwichOdd a b)
        0.0
  let a := PGA3Kernel.zero
    |>.set! 0 1.25
    |>.set! 1 (-2.0)
    |>.set! 2 0.75
    |>.set! 3 4.5
    |>.set! 4 3.0
    |>.set! 5 (-1.5)
    |>.set! 6 2.0
    |>.set! 7 0.25
  let b := PGA3Kernel.zero
    |>.set! 0 (-0.5)
    |>.set! 1 3.0
    |>.set! 2 2.25
    |>.set! 3 (-1.0)
    |>.set! 4 1.5
    |>.set! 5 0.5
    |>.set! 6 (-3.0)
    |>.set! 7 4.0
  requireArrays "motorMul mixed coefficients"
    (PGA3Kernel.motorMul a b)
    (MV.mulKernelPGA3EvenEven a b)
    0.0
  requireArrays "motorMul mixed coefficients versus table"
    (PGA3Kernel.motorMul a b)
    (MV.mulKernelEvenEven 4 EvenMV.Kernel.evenMulSignPGA3 a b)
    0.0
  requireArrays "evenOddMul mixed coefficients versus direct"
    (PGA3Kernel.evenOddMul a b)
    (MV.mulKernelDirect PGA3 .even .odd a b)
    0.0
  requireArrays "evenOddMul mixed coefficients versus generic"
    (PGA3Kernel.evenOddMul a b)
    (MV.mulKernelGeneric PGA3 .even .odd a b)
  requireArrays "oddEvenMul mixed coefficients versus direct"
    (PGA3Kernel.oddEvenMul a b)
    (MV.mulKernelDirect PGA3 .odd .even a b)
    0.0
  requireArrays "oddEvenMul mixed coefficients versus generic"
    (PGA3Kernel.oddEvenMul a b)
    (MV.mulKernelGeneric PGA3 .odd .even a b)
  requireArrays "motorSandwichOdd mixed coefficients versus composed"
    (PGA3Kernel.motorSandwichOdd a b)
    (composedMotorSandwichOdd a b)
    0.0
  let packedMotor :=
    (MV.ofDataArray? PGA3 .even a).getD (MV.zero PGA3 .even)
  let packedOdd :=
    (MV.ofDataArray? PGA3 .odd b).getD (MV.zero PGA3 .odd)
  requireArrays "mvSandwich mixed coefficients versus composed"
    (mvSandwich packedMotor packedOdd).coeffs
    (composedMotorSandwichOdd a b)
    0.0

private def checkTranslation : IO Unit := do
  let expected : Coord3 := (5.0, 7.0, 9.0)
  let kernelMotor := PGA3Kernel.translator 1.0 2.0 3.0
  let kernelPoint := PGA3Kernel.point 4.0 5.0 6.0
  let kernelResult := PGA3Kernel.motorApplyPoint kernelMotor kernelPoint
  let kernelCoords := PGA3Kernel.pointCoordinates kernelResult
  let highMotor := PGA.translator3 1.0 2.0 3.0
  let highPoint := PGA.point3 4.0 5.0 6.0
  let highResult := PGA.Motor.transformPoint highMotor highPoint
  let highCoords := PGA.extractPoint3 highResult
  requireCoords "translation kernel versus Euclidean target" kernelCoords expected
  requireCoords "translation high-level versus Euclidean target" highCoords expected
  requireCoords "translation kernel versus high-level" kernelCoords highCoords
  requireArrays "translation packed point versus high-level"
    kernelResult highResult.toMV.coeffs

private def checkAxisRotation
    (label : String)
    (axisX axisY axisZ : Float)
    (pointX pointY pointZ : Float)
    (expected : Coord3) : IO Unit := do
  let angle := pi / 2.0
  let kernelMotor := PGA3Kernel.rotor axisX axisY axisZ angle
  let kernelPoint := PGA3Kernel.point pointX pointY pointZ
  let kernelResult := PGA3Kernel.motorApplyPoint kernelMotor kernelPoint
  let kernelCoords := PGA3Kernel.pointCoordinates kernelResult
  let highMotor := PGA.motor3 axisX axisY axisZ angle
  let highPoint := PGA.point3 pointX pointY pointZ
  let highResult := PGA.Motor.transformPoint highMotor highPoint
  let highCoords := PGA.extractPoint3 highResult
  requireCoords s!"{label} kernel versus right-handed target" kernelCoords expected
  requireCoords s!"{label} high-level versus right-handed target" highCoords expected
  requireCoords s!"{label} kernel versus high-level" kernelCoords highCoords
  requireArrays s!"{label} packed point versus high-level"
    kernelResult highResult.toMV.coeffs

private def checkComposition : IO Unit := do
  let angle := pi / 2.0
  let expected : Coord3 := (1.0, 3.0, 3.0)
  -- `after * before`: rotate (1, 0, 0) to (0, 1, 0), then translate.
  let kernelBefore := PGA3Kernel.rotor 0.0 0.0 1.0 angle
  let kernelAfter := PGA3Kernel.translator 1.0 2.0 3.0
  let kernelComposed := PGA3Kernel.motorMul kernelAfter kernelBefore
  let kernelPoint := PGA3Kernel.point 1.0 0.0 0.0
  let kernelComposedResult :=
    PGA3Kernel.motorApplyPoint kernelComposed kernelPoint
  let kernelSequentialResult :=
    PGA3Kernel.motorApplyPoint kernelAfter
      (PGA3Kernel.motorApplyPoint kernelBefore kernelPoint)
  let kernelComposedCoords := PGA3Kernel.pointCoordinates kernelComposedResult
  let kernelSequentialCoords := PGA3Kernel.pointCoordinates kernelSequentialResult
  let highBefore := PGA.motor3 0.0 0.0 1.0 angle
  let highAfter := PGA.translator3 1.0 2.0 3.0
  let highComposed := PGA.Motor.compose highAfter highBefore
  let highPoint := PGA.point3 1.0 0.0 0.0
  let highComposedResult := PGA.Motor.transformPoint highComposed highPoint
  let highSequentialResult :=
    PGA.Motor.transformPoint highAfter
      (PGA.Motor.transformPoint highBefore highPoint)
  let highComposedCoords := PGA.extractPoint3 highComposedResult
  let highSequentialCoords := PGA.extractPoint3 highSequentialResult
  requireCoords "composition kernel versus Euclidean target"
    kernelComposedCoords expected
  requireCoords "composition kernel versus sequential kernel"
    kernelComposedCoords kernelSequentialCoords
  requireCoords "composition high-level versus Euclidean target"
    highComposedCoords expected
  requireCoords "composition high-level versus sequential high-level"
    highComposedCoords highSequentialCoords
  requireCoords "composition kernel versus high-level"
    kernelComposedCoords highComposedCoords
  requireArrays "composition packed motor versus high-level"
    kernelComposed highComposed.toMV.coeffs
  requireArrays "composition packed point versus high-level"
    kernelComposedResult highComposedResult.toMV.coeffs

def run : IO Unit := do
  checkMotorMulBasis
  checkTranslation
  checkComposition
  checkAxisRotation "+90 degrees around x" 1.0 0.0 0.0
    0.0 1.0 0.0 (0.0, 0.0, 1.0)
  checkAxisRotation "+90 degrees around y" 0.0 1.0 0.0
    0.0 0.0 1.0 (1.0, 0.0, 0.0)
  checkAxisRotation "+90 degrees around z" 0.0 0.0 1.0
    1.0 0.0 0.0 (0.0, 1.0, 0.0)
  IO.println "PGA3 Init-only kernel regression tests passed"

end Grassmann.PGA3KernelTests

def main : IO Unit := Grassmann.PGA3KernelTests.run

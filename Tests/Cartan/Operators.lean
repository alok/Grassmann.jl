import Tests.Cartan.Common
import Cartan.Operator

/-!
# Operator-, couple- and phasor-valued fields (`oracle/golden/cartan/element/operators.json`)

Fields over `TensorField(0:0.25:1)` (generator `oracle/cartan/element/operators.jl`): the
endomorphism field `E(x) = [1+x -x; x² 2]` (columns `(1+x, x²)`, `(-x, 2)`), the diagonal field
`D(x) = diag(1+x, 2x)`, the outermorphism of `E`, the couple field `cos x + sin x·v₁₂` and its
polar form, and the complex field `x + 2x·i`. Julia's own `cos`/`sin` (`JuliaBase.F64`) make the
couples bit-exact; eigenvalues (LAPACK in Julia, `Forms.Eigen` here) are compared to `1e-12`.
-/

open Lean Tests.Small Cartan JuliaBase Grassmann DirectSum StaticVectors

namespace Tests.CartanTests.Operators

/-- The base `TensorField(0:0.25:1)`. -/
def ax : Axis := Axis.colon 0 0.25 1

/-- `E(x)`. -/
def E : TensorField (GridBundle.ofAxis ax) (Endomorphism ℝ2 (.chain 1) Float) :=
  TensorField.ofAxisFn ax fun x => TensorOperator.ofFn fun i j =>
    if j.1 = 0 then (if i.1 = 0 then 1 + x else x * x) else (if i.1 = 0 then -x else 2)

/-- `D(x)`. -/
def D : TensorField (GridBundle.ofAxis ax) (DiagonalMorphism ℝ2 Float) :=
  TensorField.ofAxisFn ax fun x => ⟨Values.ofFn fun i => if i.1 = 0 then 1 + x else 2 * x⟩

/-- `cos x + sin x·v₁₂`. -/
def C : TensorField (GridBundle.ofAxis ax) (Couple ℝ2 Float) :=
  TensorField.ofAxisFn ax fun x => ⟨3, F64.cos x, F64.sin x⟩

/-- `x + 2x·i`. -/
def Z : TensorField (GridBundle.ofAxis ax) (Complex Float) :=
  TensorField.ofAxisFn ax fun x => ⟨x, 2 * x⟩

/-- `[0 -1; 1 x]` (complex eigenvalues for `|x| < 2`). -/
def E3 : TensorField (GridBundle.ofAxis ax) (Endomorphism ℝ2 (.chain 1) Float) :=
  TensorField.ofAxisFn ax fun x => TensorOperator.ofFn fun i j =>
    if j.1 = 0 then (if i.1 = 0 then 0 else 1) else (if i.1 = 0 then -1 else x)

/-- Compare float arrays to a relative tolerance (absolute near zero). -/
def checkClose (label : String) (got want : FloatArray) (rtol : Float := 1e-12) : TestM Unit := do
  if got.size != want.size then
    check label false fun _ => s!"length {got.size}, expected {want.size}"
    return
  let bad := (List.range got.size).find? fun i =>
    let x := got[i]!
    let y := want[i]!
    !((x - y).abs ≤ rtol * (F64.max x.abs y.abs) + 1e-14)
  match bad with
  | none => check label true
  | some i => check label false fun _ => s!"[{i}] got {fmt got[i]!}, expected {fmt want[i]!}"

/-- Run the checks. -/
def run : TestM Unit := do
  let g ← load "element/operators"
  let fl (k : String) : TestM FloatArray := do gFloats (← jField g k)
  checkFloats "ops E" E.data (← fl "E")
  checkFloats "ops det E" E.det.data (← fl "detE")
  checkFloats "ops tr E" E.tr.data (← fl "trE")
  checkFloats "ops transpose E" E.transpose.data (← fl "transposeE")
  checkFloats "ops inv E" E.invOp.data (← fl "invE")
  checkFloats "ops DiagonalOperator E" E.diagonal.data (← fl "diagE")
  checkClose "ops eigvals E" E.eigvalscomplex.data (← fl "eigE")
  checkClose "ops eigvals E3" E3.eigvalscomplex.data (← fl "eigE3")
  checkFloats "ops D" D.data (← fl "D")
  checkFloats "ops det D" D.detDiag.data (← fl "detD")
  checkFloats "ops tr D" D.trDiag.data (← fl "trD")
  let O := E.outermorphism
  checkFloats "ops outermorphism E" O.data (← fl "O") prods
  checkFloats "ops det O" O.detOuter.data (← fl "detO")
  checkFloats "ops tr O" O.trOuter.data (← fl "trO")
  checkFloats "ops C" C.data (← fl "C")
  let P := C.polarize
  checkFloats "ops polarize" P.data (← fl "polarize") libm
  let Cc := P.complexify
  checkFloats "ops complexify" (flatOf (Cc.fiberArray.toList.map fun z => Complex.mk z.re z.im))
    (← fl "complexify") libm
  checkFloats "ops vectorize" C.vectorize.data (← fl "vectorize")
  checkFloats "ops radius" C.radius.data (← fl "radius") libm
  checkFloats "ops angle" (flatOf (C.angleC.fiberArray.toList.map (·.val))) (← fl "angle") libm
  checkFloats "ops realvalue" C.realvalue.data (← fl "realvalue")
  checkFloats "ops imagvalue" C.imagvalue.data (← fl "imagvalue")
  checkFloats "ops amplitude" P.amplitude.data (← fl "amplitude") libm
  checkFloats "ops vectorize complex" Z.vectorizeC.data (← fl "vectorizeZ")
  let sh ← jField g "show"
  checkStr "ops show E[2]" (showFiber false (E.get 1)) (← jField sh "E2")
  checkStr "ops show C[2]" (showFiber false (C.get 1)) (← jField sh "C2")
  checkStr "ops show O[2]" (showFiber false (O.get 1)) (← jField sh "O2")
  checkStr "ops show D[2]" (showFiber false (D.get 1)) (← jField sh "D2")
  -- round trips of the blade encodings
  check "ops couple read-back" (C.fiberArray.toList.all fun z => z.bits == 3)
  check "ops phasor read-back" (P.fiberArray.toList.all fun z => z.angle.bits == 3)
  -- flat linear algebra of operator fields agrees with the pointwise operations
  let s := E + E
  check "ops E + E" ((List.range 5).all fun i =>
    (s.get i).mat.v.toList == ((E.get i).mat.v.toList.map fun x => x + x))

end Tests.CartanTests.Operators

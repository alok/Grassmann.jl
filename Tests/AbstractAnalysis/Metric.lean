import AbstractAnalysis
import Tests.AbstractAnalysis.Harness

/-!
Oracle tests for norms, residuals and convergence predicates
(`oracle/golden/abstractanalysis/metric.json`, 200 random vectors).
-/

open Lean AbstractAnalysis Tests.Golden

namespace Tests.AbstractAnalysis.Metric

/-- Bitwise array comparison. -/
def arrEq (a b : Array Float) : Bool := a.size == b.size && (a.zip b).all fun (x, y) => sameFloat x y

/-- `|x - y|` as the scalar metric. -/
def d (x y : Float) : Float := (x - y).abs

/-- The suite. -/
def suite : TestM Unit := do
  let j ← loadJson "oracle/golden/abstractanalysis/metric.json"
  let mut i := 0
  for r in jArr (jGet j "vectors") do
    i := i + 1
    let x := jFloats (jGet r "x")
    let xs : FloatArray := ⟨x⟩
    check s!"v{i}.residuals" (arrEq (residuals xs d).data (jFloats (jGet r "residuals")))
    check s!"v{i}.lipschitz" (arrEq (lipschitz xs d).data (jFloats (jGet r "lipschitz")))
    checkEq s!"v{i}.isdiverging" (isDiverging x d) (jBool (jGet r "isdiverging"))
    checkEq s!"v{i}.iscauchy" (isCauchy x d) (jBool (jGet r "iscauchy"))
    checkEq s!"v{i}.isincreasing" (isIncreasing x) (jBool (jGet r "isincreasing"))
    checkEq s!"v{i}.isdecreasing" (isDecreasing x) (jBool (jGet r "isdecreasing"))
    checkEq s!"v{i}.ismonotonic" (isMonotonic x) (jBool (jGet r "ismonotonic"))
    check s!"v{i}.supseq" (arrEq (supseq x) (jFloats (jGet r "supseq")))
    check s!"v{i}.infseq" (arrEq (infseq x) (jFloats (jGet r "infseq")))
    checkFloat s!"v{i}.maxabs" (maxabs x) (jFloat (jGet r "maxabs"))
    checkFloat s!"v{i}.minabs" (minabs x) (jFloat (jGet r "minabs"))
    checkFloat s!"v{i}.supnorm" (supnorm xs) (jFloat (jGet r "supnorm"))
    for m in [1, 2, 5] do
      if (jGet r s!"limsup{m}") != .null then
        checkFloat s!"v{i}.limsup{m}" (limsup x m) (jFloat (jGet r s!"limsup{m}"))
        checkFloat s!"v{i}.liminf{m}" (liminf x m) (jFloat (jGet r s!"liminf{m}"))
  let s := jGet j "scalars"
  checkFloat "supnorm(3,5)" (dist (3 : Int) 5) (jFloat (jGet s "supnorm_3_5"))
  checkFloat "supnorm(-2.5)" (supnorm (-2.5 : Float)) (jFloat (jGet s "supnorm_m2.5"))
  checkFloat "supnorm([3,4])" (supnorm (#[3, 4] : Array Int)) (jFloat (jGet s "supnorm_34"))
  checkFloat "infnorm([3.0,4.0])" (infnorm (⟨#[3.0, 4.0]⟩ : FloatArray)) (jFloat (jGet s "infnorm_34"))
  checkFloat "maxabs" (maxabs (#[1, -5, 3] : Array Int)) (jFloat (jGet s "maxabs"))
  checkFloat "minabs" (minabs (#[1, -5, 3] : Array Int)) (jFloat (jGet s "minabs"))
  checkFloat "supnorm(a,b)" (dist (⟨#[1.0, 2.0]⟩ : FloatArray) ⟨#[4.0, 6.0]⟩) (jFloat (jGet s "supnorm_vec_diff"))
  checkFloat "derivative step" derivativeStep (jFloat (jGet j "h1"))
  checkFloat "derivative2 step" 1.220703125e-4 (jFloat (jGet j "h2"))
  for r in jArr (jGet j "derivatives") do
    let name := jStr (jGet r "name")
    let f : Float → Float := match name with
      | "sin" => Float.sin
      | "exp" => JuliaBase.F64.exp
      | _ => fun x => x * x * x
    -- Julia's own `exp` is `JuliaBase.F64.exp`, bit for bit; `sin` is still the C `libm`
    let rtol := if jBool (jGet r "libm") && name != "exp" then 1e-9 else 0
    let xs := jFloats (jGet r "x")
    let d1 := jFloats (jGet r "d1")
    let d2 := jFloats (jGet r "d2")
    for k in [0:xs.size] do
      checkFloat s!"{name}.derivative({xs[k]!})" (derivative f xs[k]!) d1[k]! rtol
      checkFloat s!"{name}.derivative2({xs[k]!})" (derivative2 f xs[k]!) d2[k]! (if rtol == 0 then 0 else 1e-6)

end Tests.AbstractAnalysis.Metric

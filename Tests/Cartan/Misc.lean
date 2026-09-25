import Tests.Cartan.Field2d
import Tests.Cartan.Mesh

/-!
# Utilities (`oracle/golden/cartan/misc.json`)

`besseljzero`, `spacing` (1-D, per axis and N-D), `interval_scale`, `affinepoint`, `⧺`,
`graphbundle` and `discontinuous` of a simplex field.
-/

open Lean Tests.Small Cartan JuliaBase Grassmann

namespace Tests.CartanTests.MiscTests

/-- Run the utility checks. -/
def run : TestM Unit := do
  let c ← jField (← load "misc") "cases"
  checkFloat "misc besseljzero(0,1)" (besseljzero 0 1) (← jField c "besseljzero(0,1)")
  checkFloat "misc besseljzero(2,3)" (besseljzero 2 3) (← jField c "besseljzero(2,3)")
  let p := TensorField.ofAxisFn (Axis.colon 0 0.25 2) fun x => x * x / 7 - x / 3
  checkFloat "misc spacing(p)" p.spacing1 (← jField c "spacing(p)")
  checkFloat "misc spacing(a)" Field2d.a.spacing (← jField c "spacing(a)")
  checkFloat "misc spacing(v)" Field2d.v.spacing (← jField c "spacing(v)")
  checkFloat "misc spacing(a,1)" (Field2d.a.spacingAxis 0) (← jField c "spacing(a,1)")
  checkFloat "misc spacing(a,2)" (Field2d.a.spacingAxis 1) (← jField c "spacing(a,2)")
  checkFloat "misc interval_scale(t)" (GridBundle.ofAxis (Axis.colon 0 0.25 2)).intervalScale1
    (← jField c "interval_scale(t)")
  checkFloats "misc interval_scale(g2)" (flatOf Field2d.g.intervalScale.toList) (← gFloats (← jField c "interval_scale(g2)"))
  let ap := (Field2d.ps.point 5).homogeneous
  checkFloats "misc affinepoint" (flatOf [ap]) (← gFloats (← jField c "affinepoint"))
  checkStr "misc affinepoint show" (showFiber false ap) (← jField c "affinepoint show")
  let c12 : Chain ℝ2 1 Float := Chain.ofFn fun i => #[1, 2][i.1]!
  let c3 : Chain ℝ1 1 Float := Chain.ofFn fun _ => 3
  checkFloats "misc concat" (flatOf [c12 ⧺ c3]) (← gFloats (← jField c "concat"))
  let ⟨_, gb⟩ := Mesh.tf.graphBundle
  checkField "misc graphbundle" (out gb) (← jField c "graphbundle")
  let ⟨_, dt⟩ := Mesh.tf.disconnect
  checkField "misc discontinuous" (out dt) (← jField c "discontinuous")

end Tests.CartanTests.MiscTests

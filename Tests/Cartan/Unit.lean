import Tests.Cartan.Common

/-!
# Unit checks of the Cartan API

The module-documentation example (it must keep compiling), static types of results, and a few
facts that the kernel checks at compile time.
-/

open Lean Tests.Small Cartan JuliaBase Grassmann

namespace Tests.CartanTests.Unit

/-- Julia `t = TensorField(0:0.25:2)`. -/
def t := TensorField.ofAxis (Axis.colon 0 0.25 2)
/-- A 4×5 grid. -/
def g := GridBundle.ofSpace (.ofAxes #v[Axis.colon 0 0.5 1.5, Axis.colon 0 0.25 1])
/-- Julia `v = (x -> Chain(x[1], x[2], 1.0)).(TensorField(g))`. -/
def v : TensorField g (Chain ℝ3 1 Float) :=
  .tabulatePoint g fun x => Chain.ofFn fun i => #[x.get! 0, x.get! 1, 1.0][i.1]!
/-- Julia `TorusParameter(60, 60)`. -/
def T := Cartan.Parameter.torus #v[60, 60]

/-! Static result types: the grade arithmetic of the Grassmann layer, lifted. -/

example : TensorField g (Chain ℝ3 2 Float) := v ∧ v
example : TensorField g (Chain ℝ3 3 Float) := v ∧ ⋆v
example : TensorField g (Spinor ℝ3 Float) := v * v
example : TensorField g (Chain ℝ3 0 Float) := v ⋅ v
example : TensorField g (Chain ℝ3 1 Float) := v × v
example : TensorField g Float := v.norm
example : TensorField (GridBundle.ofAxis (Axis.colon 0 0.25 2)) Float := t.sin + t

/-! Sizes and shapes the kernel computes. -/

example : card (GridBundle.ofAxis (Axis.oneTo 5)) = 5 := by
  rw [GridBundle.card_ofAxis]; rfl
example : card (GridBundle.ofSpace (.ofAxes #v[Axis.oneTo 3, Axis.oneTo 4])) = 12 := by
  simp [GridBundle.card_ofSpace, ProductSpace.length, ProductSpace.size, ProductSpace.ofAxes,
    MeshTopology.gridLength, Axis.length, Axis.oneTo]
example : FlatFiber.width (Chain ℝ3 2 Float) = 3 := by decide
example : FlatFiber.width (Multivector ℝ4 Float) = 16 := by decide

/-- Run the unit checks. -/
def run : TestM Unit := do
  checkEq "t.sin + t at 2" ((t.sin + t).get 2) (Float.sin 0.5 + 0.5)
  check "(v ∧ ⋆v) at 5" (toString ((v ∧ ⋆v).localAt 5) == "0.5v₂ + 0.25v₃ ↦ 1.3125v₁₂₃")
    fun _ => toString ((v ∧ ⋆v).localAt 5)
  check "v(0.3, 0.6)" (toString (v.eval2 0.3 0.6) == "0.3v₁ + 0.6v₂ + 1.0v₃")
    fun _ => toString (v.eval2 0.3 0.6)
  checkEq "TorusParameter(60,60) size" (BaseShape.shape T.base) [60, 60]
  checkEq "torus seam: first point = last point" (T.get 0).coords.toList.head! 0
  check "torus glued" T.immersion.isCompact
  let ⟨b', w⟩ : AnyField (GridBundle 2 (AffinePoint 2)) (Chain ℝ3 1 Float) := ⟨g, v⟩
  checkEq "AnyField keeps its base" (card b') 20
  checkEq "AnyField keeps its field" (w.get 3).v.toList (v.get 3).v.toList

end Tests.CartanTests.Unit

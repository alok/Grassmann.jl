import Tests.Cartan.Common
import Cartan.Aliases

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

/-! Julia's field kinds (`Cartan.jl:118-148`) name the same types. -/

example : VectorField g ℝ3 := v
example : BivectorField g ℝ3 := v ∧ v
example : ScalarField g := v.norm
example : RectangleMap g (Chain ℝ3 1 Float) := v
example : RealFunction (GridBundle.ofAxis (Axis.colon 0 0.25 2)) := t
example : SurfaceGrid g := v.norm

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
  -- `map` reads each point into the previous one's storage: the same fibers as reading afresh
  let gT (q : AffinePoint 2) : Chain ℝ3 1 Float :=
    Chain.ofFn fun i => if i.1 = 0 then Float.cos (q.get! 0) else if i.1 = 1 then q.get! 1 else 1
  checkEq "map over points = pointwise" ((T.map gT).fiberArray.toList.map (·.v.toList))
    (T.fiberArray.toList.map fun q => (gT q).v.toList)
  checkEq "map keeping the point" ((T.map id).data.toList) T.data.toList
  -- port notes §4.4, §4.14: `extend(0:0.5:1, 5) == 0.0:0.5:2.0`, `resample(0:0.5:2, 9)`
  match (Axis.colon 0 0.5 1).extend 5 with
  | some e => checkEq "extend(0:0.5:1, 5)" e.toFloatArray.toList (Axis.colon 0 0.5 2).toFloatArray.toList
  | none => check "extend(0:0.5:1, 5)" false
  checkEq "resample(0:0.5:2, 9)" ((Axis.colon 0 0.5 2).resample 9).toFloatArray.toList
    [0, 0.25, 0.5, 0.75, 1, 1.25, 1.5, 1.75, 2]
  -- the materialized range (`stepLenFill`) has the bits of `r[i]` element by element
  for a in [Axis.colon 0 0.1 1, Axis.colon (-1) 0.1 1, Axis.colon 1 (-0.3) (-2),
      Axis.colon 0.1 0.2 5.3, Axis.range 0 10 1000, Axis.range (-piF) piF 61,
      Axis.range 0 twoPiF 100, Axis.range 0.001 1000 777] do
    checkEq s!"collect({a}) bits" (a.toFloatArray.toList.map Float.toBits)
      ((buildFlat a.length a.get).toList.map Float.toBits)
  -- explicit-axes parameters are the size forms on the same axes
  let T' := Parameter.torusOn (Parameter.linSpace (fun _ => 0) (fun _ => twoPiF) #v[60, 60])
  checkEq "TorusParameter(axes) = TorusParameter(60, 60)" T'.data.toList T.data.toList
  check "TorusParameter(axes) glued" T'.immersion.isCompact
  let ps : ProductSpace 2 := .ofAxes #v[Axis.colon (-5) 2 5, Axis.linRange 0 1 7]
  let O := Parameter.openOn ps
  checkEq "OpenParameter(-5:2:5, LinRange(0,1,7)) shape" (BaseShape.shape O.base) [6, 7]
  checkEq "OpenParameter(-5:2:5, …) point 8" (O.get 8).coords.toList [-1, 1 / 6]
  let M := Parameter.mobiusOn (.ofAxes #v[Axis.linRange (-piF) piF 9, Axis.linRange (-1) 1 5])
  checkEq "MobiusParameter(axes) = MobiusParameter(9, 5)" M.data.toList (Parameter.mobius 9 5).data.toList
  let c1 := Parameter.torusOn1 (Axis.linRange 0 twoPiF 13)
  checkEq "TorusParameter(r) = TorusParameter(13)" c1.data.toList (Parameter.torus1 13).data.toList
  check "TorusParameter(r) keeps the range" c1.range?.isSome
  checkEq "codomain = fibers" t.codomain.size 9
  check "no extrinsic metric" (!t.isextrinsic)
  checkEq "show of a range axis" (toString (Axis.colon 0 0.5 2)) "0.0:0.5:2.0"
  checkEq "show of a LinRange axis" (toString (Axis.linRange 0 1 5)) "LinRange{Float64}(0.0, 1.0, 5)"
  checkEq "Global display" (MetricStore.induced.showGlobal 2) "Global{2}(InducedMetric())"
  let t' := (t.set 3 42).set 100 7
  checkEq "set replaces one fiber" t'.fiberArray.toList ((t.fiberArray.set! 3 42).toList)
  let v' := v.set 2 (Chain.ofFn fun _ => 5)
  checkEq "set on a chain field" (v'.get 2).v.toList [5, 5, 5]
  checkEq "set keeps the other fibers" (v'.get 3).v.toList (v.get 3).v.toList
  let ⟨b', w⟩ : AnyField (GridBundle 2 (AffinePoint 2)) (Chain ℝ3 1 Float) := ⟨g, v⟩
  checkEq "AnyField keeps its base" (card b') 20
  checkEq "AnyField keeps its field" (w.get 3).v.toList (v.get 3).v.toList

end Tests.CartanTests.Unit

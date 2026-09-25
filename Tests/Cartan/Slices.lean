import Tests.Cartan.Common

/-!
# Slices, leaves, boundary components and sliced topologies (`slices.json`)

Julia:

```julia
aa = (x -> x[1] + 10x[2]).(TensorField(ProductSpace(0:1.0:3, 0:0.5:1)))
a3 = (x -> x[1] + 10x[2] + 100x[3]).(TensorField(ProductSpace(0:1.0:2, 0:1.0:3, 0:1.0:1)))
M = MobiusParameter(5,7); S = SphereParameter(5,7); B = BallParameter(5,7); T3 = TorusParameter(3,4,5)
```

Indices in the Lean calls are 0-based (Julia `aa[:,2]` is `sliceLine 0 #v[_, 1]`).
-/

open Lean Tests.Small Cartan JuliaBase Grassmann MeshTopology

namespace Tests.CartanTests.Slices

/-- The grid of `aa`. -/
def gaa : GridBundle 2 (AffinePoint 2) := .ofSpace (.ofAxes #v[Axis.colon 0 1 3, Axis.colon 0 0.5 1])
/-- Julia `aa`. -/
def aa : TensorField gaa Float := .tabulatePoint gaa fun x => x.get! 0 + 10 * x.get! 1
/-- The grid of `a3`. -/
def ga3 : GridBundle 3 (AffinePoint 3) :=
  .ofSpace (.ofAxes #v[Axis.colon 0 1 2, Axis.colon 0 1 3, Axis.colon 0 1 1])
/-- Julia `a3`. -/
def a3 : TensorField ga3 Float := .tabulatePoint ga3 fun x => x.get! 0 + 10 * x.get! 1 + 100 * x.get! 2

/-- A sliced topology and its field. -/
structure TopOut where
  /-- The field. -/
  field : FieldOut
  /-- The size of the topology. -/
  size : List Nat
  /-- Julia `p`. -/
  p : Array Nat
  /-- Julia `r`. -/
  r : Array Nat
  /-- Julia `c`. -/
  c : Array Nat

/-- Summarize a sliced grid field. -/
def tout {N : Nat} {P F : Type} [GridPoint N P] [FlatFiber P] [FlatFiber F] {b : GridBundle N P}
    (t : TensorField b F) : TopOut :=
  let (p, _, r) := b.top.toTable
  ⟨out t, b.top.size.toList, p, r, b.top.collapse.toArray.map (if · then 1 else 0)⟩

/-- The sliced parameter fields of the goldens. -/
def tops : List (String × TopOut) :=
  let M := Parameter.mobius 5 7
  let S := Parameter.sphere #v[5, 7]
  let B := Parameter.ball #v[5, 7]
  let T3 := Parameter.torus #v[3, 4, 5]
  [("M[:,4]", tout (M.sliceLine 0 #v[0, 3])), ("M[:,1]", tout (M.sliceLine 0 #v[0, 0])),
   ("M[2,:]", tout (M.sliceLine 1 #v[1, 0])), ("S[:,3]", tout (S.sliceLine 0 #v[0, 2])),
   ("S[2,:]", tout (S.sliceLine 1 #v[1, 0])), ("B[:,3]", tout (B.sliceLine 0 #v[0, 2])),
   ("B[3,:]", tout (B.sliceLine 1 #v[2, 0])), ("T3[:,:,2]", tout (T3.slice #v[0, 1] #v[0, 0, 1])),
   ("T3[2,:,:]", tout (T3.slice #v[1, 2] #v[1, 0, 0])), ("T3[:,3,2]", tout (T3.sliceLine 0 #v[0, 2, 1]))]

/-- Compare a list of golden fields with Lean fields. -/
def checkFields (label : String) (got : Array FieldOut) (want : Json) : TestM Unit := do
  let ws ← jArr want
  check s!"{label} count" (got.size == ws.size) fun _ => s!"got {got.size}, expected {ws.size}"
  for (g, w, i) in (got.toList.zip ws.toList).zipIdx.map (fun ((g, w), i) => (g, w, i)) do
    checkField s!"{label}[{i}]" g w

/-- Run the slice checks. -/
def run : TestM Unit := do
  let c ← jField (← load "slices") "cases"
  checkField "slices aa" (out aa) (← jField c "aa")
  checkField "slices leaf(aa,2)" (out (aa.leaf 1)) (← jField c "leaf(aa,2)")
  checkField "slices leaf(aa,2,1)" (out (aa.leaf 1 0)) (← jField c "leaf(aa,2,1)")
  checkField "slices aa[:,2]" (out (aa.sliceLine 0 #v[0, 1])) (← jField c "aa[:,2]")
  checkField "slices aa[3,:]" (out (aa.sliceLine 1 #v[2, 0])) (← jField c "aa[3,:]")
  checkFields "slices boundarycomponents(aa)" ((aa.boundaryComponents).map (out ·.field))
    (← jField c "boundarycomponents(aa)")
  checkFields "slices boundarycomponents(aa,2)" ((aa.boundaryComponents 1).map (out ·.field))
    (← jField c "boundarycomponents(aa,2)")
  checkFields "slices boundarycomponents(aa,[1,2])" ((aa.boundaryComponentsAt [0, 1]).map (out ·.field))
    (← jField c "boundarycomponents(aa,[1,2])")
  checkField "slices a3" (out a3) (← jField c "a3")
  checkField "slices leaf(a3,2)" (out (a3.leafAt 1)) (← jField c "leaf(a3,2)")
  checkFields "slices boundarycomponents(a3)" ((a3.boundaryComponentsN).map (out ·.field))
    (← jField c "boundarycomponents(a3)")
  checkField "slices a3[2,:,:]" (out (a3.slice #v[1, 2] #v[1, 0, 0])) (← jField c "a3[2,:,:]")
  checkField "slices a3[:,3,:]" (out (a3.slice #v[0, 2] #v[0, 2, 0])) (← jField c "a3[:,3,:]")
  checkField "slices a3[:,:,1]" (out (a3.slice #v[0, 1] #v[0, 0, 0])) (← jField c "a3[:,:,1]")
  checkField "slices a3[:,2,1]" (out (a3.sliceLine 0 #v[0, 1, 0])) (← jField c "a3[:,2,1]")
  checkField "slices leaf(aa,0.3)" (out (aa.leafInterp 0.3)) (← jField c "leaf(aa,0.3)")
  checkField "slices leaf(aa,1.7,1)" (out (aa.leafInterp 1.7 0)) (← jField c "leaf(aa,1.7,1)")
  let p0 := TensorField.ofAxisFn (Axis.colon 0 0.5 1.5) fun x => x * x / 7 - x / 3
  let ob := TensorField.orbit (fun x => x / (2 : Float) + (1 : Float)) p0
    (Axis.ofArray [(0 : Float), 0.5, 1, 1.5].toFloatArray)
  checkField "slices orbit" (out ob) (← jField c "orbit")
  let ex := aa.extract 1
  let jx ← jField c "extract(aa,2)"
  checkFloat "slices extract base" ex.base (← jField jx "base")
  checkField "slices extract fiber" (out ex.fiber) (← jField jx "fiber")
  let jt ← jField c "tops"
  for (name, o) in tops do
    let w ← jField jt name
    let size ← (← jArr (← jField w "size")).mapM jNat
    let p ← (← jArr (← jField w "p")).mapM jNat
    let r ← (← jArr (← jField w "r")).mapM jNat
    let cc ← (← jArr (← jField w "c")).mapM jNat
    check s!"slices {name} size" (o.size == size.toList) fun _ => s!"got {o.size}, expected {size}"
    check s!"slices {name} p" (o.p == p) fun _ => s!"got {o.p}, expected {p}"
    check s!"slices {name} r" (o.r == r) fun _ => s!"got {o.r}, expected {r}"
    check s!"slices {name} c" (o.c == cc) fun _ => s!"got {o.c}, expected {cc}"
    checkField s!"slices {name} field" o.field (← jField w "field")
  -- `assign!` along the last axis: `leafAt` then `assignLeaf` is the identity, and a new slice
  -- lands in its contiguous block
  check "assign! leaf round trip" ((List.range 3).all fun i =>
    ((a3.assignLeaf i (a3.leafAt i)).data.toList.map Float.toBits) == a3.data.toList.map Float.toBits)
  let new : FloatArray := ⟨(Array.range 12).map fun k => Float.ofNat k + 0.5⟩
  let a3' := a3.assignLast 1 new
  checkEq "assign! slice 1" (a3'.leafAt 1).data.toList new.toList
  checkEq "assign! keeps slice 0" (a3'.leafAt 0).data.toList (a3.leafAt 0).data.toList
  checkEq "assign! wrong size is a no-op" (a3.assignLast 1 ⟨#[1, 2]⟩).data.toList a3.data.toList
  -- fields of leaves (`element/variation.json`): Variation, alteration, modification
  let gv ← load "element/variation"
  let av : TensorField gaa Float := .tabulatePoint gaa fun x =>
    x.get! 0 + 10 * x.get! 1 + x.get! 0 * x.get! 1
  for (name, ls) in [("variation", av.variation), ("alteration", av.alteration),
      ("modification", av.modification)] do
    let j ← jField gv name
    checkFloats s!"{name} base" ⟨ls.map (·.base)⟩ (← gFloats (← jField j "base"))
    let jl ← jArr (← jField j "leaves")
    check s!"{name} leaves" (jl.size == ls.size)
    for (l, k) in ls.toList.zipIdx do
      let w := jl[k]!
      checkFloats s!"{name} leaf {k} base" l.fiber.base.space.coords[0] (← gFloats (← jField w "base"))
      checkFloats s!"{name} leaf {k} fiber" l.fiber.field.data (← gFloats (← jField w "fiber"))

end Tests.CartanTests.Slices

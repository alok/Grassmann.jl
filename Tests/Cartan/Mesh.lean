import Tests.Cartan.Field2d
import Tests.Cartan.Field1d

/-!
# Simplex bundles, face bundles and display (`simplex.json`, `display.json`)

Julia (the mesh):

```julia
pts = [Chain{varmanifold(3)}(1.0, x, y) for (x, y) in ((0,0), (1,0), (0,1), (1,1), (2,0.5))]
st = SimplexTopology(0, [Values(1,2,3), Values(2,4,3), Values(2,5,4)]);  sb = PointCloud(pts)(st)
```

The display goldens cover `LocalTensor`, `Coordinate` (with the induced and a stored metric),
`ProductSpace` and field elements (non-compact and compact).
-/

open Lean Tests.Small Cartan JuliaBase Grassmann MeshTopology

namespace Tests.CartanTests.Mesh

/-- A homogeneous point `(1, x, y)` (Julia `Chain{varmanifold(3)}(1.0, x, y)`). -/
def hp (x y : Float) : Chain ℝ3 1 Float := Chain.ofFn fun i => #[1, x, y][i.1]!

/-- Julia `sb`. -/
def sb : SimplexBundle 3 (Chain ℝ3 1 Float) :=
  .ofPoints #[hp 0 0, hp 1 0, hp 0 1, hp 1 1, hp 2 0.5] #[#v[1, 2, 3], #v[2, 4, 3], #v[2, 5, 4]]

/-- Julia `tf = TensorField(sb, [1.0, 2.0, 3.0, 4.0, 5.0])`. -/
def tf : TensorField sb Float := (TensorField.ofArray? sb #[(1 : Float), 2, 3, 4, 5]).get!

/-- Julia `FaceBundle(sb)`. -/
def fb : FaceBundle 3 (Chain ℝ3 1 Float) := .ofSimplex sb

/-- Julia `sb(st[[2, 3]])`. -/
def sub : SimplexBundle 3 (Chain ℝ3 1 Float) := sb.getSub #[2, 3]

/-- Run the mesh checks. -/
def runMesh : TestM Unit := do
  let c ← jField (← load "simplex") "cases"
  checkField "simplex tf" (out tf) (← jField c "tf")
  checkField "simplex sin(tf)" (out tf.sin) (← jField c "sin(tf)") libm
  checkField "simplex tf*tf" (out (tf * tf)) (← jField c "tf*tf")
  checkFloats "simplex face points" (FrameBundle.pointsFlat fb) (← gFloats (← jField c "face_points"))
  checkField "simplex face field" (out ((TensorField.ofArray? fb #[(10 : Float), 20, 30]).get!)) (← jField c "face_field")
  checkFloats "simplex sub points" (FrameBundle.pointsFlat sub) (← gFloats (← jField c "sub_points"))
  let size ← (← jArr (← jField c "sub_size")).mapM jNat
  check "simplex sub size" ([card sub] == size.toList) fun _ => s!"got {card sub}"
  checkField "simplex sub field" (out ((TensorField.ofArray? sub #[(7 : Float), 8, 9, 10]).get!)) (← jField c "sub_field")
  checkStr "simplex elem2" (toString (tf.localAt 1)) (← jField c "elem2")
  let fp := FiberProductBundle.ofBase sb (Axis.colon 0 0.5 1)
  let fsize ← (← jArr (← jField c "fiberproduct_size")).mapM jNat
  check "fiberproduct size" (BaseShape.shape fp == fsize.toList) fun _ => s!"got {BaseShape.shape fp}"
  checkFloats "fiberproduct points" (FrameBundle.pointsFlat fp) (← gFloats (← jField c "fiberproduct_points"))
  checkStr "fiberproduct elem" (toString (FrameBundle.coordinate fp (1 + 2 * 5)))
    (← jField c "fiberproduct_elem")
  checkFloats "timeparameter" (timeParameter sb (Axis.colon 0 0.5 1)).data
    (← gFloats (← jField c "timeparameter"))
  let tpf := timeParameterOn sb #[2, 3, 4] (Axis.colon 0 0.25 1)
  checkFloats "timeparameter fixed" tpf.data (← gFloats (← jField c "timeparameter_fixed"))
  let tsize ← (← jArr (← jField c "timeparameter_fixed_size")).mapM jNat
  check "timeparameter fixed size" (BaseShape.shape tpf.base == tsize.toList)

/-- `ProductSpace(0:0.5:1, 0:1.0:2)`. -/
def ps32 : ProductSpace 2 := .ofAxes #v[Axis.colon 0 0.5 1, Axis.colon 0 1 2]

/-- Julia `PointArray(0, 0:0.5:1, [2.0, 3.0, 4.0])`. -/
def pa : GridBundle 1 Float Float := (GridBundle.ofAxis (Axis.colon 0 0.5 1)).withMetric? #[(2 : Float), 3, 4] |>.get!

/-- Run the display checks. -/
def runDisplay : TestM Unit := do
  let c ← jField (← load "display") "cases"
  let c12 : Chain ℝ2 1 Float := Chain.ofFn fun i => #[1, 2][i.1]!
  let c34 : Chain ℝ2 1 Float := Chain.ofFn fun i => #[3, 4][i.1]!
  let lt := LocalTensor.mk (Coordinate.induced c12) c34
  checkStr "display LocalTensor(1.0,2.0)" (toString (LocalTensor.mk (1 : Float) (2 : Float)))
    (← jField c "LocalTensor(1.0,2.0)")
  checkStr "display LT(Coord(Chain),Chain)" (toString lt) (← jField c "LT(Coord(Chain),Chain)")
  checkStr "display LT compact" (showFiber true lt) (← jField c "LT(Coord(Chain),Chain) compact")
  checkStr "display Coordinate(Chain)" (toString (Coordinate.induced c12)) (← jField c "Coordinate(Chain)")
  checkStr "display Coordinate(1.0,3.0)" (toString (Coordinate.mk (1 : Float) (3 : Float)))
    (← jField c "Coordinate(1.0,3.0)")
  checkStr "display LT(Coordinate(1.0,3.0),1.0)"
    (toString (LocalTensor.mk (Coordinate.mk (1 : Float) (3 : Float)) (1 : Float)))
    (← jField c "LT(Coordinate(1.0,3.0),1.0)")
  checkStr "display ProductSpace 2D" (toString ps32) (← jField c "ProductSpace 2D")
  checkStr "display ProductSpace 1D" (toString (ProductSpace.ofAxes #v[Axis.colon 0 0.5 2]))
    (← jField c "ProductSpace 1D")
  checkStr "display t[2]" (toString ((TensorField.ofAxis (Axis.colon 0 0.5 2)).localAt 1)) (← jField c "t[2]")
  let e := (TensorField.ofSpace ps32).localAt 7
  checkStr "display tf 2D [2,3]" (toString e) (← jField c "tf 2D [2,3]")
  checkStr "display tf 2D [2,3] compact" (showFiber true e) (← jField c "tf 2D [2,3] compact")
  checkStr "display v[2,3]" (toString (Field2d.v.localAt 9)) (← jField c "v[2,3]")
  checkStr "display v[2,3] compact" (showFiber true (Field2d.v.localAt 9)) (← jField c "v[2,3] compact")
  checkStr "display q[2,3]" (toString (Field2d.q.localAt 9)) (← jField c "q[2,3]")
  checkStr "display (v∧w)[2,3]" (toString ((Field2d.v ∧ Field2d.w).localAt 9)) (← jField c "(v∧w)[2,3]")
  checkStr "display z[2]" (toString (Field1d.z.localAt 1)) (← jField c "z[2]")
  checkStr "display pointwise metric base[2]" (toString (FrameBundle.coordinate pa 1))
    (← jField c "pointwise metric base[2]")
  let tfm : TensorField pa Float := (TensorField.ofArray? pa #[(1 : Float), 2, 3]).get!
  checkStr "display pointwise metric tfm[2]" (toString (tfm.localAt 1)) (← jField c "pointwise metric tfm[2]")
  let T := Parameter.torus #v[4, 5]
  checkStr "display T[1]" (toString (T.localAt 0)) (← jField c "T[1]")
  checkStr "display T[7]" (toString (T.localAt 6)) (← jField c "T[7]")
  checkStr "display sb[2]" (toString (FrameBundle.coordinate sb 1)) (← jField c "sb[2]")

/-- Run the mesh and display checks. -/
def run : TestM Unit := do
  runMesh
  runDisplay

end Tests.CartanTests.Mesh

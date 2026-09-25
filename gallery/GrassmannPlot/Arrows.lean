import GrassmannPlot.Surfaces

/-!
# Vector fields and frames: `arrows`, `arrows2d`, `arrows3d`, `scaledarrows`, `arrowsbundle`,
`planes`, `spaces` and their scaled and bundle forms, `graylines`

Cartan's methods (`ext/MakieExt.jl:34-58, 227-428, 562-597`, `src/Cartan.jl:906-982`):

* `arrows(t::VectorField)` draws `arrows2d`, or `arrows3d` when the fiber is 3-D; the arrows start
  at the base points (`arrows2d(f over GridBundle) = arrows2d(Point.(points(t)), Point.(fiber(t)))`),
  or at the fibers of a first field (`arrows(M, t)`: the points of an embedding `M`);
* `scaledarrows(M, t)`: `lengthscale = s/3` with `s = spacing(M)/(Σ|t|/n)`
  (`spacing`: `Cartan.TensorField.spacing`), after `gridargs` (`gridsize` resamples both fields);
* frames (Julia `TensorOperator` fibers, one arrow set per column) are given as an array of
  column fields: `scaledarrows(M, cols)` uses `s = spacing(M)/max(Σ|col|/n)`;
* `arrowsbundle(M, t)`: `scatter(fiber(M))` and arrows of `t` and `-t` with `lengthscale = s/2`;
* `planes`/`spaces`: per point the oriented parallelogram(s) `p + [0 v₁+v₂; v₁ v₂]` of two (three
  pairs of) frame columns, as 2×2 grid meshes (`_orientedplane`, `Cartan.jl:907`), then a black
  `scatter!` of the points; `planesbundle`/`spacesbundle` the centred parallelograms
  `p + [-v₁-v₂ v₁+v₂; v₁-v₂ v₂-v₁]` (`_unorientedplane`, `Cartan.jl:906`) and arrows of `Σ cols`;
  their scaled forms use `s = spacing(M)/min(Σ|col|/n)` and `lengthscale = s/2`.

Fixes of upstream defects: `planesbundle` reads the undefined `M`, `t` (B4; here its own
arguments); `orientedplane`/`unorientedplane` build their 2×2 fields over `OpenParameter(2,2)`,
which throws in Cartan 0.4.16 (B2; here the intended grid). `arrows3d` is drawn as Makie's
shaded shaft cylinders and tip cones (`Recipes.Algo.Arrows.placements3d`), each coloured by
`shaftcolor`/`tipcolor` or by the arrow's value.
-/

namespace GrassmannPlot

open LeanPlot Cartan MeshTopology
open LeanPlot.Recipes.Algo

/-! ## 3-D arrows as meshes -/

/-- Makie `arrows3d(origins, directions)`: shaded shaft cylinders and tip cones (Makie's
`meshscatter` markers placed by `Arrows.placements3d`, with `align`, `lengthscale`,
`normalize`), shafts in `shaftcolor`, tips in `tipcolor` (both default to `color`, black). A
colour given as values gives every arrow's markers its value. -/
def drawArrows3d (c : Canvas) (o d : Pts3) (a : Attrs) : Canvas :=
  let (starts, ends) := Arrows.processArrows 3 o d (.frac a.align) a.lengthscale a.normalize
  let st : Arrows.Style3D := {}
  let pl := Arrows.placements3d st starts ends
  let cyl := Arrows.cylinderMarker st.quality
  let cone := Arrows.coneMarker st.quality
  let build (m : Arrows.NormalMesh) (pick : (Arrows.Metrics × Arrows.Placement × Arrows.Placement × Arrows.Placement) → Arrows.Placement)
      (vals : Option FloatArray) : TriMesh × FloatArray := Id.run do
    let mut xs : FloatArray := .empty
    let mut ys : FloatArray := .empty
    let mut zs : FloatArray := .empty
    let mut cv : FloatArray := .empty
    let mut tri : Array UInt32 := #[]
    let mut k := 0
    for p in pl do
      let base := xs.size
      let (pts, _) := Arrows.placeMarker m (pick p)
      xs := appendFloats xs pts.xs; ys := appendFloats ys pts.ys; zs := appendFloats zs pts.zs
      match vals with
      | some v => for _ in [0:pts.size] do cv := cv.push (v.get! k)
      | none => pure ()
      tri := tri ++ m.mesh.tri.map (· + base.toUInt32)
      k := k + 1
    return ((TriMesh.mk? (Pts3.ofArrays xs ys zs) tri).getD default, cv)
  let valsOf : Option ColorSpec → Option FloatArray
    | some (.values vs _) => some vs
    | _ => none
  let colorFor (spec : Option ColorSpec) (cv : FloatArray) : ColorSpec :=
    match spec with
    | some (.values _ m) => .values cv m
    | some s => s
    | none => .black
  let shaftSpec := a.shaftcolor.orElse fun _ => a.color
  let tipSpec := a.tipcolor.orElse fun _ => a.color
  let (sm, scv) := build cyl (fun (_, _, s, _) => s) (valsOf shaftSpec)
  let (tm, tcv) := build cone (fun (_, _, _, t) => t) (valsOf tipSpec)
  let c := c.drawMesh sm (some (colorFor shaftSpec scv)) true a
  c.drawMesh tm (some (colorFor tipSpec tcv)) true a

/-- Draw arrows from `o` along `d`: `arrows2d`, or `arrows3d` when `dim = 3`. -/
def drawArrowsDim (c : Canvas) (dim : Nat) (o d : Pts3) (a : Attrs) : Canvas :=
  if dim == 3 then drawArrows3d c o d a else c.drawArrows o d (a.color.getD .black) a

/-! ## `arrows` of vector fields -/

section Arrows

variable {N : Nat} {P G F : Type} [Inhabited G] [GridPoint N P] [FlatFiber P] [FlatFiber F]

/-- The base points of a grid field (Julia `Makie.Point.(vec(points(t)))`). -/
def gridBasePoints {b : GridBundle N P G} (_ : TensorField b F) : Pts3 :=
  pointsOf (FrameBundle.pointsFlat (P := P) (G := G) b) (FlatFiber.width P) (card b)

/-- Cartan `gridargs(t, args)` (`Cartan.jl:970-982`): the field resampled to `gridsize`. -/
def gridArgs1 {b : GridBundle N P G} [LinearFiber F] (t : TensorField b F) (a : Attrs) :
    AnyField (GridBundle N P G) F :=
  match a.gridsize with
  | some gs => ⟨_, t.resample (Vector.ofFn fun i => gs.getD i.1 (gs.back?.getD 2))⟩
  | none => ⟨_, t⟩

/-- Julia `arrows2d(f::VectorField over GridBundle)` (`MakieExt.jl:575-586`): arrows from the
base points along the fibers. -/
instance instArrows2dGrid [LinearFiber F] {b : GridBundle N P G} : MakiePlot .arrows2d (TensorField b F) where
  plot c t a :=
    let r := gridArgs1 t a
    c.drawArrows (gridBasePoints r.field) (Field.fiberPoints r.field) (a.color.getD .black) a
  dim _ := 2

/-- Julia `arrows3d(f::VectorField over GridBundle)`. -/
instance instArrows3dGrid [LinearFiber F] {b : GridBundle N P G} : MakiePlot .arrows3d (TensorField b F) where
  plot c t a :=
    let r := gridArgs1 t a
    drawArrows3d c (gridBasePoints r.field) (Field.fiberPoints r.field) a
  dim _ := 3

/-- Julia `arrows(t::VectorField)` (`MakieExt.jl:563-565`): `arrows3d` for 3-D fibers, else
`arrows2d`. -/
instance instArrowsGrid [LinearFiber F] {b : GridBundle N P G} : MakiePlot .arrows (TensorField b F) where
  plot c t a :=
    let r := gridArgs1 t a
    drawArrowsDim c (dimOfWidth (FlatFiber.width F)) (gridBasePoints r.field) (Field.fiberPoints r.field) a
  dim _ := dimOfWidth (FlatFiber.width F)

end Arrows

/-! ## Arrows along an embedding: `arrows(M, t)`, `scaledarrows`, `arrowsbundle` -/

section Embedded

variable {N : Nat} {P G E F : Type} [Inhabited G] [FlatFiber E] [FlatFiber F]
  [LinearFiber E] [LinearFiber F] [FiberNorm E] [FiberNorm F]

/-- Cartan `gridargs(M, t, args)` (`Cartan.jl:956-969`): both fields resampled to `gridsize`. -/
def gridArgs2 {b : GridBundle N P G} (M : TensorField b E) (t : TensorField b F) (a : Attrs) :
    Σ b' : GridBundle N P G, TensorField b' E × TensorField b' F :=
  match a.gridsize with
  | some gs =>
    let n : Vector Nat N := Vector.ofFn fun i => gs.getD i.1 (gs.back?.getD 2)
    ⟨_, M.resample n, t.resample n⟩
  | none => ⟨_, M, t⟩

/-- Cartan `spacing(M)` of a grid field (`Cartan.jl:324-329`): the 1-D mean step for curves, the
least mean step over the axes otherwise. -/
def spacingOf {b : GridBundle N P G} (M : TensorField b E) : Float :=
  if N == 1 then M.spacing1 else M.spacing

/-- `Σ|t|/n` (Julia `sum(fiber(norm(t)))/length(t)`, Julia's pairwise sum). -/
def meanNorm {M : Type} [FrameBundle M] {m : M} (t : TensorField m F) : Float :=
  TensorField.sumF t.norm / (card m).toUInt64.toFloat

/-- Julia `arrows(M::VectorField, t::VectorField)` (`MakieExt.jl:567-570, 587-590`): arrows from
the fiber points of `M` along `t`, `arrows3d` for a 3-D `M`. -/
instance instArrowsPair {b : GridBundle N P G} : MakiePlot .arrows (TensorField b E × TensorField b F) where
  plot c Mt a :=
    let ⟨_, M, t⟩ := gridArgs2 Mt.1 Mt.2 a
    drawArrowsDim c (dimOfWidth (FlatFiber.width E)) (Field.fiberPoints M) (Field.fiberPoints t) { a with gridsize := none }
  dim _ := dimOfWidth (FlatFiber.width E)

/-- The `scaledarrows` length scale `s/3`, `s = spacing(M)/(Σ|t|/n)` (`MakieExt.jl:375-379`). -/
def scaledLengthscale {b : GridBundle N P G} (M : TensorField b E) (t : TensorField b F) : Float :=
  spacingOf M / meanNorm t / 3

/-- Julia `scaledarrows(M::VectorField, t::VectorField)` (`MakieExt.jl:375-379`). -/
instance instScaledArrowsPair {b : GridBundle N P G} : MakiePlot .scaledarrows (TensorField b E × TensorField b F) where
  plot c Mt a :=
    let ⟨_, M, t⟩ := gridArgs2 Mt.1 Mt.2 a
    drawArrowsDim c (dimOfWidth (FlatFiber.width E)) (Field.fiberPoints M) (Field.fiberPoints t)
      { a with gridsize := none, lengthscale := scaledLengthscale M t }
  dim _ := dimOfWidth (FlatFiber.width E)

/-- Julia `scaledarrows(M, t::TensorOperator)` (`MakieExt.jl:380-384, 407-413`) with the frame
given by its columns: `s = spacing(M)/max(Σ|colᵢ|/n)`, one arrow set per column. -/
instance instScaledArrowsFrame {b : GridBundle N P G} :
    MakiePlot .scaledarrows (TensorField b E × Array (TensorField b F)) where
  plot c Mt a :=
    let n : Option (Vector Nat N) := a.gridsize.map fun gs => Vector.ofFn fun i => gs.getD i.1 (gs.back?.getD 2)
    match n with
    | some n =>
      let M := Mt.1.resample n
      let cols := Mt.2.map (·.resample n)
      let s := spacingOf M / cols.foldl (fun m t => JuliaBase.F64.max m (meanNorm t)) 0
      cols.foldl (fun c t => drawArrowsDim c (dimOfWidth (FlatFiber.width E)) (Field.fiberPoints M)
        (Field.fiberPoints t) { a with gridsize := none, lengthscale := s / 3 }) c
    | none =>
      let s := spacingOf Mt.1 / Mt.2.foldl (fun m t => JuliaBase.F64.max m (meanNorm t)) 0
      Mt.2.foldl (fun c t => drawArrowsDim c (dimOfWidth (FlatFiber.width E)) (Field.fiberPoints Mt.1)
        (Field.fiberPoints t) { a with lengthscale := s / 3 }) c
  dim _ := dimOfWidth (FlatFiber.width E)

/-- The negated fiber points (Julia `-t`). -/
def negPoints (p : Pts3) : Pts3 :=
  Pts3.ofArrays (FloatArray.mk (p.xs.data.map (-·))) (FloatArray.mk (p.ys.data.map (-·))) (FloatArray.mk (p.zs.data.map (-·)))

/-- Julia `arrowsbundle(M::VectorField, t::VectorField)` (`MakieExt.jl:290-299`): the points,
then arrows of `t` and of `-t` with `lengthscale = s/2`, `s = spacing(M)/(Σ|t|/n)`. -/
instance instArrowsBundlePair {b : GridBundle N P G} : MakiePlot .arrowsbundle (TensorField b E × TensorField b F) where
  plot c Mt a :=
    let ⟨_, M, t⟩ := gridArgs2 Mt.1 Mt.2 a
    let a := { a with gridsize := none, lengthscale := spacingOf M / meanNorm t / 2 }
    let d := dimOfWidth (FlatFiber.width E)
    let pts := Field.fiberPoints M
    let dirs := Field.fiberPoints t
    let c := c.drawScatter pts none {}
    drawArrowsDim (drawArrowsDim c d pts dirs a) d pts (negPoints dirs) a
  dim _ := dimOfWidth (FlatFiber.width E)

end Embedded

/-! ## Planes and spaces of frames -/

section Planes

variable {N : Nat} {P G E F : Type} [Inhabited G] [FlatFiber E] [FlatFiber F]
  [LinearFiber E] [LinearFiber F] [FiberNorm E] [FiberNorm F]

/-- Julia `_orientedplane(p, v₁, v₂) = p .+ [0 v₁+v₂; v₁ v₂]` (`Cartan.jl:907`) in column-major
order: `p, p+v₁, p+v₁+v₂, p+v₂`. -/
def orientedQuad (p v1 v2 : Vec3) : Array Vec3 := #[p, p + v1, p + (v1 + v2), p + v2]

/-- Julia `_unorientedplane(p, v₁, v₂) = p .+ [-v₁-v₂ v₁+v₂; v₁-v₂ v₂-v₁]` (`Cartan.jl:906`):
`p-v₁-v₂, p+v₁-v₂, p+v₁+v₂, p-v₁+v₂`. -/
def unorientedQuad (p v1 v2 : Vec3) : Array Vec3 :=
  #[p + (-v1 - v2), p + (v1 - v2), p + (v1 + v2), p + (v2 - v1)]

/-- A 2×2 grid mesh (`mesh(TensorField(base(OpenParameter(2,2)), quad))`, one quad `(0,1,2,3)`),
or a polygon (`poly`). -/
def drawQuad (c : Canvas) (q : Array Vec3) (dim : Nat) (a : Attrs) : Canvas :=
  let pts : Pts3 := Pts3.ofArrays ⟨q.map (·.x)⟩ ⟨q.map (·.y)⟩ ⟨q.map (·.z)⟩
  if a.poly then
    c.map2 fun ax => ax.poly pts.xy a.color (label := a.label)
  else drawGridMesh c 2 2 pts dim a.color a

/-- `v * s` for a point. -/
@[inline] def scalePt (s : Float) (v : Vec3) : Vec3 := ⟨s * v.x, s * v.y, s * v.z⟩

/-- The sum of the frame columns at every point (Julia `sum.(value.(value.(fiber(t))))`). -/
def columnSum (cols : Array Pts3) (n : Nat) : Pts3 :=
  let at_ (i : Nat) : Vec3 := cols.foldl (fun s p => s + p.get! i) ⟨0, 0, 0⟩
  let vs := (Array.range n).map at_
  Pts3.ofArrays ⟨vs.map (·.x)⟩ ⟨vs.map (·.y)⟩ ⟨vs.map (·.z)⟩

/-- Julia `planes(M, t; lengthscale = 1, poly = false)` (`MakieExt.jl:329-346`) and
`spaces(M, t)` (`:348-369`) for a frame of two (three) columns: the oriented parallelogram of each
column pair at every point (planes of `v₁v₂`; spaces also `v₁v₃`, `v₂v₃` and the arrows of
`Σ cols` first), then (planes) the points in black. -/
def planesSpaces {b : GridBundle N P G} (c : Canvas) (M : TensorField b E) (cols : Array (TensorField b F))
    (unoriented : Bool) (arrowsFirst : Bool) (scatterAfter : Bool) (a : Attrs) : Canvas :=
  let n := card b
  let d := dimOfWidth (FlatFiber.width E)
  let pts := Field.fiberPoints M
  let cs := cols.map Field.fiberPoints
  let ls := a.lengthscale
  let c := if arrowsFirst then drawArrowsDim c d pts (columnSum cs n) a else c
  let pairs : List (Nat × Nat) := if cs.size ≥ 3 then [(0, 1), (0, 2), (1, 2)] else [(0, 1)]
  let quad := if unoriented then unorientedQuad else orientedQuad
  let c := (List.range n).foldl (init := c) fun c i =>
    let p := pts.get! i
    pairs.foldl (init := c) fun c (j, k) =>
      drawQuad c (quad p (scalePt ls ((cs.getD j default).get! i)) (scalePt ls ((cs.getD k default).get! i))) d
        { a with lengthscale := 1 }
  if scatterAfter then c.drawScatter pts (some (.solid RGBA.black)) {} else c

/-- `min(Σ|colᵢ|/n)` of a frame. -/
def minColumnNorm {M : Type} [FrameBundle M] {m : M} (cols : Array (TensorField m F)) : Float :=
  cols.foldl (fun x t => JuliaBase.F64.min x (meanNorm t)) ((1 : Float) / 0)

/-- Julia `planes(M, t::TensorOperator)` with the frame columns. -/
instance instPlanes {b : GridBundle N P G} : MakiePlot .planes (TensorField b E × Array (TensorField b F)) where
  plot c Mt a := planesSpaces c Mt.1 Mt.2 false false true a
  dim _ := dimOfWidth (FlatFiber.width E)

/-- Julia `spaces(M, t::TensorOperator)` with the frame columns. -/
instance instSpaces {b : GridBundle N P G} : MakiePlot .spaces (TensorField b E × Array (TensorField b F)) where
  plot c Mt a := planesSpaces c Mt.1 Mt.2 false true false a
  dim _ := dimOfWidth (FlatFiber.width E)

/-- Julia `scaledplanes(M, t)` (`MakieExt.jl:321-327`): `planes` with `lengthscale = s/2`,
`s = spacing(M)/min(Σ|colᵢ|/n)`. -/
instance instScaledPlanes {b : GridBundle N P G} : MakiePlot .scaledplanes (TensorField b E × Array (TensorField b F)) where
  plot c Mt a := planesSpaces c Mt.1 Mt.2 false false true { a with lengthscale := spacingOf Mt.1 / minColumnNorm Mt.2 / 2 }
  dim _ := dimOfWidth (FlatFiber.width E)

/-- Julia `scaledspaces(M, t)`: `spaces` with `lengthscale = s/2`. -/
instance instScaledSpaces {b : GridBundle N P G} : MakiePlot .scaledspaces (TensorField b E × Array (TensorField b F)) where
  plot c Mt a := planesSpaces c Mt.1 Mt.2 false true false { a with lengthscale := spacingOf Mt.1 / minColumnNorm Mt.2 / 2 }
  dim _ := dimOfWidth (FlatFiber.width E)

/-- Julia `planesbundle(M, t)` (`MakieExt.jl:247-264`, fixing B4) and `spacesbundle(M, t)`
(`:266-288`): arrows of `Σ cols` and the centred parallelograms, `lengthscale = s/2`,
`s = spacing(M)/min(Σ|colᵢ|/n)`. -/
instance instPlanesBundle {b : GridBundle N P G} : MakiePlot .planesbundle (TensorField b E × Array (TensorField b F)) where
  plot c Mt a := planesSpaces c Mt.1 Mt.2 true true false { a with lengthscale := spacingOf Mt.1 / minColumnNorm Mt.2 / 2 }
  dim _ := dimOfWidth (FlatFiber.width E)

/-- Julia `spacesbundle(M, t)`. -/
instance instSpacesBundle {b : GridBundle N P G} : MakiePlot .spacesbundle (TensorField b E × Array (TensorField b F)) where
  plot c Mt a := planesSpaces c Mt.1 Mt.2 true true false { a with lengthscale := spacingOf Mt.1 / minColumnNorm Mt.2 / 2 }
  dim _ := dimOfWidth (FlatFiber.width E)

/-- Julia `arrowsbundle(M, t::TensorOperator)` (`MakieExt.jl:300-308`): the points, then arrows of
every column and its negative, `lengthscale = s/2`, `s = spacing(M)/min(Σ|colᵢ|/n)`. -/
instance instArrowsBundleFrame {b : GridBundle N P G} : MakiePlot .arrowsbundle (TensorField b E × Array (TensorField b F)) where
  plot c Mt a :=
    let a := { a with lengthscale := spacingOf Mt.1 / minColumnNorm Mt.2 / 2 }
    let d := dimOfWidth (FlatFiber.width E)
    let pts := Field.fiberPoints Mt.1
    let c := c.drawScatter pts none {}
    Mt.2.foldl (fun c t => let dirs := Field.fiberPoints t
      drawArrowsDim (drawArrowsDim c d pts dirs a) d pts (negPoints dirs) a) c
  dim _ := dimOfWidth (FlatFiber.width E)

/-- Julia `scaledfield(M, t)` (`MakieExt.jl:311-319`): `scaledarrows` of a vector field. -/
instance instScaledFieldVec {b : GridBundle N P G} : MakiePlot .scaledfield (TensorField b E × TensorField b F) where
  plot c Mt a := c.plot .scaledarrows Mt a
  dim _ := dimOfWidth (FlatFiber.width E)

/-- Julia `scaledfield(M, t::TensorOperator)`: by the number of columns, `scaledarrows` (1),
`scaledplanes` (2), `scaledspaces` (3). -/
instance instScaledFieldFrame {b : GridBundle N P G} : MakiePlot .scaledfield (TensorField b E × Array (TensorField b F)) where
  plot c Mt a :=
    if Mt.2.size == 1 then c.plot .scaledarrows Mt a
    else if Mt.2.size == 2 then c.plot .scaledplanes Mt a else c.plot .scaledspaces Mt a
  dim _ := dimOfWidth (FlatFiber.width E)

/-- Julia `scaledbundle(M, t)`: `arrowsbundle` of a vector field. -/
instance instScaledBundleVec {b : GridBundle N P G} : MakiePlot .scaledbundle (TensorField b E × TensorField b F) where
  plot c Mt a := c.plot .arrowsbundle Mt a
  dim _ := dimOfWidth (FlatFiber.width E)

/-- Julia `scaledbundle(M, t::TensorOperator)`: `arrowsbundle` (1 column), `planesbundle` (2),
`spacesbundle` (3). -/
instance instScaledBundleFrame {b : GridBundle N P G} : MakiePlot .scaledbundle (TensorField b E × Array (TensorField b F)) where
  plot c Mt a :=
    if Mt.2.size == 1 then c.plot .arrowsbundle Mt a
    else if Mt.2.size == 2 then c.plot .planesbundle Mt a else c.plot .spacesbundle Mt a
  dim _ := dimOfWidth (FlatFiber.width E)

end Planes

/-! ## `graylines` -/

/-- Julia `graylines(x, lw = 3)` (`MakieExt.jl:34-38`): `lines(x; colormap = :grays, linewidth = lw)`
then `lines!(x; color = :black, linestyle = :dash)`. -/
instance instGraylines {T : Type} [MakiePlot .lines T] : MakiePlot .graylines T where
  plot c t a :=
    let c := c.plot .lines t { a with colormap := Colormap.named "grays", linewidth := some (a.lw 3) }
    c.plot .lines t { a with color := some (.solid RGBA.black), linestyle := .dash }
  dim t := MakiePlot.dim .lines t

section Named

variable {T : Type}

/-- Cartan `arrowsbundle(M, t)`. -/
def arrowsbundle [MakiePlot .arrowsbundle T] (t : T) (a : Attrs := {}) : Canvas := plot .arrowsbundle t a
/-- Cartan `scaledfield(M, t)`. -/
def scaledfield [MakiePlot .scaledfield T] (t : T) (a : Attrs := {}) : Canvas := plot .scaledfield t a
/-- Cartan `scaledbundle(M, t)`. -/
def scaledbundle [MakiePlot .scaledbundle T] (t : T) (a : Attrs := {}) : Canvas := plot .scaledbundle t a
/-- Cartan `planes(M, t)`. -/
def planes [MakiePlot .planes T] (t : T) (a : Attrs := {}) : Canvas := plot .planes t a
/-- Cartan `spaces(M, t)`. -/
def spaces [MakiePlot .spaces T] (t : T) (a : Attrs := {}) : Canvas := plot .spaces t a
/-- Cartan `scaledplanes(M, t)`. -/
def scaledplanes [MakiePlot .scaledplanes T] (t : T) (a : Attrs := {}) : Canvas := plot .scaledplanes t a
/-- Cartan `scaledspaces(M, t)`. -/
def scaledspaces [MakiePlot .scaledspaces T] (t : T) (a : Attrs := {}) : Canvas := plot .scaledspaces t a
/-- Cartan `planesbundle(M, t)`. -/
def planesbundle [MakiePlot .planesbundle T] (t : T) (a : Attrs := {}) : Canvas := plot .planesbundle t a
/-- Cartan `spacesbundle(M, t)`. -/
def spacesbundle [MakiePlot .spacesbundle T] (t : T) (a : Attrs := {}) : Canvas := plot .spacesbundle t a
/-- Cartan `graylines(x)`. -/
def graylines [MakiePlot .graylines T] (t : T) (a : Attrs := {}) : Canvas := plot .graylines t a

end Named

end GrassmannPlot

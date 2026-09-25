import GrassmannPlot.Volume

/-!
# `variation`, `alteration`, `modification`: leaves of a field, overlaid or as animation frames

Cartan's drivers (`src/Cartan.jl:683-858`) plot the leaves of a grid field one after another:
`variation` along the last axis, `alteration` along the first, `modification` along the second.

* `variation!(v, fun, fun!)` (`Val(false)`): the first leaf with `fun`, the others added with
  `fun!` on the same axis: `overlay` (the Hopf fibration of `fiber.md:765-775` is
  `alteration!(hs, wireframe, wireframe!)`);
* `variation(v, t, fun, fun!)` (`Val(true)`): an animation, the axis emptied before every leaf and
  `sleep(t)` between them: `frames`, one canvas per leaf, for `LeanPlot.Figure.saveFrames` (Makie's
  reactivity and `sleep` are not modelled, DESIGN.md §0);
* the `n::Int` forms (2-D fields) resample the leaf axis to `n` points and interpolate the leaves
  between grid lines (`leaf(v, x::AbstractFloat)`): `variation!(v, fun, fun!, n)` draws the leaves at
  the first index, the interior resampled points and the last index (`Cartan.jl:703-717`);
  `alteration`/`modification` all `n` resampled points (`:793-803`, `:845-858`).
-/

namespace GrassmannPlot

open LeanPlot Cartan

/-- The axis a driver steps along. -/
inductive Driver where
  /-- `variation`: the last axis. -/
  | variation
  /-- `alteration`: the first axis. -/
  | alteration
  /-- `modification`: the second axis. -/
  | modification
  deriving BEq, Repr, Inhabited

section Two

variable {P G F : Type} [Inhabited G] [FlatFiber F] [LinearFiber F] {b : GridBundle 2 P G}

/-- The fixed axis of a driver on a 2-D field. -/
def Driver.axis2 : Driver → Fin 2
  | .alteration => 0
  | _ => 1

/-- A leaf of a 2-D field: a grid leaf (with the field's metric) or a leaf interpolated between
grid lines (Julia `leaf(v, x::AbstractFloat)`: a field over the other axis, induced metric). -/
abbrev Leaf2 (G F : Type) [FlatFiber F] := AnyField (GridBundle 1 Float G) F ⊕ AnyField (GridBundle 1 Float) F

/-- The leaves a driver visits on a 2-D field: every grid leaf, or with `n` the resampled
positions (interpolated leaves). -/
def leaves2 (d : Driver) (t : TensorField b F) (n : Option Nat := none) : Array (Leaf2 G F) :=
  let j := d.axis2
  let ax := b.space.axis j
  match n with
  | none => (Array.range ax.length).map fun i => .inl ⟨_, t.leaf i j⟩
  | some n =>
    let x := ax.resample n
    let interp : Array (Leaf2 G F) := (Array.range x.length).map fun i => .inr ⟨_, t.leafInterp (x.get i) j⟩
    if d == .variation then
      -- `variation(…, n)`: the first leaf, the interior resampled points, the last leaf
      #[.inl ⟨_, t.leaf 0 j⟩] ++ interp.extract 1 (x.length - 1) ++ #[.inl ⟨_, t.leaf (ax.length - 1) j⟩]
    else interp

variable (m : Method) [instG : ∀ b' : GridBundle 1 Float G, MakiePlot m (TensorField b' F)]
  [instI : ∀ b' : GridBundle 1 Float, MakiePlot m (TensorField b' F)]

/-- Draw one leaf with the method `m`. -/
def plotLeaf2 (c : Canvas) (l : Leaf2 G F) (a : Attrs) : Canvas :=
  match l with
  | .inl l => (instG l.base).plot c l.field a
  | .inr l => (instI l.base).plot c l.field a

/-- The axis dimension of a leaf. -/
def dimLeaf2 (l : Leaf2 G F) : Nat :=
  match l with
  | .inl l => (instG l.base).dim l.field
  | .inr l => (instI l.base).dim l.field

/-- Julia `variation!(v, fun, fun!)` and friends: every leaf drawn on one canvas with the Makie
function `m`. -/
def overlay2 (d : Driver) (c : Canvas) (t : TensorField b F) (a : Attrs := {}) (n : Option Nat := none) : Canvas :=
  (leaves2 d t n).foldl (fun c l => plotLeaf2 m c l a) c

/-- Julia `variation(v, t, fun, fun!)`: one fresh canvas per leaf (the animation frames). -/
def frames2 (d : Driver) (t : TensorField b F) (a : Attrs := {}) (n : Option Nat := none) : Array Canvas :=
  (leaves2 d t n).map fun l => plotLeaf2 m (Canvas.fresh (dimLeaf2 m l)) l a

end Two

section Three

variable {P G F : Type} [Inhabited G] [FlatFiber F] {b : GridBundle 3 P G}

/-- The fixed axis of a driver on a 3-D field. -/
def Driver.axis3 : Driver → Fin 3
  | .variation => 2
  | .alteration => 0
  | .modification => 1

/-- The leaves (2-D slices) a driver visits on a 3-D field. -/
def leaves3 (d : Driver) (t : TensorField b F) : Array (AnyField (GridBundle 2 (AffinePoint 2) G) F) :=
  let j := d.axis3
  (Array.range b.size[j]).map fun i => ⟨_, t.leafAt i j⟩

/-- Julia `alteration!(v, fun, fun!)` of a 3-D field: every 2-D leaf on one canvas (e.g.
`alteration!(hs, wireframe, wireframe!)`). -/
def overlay3 (m : Method) [inst : ∀ b' : GridBundle 2 (AffinePoint 2) G, MakiePlot m (TensorField b' F)]
    (d : Driver) (c : Canvas) (t : TensorField b F) (a : Attrs := {}) : Canvas :=
  (leaves3 d t).foldl (fun c l => (inst l.base).plot c l.field a) c

/-- Julia `alteration(v, t, fun, fun!)` of a 3-D field: one fresh canvas per leaf. -/
def frames3 (m : Method) [inst : ∀ b' : GridBundle 2 (AffinePoint 2) G, MakiePlot m (TensorField b' F)]
    (d : Driver) (t : TensorField b F) (a : Attrs := {}) : Array Canvas :=
  (leaves3 d t).map fun l => (inst l.base).plot (Canvas.fresh ((inst l.base).dim l.field)) l.field a

end Three

/-- Write animation frames `dir/frame_0001.png`, … (Makie's `record` without a video encoder). -/
def saveFrames (cs : Array Canvas) (dir : System.FilePath) (size : Nat × Nat := (600, 450)) (ext : String := "png") :
    IO Unit :=
  Figure.saveFrames (fun i => (cs.getD i default).figure size) cs.size dir ext

end GrassmannPlot

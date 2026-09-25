/-
Sampled curves and vector fields of versors (Grassmann.jl `src/Grassmann.jl:68, 312-314`
and `ext/GeometryBasicsExt.jl:28-33`): the README's `points`, `chainfield`,
`vectorfield`/`pointfield`.

* `points(f, r = -2π:0.0001:2π) = vector.(f.(r))` (`src/Grassmann.jl:68`): a curve sampled
  on a range. `points` returns the vectors (`Array (Chain V 1 Float)`, Julia's
  `Vector{Chain}`); `pointsCoords` returns the coordinates of chosen generators as one
  `FloatArray` each (Julia's `V(2,3,4).(points(f))`, what a plot consumes), without
  keeping the vectors.
* `chainfield(t, V = Manifold(t), W = V) = p -> V(vector(↓(↑((V∪Manifold(t))(p)) ⊘ t)))`
  (`src/Grassmann.jl:314`): the vector field of a versor `t` acting on points, a point `p`
  of the subspace `W` embedded in `t`'s space, lifted (`↑`), sandwiched (`x ⊘ t`),
  projected down (`↓`), and read in the subspace `V`.
* `vectorfield`/`pointfield` (GeometryBasics extension; `vectorfield = pointfield`): the
  same map on coordinate vectors (Julia's `Point`s), here `Values Float`.

Mesh interpolation (`scalarfield`, `chainfield(t, ϕ)`, `rectanglefield`) is not ported yet.
-/
import Grassmann.Composite.Project
import JuliaBase.Range

namespace Grassmann

open DirectSum StaticVectors AbstractTensors JuliaBase

namespace Fields

variable {V : TensorBundle}

/-- The grade-1 part of a sandwich result (Julia `vector(x)`), as a vector. -/
class VectorPart (Z : Type) (V : outParam TensorBundle) where
  /-- Julia `vector(z)`. -/
  vec : Z → Chain V 1 Float

instance : VectorPart (Chain V 1 Float) V := ⟨id⟩
instance : VectorPart (Multivector V Float) V := ⟨fun m => gradePart m 1⟩

/-- `2π` as Julia evaluates it. -/
def twoPi : Float := f64! 6.283185307179586

/-- Julia's default sample range of `points`, `-2π:0.0001:2π` (125 664 values). -/
def pointsRange : FloatArray := (colon (-twoPi) (f64! 0.0001) twoPi).toFloatArray

/-- The loop of `points`. -/
@[specialize] def pointsLoop (f : Float → Chain V 1 Float) (r : FloatArray) (i : Nat)
    (out : Array (Chain V 1 Float)) : Array (Chain V 1 Float) :=
  if h : i < r.size then pointsLoop f r (i + 1) (out.push (f r[i])) else out
termination_by r.size - i

/-- Julia `points(f, r)` (`src/Grassmann.jl:68`, `vector.(f.(r))`): the curve `f` sampled at
every value of `r` (default `pointsRange`). -/
@[inline] def points (f : Float → Chain V 1 Float) (r : FloatArray := pointsRange) : Array (Chain V 1 Float) :=
  pointsLoop f r 0 (Array.mkEmpty r.size)

/-- Push the coordinates `idx` (0-based chain indices) of `w` onto the columns. -/
@[inline] def pushCoords {n : Nat} (w : Values Float n) (idx : Array Nat) (cols : Array FloatArray) :
    Array FloatArray :=
  (idx.zip cols).map fun (k, c) => c.push (getD w k)

/-- The loop of `pointsCoords`. -/
@[specialize] def coordsLoop (f : Float → Chain V 1 Float) (idx : Array Nat) (r : FloatArray) (i : Nat)
    (cols : Array FloatArray) : Array FloatArray :=
  if h : i < r.size then coordsLoop f idx r (i + 1) (pushCoords (f r[i]).v idx cols) else cols
termination_by r.size - i

/-- The coordinates `idx` (0-based generator indices of `V`) of `points(f, r)`, one column
each: Julia `V(i₁+1, …).(points(f, r))` as plot data. -/
@[inline] def pointsCoords (f : Float → Chain V 1 Float) (idx : Array Nat) (r : FloatArray := pointsRange) :
    Array FloatArray :=
  coordsLoop f idx r 0 (idx.map fun _ => FloatArray.emptyWithCapacity r.size)

variable [Kernels V]

/-- The point map of a versor, `p ↦ vector(↓(↑p ⊘ t))` on vectors of `t`'s space. -/
@[inline] def versorMap {X Z : Type} [Sandwich (Chain V 1 Float) X Z] [VectorPart Z V] (t : X)
    (p : Chain V 1 Float) : Chain V 1 Float :=
  Chain.down (VectorPart.vec (Sandwich.sandwich (Chain.up p) t : Z))

/-- Julia `chainfield(t, V, W)` (`src/Grassmann.jl:314`): the field of the versor `t` on the
points of the subspace `W` (embedded in `t`'s space), read in the subspace `S`. -/
@[inline] def chainfield {X Z : Type} [Sandwich (Chain V 1 Float) X Z] [VectorPart Z V] (t : X)
    (S W : SubSpace V) (p : Chain (Forms.restrict V W.mask) 1 Float) :
    Chain (Forms.restrict V S.mask) 1 Float :=
  (versorMap t (Chain.embedSub W p)).project S

/-- Julia `chainfield(t)` on the whole space (`V = W = Manifold(t)`). -/
@[inline] def chainfieldFull {X Z : Type} [Sandwich (Chain V 1 Float) X Z] [VectorPart Z V] (t : X)
    (p : Chain V 1 Float) : Chain V 1 Float :=
  versorMap t p

/-- Julia `vectorfield(t, V, W)` (`ext/GeometryBasicsExt.jl:30`, `pointfield` is the same
function): `chainfield` on coordinate vectors (a `Point` of `W`'s coordinates in, of `S`'s
out). -/
@[inline] def vectorfield {X Z : Type} [Sandwich (Chain V 1 Float) X Z] [VectorPart Z V] (t : X)
    (S W : SubSpace V) (p : Values Float ((Layout.chain 1).size (Forms.restrict V W.mask).n)) :
    Values Float ((Layout.chain 1).size (Forms.restrict V S.mask).n) :=
  (chainfield t S W ⟨p⟩).v

/-- Julia `pointfield` (`vectorfield = pointfield`). -/
@[inline] def pointfield {X Z : Type} [Sandwich (Chain V 1 Float) X Z] [VectorPart Z V] (t : X)
    (S W : SubSpace V) (p : Values Float ((Layout.chain 1).size (Forms.restrict V W.mask).n)) :
    Values Float ((Layout.chain 1).size (Forms.restrict V S.mask).n) :=
  vectorfield t S W p

end Fields

end Grassmann

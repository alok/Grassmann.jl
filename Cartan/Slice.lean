import Cartan.Parameters

/-!
# Slices, leaves and boundary components of grid fields

Julia slices a field by calling its base: `t[i…, :, j…] = TensorField(base(t)(i…, :, j…),
fiber(t)[i…, :, j…])` (`Cartan.jl:228`), which slices the points *and* the quotient topology
(`subtopology`, MeshTopology `quotient.jl:579-752`): a slice keeps a gluing only when it maps the
slice to itself (the Möbius centerline is closed, the other rows open).

* One kept axis gives a 1-D field with *real* points (Julia returns the range itself), the
  `IntervalMap` the curve algorithms of the grid stage dispatch on: `sliceLine`, `leaf`.
* Several kept axes give a product grid of the kept axes: `slice`, `sliceAt`, `leafAt`.
* `boundaryComponents` (`Cartan.jl:610-661`): the `2N` leaves at depth `n` from each face, in the
  order (axis 1 low, axis 1 high, axis 2 low, …).
* `extract` (`Cartan.jl:253-256`): the last-axis coordinate paired with the slice there.
* `variation`, `alteration`, `modification` (`Cartan.jl:663-681`): the leaves along the last,
  first and second axis, with their coordinates (Julia's field of fields; its animation drivers,
  which `display` and `sleep`, are not ported).

Indices are 0-based (Julia's `leaf(a, 2)` is `leaf a 1` here). Leaves at different positions
live over different bases, so collections of them are `AnyField`s.
-/

namespace Cartan

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase MeshTopology

namespace TensorField

variable {N : Nat} {P G : Type} [Inhabited G] {F : Type} [FlatFiber F]

/-- Julia `t[i…, :, …, :, j…]` with colons at the axes `ks` (ascending) and the other axes at the
0-based indices `fixed` (entries of kept axes ignored): the field over the sub-grid. -/
def slice {K : Nat} {b : GridBundle N P G} (t : TensorField b F) (ks : Vector (Fin N) K)
    (fixed : Vector Nat N) : TensorField (b.slice ks fixed) F :=
  let idx := b.sliceIndices ks fixed
  ofFn _ fun k => t.get idx[k]!

/-- Julia `t[i…, :, j…]` with one colon at axis `a`: the 1-D field along that axis, over real
points (an `IntervalMap`). -/
def sliceLine {b : GridBundle N P G} (t : TensorField b F) (a : Fin N) (fixed : Vector Nat N) :
    TensorField (b.sliceLine a fixed) F :=
  let idx := b.sliceIndices #v[a] fixed
  ofFn _ fun k => t.get idx[k]!

/-- Julia `t[…, i, …]` fixing axis `a` at the 0-based index `i` (a product grid of the other
axes; for a 2-D field use `leaf`). -/
def sliceAt {b : GridBundle (N + 1) P G} (t : TensorField b F) (a : Fin (N + 1)) (i : Nat) :
    TensorField (b.sliceAt a i) F :=
  t.slice (GridBundle.otherAxes a) (Vector.replicate (N + 1) i)

/-- The axis a 2-D leaf keeps: the one not fixed. -/
@[inline] def otherAxis2 (j : Fin 2) : Fin 2 := ⟨1 - j.1, by omega⟩

/-- Julia `leaf(m::RectangleMap, i, j = 2)` (`grid.jl:147`): the 1-D field fixing axis `j`
(0-based, default the last) at the 0-based index `i`, i.e. `m[:, i]` for `j = 1` and `m[i, :]`
for `j = 0`. -/
def leaf {b : GridBundle 2 P G} (t : TensorField b F) (i : Nat) (j : Fin 2 := 1) :
    TensorField (b.sliceLine (otherAxis2 j) (Vector.replicate 2 i)) F :=
  t.sliceLine (otherAxis2 j) (Vector.replicate 2 i)

/-- Julia `leaf(m, i, j = N)` for an `(N+1)`-dimensional field, `N ≥ 2` (`grid.jl:158-256`): the
`N`-dimensional slice fixing axis `j` (0-based, default the last) at the 0-based index `i`. -/
def leafAt {b : GridBundle (N + 1) P G} (t : TensorField b F) (i : Nat)
    (j : Fin (N + 1) := Fin.last N) : TensorField (b.sliceAt j i) F :=
  t.sliceAt j i

/-- Julia `boundarycomponents(f, n)` for a 1-D field (`Cartan.jl:614`): the local tensors at depth
`n` (0-based) from both ends. -/
def boundaryComponents1 {M : Type} [FrameBundle M] {m : M} {Q : Type} [Coordinates M P Q]
    (t : TensorField m F) (n : Nat := 0) :
    LocalTensor (Coordinate P Q) F × LocalTensor (Coordinate P Q) F :=
  (t.localAt n, t.localAt (card m - 1 - n))

/-- Julia `boundarycomponents(f, n)` for a 2-D field (`Cartan.jl:615-620`): the leaves at depth `n`
(0-based) from the four faces, `[axis 1 low, axis 1 high, axis 2 low, axis 2 high]`, where the
faces of axis 1 are the rows `f[n, :]`, `f[end-n, :]`. -/
def boundaryComponents {b : GridBundle 2 P G} (t : TensorField b F) (n : Nat := 0) :
    Array (AnyField (GridBundle 1 Float G) F) :=
  let s := b.size
  #[⟨_, t.leaf n 0⟩, ⟨_, t.leaf (s[0] - 1 - n) 0⟩, ⟨_, t.leaf n 1⟩, ⟨_, t.leaf (s[1] - 1 - n) 1⟩]

/-- Julia `boundarycomponents(f, n)` for an `(N+1)`-dimensional field, `N ≥ 2`
(`Cartan.jl:621-653`): the `2(N+1)` leaves at depth `n` (0-based), ordered by axis, low face
first. (Julia declares a length-8 vector for the ten 5-D leaves and throws, B12.) -/
def boundaryComponentsN {b : GridBundle (N + 1) P G} (t : TensorField b F) (n : Nat := 0) :
    Array (AnyField (GridBundle N (AffinePoint N) G) F) :=
  (List.finRange (N + 1)).toArray.flatMap fun a =>
    #[⟨_, t.leafAt n a⟩, ⟨_, t.leafAt (b.size[a] - 1 - n) a⟩]

/-- Julia `extract(x, i)` for a 2-D field (`Cartan.jl:253`): the last-axis coordinate `i` (0-based)
paired with the slice `x[:, i]`. -/
def extract {b : GridBundle 2 P G} (t : TensorField b F) (i : Nat) :
    LocalTensor Float (TensorField (b.sliceLine (otherAxis2 1) (Vector.replicate 2 i)) F) :=
  ⟨(b.space.axis 1).get i, t.leaf i 1⟩

/-- Julia `extract(x, i)` for an `(N+1)`-dimensional field, `N ≥ 2` (`Cartan.jl:254-256`). -/
def extractN {b : GridBundle (N + 1) P G} (t : TensorField b F) (i : Nat) :
    LocalTensor Float (TensorField (b.sliceAt (Fin.last N) i) F) :=
  ⟨(b.space.axis (Fin.last N)).get i, t.leafAt i⟩

/-- Julia `Variation(cod)` (`Cartan.jl:663-666`): the leaves along the last axis of a 2-D field,
paired with the last-axis coordinates (Julia's field of fields over that axis). -/
def variation {b : GridBundle 2 P G} (t : TensorField b F) :
    Array (LocalTensor Float (AnyField (GridBundle 1 Float G) F)) :=
  let ax := b.space.axis 1
  (Array.range ax.length).map fun i => ⟨ax.get i, ⟨_, t.leaf i 1⟩⟩

/-- Julia `alteration(cod)` (`Cartan.jl:673-676`): the leaves along the first axis. -/
def alteration {b : GridBundle 2 P G} (t : TensorField b F) :
    Array (LocalTensor Float (AnyField (GridBundle 1 Float G) F)) :=
  let ax := b.space.axis 0
  (Array.range ax.length).map fun i => ⟨ax.get i, ⟨_, t.leaf i 0⟩⟩

/-- Julia `modification(cod)` (`Cartan.jl:678-681`): the leaves along the second axis (for a 2-D
field, the same as `variation`). -/
def modification {b : GridBundle 2 P G} (t : TensorField b F) :
    Array (LocalTensor Float (AnyField (GridBundle 1 Float G) F)) := t.variation

/-! ## Re-gluing (Julia `XTopology(t::TensorField)`, `Cartan.jl:313-318`) -/

/-- Julia `t(i::ImmersedTopology)` for a grid field (`Cartan.jl:312`): the same fibers over the same
points glued by `top`. -/
def withTop {b : GridBundle N P G} (t : TensorField b F) (top : QuotientTopology N)
    (h : top.size = b.space.size) : TensorField (b.withTop top h) F :=
  ⟨t.data, t.size_data, t.range?⟩

/-- Julia `TorusTopology(t)`. -/
def torus {b : GridBundle N P G} (t : TensorField b F) : TensorField b.torus F := ⟨t.data, t.size_data, t.range?⟩
/-- Julia `MirrorTopology(t)`. -/
def mirror {b : GridBundle N P G} (t : TensorField b F) : TensorField b.mirror F := ⟨t.data, t.size_data, t.range?⟩
/-- Julia `ClampedTopology(t)`. -/
def clamped {b : GridBundle N P G} (t : TensorField b F) : TensorField b.clamped F := ⟨t.data, t.size_data, t.range?⟩
/-- Julia `SphereTopology(t)`. -/
def sphere {b : GridBundle N P G} (t : TensorField b F) : TensorField b.sphere F := ⟨t.data, t.size_data, t.range?⟩
/-- Julia `BallTopology(t)`. -/
def ball {b : GridBundle N P G} (t : TensorField b F) : TensorField b.ball F := ⟨t.data, t.size_data, t.range?⟩
/-- Julia `OpenTopology(t)`. -/
def openTop {b : GridBundle N P G} (t : TensorField b F) : TensorField b.openTop F := ⟨t.data, t.size_data, t.range?⟩

end TensorField

end Cartan

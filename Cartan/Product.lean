import Cartan.Algebra

/-!
# Fiber products of bases, `TimeParameter`, and Julia's accessor names

* `FiberProductBundle` (Cartan.jl `src/fiber.jl:819-848`): a base times a 1-D coordinate vector
  (`sb ⊕ (0:0.5:1)`), the space-time domain of a time-dependent field on a mesh. Its point at
  `(i, j)` is `points(s)[i] ⧺ g[j]` (the space point with the time appended, a `Chain` one
  dimension up), with the induced metric; its shape is `(length(s), length(g))`.
* `TimeParameter(m, time)` (`fiber.jl:859-865`): the field of times over `m ⊕ time`.
* `Immersion`: Julia `immersion(m)` of a base (its topology); with it and the classes of
  `Cartan.Bundle`, a field has Julia's accessors `base`, `points`, `immersion` and `metricAt`.
-/

namespace Cartan

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase MeshTopology

/-- Julia `FiberProductBundle{P}(s, g)` of a base `s` and a 1-D coordinate vector `g`
(`fiber.jl:819-848`). -/
structure FiberProductBundle (M : Type) where
  /-- The space base (Julia `m.s`). -/
  space : M
  /-- The appended axis (Julia `m.g`, a 1-D `ProductSpace`). -/
  axis : Axis

namespace FiberProductBundle

variable {M P : Type} [FrameBundle M] [FlatFiber P] [Coordinates M P Induced]

/-- Julia `s ⊕ g` of a simplex (or any) base and a vector (`fiber.jl:827-834`). -/
def ofBase (s : M) (g : Axis) : FiberProductBundle M := ⟨s, g⟩

instance : FrameBundle (FiberProductBundle M) := ⟨fun m => card m.space * m.axis.length⟩

/-- Julia `m[i, j] = Coordinate(points(s)[i] ⧺ g[j], InducedMetric())` (`fiber.jl:847`): the space
point followed by the axis coordinate, a vector of the Euclidean algebra one dimension up. -/
def pointAt (m : FiberProductBundle M) (i j : Nat) :
    Chain (TensorBundle.euclidean (FlatFiber.width P + 1)) 1 Float :=
  let buf := (FlatFiber.push FloatArray.empty (Coordinates.point m.space i)).push (m.axis.get j)
  ⟨Values.ofFn fun k => buf.get! k.1⟩

instance : Coordinates (FiberProductBundle M)
    (Chain (TensorBundle.euclidean (FlatFiber.width P + 1)) 1 Float) Induced where
  point m k := let c := card m.space; m.pointAt (k % c) (k / c)
  metricAt _ _ := {}

end FiberProductBundle

/-- Julia `TimeParameter(m, time)` (`fiber.jl:859-861`): over `m ⊕ time`, the fiber at `(j, l)` is
`time[l]`. -/
def timeParameter {M : Type} [FrameBundle M] (m : M) (time : Axis) :
    TensorField (FiberProductBundle.ofBase m time) Float :=
  TensorField.ofFn _ fun k => time.get (k / card m)

/-- Julia `TimeParameter(m, fixed, time)` (`fiber.jl:862-864`): the time parameter of the
sub-mesh on the vertices `fixed` (1-based). -/
def timeParameterOn {n : Nat} {P G : Type} (m : SimplexBundle n P G) (fixed : Array Nat) (time : Axis) :
    TensorField (FiberProductBundle.ofBase (m.byVertices fixed) time) Float :=
  timeParameter (m.byVertices fixed) time

/-! ## Julia's accessors -/

/-- Julia `immersion(m)`: the topology of a base. -/
class Immersion (M : Type) (T : outParam Type) where
  /-- Julia `immersion(m)`. -/
  immersion : M → T

instance {N : Nat} {P G : Type} : Immersion (GridBundle N P G) (QuotientTopology N) := ⟨(·.top)⟩
instance {n : Nat} {P G : Type} : Immersion (SimplexBundle n P G) (SimplexTopology n) := ⟨(·.top)⟩
instance {n : Nat} {P G : Type} : Immersion (FaceBundle n P G) (SimplexTopology n) := ⟨(·.top)⟩

namespace TensorField

variable {M F : Type} [FrameBundle M] [FlatFiber F] {m : M}

/-- Julia `immersion(t) = immersion(base(t))` (`Cartan.jl:201-206`). -/
@[inline] def immersion {T : Type} [Immersion M T] (_ : TensorField m F) : T := Immersion.immersion m

/-- Julia `metricextensor(t)[i+1]`. -/
@[inline] def metricAt {P G : Type} [Coordinates M P G] (_ : TensorField m F) (i : Nat) : G :=
  Coordinates.metricAt m i

/-- Julia `points(t)[i+1]`. -/
@[inline] def pointAt {P G : Type} [Coordinates M P G] (_ : TensorField m F) (i : Nat) : P :=
  Coordinates.point m i

end TensorField

/-- Julia `show(Global{N}(g))` (`topology.jl:269`): `Global{2}(InducedMetric())`. -/
def MetricStore.showGlobal {G : Type} [ShowFiber G] (N : Nat) : MetricStore G → String
  | .global g => s!"Global\{{N}}({showFiber false g})"
  | .pointwise a => "[" ++ ", ".intercalate (a.toList.map (showFiber false)) ++ "]"

end Cartan
